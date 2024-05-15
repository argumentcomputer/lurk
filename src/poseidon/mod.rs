use core::borrow::Borrow;
use core::mem::size_of;
use p3_air::AirBuilder;
use p3_air::{Air, BaseAir};
use p3_field::AbstractField;
use p3_matrix::Matrix;
use p3_poseidon2::matmul_internal;
use std::marker::PhantomData;

use loam_macros::AlignedBorrow;

use self::config::PoseidonConfig;
use self::util::apply_m_4;

mod config;
mod constants;
mod util;

/// A chip that implements addition for the opcode ADD.
pub struct Poseidon2Chip<const WIDTH: usize, C>
where
    C: PoseidonConfig<WIDTH>,
{
    _p: PhantomData<C>,
}

/// The column layout for the chip.
#[derive(AlignedBorrow, Clone, Copy)]
#[repr(C)]
pub struct Poseidon2Cols<T, const WIDTH: usize, C>
where
    C: PoseidonConfig<WIDTH>,
{
    pub input: [T; WIDTH],
    pub rounds: [T; 31],
    pub add_rc: [T; WIDTH],
    pub sbox_deg_3: [T; WIDTH],
    pub sbox_deg_7: [T; WIDTH],
    pub output: [T; WIDTH],
    pub is_initial: T,
    pub is_internal: T,
    pub is_external: T,
    _p: PhantomData<C>,
}

impl<F, const WIDTH: usize, C> BaseAir<F> for Poseidon2Chip<WIDTH, C>
where
    C: PoseidonConfig<WIDTH>,
{
    fn width(&self) -> usize {
        size_of::<Poseidon2Cols<u8, WIDTH, C>>()
    }
}

impl<AB, const WIDTH: usize, C> Air<AB> for Poseidon2Chip<WIDTH, C>
where
    AB: AirBuilder,
    C: PoseidonConfig<WIDTH>,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &Poseidon2Cols<AB::Var, WIDTH, C> = (*local).borrow();

        let rounds_f = C::R_F;
        let rounds_p = C::R_P;
        let rounds = rounds_f + rounds_p;

        // Convert the u32 round constants to field elements.
        let constants: Vec<[AB::F; WIDTH]> = C::round_constants()
            .into_iter()
            .map(|round| round.map(AB::F::from_wrapped_u32))
            .collect();

        // Apply the round constants.
        //
        // Initial Layer: Don't apply the round constants.
        // External Layers: Apply the round constants.
        // Internal Layers: Only apply the round constants to the first element.
        for i in 0..WIDTH {
            let mut result: AB::Expr = local.input[i].into();
            for r in 0..rounds {
                if i == 0 {
                    result += local.rounds[r + 1]
                        * constants[r][i]
                        * (local.is_external + local.is_internal);
                } else {
                    result += local.rounds[r + 1] * constants[r][i] * local.is_external;
                }
            }
            builder.assert_eq(result, local.add_rc[i]);
        }

        // Apply the sbox.
        //
        // To differentiate between external and internal layers, we use a masking operation
        // to only apply the state change to the first element for internal layers.
        for i in 0..WIDTH {
            let sbox_deg_3 = local.add_rc[i] * local.add_rc[i] * local.add_rc[i];
            builder.assert_eq(sbox_deg_3, local.sbox_deg_3[i]);
            let sbox_deg_7 = local.sbox_deg_3[i] * local.sbox_deg_3[i] * local.add_rc[i];
            builder.assert_eq(sbox_deg_7, local.sbox_deg_7[i]);
        }
        let sbox_result: [AB::Expr; WIDTH] = local
            .sbox_deg_7
            .iter()
            .enumerate()
            .map(|(i, x)| {
                // The masked first result of the sbox.
                //
                // Initial Layer: Pass through the result of the round constant layer.
                // External Layer: Pass through the result of the sbox layer.
                // Internal Layer: Pass through the result of the sbox layer.
                if i == 0 {
                    local.is_initial * local.add_rc[i] + (AB::Expr::one() - local.is_initial) * *x
                }
                // The masked result of the rest of the sbox.
                //
                // Initial layer: Pass through the result of the round constant layer.
                // External layer: Pass through the result of the sbox layer.
                // Internal layer: Pass through the result of the round constant layer.
                else {
                    (local.is_initial + local.is_internal) * local.add_rc[i]
                        + (AB::Expr::one() - (local.is_initial + local.is_internal)) * *x
                }
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // EXTERNAL LAYER + INITIAL LAYER
        {
            // First, we apply M_4 to each consecutive four elements of the state.
            // In Appendix B's terminology, this replaces each x_i with x_i'.
            let mut state: [AB::Expr; WIDTH] = sbox_result.clone();
            for i in (0..WIDTH).step_by(4) {
                apply_m_4(&mut state[i..i + 4]);
            }

            // Now, we apply the outer circulant matrix (to compute the y_i values).
            //
            // We first precompute the four sums of every four elements.
            let sums: [AB::Expr; 4] = core::array::from_fn(|k| {
                (0..WIDTH)
                    .step_by(4)
                    .map(|j| state[j + k].clone())
                    .sum::<AB::Expr>()
            });

            // The formula for each y_i involves 2x_i' term and x_j' terms for each j that equals i mod 4.
            // In other words, we can add a single copy of x_i' to the appropriate one of our precomputed sums.
            for i in 0..WIDTH {
                state[i] += sums[i % 4].clone();
                builder
                    .when(local.is_external + local.is_initial)
                    .assert_eq(state[i].clone(), local.output[i]);
            }
        }

        // INTERNAL LAYER
        {
            // Use a simple matrix multiplication as the permutation.
            let mut state: [AB::Expr; WIDTH] = sbox_result.clone();
            let matmul_constants: [<<AB as AirBuilder>::Expr as AbstractField>::F; WIDTH] =
                C::MATRIX_DIAG
                    .map(<<AB as AirBuilder>::Expr as AbstractField>::F::from_wrapped_u32);
            matmul_internal(&mut state, matmul_constants);
            for i in 0..WIDTH {
                builder
                    .when(local.is_internal)
                    .assert_eq(state[i].clone(), local.output[i]);
            }
        }

        // Range check all flags.
        for i in 0..local.rounds.len() {
            builder.assert_bool(local.rounds[i]);
        }
        builder.assert_bool(local.is_initial);
        builder.assert_bool(local.is_external);
        builder.assert_bool(local.is_internal);
        builder.assert_bool(local.is_initial + local.is_external + local.is_internal);

        // Constrain the initial flag.
        builder.assert_eq(local.is_initial, local.rounds[0]);

        // Constrain the external flag.
        let is_external_first_half = (0..4).map(|i| local.rounds[i + 1].into()).sum::<AB::Expr>();
        let is_external_second_half = (26..30)
            .map(|i| local.rounds[i + 1].into())
            .sum::<AB::Expr>();
        builder.assert_eq(
            local.is_external,
            is_external_first_half + is_external_second_half,
        );

        // Constrain the internal flag.
        let is_internal = (4..26)
            .map(|i| local.rounds[i + 1].into())
            .sum::<AB::Expr>();
        builder.assert_eq(local.is_internal, is_internal);
    }
}

#[cfg(test)]
mod tests {
    use self::config::BabyBearConfig4;

    use super::*;

    use itertools::Itertools;
    use std::borrow::Borrow;
    use std::time::Instant;

    use p3_baby_bear::{BabyBear, DiffusionMatrixBabybear};
    use p3_field::AbstractField;
    use p3_matrix::{dense::RowMajorMatrix, Matrix};
    use p3_poseidon2::Poseidon2;
    use p3_poseidon2::Poseidon2ExternalMatrixGeneral;
    use p3_symmetric::Permutation;

    fn generate_trace_with<const WIDTH: usize>() {
        // TODO: Fix this test
        let config = BabyBearConfig4 {};
        let chip = Poseidon2Chip::<4, BabyBearConfig4> { _p: PhantomData };
        let test_inputs = vec![
            [BabyBear::from_canonical_u32(1); WIDTH],
            [BabyBear::from_canonical_u32(2); WIDTH],
            [BabyBear::from_canonical_u32(3); WIDTH],
            [BabyBear::from_canonical_u32(4); WIDTH],
        ];

        // let gt: Poseidon2<
        //     BabyBear,
        //     Poseidon2ExternalMatrixGeneral,
        //     DiffusionMatrixBabybear,
        //     WIDTH,
        //     7,
        // > = inner_perm();

        // let expected_outputs = test_inputs
        //     .iter()
        //     .map(|input| gt.permute(*input))
        //     .collect::<Vec<_>>();
    }

    #[test]
    fn generate_trace() {
        generate_trace_with::<4>();
    }

    // #[test]
    // fn prove_babybear() {
    //     let config = BabyBearPoseidon2::new();
    //     let mut challenger = config.challenger();

    //     let chip = Poseidon2Chip;

    //     let test_inputs = (0..16)
    //         .map(|i| [BabyBear::from_canonical_u32(i); WIDTH])
    //         .collect_vec();

    //     let mut input_exec = ExecutionRecord::<BabyBear>::default();
    //     for input in test_inputs.iter().cloned() {
    //         input_exec.poseidon2_events.push(Poseidon2Event { input });
    //     }
    //     let trace: RowMajorMatrix<BabyBear> =
    //         chip.generate_trace(&input_exec, &mut ExecutionRecord::<BabyBear>::default());
    //     println!(
    //         "trace dims is width: {:?}, height: {:?}",
    //         trace.width(),
    //         trace.height()
    //     );

    //     let start = Instant::now();
    //     let proof = uni_stark_prove(&config, &chip, &mut challenger, trace);
    //     let duration = start.elapsed().as_secs_f64();
    //     println!("proof duration = {:?}", duration);

    //     let mut challenger: p3_challenger::DuplexChallenger<
    //         BabyBear,
    //         Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, DiffusionMatrixBabybear, 16, 7>,
    //         16,
    //     > = config.challenger();
    //     let start = Instant::now();
    //     uni_stark_verify(&config, &chip, &mut challenger, &proof)
    //         .expect("expected proof to be valid");

    //     let duration = start.elapsed().as_secs_f64();
    //     println!("verify duration = {:?}", duration);
    // }
}
