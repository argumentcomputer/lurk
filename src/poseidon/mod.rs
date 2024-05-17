use core::borrow::Borrow;
use core::mem::size_of;
use hybrid_array::{typenum::Unsigned, Array};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::AbstractField;
use p3_matrix::Matrix;
use std::marker::PhantomData;

use loam_macros::AlignedBorrow;

use self::{
    config::PoseidonConfig,
    util::{apply_m_4, matmul_generic},
};

mod config;
mod constants;
mod util;

/// A chip that implements addition for the opcode ADD.
pub struct Poseidon2Chip<C>
where
    C: PoseidonConfig,
{
    _p: PhantomData<C>,
}

/// The column layout for the chip.
#[derive(AlignedBorrow, Clone)]
#[repr(C)]
pub struct Poseidon2Cols<T, C>
where
    C: PoseidonConfig,
{
    pub input: Array<T, C::WIDTH>,
    pub rounds: Array<T, C::R>,
    pub add_rc: Array<T, C::WIDTH>,
    pub sbox_deg_3: Array<T, C::WIDTH>,
    pub sbox_deg_7: Array<T, C::WIDTH>,
    pub output: Array<T, C::WIDTH>,
    pub is_initial: T,
    pub is_internal: T,
    pub is_external: T,
    _p: PhantomData<C>,
}

impl<F, C> BaseAir<F> for Poseidon2Chip<C>
where
    C: PoseidonConfig,
{
    fn width(&self) -> usize {
        size_of::<Poseidon2Cols<u8, C>>()
    }
}

impl<AB, C> Air<AB> for Poseidon2Chip<C>
where
    AB: AirBuilder,
    C: PoseidonConfig,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &Poseidon2Cols<AB::Var, C> = (*local).borrow();

        let width = <C::WIDTH as Unsigned>::USIZE;
        let rounds_f = C::R_F;
        let rounds_p = C::R_P;
        let rounds = <C::R as Unsigned>::USIZE - 1;

        // Convert the u32 round constants to field elements.
        let constants: Vec<_> = C::round_constants()
            .into_iter()
            .map(|round| round.map(AB::F::from_wrapped_u32))
            .collect();

        // Apply the round constants.
        //
        // Initial Layer: Don't apply the round constants.
        // External Layers: Apply the round constants.
        // Internal Layers: Only apply the round constants to the first element.
        for i in 0..width {
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
        for i in 0..width {
            let sbox_deg_3 = local.add_rc[i] * local.add_rc[i] * local.add_rc[i];
            builder.assert_eq(sbox_deg_3, local.sbox_deg_3[i]);
            let sbox_deg_7 = local.sbox_deg_3[i] * local.sbox_deg_3[i] * local.add_rc[i];
            builder.assert_eq(sbox_deg_7, local.sbox_deg_7[i]);
        }
        let sbox_result: Vec<AB::Expr> = local
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
            .collect::<Vec<_>>();

        // EXTERNAL LAYER + INITIAL LAYER
        {
            // First, we apply M_4 to each consecutive four elements of the state.
            // In Appendix B's terminology, this replaces each x_i with x_i'.
            let mut state: Vec<_> = sbox_result.clone();
            for i in (0..width).step_by(4) {
                apply_m_4(&mut state[i..i + 4]);
            }

            // Now, we apply the outer circulant matrix (to compute the y_i values).
            //
            // We first precompute the four sums of every four elements.
            let sums: [AB::Expr; 4] = core::array::from_fn(|k| {
                (0..width)
                    .step_by(4)
                    .map(|j| state[j + k].clone())
                    .sum::<AB::Expr>()
            });

            // The formula for each y_i involves 2x_i' term and x_j' terms for each j that equals i mod 4.
            // In other words, we can add a single copy of x_i' to the appropriate one of our precomputed sums.
            for i in 0..width {
                state[i] += sums[i % 4].clone();
                builder
                    .when(local.is_external + local.is_initial)
                    .assert_eq(state[i].clone(), local.output[i]);
            }
        }

        // INTERNAL LAYER
        {
            // Use a simple matrix multiplication as the permutation.
            let mut state: Vec<AB::Expr> = sbox_result.clone();
            let matmul_constants: Array<<<AB as AirBuilder>::Expr as AbstractField>::F, C::WIDTH> =
                C::matrix_diag()
                    .map(<<AB as AirBuilder>::Expr as AbstractField>::F::from_wrapped_u32);
            matmul_generic(&mut state, matmul_constants); // matmul_internal(&mut state, matmul_constants); // TODO: Fix this
            for i in 0..width {
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

        let external_end = rounds_f / 2;
        let internal_end = external_end + rounds_p;

        // Constrain the external flag.
        let is_external_first_half = (0..external_end)
            .map(|i| local.rounds[i + 1].into())
            .sum::<AB::Expr>();
        let is_external_second_half = (internal_end..rounds)
            .map(|i| local.rounds[i + 1].into())
            .sum::<AB::Expr>();
        builder.assert_eq(
            local.is_external,
            is_external_first_half + is_external_second_half,
        );

        // Constrain the internal flag.
        let is_internal = (external_end..internal_end)
            .map(|i| local.rounds[i + 1].into())
            .sum::<AB::Expr>();
        builder.assert_eq(local.is_internal, is_internal);
    }
}

#[cfg(test)]
mod tests {
    use crate::air::DebugConstraintBuilder;

    use super::*;

    use self::config::{BabyBearConfig16, BabyBearConfig4};

    use hybrid_array::{typenum::*, ArraySize};
    use itertools::Itertools;
    use std::{borrow::Borrow, time::Instant};
    use wp1_core::runtime::ExecutionRecord;

    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::{
        dense::{DenseMatrix, RowMajorMatrix},
        stack::VerticalPair,
        Matrix,
    };
    use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
    use p3_symmetric::Permutation;

    fn generate_trace_with<Config: PoseidonConfig>() {
        let chip = Poseidon2Chip::<Config> { _p: PhantomData };

        let first_values = [0; 52].map(BabyBear::from_canonical_u32);
        let second_values = [0; 7].map(BabyBear::from_canonical_u32);

        let first: DenseMatrix<BabyBear, &[_]> = DenseMatrix::new(first_values.as_slice(), 52);
        let second: DenseMatrix<_, &[_]> = DenseMatrix::new(second_values.as_slice(), 7);

        let main = VerticalPair::new(first, second);

        let mut builder = DebugConstraintBuilder::new(main, 3, 3);

        // dbg!(BaseAir::<BabyBear>::width(&chip));

        chip.eval(&mut builder);

        // let test_inputs = vec![];

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
        generate_trace_with::<BabyBearConfig4>();
        generate_trace_with::<BabyBearConfig16>();
    }

    fn prove_babybear_with() {
        todo!()
    }

    #[test]
    fn prove_babybear() {
        prove_babybear_with()
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
