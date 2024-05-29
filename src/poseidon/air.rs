//! This module defines the AIR constraints for the Poseidon2Chip
use core::mem::size_of;

use std::borrow::Borrow;

use hybrid_array::{typenum::Unsigned, Array};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::AbstractField;
use p3_matrix::Matrix;

use super::{
    columns::Poseidon2Cols,
    config::PoseidonConfig,
    util::{apply_m_4, matmul_generic},
    Poseidon2Chip,
};

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
        let rounds = <C::R as Unsigned>::USIZE;

        // Convert the u32 round constants to field elements.
        let full_constants: Vec<_> = C::full_round_constants()
            .into_iter()
            .map(|round| round.map(AB::F::from_wrapped_u32))
            .collect();

        let partial_constants: Vec<_> = C::partial_round_constants()
            .into_iter()
            .map(AB::F::from_wrapped_u32)
            .collect();

        // Apply the round constants.
        // External Layers: Apply the round constants.
        // Internal Layers: Only apply the round constants to the first element.
        for i in 0..width {
            let mut result: AB::Expr = local.input[i].into();
            for r in 0..rounds {
                let offset = rounds_f / 2;
                let is_first_full_rounds = r < offset;
                let is_second_full_rounds = r >= offset + rounds_p;
                // let is_external = is_first_full_rounds || is_second_full_rounds;
                if i == 0 {
                    if is_first_full_rounds {
                        result += local.rounds[r] * full_constants[r][i];
                    } else if is_second_full_rounds {
                        result += local.rounds[r] * full_constants[r + offset][i];
                    } else {
                        result += local.rounds[r] * partial_constants[r - offset];
                    }
                } else {
                    // FIX: Not sure this is right
                    if is_first_full_rounds {
                        result += local.rounds[r] * full_constants[r][i] // * local.is_external;
                    } else if is_second_full_rounds {
                        result += local.rounds[r] * full_constants[r + offset][i]
                    // * local...
                    } else {
                        result += local.rounds[r].into() // * partial_constants[r] * local.is_external;
                    }
                }
            }
            builder.assert_eq(result, local.add_rc[i]);
        }

        // Apply the sbox.
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
                // All Layers: Pass through the result of the sbox layer.
                if i == 0 {
                    (*x).into()
                }
                // The masked result of the rest of the sbox.
                //
                // External layer: Pass through the result of the sbox layer.
                // Internal layer: Pass through the result of the round constant layer.
                else {
                    local.is_internal * local.add_rc[i] + (AB::Expr::one() - local.is_internal) * *x
                }
            })
            .collect::<Vec<_>>();

        // EXTERNAL LAYER
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
                    .when(local.is_external)
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
            matmul_generic(&mut state, matmul_constants);
            for i in 0..width {
                builder
                    .when(local.is_internal)
                    .assert_eq(state[i].clone(), local.output[i]);
            }
        }

        // When not the final layer, constrain the output to be the input of the next layer.
        let next_input = main.row_slice(1);
        let next_input: &Poseidon2Cols<AB::Var, C> = (*next_input).borrow();
        for i in 0..width {
            builder
                .when(AB::Expr::one() - local.rounds[width - 1])
                .assert_eq(local.output[i], next_input.input[i]);
        }

        // Range check all flags.
        for i in 0..local.rounds.len() {
            builder.assert_bool(local.rounds[i]);
        }
        builder.assert_bool(local.is_external);
        builder.assert_bool(local.is_internal);
        builder.assert_bool(local.is_external + local.is_internal);

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
