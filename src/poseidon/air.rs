//! This module defines the AIR constraints for the Poseidon2Chip

use core::mem::size_of;

use std::iter::zip;

use hybrid_array::{typenum::Unsigned, Array};
use itertools::izip;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;

use super::{
    columns::Poseidon2Cols,
    config::PoseidonConfig,
    util::{apply_m_4, matmul_internal},
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
    C: PoseidonConfig<F = AB::F>,
{
    #[allow(non_snake_case)]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &Poseidon2Cols<AB::Var, C> = Poseidon2Cols::from_slice(&local);
        let next = main.row_slice(1);
        let next: &Poseidon2Cols<AB::Var, C> = Poseidon2Cols::from_slice(&next);

        let W = <C::WIDTH as Unsigned>::USIZE;
        let R_F = C::R_F;
        let R_P = C::R_P;

        let RF_HALF = R_F / 2;

        let R_E1_START = 0;
        let R_P_START = R_E1_START + RF_HALF;
        let R_E2_START = R_P_START + R_P;

        let ROUNDS_E1 = R_E1_START..(R_E1_START + RF_HALF);
        let ROUNDS_P = R_P_START..(R_P_START + R_P);
        let ROUNDS_E2 = R_E2_START..(R_E2_START + RF_HALF);

        // Computes the sum of boolean flags
        let round_flag_sum =
            |flags: &[AB::Var]| flags.iter().map(|&flag| flag.into()).sum::<AB::Expr>();

        let rounds_external_first = &local.rounds[ROUNDS_E1.clone()];
        let rounds_internal = &local.rounds[ROUNDS_P.clone()];
        let rounds_external_second = &local.rounds[ROUNDS_E2.clone()];

        let is_init = local.is_init;
        let is_external_first = round_flag_sum(rounds_external_first);
        let is_internal = round_flag_sum(rounds_internal);
        let is_external_second = round_flag_sum(rounds_external_second);
        let is_external: AB::Expr = is_external_first.clone() + is_external_second.clone();

        // Range check all flags.
        builder.assert_bool(is_init);
        for &round_flag in &local.rounds {
            builder.assert_bool(round_flag);
        }
        let is_real: AB::Expr = is_init + is_internal.clone() + is_external.clone();
        builder.assert_bool(is_real.clone());

        // Apply the round constants.
        // External Layers: Apply the round constants.
        // Internal Layers: Only apply the round constants to the first element.
        let mut add_rc = local.input.clone().map(Into::into);
        for (round, (&round_flag, round_constants)) in
            zip(&local.rounds, C::round_constants()).enumerate()
        {
            // Check the `round_constants` have the correct length and are only being added to the
            // first component in the internal partial rounds.
            debug_assert!(
                if ROUNDS_E1.contains(&round) || ROUNDS_E2.contains(&round) {
                    round_constants.len() == W
                } else if ROUNDS_P.contains(&round) {
                    round_constants.len() == 1
                } else {
                    true
                }
            );

            // Select the constants only if they are those for this round.
            let round_constants = round_constants
                .iter()
                .map(|&constant| round_flag.into() * constant);

            // By the check above, this `zip` will have length 1 in the internal rounds, so is only
            // added to the first component.
            for (result, constant) in zip(add_rc.iter_mut(), round_constants) {
                *result += constant;
            }
        }
        // Enforce round constant computation.
        // When is_real.is_zero(), `add_rc` is zero.
        for (add_rc, &add_rc_expected) in zip(add_rc, &local.add_rc) {
            builder
                .when(is_real.clone())
                .assert_eq(add_rc, add_rc_expected);
        }

        // Verify sbox computations
        for (&input, &sbox_deg_3_expected, &sbox_deg_7_expected) in
            izip!(&local.add_rc, &local.sbox_deg_3, &local.sbox_deg_7)
        {
            let sbox_deg_3 = input * input * input;
            let sbox_deg_7 = sbox_deg_3_expected * sbox_deg_3_expected * input;
            builder.assert_eq(sbox_deg_3, sbox_deg_3_expected);
            builder.assert_eq(sbox_deg_7, sbox_deg_7_expected);
        }

        // Only apply sbox to
        // - First element in internal and external rounds
        // - All elements in external rounds
        let sbox_result = Array::<AB::Expr, C::WIDTH>::from_fn(|i| {
            if i == 0 {
                is_init * local.add_rc[i]
                    + (is_internal.clone() + is_external.clone()) * local.sbox_deg_7[i]
            } else {
                (is_init + is_internal.clone()) * local.add_rc[i]
                    + is_external.clone() * local.sbox_deg_7[i]
            }
        });

        // EXTERNAL + INITIAL LAYER = Linear Layer
        let is_linear = is_init + is_external.clone();
        {
            // First, we apply M_4 to each consecutive four elements of the state.
            // In Appendix B's terminology, this replaces each x_i with x_i'.
            let mut state = sbox_result.clone();
            for state_chunk in state.chunks_mut(4) {
                apply_m_4(state_chunk);
            }

            // Now, we apply the outer circulant matrix (to compute the y_i values).
            //
            // We first precompute the four sums of every four elements.
            let sums: [AB::Expr; 4] = core::array::from_fn(|k| {
                (0..W)
                    .step_by(4)
                    .map(|j| state[j + k].clone())
                    .sum::<AB::Expr>()
            });

            // The formula for each y_i involves 2x_i' term and x_j' terms for each j that equals i mod 4.
            // In other words, we can add a single copy of x_i' to the appropriate one of our precomputed sums.
            for (state, sum, &output_expected) in
                izip!(state, sums.into_iter().cycle(), &local.output)
            {
                let output = state + sum;
                builder
                    .when(is_linear.clone())
                    .assert_eq(output, output_expected);
            }
        }

        // INTERNAL LAYER
        {
            // Use a simple matrix multiplication as the permutation.
            let mut state = sbox_result;
            let matmul_constants = C::matrix_diag().iter().copied().map(AB::Expr::from);
            matmul_internal(&mut state, matmul_constants);

            for (state, &output_expected) in zip(state, &local.output) {
                builder
                    .when(is_internal.clone())
                    .assert_eq(state, output_expected);
            }
        }

        // When not the final layer, constrain the output to be the input of the next layer.
        let is_not_last_round = is_real - *local.rounds.last().unwrap();
        for (&local_output, &next_input) in zip(&local.output, &next.input) {
            builder
                .when(is_not_last_round.clone())
                .assert_eq(local_output, next_input);
        }
    }
}
