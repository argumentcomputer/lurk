//! This module defines the AIR constraints for the Poseidon2Chip

use core::mem::size_of;
use std::array;
use std::iter::zip;

use itertools::izip;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_matrix::Matrix;
use p3_symmetric::Permutation;

use super::{columns::Poseidon2Cols, config::PoseidonConfig, Poseidon2Chip};

impl<F, C: PoseidonConfig<WIDTH>, const WIDTH: usize> BaseAir<F> for Poseidon2Chip<C, WIDTH> {
    fn width(&self) -> usize {
        size_of::<Poseidon2Cols<u8, C, WIDTH>>()
    }
}

impl<AB: AirBuilder, C: PoseidonConfig<WIDTH, F = AB::F>, const WIDTH: usize> Air<AB>
    for Poseidon2Chip<C, WIDTH>
{
    #[allow(non_snake_case)]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local = Poseidon2Cols::<AB::Var, C, WIDTH>::from_slice(&local);
        let next = main.row_slice(1);
        let next = Poseidon2Cols::<AB::Var, C, WIDTH>::from_slice(&next);

        let R_F = C::r_f();
        let R_P = C::r_p();

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
        let is_linear = is_init + is_external.clone();

        // Range check all flags.
        builder.assert_bool(is_init);
        for &round_flag in &local.rounds {
            builder.assert_bool(round_flag);
        }
        let is_real: AB::Expr = is_init + is_internal.clone() + is_external.clone();
        builder.assert_bool(is_real.clone());

        // Apply the round constants.
        // Initial Layer: add_rc = input
        // External Layers: Apply the round constants.
        // Internal Layers: Only apply the round constants to the first element.
        let mut add_rc = local.input.map(Into::into);
        for (round, (&round_flag, round_constants)) in
            zip(&local.rounds, C::round_constants_iter()).enumerate()
        {
            // Check the `round_constants` have the correct length and are only being added to the
            // first component in the internal partial rounds.
            debug_assert!(
                if ROUNDS_E1.contains(&round) || ROUNDS_E2.contains(&round) {
                    round_constants.len() == WIDTH
                } else if ROUNDS_P.contains(&round) {
                    round_constants.len() == 1
                } else {
                    false
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
        // For initial round, add_rc = input
        for (add_rc, &add_rc_expected) in zip(add_rc, &local.add_rc) {
            builder
                .when(is_real.clone())
                .assert_eq(add_rc, add_rc_expected);
        }

        // Verify sbox computations
        // sbox_deg_7[i] = add_rc[i]^7
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
        let sbox_result: [AB::Expr; WIDTH] = array::from_fn(|i| {
            if i == 0 {
                is_init * local.add_rc[i]
                    + (is_internal.clone() + is_external.clone()) * local.sbox_deg_7[i]
            } else {
                (is_init + is_internal.clone()) * local.add_rc[i]
                    + is_external.clone() * local.sbox_deg_7[i]
            }
        });

        // EXTERNAL + INITIAL LAYER = Linear Layer
        {
            // First, we apply M_4 to each consecutive four elements of the state.
            // In Appendix B's terminology, this replaces each x_i with x_i'.
            let state = C::external_linear_layer().permute(sbox_result.clone());

            // The formula for each y_i involves 2x_i' term and x_j' terms for each j that equals i mod 4.
            // In other words, we can add a single copy of x_i' to the appropriate one of our precomputed sums.
            for (state, &output_expected) in zip(state, &local.output) {
                builder
                    .when(is_linear.clone())
                    .assert_eq(state, output_expected);
            }
        }

        // INTERNAL LAYER
        {
            // Use a simple matrix multiplication as the permutation.
            let state = C::internal_linear_layer().permute(sbox_result);

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
