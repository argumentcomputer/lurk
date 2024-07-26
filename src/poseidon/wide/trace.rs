use crate::poseidon::config::PoseidonConfig;
use crate::poseidon::wide::columns::Poseidon2Cols;
use hybrid_array::{typenum::Sub1, ArraySize};
use p3_field::AbstractField;
use p3_symmetric::Permutation;
use std::iter::zip;

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2Cols<C::F, C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    pub fn populate(&mut self, input: [C::F; WIDTH]) -> [C::F; WIDTH] {
        let mut state = C::external_linear_layer().permute(input);

        for r in 0..C::r_f() / 2 {
            self.populate_external_round(&mut state, r)
        }

        for r in 0..C::r_p() {
            self.populate_internal_round(&mut state, r);
        }

        for r in C::r_f() / 2..C::r_f() {
            self.populate_external_round(&mut state, r)
        }

        state
    }

    fn populate_external_round(&mut self, state: &mut [C::F; WIDTH], round: usize) {
        self.external_rounds_state[round] = *state;
        // Add round constants.
        //
        // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
        // columns for it, and instead include it in the constraint for the x^3 part of the sbox.
        for (state, constant) in zip(state.iter_mut(), C::external_constants()[round]) {
            *state += constant;
        }

        // Apply the sboxes.
        // Optimization: since the linear layer that comes after the sbox is degree 1, we can
        // avoid adding columns for the result of the sbox, and instead include the x^3 -> x^7
        // part of the sbox in the constraint for the linear layer
        for (state, sbox_3) in zip(
            state.iter_mut(),
            self.external_rounds_sbox[round].iter_mut(),
        ) {
            *sbox_3 = state.cube();
            *state *= sbox_3.square();
        }

        // Apply the linear layer.
        C::external_linear_layer().permute_mut(state);
    }

    fn populate_internal_round(&mut self, state: &mut [C::F; WIDTH], round: usize) {
        // Optimization: since we're only applying the sbox to the 0th state element, we only
        // need to have columns for the 0th state element at every step. This is because the
        // linear layer is degree 1, so all state elements at the end can be expressed as a
        // degree-3 polynomial of the state at the beginning of the internal rounds and the 0th
        // state element at rounds prior to the current round
        if round == 0 {
            self.internal_rounds_state_init = *state;
        } else {
            self.internal_rounds_state0[round - 1] = state[0];
        }

        // Add the round constant to the 0th state element.
        // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
        // columns for it, just like for external rounds.
        state[0] += C::internal_constants()[round];

        // Apply the sboxes.
        // Optimization: since the linear layer that comes after the sbox is degree 1, we can
        // avoid adding columns for the result of the sbox, just like for external rounds.
        let sbox_3 = state[0].cube();
        self.internal_rounds_sbox[round] = sbox_3;
        state[0] *= sbox_3.square();

        // Apply the linear layer.
        C::internal_linear_layer().permute_mut(state);
    }
}
