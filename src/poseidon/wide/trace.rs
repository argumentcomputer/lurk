use std::iter::zip;
use std::ops::Sub;

use super::{columns::Poseidon2WideCols, Poseidon2WideChip};
use crate::poseidon::config::PoseidonConfig;

use hybrid_array::{typenum::B1, Array, ArraySize};
use p3_air::BaseAir;
use p3_field::AbstractField;
use p3_matrix::dense::RowMajorMatrix;
use p3_symmetric::Permutation;

impl<const WIDTH: usize, C: PoseidonConfig<WIDTH>> Poseidon2WideChip<C, WIDTH>
where
    C::R_P: Sub<B1>,
    <<C as PoseidonConfig<WIDTH>>::R_P as Sub<B1>>::Output: ArraySize,
{
    pub fn generate_trace(
        &self,
        inputs: &[[C::F; WIDTH]],
    ) -> (Vec<[C::F; WIDTH]>, RowMajorMatrix<C::F>) {
        let num_cols = <Poseidon2WideChip<C, WIDTH> as BaseAir<C::F>>::width(self);

        let full_num_rows = inputs.len();
        let full_trace_len_padded = full_num_rows.next_power_of_two() * num_cols;

        let mut trace = RowMajorMatrix::new(vec![C::F::zero(); full_trace_len_padded], num_cols);

        let (prefix, rows, suffix) = unsafe {
            trace
                .values
                .align_to_mut::<Poseidon2WideCols<C::F, C, WIDTH>>()
        };
        assert!(prefix.is_empty(), "Alignment should match");
        assert!(suffix.is_empty(), "Alignment should match");
        assert_eq!(rows.len(), full_num_rows.next_power_of_two());

        let mut outputs = vec![];
        for (&input, row) in zip(inputs.iter(), rows.iter_mut()) {
            let output = row.populate_columns(input);
            outputs.push(output);
        }

        (outputs, trace)
    }
}

impl<const WIDTH: usize, C: PoseidonConfig<WIDTH>> Poseidon2WideCols<C::F, C, WIDTH>
where
    C::R_P: Sub<B1>,
    <<C as PoseidonConfig<WIDTH>>::R_P as Sub<B1>>::Output: ArraySize,
{
    pub fn populate_columns(&mut self, input: [C::F; WIDTH]) -> [C::F; WIDTH] {
        let mut state = C::external_linear_layer().permute(input);

        for r in 0..C::r_f() / 2 {
            state = self.populate_external_round(state, r)
        }

        state = self.populate_internal_rounds(state);

        for r in C::r_f() / 2..C::r_f() {
            state = self.populate_external_round(state, r)
        }
        state
    }

    fn populate_external_round(&mut self, input: [C::F; WIDTH], round: usize) -> [C::F; WIDTH] {
        let mut state = {
            // Add round constants.
            //
            // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
            // columns for it, and instead include it in the constraint for the x^3 part of the sbox.
            let mut add_rc = input;
            for (add_rc, constant) in zip(add_rc.iter_mut(), C::external_constants()[round]) {
                *add_rc += constant;
            }

            // Apply the sboxes.
            // Optimization: since the linear layer that comes after the sbox is degree 1, we can
            // avoid adding columns for the result of the sbox, and instead include the x^3 -> x^7
            // part of the sbox in the constraint for the linear layer
            let mut sbox_deg_7: [C::F; WIDTH] = [C::F::zero(); WIDTH];
            let mut sbox_deg_3: [C::F; WIDTH] = [C::F::zero(); WIDTH];
            for i in 0..WIDTH {
                sbox_deg_3[i] = add_rc[i] * add_rc[i] * add_rc[i];
                sbox_deg_7[i] = sbox_deg_3[i] * sbox_deg_3[i] * add_rc[i];
            }

            self.external_rounds_sbox[round] = sbox_deg_3;

            sbox_deg_7
        };

        // Apply the linear layer.
        C::external_linear_layer().permute_mut(&mut state);
        self.external_rounds_state[round] = state;

        state
    }

    fn populate_internal_rounds(&mut self, input: [C::F; WIDTH]) -> [C::F; WIDTH] {
        let mut state: [C::F; WIDTH] = input;
        let mut sbox_deg_3: Array<C::F, C::R_P> = Array::from_fn(|_| C::F::zero());
        for r in 0..C::r_p() {
            // Add the round constant to the 0th state element.
            // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
            // columns for it, just like for external rounds.
            let add_rc = state[0] + (C::internal_constants())[r];

            // Apply the sboxes.
            // Optimization: since the linear layer that comes after the sbox is degree 1, we can
            // avoid adding columns for the result of the sbox, just like for external rounds.
            sbox_deg_3[r] = add_rc.cube();
            let sbox_deg_7 = sbox_deg_3[r].square() * add_rc;

            // Apply the linear layer.
            state[0] = sbox_deg_7;
            C::internal_linear_layer().permute_mut(&mut state);

            // Optimization: since we're only applying the sbox to the 0th state element, we only
            // need to have columns for the 0th state element at every step. This is because the
            // linear layer is degree 1, so all state elements at the end can be expressed as a
            // degree-3 polynomial of the state at the beginning of the internal rounds and the 0th
            // state element at rounds prior to the current round
            if r < C::r_p() - 1 {
                self.internal_rounds_s0[r] = state[0];
            }
        }

        self.internal_rounds_sbox = sbox_deg_3;

        state
    }
}
