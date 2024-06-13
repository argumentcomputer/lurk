//! This module defines the trace generation for the Poseidon2 AIR Chip
use std::iter::zip;

use super::{columns::Poseidon2Cols, config::PoseidonConfig, Poseidon2Chip};

use itertools::Itertools;
use p3_air::BaseAir;
use p3_field::AbstractField;
use p3_matrix::dense::RowMajorMatrix;

impl<const WIDTH: usize, C> Poseidon2Chip<WIDTH, C>
where
    C: PoseidonConfig<WIDTH>,
{
    pub fn generate_trace(&self, inputs: Vec<[C::F; WIDTH]>) -> RowMajorMatrix<C::F> {
        let full_rounds = C::r_f();
        let part_rounds = C::r_p();
        let rounds = full_rounds + part_rounds;
        let num_cols = <Poseidon2Chip<WIDTH, C> as BaseAir<C::F>>::width(self);

        let full_num_rows = inputs.len() * (rounds + 1);
        let full_trace_len_padded = full_num_rows.next_power_of_two() * num_cols;

        let mut trace = RowMajorMatrix::new(vec![C::F::zero(); full_trace_len_padded], num_cols);

        let (prefix, rows, suffix) =
            unsafe { trace.values.align_to_mut::<Poseidon2Cols<C::F, WIDTH, C>>() };
        assert!(prefix.is_empty(), "Alignment should match");
        assert!(suffix.is_empty(), "Alignment should match");
        assert_eq!(rows.len(), full_num_rows.next_power_of_two());

        for (input, rounds_row) in zip(inputs, rows.chunks_mut(rounds + 1)) {
            let constants = C::round_constants_iter();

            // Generate the initial round
            let mut next_input = rounds_row[0].set_initial_round(input);

            for (round, (row, constants)) in
                rounds_row.iter_mut().skip(1).zip_eq(constants).enumerate()
            {
                let input = next_input;
                next_input = row.set_round(input, round, constants);
            }
        }
        trace
    }
}
