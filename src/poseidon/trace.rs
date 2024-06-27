//! This module defines the trace generation for the Poseidon2 AIR Chip

use super::{columns::Poseidon2Cols, config::PoseidonConfig, Poseidon2Chip};

use p3_air::BaseAir;
use p3_field::AbstractField;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;

use itertools::Itertools;
use std::borrow::BorrowMut;

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2Chip<C, WIDTH> {
    pub fn generate_trace(&self, inputs: Vec<[C::F; WIDTH]>) -> RowMajorMatrix<C::F> {
        let full_rounds = C::r_f();
        let part_rounds = C::r_p();
        let rounds = full_rounds + part_rounds;
        let num_cols = <Poseidon2Chip<C, WIDTH> as BaseAir<C::F>>::width(self);

        let full_num_rows = inputs.len() * (rounds + 1);
        let full_trace_len_padded = full_num_rows.next_power_of_two() * num_cols;

        let mut trace = RowMajorMatrix::new(vec![C::F::zero(); full_trace_len_padded], num_cols);

        trace
            .par_row_chunks_exact_mut(rounds + 1)
            .zip_eq(inputs.into_par_iter())
            .for_each(|(mut round_rows, input)| {
                let constants = C::round_constants_iter();

                let mut rows_iter = round_rows.rows_mut().map(|row| {
                    let cols: &mut Poseidon2Cols<C::F, C, WIDTH> = row.borrow_mut();
                    cols
                });

                // Generate the initial round
                let mut next_input = rows_iter.next().unwrap().set_initial_round(input);

                for (round, (row, constants)) in rows_iter.zip_eq(constants).enumerate() {
                    let input = next_input;
                    next_input = row.set_round(input, round, constants);
                }
            });

        trace
    }
}
