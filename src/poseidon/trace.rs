//! This module defines the trace generation for the Poseidon2 AIR Chip
use core::iter;

use hybrid_array::{typenum::Unsigned, Array};
use itertools::Itertools;
use p3_air::BaseAir;
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use p3_matrix::dense::RowMajorMatrix;

use super::{
    columns::Poseidon2Cols,
    config::PoseidonConfig,
    util::{apply_m_4, matmul_generic},
    Poseidon2Chip,
};

type F = BabyBear;

impl<C: PoseidonConfig> Poseidon2Chip<C> {
    pub fn generate_trace(&self, inputs: Vec<Array<F, C::WIDTH>>) -> RowMajorMatrix<F> {
        let width = <C::WIDTH as Unsigned>::USIZE;
        let rounds = <C::R as Unsigned>::USIZE;
        let num_cols = <Poseidon2Chip<C> as BaseAir<F>>::width(self);

        let full_trace_len = inputs.len() * num_cols * rounds;

        let full_trace_len = full_trace_len.next_power_of_two();

        let mut trace = RowMajorMatrix::new(vec![F::zero(); full_trace_len], width);

        let (prefix, rows, suffix) = unsafe { trace.values.align_to_mut::<Poseidon2Cols<F, C>>() };
        assert!(prefix.is_empty(), "Alignment should match");
        assert!(suffix.is_empty(), "Alignment should match");
        assert_eq!(rows.len(), full_trace_len);

        let zero_row: Array<F, C::WIDTH> = Array::clone_from_slice(&vec![F::zero(); width]);

        let padded_inputs = inputs.into_iter().chain(iter::repeat(zero_row));
        for (rounds_row, input) in rows.chunks_mut(rounds).zip_eq(padded_inputs) {
            self.generate_round_trace(rounds_row.to_vec(), input);
        }
        trace
    }

    fn generate_round_trace(&self, mut rows: Vec<Poseidon2Cols<F, C>>, input: Array<F, C::WIDTH>) {
        let full_constants = C::full_round_constants()
            .into_iter()
            .map(|round| round.map(F::from_wrapped_u32))
            .collect::<Vec<_>>();
        let partial_constants = C::partial_round_constants()
            .into_iter()
            .map(F::from_wrapped_u32)
            .collect::<Vec<_>>();

        let width = <C::WIDTH as Unsigned>::USIZE;
        let rounds_f = C::R_F;
        let rounds_p = C::R_P;
        let mut input = input.clone();

        for (round, row) in rows.iter_mut().enumerate() {
            // Trick to get lsp to recognize everything?
            let round: usize = round;
            let row: &mut Poseidon2Cols<BabyBear, C> = row;

            // let row: &mut Poseidon2Cols<BabyBear, _> = &mut row;
            row.input = input.clone();

            // Set the boolean flags
            let is_external_first_half = round < rounds_f / 2;
            let is_external_second_half = round >= rounds_f / 2 + rounds_p;
            let is_external = is_external_first_half || is_external_second_half;
            let is_internal = !is_external;

            row.rounds[round] = F::one();

            if is_external {
                row.is_external = F::one();
            } else if is_internal {
                row.is_internal = F::one();
            }

            // Apply the round constants
            for i in 0..width {
                if is_external_first_half {
                    row.add_rc[i] = input[i] + full_constants[round][i];
                } else if is_external_second_half {
                    let offset = rounds_f / 2;
                    row.add_rc[i] = input[i] + full_constants[offset + round][i];
                } else if is_internal {
                    let offset = rounds_f / 2;
                    if i == 0 {
                        row.add_rc[i] = input[i] + partial_constants[round - offset];
                    } else {
                        row.add_rc[i] = input[i];
                    }
                } else {
                    panic!("This shouldn't happen")
                }
            }

            // Apply the degree 3 sbox
            for i in 0..width {
                row.sbox_deg_3[i] = row.add_rc[i] * row.add_rc[i] * row.add_rc[i];
            }
            // Apply the degree 7 sbox
            for i in 0..width {
                row.sbox_deg_7[i] = row.sbox_deg_3[i] * row.sbox_deg_3[i] * row.add_rc[i];
            }

            let mut linear_input = row
                .sbox_deg_7
                .iter()
                .enumerate()
                .map(|(i, x)| {
                    if i == 0 || is_external {
                        *x
                    } else {
                        row.add_rc[i]
                    }
                })
                .collect::<Vec<BabyBear>>();

            // Apply the linear layer
            if is_external {
                for i in (0..width).step_by(4) {
                    apply_m_4(&mut linear_input[i..i + 4]);
                }
                let sums = (0..4)
                    .map(|k| {
                        (0..width)
                            .step_by(4)
                            .map(|j| linear_input[j + k].clone())
                            .sum::<BabyBear>()
                    })
                    .collect::<Vec<BabyBear>>();

                for i in 0..width {
                    linear_input[i] += sums[i % 4];
                }
            } else {
                let matmul_constants = C::matrix_diag().map(F::from_wrapped_u32);
                matmul_generic(&mut linear_input, matmul_constants);
            }
            for i in 0..width {
                row.output[i] = linear_input[i];
            }

            // Update the input for the next round
            input = row.output.clone();
        }
    }
}
