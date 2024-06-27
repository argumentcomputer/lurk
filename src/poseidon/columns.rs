//! This module defines the columns for the Poseidon 2 chip

use core::array;
use std::iter::zip;

use super::config::PoseidonConfig;

use hybrid_array::Array;
use p3_field::AbstractField;
use p3_symmetric::Permutation;
use sphinx_derive::AlignedBorrow;

/// The column layout for the chip.
#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct Poseidon2Cols<T, C: PoseidonConfig<WIDTH>, const WIDTH: usize> {
    pub(crate) input: [T; WIDTH],
    pub(crate) is_init: T,
    pub(crate) rounds: Array<T, C::R>,
    pub(crate) add_rc: [T; WIDTH],
    pub(crate) sbox_deg_3: [T; WIDTH],
    pub(crate) sbox_deg_7: [T; WIDTH],
    pub(crate) output: [T; WIDTH],
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2Cols<C::F, C, WIDTH> {
    pub fn set_initial_round(&mut self, input: [C::F; WIDTH]) -> [C::F; WIDTH] {
        self.input = input;
        self.is_init = C::F::one();
        self.add_rc = input;
        self.evaluate_sbox();
        self.output = input;

        C::external_linear_layer().permute_mut(&mut self.output);
        self.output
    }

    pub fn set_round(
        &mut self,
        input: [C::F; WIDTH],
        round: usize,
        constants: &[C::F],
    ) -> [C::F; WIDTH] {
        self.input = input;

        // Set the boolean flags
        let rounds_half = C::r_f() / 2;
        let partial_rounds = C::r_p();
        let is_external_first_half = round < rounds_half;
        let is_external_second_half = round >= rounds_half + partial_rounds;
        let is_external = is_external_first_half || is_external_second_half;

        self.rounds[round] = C::F::one();

        self.add_rc = self.input;
        // Apply the round constants
        // Internal round: constants.len() = 1
        // External round: constants.len() = WIDTH
        for (add_rc, &constant) in zip(self.add_rc.iter_mut(), constants) {
            *add_rc += constant;
        }

        // Evaluate sbox over add_rc
        self.evaluate_sbox();

        let mut linear_input: [C::F; WIDTH] = array::from_fn(|i| {
            if i == 0 || is_external {
                self.sbox_deg_7[i]
            } else {
                self.add_rc[i]
            }
        });

        // Apply the linear layer
        if is_external {
            C::external_linear_layer().permute_mut(&mut linear_input)
        } else {
            C::internal_linear_layer().permute_mut(&mut linear_input);
        }

        self.output = linear_input;

        self.output
    }

    fn evaluate_sbox(&mut self) {
        self.sbox_deg_3 = array::from_fn(|i| self.add_rc[i].cube());
        self.sbox_deg_7 = array::from_fn(|i| self.sbox_deg_3[i].square() * self.add_rc[i]);
    }
}
