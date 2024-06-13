//! This module defines the columns for the Poseidon 2 chip

use core::array;
use std::iter::zip;
use std::mem::size_of;

use super::config::PoseidonConfig;
use crate::poseidon::util::{matmul_exterior, matmul_internal};

use hybrid_array::Array;
use p3_field::AbstractField;

/// The column layout for the chip.
#[derive(Clone, Debug)]
#[repr(C)]
pub struct Poseidon2Cols<T, const WIDTH: usize, C: PoseidonConfig<WIDTH>> {
    pub(crate) input: [T; WIDTH],
    pub(crate) is_init: T,
    pub(crate) rounds: Array<T, C::R>,
    pub(crate) add_rc: [T; WIDTH],
    pub(crate) sbox_deg_3: [T; WIDTH],
    pub(crate) sbox_deg_7: [T; WIDTH],
    pub(crate) output: [T; WIDTH],
}

impl<T, const WIDTH: usize, C: PoseidonConfig<WIDTH>> Poseidon2Cols<T, WIDTH, C> {
    #[inline]
    pub fn from_slice(slice: &[T]) -> &Self {
        let num_cols = size_of::<Poseidon2Cols<u8, WIDTH, C>>();
        assert_eq!(slice.len(), num_cols);
        let (_, shorts, _) = unsafe { slice.align_to::<Poseidon2Cols<T, WIDTH, C>>() };
        &shorts[0]
    }
}

impl<const WIDTH: usize, C: PoseidonConfig<WIDTH>> Poseidon2Cols<C::F, WIDTH, C> {
    pub fn set_initial_round(&mut self, input: [C::F; WIDTH]) -> [C::F; WIDTH] {
        self.input = input;
        self.is_init = C::F::one();
        self.add_rc = input;
        self.evaluate_sbox();
        self.output = input;

        matmul_exterior(&mut self.output);
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
            matmul_exterior(&mut linear_input)
        } else {
            let matmul_constants = C::matrix_diag().iter().copied();
            matmul_internal(&mut linear_input, matmul_constants);
        }

        self.output = linear_input;

        self.output
    }

    fn evaluate_sbox(&mut self) {
        self.sbox_deg_3 = array::from_fn(|i| self.add_rc[i].cube());
        self.sbox_deg_7 = array::from_fn(|i| self.sbox_deg_3[i].square() * self.add_rc[i]);
    }
}
