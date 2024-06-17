//! This module defines the columns for the Poseidon 2 chip

use std::iter::zip;
use std::mem::size_of;

use crate::poseidon::util::{matmul_exterior, matmul_internal};
use hybrid_array::Array;
use p3_field::AbstractField;

use super::config::PoseidonConfig;

/// The column layout for the chip.
#[derive(Clone, Debug)]
#[repr(C)]
pub struct Poseidon2Cols<T, C>
where
    C: PoseidonConfig,
{
    pub(crate) input: Array<T, C::WIDTH>,
    pub(crate) is_init: T,
    pub(crate) rounds: Array<T, C::R>,
    pub(crate) add_rc: Array<T, C::WIDTH>,
    pub(crate) sbox_deg_3: Array<T, C::WIDTH>,
    pub(crate) sbox_deg_7: Array<T, C::WIDTH>,
    pub(crate) output: Array<T, C::WIDTH>,
}

impl<T, C: PoseidonConfig> Poseidon2Cols<T, C> {
    #[inline]
    pub fn from_slice(slice: &[T]) -> &Self {
        let num_cols = size_of::<Poseidon2Cols<u8, C>>();
        assert_eq!(slice.len(), num_cols);
        let (_, shorts, _) = unsafe { slice.align_to::<Poseidon2Cols<T, C>>() };
        &shorts[0]
    }
}

impl<C: PoseidonConfig> Poseidon2Cols<C::F, C> {
    pub fn set_initial_round(&mut self, input: Array<C::F, C::WIDTH>) -> Array<C::F, C::WIDTH> {
        self.input = input.clone();
        self.is_init = C::F::one();
        self.add_rc = input.clone();
        self.evaluate_sbox();
        self.output = input;

        matmul_exterior(&mut self.output);
        self.output.clone()
    }

    pub fn set_round(
        &mut self,
        input: Array<C::F, C::WIDTH>,
        round: usize,
        constants: &[C::F],
    ) -> Array<C::F, C::WIDTH> {
        self.input = input;

        // Set the boolean flags
        let is_external_first_half = round < C::R_F / 2;
        let is_external_second_half = round >= C::R_F / 2 + C::R_P;
        let is_external = is_external_first_half || is_external_second_half;

        self.rounds[round] = C::F::one();

        self.add_rc = self.input.clone();
        // Apply the round constants
        // Internal round: constants.len() = 1
        // External round: constants.len() = WIDTH
        for (add_rc, &constant) in zip(self.add_rc.iter_mut(), constants) {
            *add_rc += constant;
        }

        // Evaluate sbox over add_rc
        self.evaluate_sbox();

        let mut linear_input: Array<C::F, C::WIDTH> = Array::from_fn(|i| {
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

        self.output.clone()
    }

    fn evaluate_sbox(&mut self) {
        self.sbox_deg_3 = Array::from_fn(|i| self.add_rc[i].cube());
        self.sbox_deg_7 = Array::from_fn(|i| self.sbox_deg_3[i].square() * self.add_rc[i]);
    }
}
