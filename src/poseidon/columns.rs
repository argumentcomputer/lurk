//! This module defines the columns for the Poseidon 2 chip

use std::mem::size_of;

use hybrid_array::Array;

use super::config::PoseidonConfig;

/// The column layout for the chip.
#[derive(Clone, Debug)]
#[repr(C)]
pub struct Poseidon2Cols<T, C>
where
    C: PoseidonConfig,
{
    pub input: Array<T, C::WIDTH>,
    pub is_init: T,
    pub rounds: Array<T, C::R>,
    pub add_rc: Array<T, C::WIDTH>,
    pub sbox_deg_3: Array<T, C::WIDTH>,
    pub sbox_deg_7: Array<T, C::WIDTH>,
    pub output: Array<T, C::WIDTH>,
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
