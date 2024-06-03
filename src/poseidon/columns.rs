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
