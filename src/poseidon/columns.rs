//! This module defines the columns for the Poseidon 2 chip

use hybrid_array::Array;
use loam_macros::AlignedBorrow;

use super::config::PoseidonConfig;

/// The column layout for the chip.
#[derive(AlignedBorrow, Clone, Debug)]
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
