use crate::poseidon::config::PoseidonConfig;
use std::mem::size_of;

use hybrid_array::{typenum::*, Array, ArraySize};

// /// Memory columns for Poseidon2.
// #[derive(Clone, Copy)]
// #[repr(C)]
// pub struct Poseidon2MemCols<T> {
//     pub timestamp: T,
//     pub dst: T,
//     pub left: T,
//     pub right: T,
//     pub input: [MemoryReadSingleCols<T>; WIDTH],
//     pub output: [MemoryReadWriteSingleCols<T>; WIDTH],
//     pub is_real: T,
// }

/// Columns for the "narrow" Poseidon2 chip.
///
/// As an optimization, we can represent all of the internal rounds without columns for intermediate
/// states except for the 0th element. This is because the linear layer that comes after the sbox is
/// degree 1, so all state elements at the end can be expressed as a degree-3 polynomial of:
/// 1) the 0th state element at rounds prior to the current round
/// 2) the rest of the state elements at the beginning of the internal rounds
#[derive(Clone, Debug)]
#[repr(C)]
pub struct Poseidon2WideCols<T, C: PoseidonConfig<WIDTH>, const WIDTH: usize>
where
    Sub1<C::R_P>: ArraySize,
{
    /// Input states for all external rounds
    pub(crate) external_rounds_state: Array<[T; WIDTH], C::R_F>,
    /// Intermediary SBox results for external rounds
    pub(crate) external_rounds_sbox: Array<[T; WIDTH], C::R_F>,

    /// Initial state before internal rounds
    pub(crate) internal_rounds_state_init: [T; WIDTH],
    /// Expected value of the first state element in all but the first internal rounds
    pub(crate) internal_rounds_state0: Array<T, Sub1<C::R_P>>,
    /// Intermediary SBox results for internal rounds
    pub(crate) internal_rounds_sbox: Array<T, C::R_P>,
}
impl<T, C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2WideCols<T, C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    pub(crate) const fn num_cols() -> usize {
        size_of::<Poseidon2WideCols<u8, C, WIDTH>>()
    }

    #[inline]
    pub fn from_slice(slice: &[T]) -> &Self {
        let num_cols = Poseidon2WideCols::<T, C, WIDTH>::num_cols();

        debug_assert_eq!(slice.len(), num_cols);
        let (_, shorts, _) = unsafe { slice.align_to::<Poseidon2WideCols<T, C, WIDTH>>() };
        &shorts[0]
    }

    #[inline]
    pub fn from_slice_mut(slice: &mut [T]) -> &mut Self {
        let num_cols = Poseidon2WideCols::<T, C, WIDTH>::num_cols();

        debug_assert_eq!(slice.len(), num_cols);
        let (_, shorts, _) = unsafe { slice.align_to_mut::<Poseidon2WideCols<T, C, WIDTH>>() };
        &mut shorts[0]
    }
}

// pub(crate) const NUM_POSEIDON2_COLS: usize = size_of::<Poseidon2Cols<u8>>();
