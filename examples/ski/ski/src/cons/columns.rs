use wp1_derive::AlignedBorrow;

use crate::air::pointer::Pointer;

/// The column layout for the chip.
#[derive(AlignedBorrow, Default, Clone, Debug)]
#[repr(C)]
pub struct ConsCols<T> {
    pub a_ptr: Pointer<T>,
    pub b_ptr: Pointer<T>,
    pub c_ptr: Pointer<T>,
    pub mult_cons: T,
    pub mult_car: T,
    pub mult_cdr: T,
}
