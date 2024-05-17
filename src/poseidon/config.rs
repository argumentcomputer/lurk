use hybrid_array::typenum::*;
use hybrid_array::{Array, ArraySize};

use super::constants::{
    MATRIX_DIAG_16_BABYBEAR_U32, MATRIX_DIAG_4_BABYBEAR_U32, RC_16_21_U32, RC_4_29_U32,
};

trait ConstantsProvided {}

#[allow(private_bounds)]
pub trait PoseidonConfig: Clone + Copy + Sync + ConstantsProvided {
    type WIDTH: ArraySize;
    const R_P: usize;
    const R_F: usize;
    type R: ArraySize;

    fn round_constants() -> Vec<Array<u32, Self::WIDTH>>;

    fn matrix_diag() -> Array<u32, Self::WIDTH>;
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig4;

impl ConstantsProvided for BabyBearConfig4 {}

impl PoseidonConfig for BabyBearConfig4 {
    type WIDTH = U4;
    const R_P: usize = 21;
    const R_F: usize = 8;
    type R = U29;

    fn round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        RC_4_29_U32.map(|u| Array::from_iter(u)).to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_4_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig16;

impl ConstantsProvided for BabyBearConfig16 {}

impl PoseidonConfig for BabyBearConfig16 {
    type WIDTH = U16;
    const R_P: usize = 22;
    const R_F: usize = 8;
    type R = U21;

    fn round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        RC_16_21_U32.map(|u| Array::from_iter(u)).to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_16_BABYBEAR_U32)
    }
}
