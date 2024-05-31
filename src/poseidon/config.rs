use hybrid_array::{typenum::*, Array, ArraySize};
use p3_baby_bear::BabyBear;
use p3_field::Field;
use std::slice;

use super::constants::{FULL_RC_4_8, MATRIX_DIAG_4_BABYBEAR, PART_RC_4_21};
// use p3_baby_bear::BabyBear;

trait ConstantsProvided {}

#[allow(private_bounds)]
pub trait PoseidonConfig: Clone + Copy + Sync + ConstantsProvided {
    type F: Field;
    type WIDTH: ArraySize;
    const WIDTH: usize;
    const R_P: usize;
    const R_F: usize;
    type R: ArraySize;

    fn matrix_diag() -> &'static Array<Self::F, Self::WIDTH>;

    /// Returns an iterator of the hasher's round constants
    fn round_constants() -> impl IntoIterator<Item = &'static [Self::F]>;
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig4;

impl ConstantsProvided for BabyBearConfig4 {}

impl PoseidonConfig for BabyBearConfig4 {
    type F = BabyBear;
    type WIDTH = U4;
    const WIDTH: usize = 4;
    const R_P: usize = 21;
    const R_F: usize = 8;
    type R = U29;

    fn matrix_diag() -> &'static Array<Self::F, Self::WIDTH> {
        Array::from_slice(&*MATRIX_DIAG_4_BABYBEAR)
    }

    fn round_constants() -> impl IntoIterator<Item = &'static [Self::F]> {
        let first_half = FULL_RC_4_8.iter().map(|c| c.as_slice()).take(Self::R_F / 2);
        let second_half = FULL_RC_4_8.iter().map(|c| c.as_slice()).skip(Self::R_F / 2);

        let partial_round_constants = PART_RC_4_21.iter().map(slice::from_ref);

        first_half.chain(partial_round_constants).chain(second_half)
    }
}
