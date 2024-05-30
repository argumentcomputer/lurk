use std::slice;
use hybrid_array::{typenum::*, Array, ArraySize};
use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field};

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
    fn round_constants() ->impl IntoIterator<Item = &'static [Self::F]>;
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
        // Array::from_slice(&*MATRIX_DIAG_4_BABYBEAR) // Is this cursed?
        &Array::from(*MATRIX_DIAG_4_BABYBEAR) // Is this less cursed?
    }

    fn round_constants() -> impl IntoIterator<Item = &'static [Self::F]> {
        let first_half = FULL_RC_4_8
            .iter()
            .map(|c| c.as_slice())
            .take(4);
        let second_half = FULL_RC_4_8
            .iter()
            .map(|c| c.as_slice())
            .skip(4);

        let partial_round_constants = 
            PART_RC_4_21
            .iter().map(slice::from_ref);

        first_half.chain(partial_round_constants).chain(second_half)
    }
}

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig8;

// impl ConstantsProvided for BabyBearConfig8 {}

// impl PoseidonConfig for BabyBearConfig8 {
//     type F = BabyBear;
//     type WIDTH = U8;
//     const R_P: usize = 12;
//     const R_F: usize = 8;
//     type R = U20;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_8_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig12;

// impl ConstantsProvided for BabyBearConfig12 {}

// impl PoseidonConfig for BabyBearConfig12 {
//     type F = BabyBear;
//     type WIDTH = U12;
//     const R_P: usize = 10;
//     const R_F: usize = 8;
//     type R = U18;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_12_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig16;

// impl ConstantsProvided for BabyBearConfig16 {}

// impl PoseidonConfig for BabyBearConfig16 {
//     type F = BabyBear;
//     type WIDTH = U16;
//     const R_P: usize = 13;
//     const R_F: usize = 8;
//     type R = U21;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_16_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig20;

// impl ConstantsProvided for BabyBearConfig20 {}

// impl PoseidonConfig for BabyBearConfig20 {
//     type F = BabyBear;
//     type WIDTH = U20;
//     const R_P: usize = 18;
//     const R_F: usize = 8;
//     type R = U26;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_20_BABYBEAR_U32)
//     }
// }
// #[derive(Clone, Copy)]
// pub struct BabyBearConfig24;

// impl ConstantsProvided for BabyBearConfig24 {}

// impl PoseidonConfig for BabyBearConfig24 {
//     type F = BabyBear;
//     type WIDTH = U24;
//     const R_P: usize = 21;
//     const R_F: usize = 8;
//     type R = U29;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_24_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig28;

// impl ConstantsProvided for BabyBearConfig28 {}

// impl PoseidonConfig for BabyBearConfig28 {
//     type F = BabyBear;
//     type WIDTH = U28;
//     const R_P: usize = 25;
//     const R_F: usize = 8;
//     type R = U33;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_28_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig32;

// impl ConstantsProvided for BabyBearConfig32 {}

// impl PoseidonConfig for BabyBearConfig32 {
//     type F = BabyBear;
//     type WIDTH = U32;
//     const R_P: usize = 30;
//     const R_F: usize = 8;
//     type R = U38;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_32_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig36;

// impl ConstantsProvided for BabyBearConfig36 {}

// impl PoseidonConfig for BabyBearConfig36 {
//     type F = BabyBear;
//     type WIDTH = U36;
//     const R_P: usize = 34;
//     const R_F: usize = 8;
//     type R = U42;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_36_BABYBEAR_U32)
//     }
// }

// #[derive(Clone, Copy)]
// pub struct BabyBearConfig40;

// impl ConstantsProvided for BabyBearConfig40 {}

// impl PoseidonConfig for BabyBearConfig40 {
//     type F = BabyBear;
//     type WIDTH = U40;
//     const R_P: usize = 38;
//     const R_F: usize = 8;
//     type R = U46;

//     fn matrix_diag() -> Array<u32, Self::WIDTH> {
//         Array::from_iter(MATRIX_DIAG_40_BABYBEAR_U32)
//     }
// }
