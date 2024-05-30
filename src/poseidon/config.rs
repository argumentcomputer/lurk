use hybrid_array::{typenum::*, Array, ArraySize};
use p3_field::Field;
// use p3_baby_bear::BabyBear;

use super::constants::{
    FULL_RC_12_8_U32, FULL_RC_16_8_U32, FULL_RC_20_8_U32, FULL_RC_24_8_U32, FULL_RC_28_8_U32,
    FULL_RC_32_8_U32, FULL_RC_36_8_U32, FULL_RC_40_8_U32, FULL_RC_4_8_U32, FULL_RC_8_8_U32,
    MATRIX_DIAG_12_BABYBEAR_U32, MATRIX_DIAG_16_BABYBEAR_U32, MATRIX_DIAG_20_BABYBEAR_U32,
    MATRIX_DIAG_24_BABYBEAR_U32, MATRIX_DIAG_28_BABYBEAR_U32, MATRIX_DIAG_32_BABYBEAR_U32,
    MATRIX_DIAG_36_BABYBEAR_U32, MATRIX_DIAG_40_BABYBEAR_U32, MATRIX_DIAG_4_BABYBEAR_U32,
    MATRIX_DIAG_8_BABYBEAR_U32, PART_RC_12_10_U32, PART_RC_16_13_U32, PART_RC_20_18_U32,
    PART_RC_24_21_U32, PART_RC_28_25_U32, PART_RC_32_30_U32, PART_RC_36_34_U32, PART_RC_40_38_U32,
    PART_RC_4_21_U32, PART_RC_8_12_U32,
};

trait ConstantsProvided {}

#[allow(private_bounds)]
pub trait PoseidonConfig: Clone + Copy + Sync + ConstantsProvided {
    type F: Field;
    type WIDTH: ArraySize;
    const R_P: usize;
    const R_F: usize;
    type R: ArraySize;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>>;

    fn partial_round_constants() -> Vec<u32>;

    fn matrix_diag() -> Array<u32, Self::WIDTH>;

    /// Ret
    fn round_constants() -> impl IntoIterator<Item = &'static Array<Self::F, Self::WIDTH>>;
    
    // fn permute(&self, mut input: Array<BabyBear, Self::WIDTH>) -> Array<BabyBear, Self::WIDTH> {
    //     self.permute_mut(&mut input);
    //     input
    // }

    // fn permute_mut(
    //     &self,
    //     input: &mut Array<BabyBear, Self::WIDTH>,
    // ) -> Array<BabyBear, Self::WIDTH> {
    //     // let blah: &[BabyBear] = input.as_mut();
    //     // const width = <Self::WIDTH as Unsigned>::USIZE;
    //     // let array: [BabyBear; width] = core::array::from_fn(|i| blah[i]);

    //     todo!()
    // }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig4;

impl ConstantsProvided for BabyBearConfig4 {}

impl PoseidonConfig for BabyBearConfig4 {
    type WIDTH = U4;
    const R_P: usize = 21;
    const R_F: usize = 8;
    type R = U29;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_4_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_4_21_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_4_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig8;

impl ConstantsProvided for BabyBearConfig8 {}

impl PoseidonConfig for BabyBearConfig8 {
    type WIDTH = U8;
    const R_P: usize = 12;
    const R_F: usize = 8;
    type R = U20;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_8_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_8_12_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_8_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig12;

impl ConstantsProvided for BabyBearConfig12 {}

impl PoseidonConfig for BabyBearConfig12 {
    type WIDTH = U12;
    const R_P: usize = 10;
    const R_F: usize = 8;
    type R = U18;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_12_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_12_10_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_12_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig16;

impl ConstantsProvided for BabyBearConfig16 {}

impl PoseidonConfig for BabyBearConfig16 {
    type WIDTH = U16;
    const R_P: usize = 13;
    const R_F: usize = 8;
    type R = U21;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_16_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_16_13_U32.to_vec()
    }
    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_16_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig20;

impl ConstantsProvided for BabyBearConfig20 {}

impl PoseidonConfig for BabyBearConfig20 {
    type WIDTH = U20;
    const R_P: usize = 18;
    const R_F: usize = 8;
    type R = U26;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_20_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_20_18_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_20_BABYBEAR_U32)
    }
}
#[derive(Clone, Copy)]
pub struct BabyBearConfig24;

impl ConstantsProvided for BabyBearConfig24 {}

impl PoseidonConfig for BabyBearConfig24 {
    type WIDTH = U24;
    const R_P: usize = 21;
    const R_F: usize = 8;
    type R = U29;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_24_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_24_21_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_24_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig28;

impl ConstantsProvided for BabyBearConfig28 {}

impl PoseidonConfig for BabyBearConfig28 {
    type WIDTH = U28;
    const R_P: usize = 25;
    const R_F: usize = 8;
    type R = U33;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_28_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_28_25_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_28_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig32;

impl ConstantsProvided for BabyBearConfig32 {}

impl PoseidonConfig for BabyBearConfig32 {
    type WIDTH = U32;
    const R_P: usize = 30;
    const R_F: usize = 8;
    type R = U38;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_32_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_32_30_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_32_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig36;

impl ConstantsProvided for BabyBearConfig36 {}

impl PoseidonConfig for BabyBearConfig36 {
    type WIDTH = U36;
    const R_P: usize = 34;
    const R_F: usize = 8;
    type R = U42;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_36_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_36_34_U32.to_vec()
    }
    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_36_BABYBEAR_U32)
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig40;

impl ConstantsProvided for BabyBearConfig40 {}

impl PoseidonConfig for BabyBearConfig40 {
    type WIDTH = U40;
    const R_P: usize = 38;
    const R_F: usize = 8;
    type R = U46;

    fn full_round_constants() -> Vec<Array<u32, Self::WIDTH>> {
        FULL_RC_40_8_U32.map(|x| Array::from_iter(x)).to_vec()
    }

    fn partial_round_constants() -> Vec<u32> {
        PART_RC_40_38_U32.to_vec()
    }

    fn matrix_diag() -> Array<u32, Self::WIDTH> {
        Array::from_iter(MATRIX_DIAG_40_BABYBEAR_U32)
    }
}
