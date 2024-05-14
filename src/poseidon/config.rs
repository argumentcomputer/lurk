use super::constants::{
    MATRIX_DIAG_16_BABYBEAR_U32, MATRIX_DIAG_4_BABYBEAR_U32, RC_16_30_U32, RC_4_29_U32,
};

trait ConstantsProvided {}

#[allow(private_bounds)]
pub trait PoseidonConfig<const WIDTH: usize>: Clone + Copy + Sync + ConstantsProvided {
    const R_P: usize;
    const R_F: usize;
    const R: usize = Self::R_P + Self::R_F;
    const MATRIX_DIAG: [u32; WIDTH];

    fn round_constants() -> Vec<[u32; WIDTH]>;
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig4 {}

impl ConstantsProvided for BabyBearConfig4 {}

impl PoseidonConfig<4> for BabyBearConfig4 {
    const R_P: usize = 21;
    const R_F: usize = 8;
    const R: usize = Self::R_P + Self::R_F;
    const MATRIX_DIAG: [u32; 4] = MATRIX_DIAG_4_BABYBEAR_U32;

    fn round_constants() -> Vec<[u32; 4]> {
        RC_4_29_U32.to_vec()
    }
}

#[derive(Clone, Copy)]
pub struct BabyBearConfig16 {}

impl ConstantsProvided for BabyBearConfig16 {}

impl PoseidonConfig<16> for BabyBearConfig16 {
    const R_P: usize = 22;
    const R_F: usize = 8;
    const R: usize = Self::R_P + Self::R_F;
    const MATRIX_DIAG: [u32; 16] = MATRIX_DIAG_16_BABYBEAR_U32;

    fn round_constants() -> Vec<[u32; 16]> {
        RC_16_30_U32.to_vec()
    }
}
