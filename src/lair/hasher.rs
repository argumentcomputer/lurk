use p3_baby_bear::BabyBear;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use crate::poseidon::{
    config::{BabyBearConfig24, BabyBearConfig32, BabyBearConfig48, InternalDiffusion},
    Poseidon2Chip,
};

use super::List;

pub trait Hasher: Default {
    type F;

    fn hash(&self, preimg: &[Self::F]) -> List<Self::F>;
}

pub struct LurkHasher {
    hasher_24_8: Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, InternalDiffusion, 24, 7>,
    hasher_32_8: Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, InternalDiffusion, 32, 7>,
    hasher_48_8: Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, InternalDiffusion, 48, 7>,
    // chip_24_8: Poseidon2Chip<BabyBearConfig24>,
    // chip_32_8: Poseidon2Chip<BabyBearConfig32>,
    // chip_48_8: Poseidon2Chip<BabyBearConfig48>,
}

impl Default for LurkHasher {
    fn default() -> Self {
        let chip_32_8 = Poseidon2Chip::<BabyBearConfig32>::default();
        let chip_24_8 = Poseidon2Chip::<BabyBearConfig24>::default();
        let chip_48_8 = Poseidon2Chip::<BabyBearConfig48>::default();
        let hasher_24_8 = chip_24_8.hasher();
        let hasher_32_8 = chip_32_8.hasher();
        let hasher_48_8 = chip_48_8.hasher();
        Self {
            hasher_24_8,
            hasher_32_8,
            hasher_48_8,
            // chip_24_8,
            // chip_32_8,
            // chip_48_8,
        }
    }
}

impl Hasher for LurkHasher {
    type F = BabyBear;

    fn hash(&self, preimg: &[Self::F]) -> List<Self::F> {
        macro_rules! hash_with {
            ($name:ident) => {
                self.$name.permute(preimg.try_into().unwrap())[..8].into()
            };
        }
        match preimg.len() {
            24 => hash_with!(hasher_24_8),
            32 => hash_with!(hasher_32_8),
            48 => hash_with!(hasher_48_8),
            _ => unimplemented!(),
        }
    }
}
