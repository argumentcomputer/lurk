use p3_air::AirBuilder;
use p3_baby_bear::BabyBear;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use crate::{
    air::builder::{LookupBuilder, RequireRecord},
    lair::chipset::Chipset,
    poseidon::{
        config::{
            BabyBearConfig24, BabyBearConfig32, BabyBearConfig48, InternalDiffusion, PoseidonConfig,
        },
        wide::{air::eval_input, columns::Poseidon2Cols, trace::populate_witness},
    },
};

use crate::lair::{map::Map, Name};

pub enum LurkChip {
    Hasher24_8(
        Poseidon2<
            BabyBear,
            Poseidon2ExternalMatrixGeneral,
            InternalDiffusion<BabyBearConfig24>,
            24,
            7,
        >,
    ),
    Hasher32_8(
        Poseidon2<
            BabyBear,
            Poseidon2ExternalMatrixGeneral,
            InternalDiffusion<BabyBearConfig32>,
            32,
            7,
        >,
    ),
    Hasher48_8(
        Poseidon2<
            BabyBear,
            Poseidon2ExternalMatrixGeneral,
            InternalDiffusion<BabyBearConfig48>,
            48,
            7,
        >,
    ),
}

pub fn lurk_chip_map() -> Map<Name, LurkChip> {
    let hash_24_8 = LurkChip::Hasher24_8(BabyBearConfig24::hasher());
    let hash_32_8 = LurkChip::Hasher32_8(BabyBearConfig32::hasher());
    let hash_48_8 = LurkChip::Hasher48_8(BabyBearConfig48::hasher());
    let vec = vec![
        (Name("hash_24_8"), hash_24_8),
        (Name("hash_32_8"), hash_32_8),
        (Name("hash_48_8"), hash_48_8),
    ];
    Map::from_vec(vec)
}

macro_rules! sized {
    ($vector:ident) => {
        $vector.try_into().unwrap()
    };
}

impl Chipset<BabyBear> for LurkChip {
    #[inline]
    fn input_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(..) => 24,
            LurkChip::Hasher32_8(..) => 32,
            LurkChip::Hasher48_8(..) => 48,
        }
    }

    #[inline]
    fn output_size(&self) -> usize {
        8
    }

    fn require_size(&self) -> usize {
        0
    }

    fn execute(&self, preimg: &[BabyBear]) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
            LurkChip::Hasher32_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
            LurkChip::Hasher48_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig24, 24>::num_cols(),
            LurkChip::Hasher32_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig32, 32>::num_cols(),
            LurkChip::Hasher48_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig48, 48>::num_cols(),
        }
    }

    fn populate_witness(&self, preimg: &[BabyBear], witness: &mut [BabyBear]) -> Vec<BabyBear> {
        let mut out: Vec<_> = match self {
            LurkChip::Hasher24_8(..) => {
                populate_witness::<BabyBearConfig24, 24>(sized!(preimg), witness).into()
            }
            LurkChip::Hasher32_8(..) => {
                populate_witness::<BabyBearConfig32, 32>(sized!(preimg), witness).into()
            }
            LurkChip::Hasher48_8(..) => {
                populate_witness::<BabyBearConfig48, 48>(sized!(preimg), witness).into()
            }
        };
        out.truncate(8);
        out
    }

    fn eval<AB: AirBuilder<F = BabyBear> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        preimg: Vec<AB::Expr>,
        img: &[AB::Var],
        witness: &[AB::Var],
        _: AB::Expr,
        _: &[RequireRecord<AB::Var>],
    ) {
        match self {
            LurkChip::Hasher24_8(..) => eval_input::<AB, BabyBearConfig24, 24>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
            LurkChip::Hasher32_8(..) => eval_input::<AB, BabyBearConfig32, 32>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
            LurkChip::Hasher48_8(..) => eval_input::<AB, BabyBearConfig48, 48>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
        }
    }
}

// `LurkHasher` is only used in the `ZStore`. Maybe deprecate it?
#[derive(Clone)]
pub struct LurkHasher {
    hasher_24_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig24>,
        24,
        7,
    >,
    hasher_32_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig32>,
        32,
        7,
    >,
    hasher_48_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig48>,
        48,
        7,
    >,
}

impl Default for LurkHasher {
    fn default() -> Self {
        let hasher_24_8 = BabyBearConfig24::hasher();
        let hasher_32_8 = BabyBearConfig32::hasher();
        let hasher_48_8 = BabyBearConfig48::hasher();
        Self {
            hasher_24_8,
            hasher_32_8,
            hasher_48_8,
        }
    }
}

impl Chipset<BabyBear> for LurkHasher {
    #[inline]
    fn input_size(&self) -> usize {
        unimplemented!()
    }

    #[inline]
    fn output_size(&self) -> usize {
        8
    }

    fn require_size(&self) -> usize {
        unimplemented!()
    }

    fn execute(&self, preimg: &[BabyBear]) -> Vec<BabyBear> {
        macro_rules! hash_with {
            ($name:ident) => {
                self.$name.permute(sized!(preimg))[..self.output_size()].into()
            };
        }
        match preimg.len() {
            24 => hash_with!(hasher_24_8),
            32 => hash_with!(hasher_32_8),
            48 => hash_with!(hasher_48_8),
            _ => unimplemented!(),
        }
    }

    fn witness_size(&self) -> usize {
        unimplemented!()
    }

    fn populate_witness(&self, _preimg: &[BabyBear], _witness: &mut [BabyBear]) -> Vec<BabyBear> {
        unimplemented!()
    }

    fn eval<AB: AirBuilder<F = BabyBear> + LookupBuilder>(
        &self,
        _: &mut AB,
        _: AB::Expr,
        _: Vec<AB::Expr>,
        _: &[AB::Var],
        _: &[AB::Var],
        _: AB::Expr,
        _: &[RequireRecord<AB::Var>],
    ) {
        unimplemented!()
    }
}
