use std::marker::PhantomData;

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

use super::zstore::Hasher;

#[derive(Clone)]
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

    fn execute_simple(&self, preimg: &[BabyBear]) -> Vec<BabyBear> {
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

pub fn lurk_hasher() -> Hasher<BabyBear, LurkChip> {
    let comm = LurkChip::Hasher24_8(BabyBearConfig24::hasher());
    let hash2 = LurkChip::Hasher32_8(BabyBearConfig32::hasher());
    let hash3 = LurkChip::Hasher48_8(BabyBearConfig48::hasher());
    let _p = PhantomData;
    Hasher {
        comm,
        hash2,
        hash3,
        _p,
    }
}
