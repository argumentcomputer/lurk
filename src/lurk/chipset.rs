use p3_air::AirBuilder;
use p3_baby_bear::BabyBear;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    lair::{chipset::Chipset, execute::QueryRecord},
    poseidon::{
        config::{
            BabyBearConfig24, BabyBearConfig32, BabyBearConfig48, InternalDiffusion, PoseidonConfig,
        },
        wide::{air::eval_input, columns::Poseidon2Cols, trace::populate_witness},
    },
};

use crate::lair::{map::Map, Name};

use super::{u64::U64, zstore::Hasher};

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
    U64(U64),
}

pub fn lurk_chip_map() -> Map<Name, LurkChip> {
    let hash_24_8 = LurkChip::Hasher24_8(BabyBearConfig24::hasher());
    let hash_32_8 = LurkChip::Hasher32_8(BabyBearConfig32::hasher());
    let hash_48_8 = LurkChip::Hasher48_8(BabyBearConfig48::hasher());
    let u64_add = LurkChip::U64(U64::Add);
    let u64_sub = LurkChip::U64(U64::Sub);
    let u64_mul = LurkChip::U64(U64::Mul);
    let u64_divrem = LurkChip::U64(U64::DivRem);
    let u64_lessthan = LurkChip::U64(U64::LessThan);
    let vec = vec![
        (Name("hash_24_8"), hash_24_8),
        (Name("hash_32_8"), hash_32_8),
        (Name("hash_48_8"), hash_48_8),
        (Name("u64_add"), u64_add),
        (Name("u64_sub"), u64_sub),
        (Name("u64_mul"), u64_mul),
        (Name("u64_divrem"), u64_divrem),
        (Name("u64_lessthan"), u64_lessthan),
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
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::input_size(op),
        }
    }

    #[inline]
    fn output_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(..) | LurkChip::Hasher32_8(..) | LurkChip::Hasher48_8(..) => 8,
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::output_size(op),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig24, 24>::num_cols(),
            LurkChip::Hasher32_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig32, 32>::num_cols(),
            LurkChip::Hasher48_8(..) => Poseidon2Cols::<BabyBear, BabyBearConfig48, 48>::num_cols(),
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::witness_size(op),
        }
    }

    fn require_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(..) | LurkChip::Hasher32_8(..) | LurkChip::Hasher48_8(..) => 0,
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::require_size(op),
        }
    }

    fn execute_simple(&self, preimg: &[BabyBear]) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
            LurkChip::Hasher32_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
            LurkChip::Hasher48_8(hash) => hash.permute(sized!(preimg))[..self.output_size()].into(),
            LurkChip::U64(..) => panic!("use `execute`"),
        }
    }

    fn execute(
        &self,
        input: &[BabyBear],
        nonce: u32,
        queries: &mut QueryRecord<BabyBear>,
        requires: &mut Vec<Record>,
    ) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(hash) => hash.permute(sized!(input))[..self.output_size()].into(),
            LurkChip::Hasher32_8(hash) => hash.permute(sized!(input))[..self.output_size()].into(),
            LurkChip::Hasher48_8(hash) => hash.permute(sized!(input))[..self.output_size()].into(),
            LurkChip::U64(op) => op.execute(input, nonce, queries, requires),
        }
    }

    fn populate_witness(&self, input: &[BabyBear], witness: &mut [BabyBear]) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(..) => {
                let mut out: Vec<_> =
                    populate_witness::<BabyBearConfig24, 24>(sized!(input), witness).into();
                out.truncate(8);
                out
            }
            LurkChip::Hasher32_8(..) => {
                let mut out: Vec<_> =
                    populate_witness::<BabyBearConfig32, 32>(sized!(input), witness).into();
                out.truncate(8);
                out
            }
            LurkChip::Hasher48_8(..) => {
                let mut out: Vec<_> =
                    populate_witness::<BabyBearConfig48, 48>(sized!(input), witness).into();
                out.truncate(8);
                out
            }
            LurkChip::U64(op) => op.populate_witness(input, witness),
        }
    }

    fn eval<AB: AirBuilder<F = BabyBear> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        preimg: Vec<AB::Expr>,
        img: &[AB::Var],
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
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
            LurkChip::U64(op) => op.eval(builder, is_real, preimg, img, witness, nonce, requires),
        }
    }
}

pub type LurkHasher = Hasher<BabyBear, LurkChip>;

#[inline]
pub fn lurk_hasher() -> LurkHasher {
    Hasher::new(
        LurkChip::Hasher24_8(BabyBearConfig24::hasher()),
        LurkChip::Hasher32_8(BabyBearConfig32::hasher()),
        LurkChip::Hasher48_8(BabyBearConfig48::hasher()),
    )
}
