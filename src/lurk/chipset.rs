use p3_air::AirBuilder;
use p3_baby_bear::BabyBear;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    lair::{chipset::Chipset, execute::QueryRecord},
    poseidon::config::{BabyBearConfig24, BabyBearConfig32, BabyBearConfig40},
};

use crate::lair::{map::Map, Name};
use crate::lurk::poseidon::PoseidonChipset;

use super::{big_num::BigNum, u64::U64, zstore::Hasher};

#[derive(Clone)]
pub enum LurkChip {
    Hasher24_8(PoseidonChipset<BabyBearConfig24, 24>),
    Hasher32_8(PoseidonChipset<BabyBearConfig32, 32>),
    Hasher40_8(PoseidonChipset<BabyBearConfig40, 40>),
    U64(U64),
    BigNum(BigNum),
}

pub fn lurk_chip_map() -> Map<Name, LurkChip> {
    let hash_24_8 = LurkChip::Hasher24_8(PoseidonChipset::default());
    let hash_32_8 = LurkChip::Hasher32_8(PoseidonChipset::default());
    let hash_40_8 = LurkChip::Hasher40_8(PoseidonChipset::default());
    let u64_add = LurkChip::U64(U64::Add);
    let u64_sub = LurkChip::U64(U64::Sub);
    let u64_mul = LurkChip::U64(U64::Mul);
    let u64_divrem = LurkChip::U64(U64::DivRem);
    let u64_lessthan = LurkChip::U64(U64::LessThan);
    let u64_iszero = LurkChip::U64(U64::IsZero);
    let big_num_lessthan = LurkChip::BigNum(BigNum::LessThan);
    let vec = vec![
        (Name("hash_24_8"), hash_24_8),
        (Name("hash_32_8"), hash_32_8),
        (Name("hash_40_8"), hash_40_8),
        (Name("u64_add"), u64_add),
        (Name("u64_sub"), u64_sub),
        (Name("u64_mul"), u64_mul),
        (Name("u64_divrem"), u64_divrem),
        (Name("u64_lessthan"), u64_lessthan),
        (Name("u64_iszero"), u64_iszero),
        (Name("big_num_lessthan"), big_num_lessthan),
    ];
    Map::from_vec(vec)
}

impl Chipset<BabyBear> for LurkChip {
    #[inline]
    fn input_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(op) => op.input_size(),
            LurkChip::Hasher32_8(op) => op.input_size(),
            LurkChip::Hasher40_8(op) => op.input_size(),
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::input_size(op),
            LurkChip::BigNum(op) => <BigNum as Chipset<BabyBear>>::input_size(op),
        }
    }

    #[inline]
    fn output_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(op) => op.output_size(),
            LurkChip::Hasher32_8(op) => op.output_size(),
            LurkChip::Hasher40_8(op) => op.output_size(),
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::output_size(op),
            LurkChip::BigNum(op) => <BigNum as Chipset<BabyBear>>::output_size(op),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(op) => op.witness_size(),
            LurkChip::Hasher32_8(op) => op.witness_size(),
            LurkChip::Hasher40_8(op) => op.witness_size(),
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::witness_size(op),
            LurkChip::BigNum(op) => <BigNum as Chipset<BabyBear>>::witness_size(op),
        }
    }

    fn require_size(&self) -> usize {
        match self {
            LurkChip::Hasher24_8(op) => op.require_size(),
            LurkChip::Hasher32_8(op) => op.require_size(),
            LurkChip::Hasher40_8(op) => op.require_size(),
            LurkChip::U64(op) => <U64 as Chipset<BabyBear>>::require_size(op),
            LurkChip::BigNum(op) => <BigNum as Chipset<BabyBear>>::require_size(op),
        }
    }

    fn execute_simple(&self, input: &[BabyBear]) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(hasher) => hasher.execute_simple(input),
            LurkChip::Hasher32_8(hasher) => hasher.execute_simple(input),
            LurkChip::Hasher40_8(hasher) => hasher.execute_simple(input),
            LurkChip::U64(..) | LurkChip::BigNum(..) => panic!("use `execute`"),
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
            LurkChip::Hasher24_8(hasher) => hasher.execute(input, nonce, queries, requires),
            LurkChip::Hasher32_8(hasher) => hasher.execute(input, nonce, queries, requires),
            LurkChip::Hasher40_8(hasher) => hasher.execute(input, nonce, queries, requires),
            LurkChip::U64(op) => op.execute(input, nonce, queries, requires),
            LurkChip::BigNum(op) => op.execute(input, nonce, queries, requires),
        }
    }

    fn populate_witness(&self, input: &[BabyBear], witness: &mut [BabyBear]) -> Vec<BabyBear> {
        match self {
            LurkChip::Hasher24_8(hasher) => hasher.populate_witness(input, witness),
            LurkChip::Hasher32_8(hasher) => hasher.populate_witness(input, witness),
            LurkChip::Hasher40_8(hasher) => hasher.populate_witness(input, witness),
            LurkChip::U64(op) => op.populate_witness(input, witness),
            LurkChip::BigNum(op) => op.populate_witness(input, witness),
        }
    }

    fn eval<AB: AirBuilder<F = BabyBear> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        preimg: Vec<AB::Expr>,
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        match self {
            LurkChip::Hasher24_8(hasher) => {
                hasher.eval(builder, is_real, preimg, witness, nonce, requires)
            }
            LurkChip::Hasher32_8(hasher) => {
                hasher.eval(builder, is_real, preimg, witness, nonce, requires)
            }
            LurkChip::Hasher40_8(hasher) => {
                hasher.eval(builder, is_real, preimg, witness, nonce, requires)
            }
            LurkChip::U64(op) => op.eval(builder, is_real, preimg, witness, nonce, requires),
            LurkChip::BigNum(op) => op.eval(builder, is_real, preimg, witness, nonce, requires),
        }
    }
}

pub type LurkHasher = Hasher<BabyBear, LurkChip>;

#[inline]
pub fn lurk_hasher() -> LurkHasher {
    Hasher::new(
        LurkChip::Hasher24_8(PoseidonChipset::default()),
        LurkChip::Hasher32_8(PoseidonChipset::default()),
        LurkChip::Hasher40_8(PoseidonChipset::default()),
    )
}
