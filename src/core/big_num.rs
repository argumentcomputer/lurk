use std::borrow::{Borrow, BorrowMut};

use num_bigint::BigUint;
use p3_air::AirBuilder;
use p3_field::{PrimeField, PrimeField32};

use crate::gadgets::big_num::cmp::BigNumCompareWitness;
use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    gadgets::bytes::{builder::BytesAirRecordWithContext, record::DummyBytesRecord},
    lair::{chipset::Chipset, execute::QueryRecord},
};

#[derive(Clone)]
pub enum BigNum {
    LessThan,
}

impl<F: PrimeField32> Chipset<F> for BigNum {
    fn input_size(&self) -> usize {
        match self {
            BigNum::LessThan => 16,
        }
    }

    fn output_size(&self) -> usize {
        match self {
            BigNum::LessThan => 1,
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            BigNum::LessThan => BigNumCompareWitness::<F>::witness_size(),
        }
    }

    fn require_size(&self) -> usize {
        match self {
            BigNum::LessThan => BigNumCompareWitness::<F>::num_requires(),
        }
    }

    fn execute(
        &self,
        input: &[F],
        nonce: u32,
        query_index: usize,
        queries: &mut QueryRecord<F>,
        requires: &mut Vec<Record>,
    ) -> Vec<F> {
        let in1: [F; 8] = input[0..8].try_into().unwrap();
        let in2: [F; 8] = input[8..16].try_into().unwrap();
        let bytes = &mut queries.bytes.context(nonce, query_index, requires);
        match self {
            BigNum::LessThan => {
                let mut witness = BigNumCompareWitness::<F>::default();
                witness.populate(&in1, &in2, bytes);
                witness.iter_result().into_iter().collect()
            }
        }
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        let in1: [F; 8] = input[0..8].try_into().unwrap();
        let in2: [F; 8] = input[8..16].try_into().unwrap();
        let bytes = &mut DummyBytesRecord;
        match self {
            BigNum::LessThan => {
                let witness: &mut BigNumCompareWitness<F> = witness.borrow_mut();
                witness.populate(&in1, &in2, bytes);
                witness.iter_result().into_iter().collect()
            }
        }
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        ins: Vec<AB::Expr>,
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        let in1: [AB::Expr; 8] = ins[0..8].to_vec().try_into().unwrap();
        let in2: [AB::Expr; 8] = ins[8..16].to_vec().try_into().unwrap();
        let mut air_record = BytesAirRecordWithContext::default();
        let out = match self {
            BigNum::LessThan => {
                let witness: &BigNumCompareWitness<AB::Var> = witness.borrow();
                let cmp = witness.eval(builder, &in1, &in2, &mut air_record, is_real.clone());
                vec![cmp.is_less_than()]
            }
        };
        air_record.require_all(builder, nonce, requires.iter().cloned());
        out
    }
}

/// Returns a `BigUint` from a digest of field elements stored in little-endian order.
pub fn field_elts_to_biguint<F: PrimeField>(elts: &[F]) -> BigUint {
    let mut num = elts[elts.len() - 1].as_canonical_biguint();
    for l in elts[..elts.len() - 1].iter().rev() {
        num *= F::order();
        num += l.as_canonical_biguint();
    }
    num
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use sphinx_core::{stark::StarkMachine, utils::BabyBearPoseidon2};

    use crate::{
        air::debug::debug_chip_constraints_and_queries_with_sharding,
        core::chipset::lurk_chip_map_native,
        func,
        lair::{
            execute::{QueryRecord, Shard},
            func_chip::FuncChip,
            lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
            toplevel::Toplevel,
        },
    };

    #[test]
    fn big_num_lessthan_test() {
        sphinx_core::utils::setup_logger();

        let lessthan_func = func!(
        fn lessthan(a: [8], b: [8]): [1] {
            let c = extern_call(big_num_lessthan, a, b);
            return c
        });
        let lurk_chip_map = lurk_chip_map_native();
        let toplevel = Toplevel::new(&[lessthan_func], lurk_chip_map);

        let lessthan_chip = FuncChip::from_name("lessthan", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(16777216),
            f(16777216 * 2),
            f(16777216 * 3),
            f(16777216 * 4),
            f(16777216 * 5),
            f(16777216 * 6),
            f(16777216 * 7),
            f(16777216 * 8),
            //
            f(16777216 * 11),
            f(16777216 * 12),
            f(16777216 * 13),
            f(16777216 * 14),
            f(16777216 * 15),
            f(16777216 * 16),
            f(16777216 * 17),
            f(16777216 * 18),
        ];
        let out = toplevel
            .execute_by_name("lessthan", args, &mut queries, None)
            .unwrap();
        assert_eq!(out.as_ref(), &[f(1)]);

        let lair_chips = build_lair_chip_vector(&lessthan_chip);
        debug_chip_constraints_and_queries_with_sharding(&queries, &lair_chips, None);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&lessthan_chip),
            queries.expect_public_values().len(),
        );

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        machine.debug_constraints(&pk, shard.clone());
    }
}
