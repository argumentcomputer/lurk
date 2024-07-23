use std::borrow::Borrow;
use std::sync::{Arc, RwLock};

use hybrid_array::sizes::U8;
use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    gadgets::{
        bytes::{builder::BytesAirRecordWithContext, record::BytesRecordWithContext},
        unsigned::{
            add::{eval_add, eval_sub, num_requires, populate_add, populate_sub},
            mul::{eval_mul, Mul64Witness},
            Word64,
        },
    },
    lair::{chipset::Chipset, execute::QueryRecord},
};

#[derive(Clone)]
pub enum U64<F> {
    Add,
    Sub,
    Mul(Arc<RwLock<Mul64Witness<F>>>),
}

fn into_wrd<T: Clone + std::fmt::Debug>(iter: impl Iterator<Item = T>) -> Word64<T> {
    <[T; 8]>::try_from(iter.collect::<Vec<_>>()).unwrap().into()
}

fn into_u8_wrd<F: PrimeField32>(slice: &[F]) -> Word64<u8> {
    <[u8; 8]>::try_from(
        slice
            .iter()
            .map(|f| F::as_canonical_u32(f).try_into().unwrap())
            .collect::<Vec<u8>>(),
    )
    .unwrap()
    .into()
}

impl<F: PrimeField32> Chipset<F> for U64<F> {
    fn input_size(&self) -> usize {
        16
    }

    fn output_size(&self) -> usize {
        8
    }

    fn require_size(&self) -> usize {
        match self {
            U64::Add | U64::Sub => num_requires::<U8>(),
            U64::Mul(..) => Mul64Witness::<F>::num_requires(),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            U64::Add | U64::Sub => 0,
            U64::Mul(..) => Mul64Witness::<F>::num_values(),
        }
    }

    fn execute(
        &self,
        input: &[F],
        nonce: u32,
        queries: &mut QueryRecord<F>,
        requires: &mut Vec<Record>,
    ) -> Vec<F> {
        let in1 = into_u8_wrd(&input[0..8]);
        let in2 = into_u8_wrd(&input[8..16]);
        let bytes = &mut BytesRecordWithContext {
            nonce,
            requires,
            record: &mut queries.bytes,
        };
        match self {
            U64::Add => {
                let add = populate_add(in1, in2, bytes);
                add.into_field().into_iter().collect()
            }
            U64::Sub => {
                let sub = populate_sub(in1, in2, bytes);
                sub.into_field().into_iter().collect()
            }
            U64::Mul(witness) => {
                let mul = witness.write().unwrap().populate(&in1, &in2, bytes);
                mul.into_field().into_iter().collect()
            }
        }
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        let in1 = into_u8_wrd(&input[0..8]);
        let in2 = into_u8_wrd(&input[8..16]);
        match self {
            U64::Add => {
                let add = in1 + in2;
                add.into_field().into_iter().collect()
            }
            U64::Sub => {
                let sub = in1 - in2;
                sub.into_field().into_iter().collect()
            }
            U64::Mul(mul_witness) => {
                let mul = in1 * in2;
                for (i, w) in mul_witness.read().unwrap().values().into_iter().enumerate() {
                    witness[i] = w;
                }
                mul.into_field().into_iter().collect()
            }
        }
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        ins: Vec<AB::Expr>,
        out: &[AB::Var],
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) {
        let in1 = into_wrd(ins[0..8].iter().cloned());
        let in2 = into_wrd(ins[8..16].iter().cloned());
        let out = into_wrd(out.iter().map(|&o| o.into()));
        let mut air_record = BytesAirRecordWithContext::default();
        match self {
            U64::Add => eval_add(builder, (in1, in2), out, &mut air_record, is_real),
            U64::Sub => eval_sub(builder, (in1, in2), out, &mut air_record, is_real),
            U64::Mul(..) => {
                let mul_witness: &Mul64Witness<AB::Var> = witness.borrow();
                eval_mul(
                    builder,
                    (in1, in2),
                    out,
                    mul_witness,
                    &mut air_record,
                    is_real,
                )
            }
        }
        air_record.require_all(builder, nonce, requires.iter().cloned());
    }
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use sphinx_core::{stark::StarkMachine, utils::BabyBearPoseidon2};

    use crate::{
        air::debug::debug_chip_constraints_and_queries_with_sharding,
        func,
        lair::{
            execute::{QueryRecord, Shard},
            func_chip::FuncChip,
            lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
            toplevel::Toplevel,
        },
        lurk::chipset::lurk_chip_map,
    };

    #[test]
    fn u64_add_test() {
        sphinx_core::utils::setup_logger();

        let add_func = func!(
        fn add(a: [8], b: [8]): [8] {
            let c: [8] = extern_call(u64_add, a, b);
            return c
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[add_func], lurk_chip_map);

        let add_chip = FuncChip::from_name("add", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(200),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            //
            f(56),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
        ];
        let out = toplevel.execute_by_name("add", args, &mut queries);
        assert_eq!(
            out.as_ref(),
            &[f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(0)]
        );

        let lair_chips = build_lair_chip_vector(&add_chip);
        debug_chip_constraints_and_queries_with_sharding(&queries, &lair_chips, None);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&add_chip),
            queries.expect_public_values().len(),
        );

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        machine.debug_constraints(&pk, shard.clone());
    }

    #[test]
    fn u64_sub_test() {
        sphinx_core::utils::setup_logger();

        let sub_func = func!(
        fn sub(a: [8], b: [8]): [8] {
            let c: [8] = extern_call(u64_sub, a, b);
            return c
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[sub_func], lurk_chip_map);

        let sub_chip = FuncChip::from_name("sub", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(0),
            f(1),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            //
            f(1),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
        ];
        let out = toplevel.execute_by_name("sub", args, &mut queries);
        assert_eq!(
            out.as_ref(),
            &[f(255), f(0), f(0), f(0), f(0), f(0), f(0), f(0)]
        );

        let lair_chips = build_lair_chip_vector(&sub_chip);
        debug_chip_constraints_and_queries_with_sharding(&queries, &lair_chips, None);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&sub_chip),
            queries.expect_public_values().len(),
        );

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        machine.debug_constraints(&pk, shard.clone());
    }

    #[test]
    fn u64_mul_test() {
        sphinx_core::utils::setup_logger();

        let mul_func = func!(
        fn mul(a: [8], b: [8]): [8] {
            let c: [8] = extern_call(u64_mul, a, b);
            return c
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[mul_func], lurk_chip_map);

        let mul_chip = FuncChip::from_name("mul", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
            f(1),
        ];
        let out = toplevel.execute_by_name("mul", args, &mut queries);
        assert_eq!(
            out.as_ref(),
            &[f(1), f(2), f(3), f(4), f(5), f(6), f(7), f(8)]
        );

        let lair_chips = build_lair_chip_vector(&mul_chip);
        debug_chip_constraints_and_queries_with_sharding(&queries, &lair_chips, None);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&mul_chip),
            queries.expect_public_values().len(),
        );

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        machine.debug_constraints(&pk, shard.clone());
    }
}
