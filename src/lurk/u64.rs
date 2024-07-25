use std::borrow::{Borrow, BorrowMut};

use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    gadgets::{
        bytes::{
            builder::BytesAirRecordWithContext,
            record::{BytesRecordWithContext, DummyBytesRecord},
        },
        unsigned::{
            add::{Diff64, Sum64},
            mul::Product64,
            Word64,
        },
    },
    lair::{chipset::Chipset, execute::QueryRecord},
};

#[derive(Clone)]
pub enum U64 {
    Add,
    Sub,
    Mul,
}

fn into_u64<F: PrimeField32>(slice: &[F]) -> u64 {
    assert_eq!(slice.len(), 8);
    let bytes: Vec<_> = slice.iter().map(|f| F::as_canonical_u32(f) as u8).collect();
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&bytes);
    u64::from_le_bytes(buf)
}

impl<F: PrimeField32> Chipset<F> for U64 {
    fn input_size(&self) -> usize {
        16
    }

    fn output_size(&self) -> usize {
        8
    }

    fn require_size(&self) -> usize {
        match self {
            U64::Add => Sum64::<F>::num_requires(),
            U64::Sub => Diff64::<F>::num_requires(),
            U64::Mul => Product64::<F>::num_requires(),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            U64::Add => Sum64::<F>::num_values(),
            U64::Sub => Diff64::<F>::num_values(),
            U64::Mul => Product64::<F>::num_values(),
        }
    }

    fn execute(
        &self,
        input: &[F],
        nonce: u32,
        queries: &mut QueryRecord<F>,
        requires: &mut Vec<Record>,
    ) -> Vec<F> {
        let in1 = into_u64(&input[0..8]);
        let in2 = into_u64(&input[8..16]);
        let bytes = &mut BytesRecordWithContext {
            nonce,
            requires,
            record: &mut queries.bytes,
        };
        match self {
            U64::Add => {
                let mut add_witness = Sum64::<F>::default();
                let add = add_witness.populate(&in1, &in2, bytes);
                add.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
            }
            U64::Sub => {
                let mut sub_witness = Diff64::<F>::default();
                let sub = sub_witness.populate(&in1, &in2, bytes);
                sub.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
            }
            U64::Mul => {
                let mut mul_witness = Product64::<F>::default();
                let mul = mul_witness.populate(&in1, &in2, bytes);
                mul.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
            }
        }
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        let in1 = into_u64(&input[0..8]);
        let in2 = into_u64(&input[8..16]);
        let bytes = &mut DummyBytesRecord;
        match self {
            U64::Add => {
                let mut add_witness = Sum64::<F>::default();
                let add = add_witness.populate(&in1, &in2, bytes);
                add.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
            }
            U64::Sub => {
                let mut sub_witness = Diff64::<F>::default();
                let sub = sub_witness.populate(&in1, &in2, bytes);
                sub.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
            }
            U64::Mul => {
                let mut out = vec![F::zero(); 16];
                let mul_witness: &mut Product64<F> = out.as_mut_slice().borrow_mut();
                let mul = mul_witness.populate(&in1, &in2, bytes);
                witness.copy_from_slice(&mul_witness.witness.carry);
                mul.to_le_bytes()
                    .into_iter()
                    .map(|b| F::from_canonical_u8(b))
                    .collect()
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
        let in1 = ins[0..8].iter().cloned().collect::<Word64<_>>();
        let in2 = ins[8..16].iter().cloned().collect::<Word64<_>>();
        let mut air_record = BytesAirRecordWithContext::default();
        match self {
            U64::Add => {
                let add: &Sum64<AB::Var> = out.borrow();
                add.eval(builder, in1, in2, &mut air_record, is_real);
            }
            U64::Sub => {
                let sub: &Diff64<AB::Var> = out.borrow();
                sub.eval(builder, in1, in2, &mut air_record, is_real);
            }
            U64::Mul => {
                let mut vec = out.to_vec();
                println!("vec: {}", vec.len());
                vec.extend(witness);
                println!("vec: {}", vec.len());
                let mul: &Product64<AB::Var> = vec.as_slice().borrow();
                mul.eval(builder, &in1, &in2, &mut air_record, is_real);
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
