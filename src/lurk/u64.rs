use std::array;
use std::borrow::{Borrow, BorrowMut};

use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    gadgets::{
        bytes::{builder::BytesAirRecordWithContext, record::DummyBytesRecord},
        unsigned::{
            add::{Diff64, Sum64},
            div_rem::DivRem64,
            less_than::IsLessThan64,
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
    DivRem,
    LessThan,
}

fn into_u64<F: PrimeField32>(slice: &[F]) -> u64 {
    assert_eq!(slice.len(), 8);
    let buf: [u8; 8] = array::from_fn(|i| slice[i].as_canonical_u32().try_into().unwrap());
    u64::from_le_bytes(buf)
}

impl<F: PrimeField32> Chipset<F> for U64 {
    fn input_size(&self) -> usize {
        16
    }

    fn output_size(&self) -> usize {
        match self {
            U64::DivRem => 16,  // returns (quot, rem)
            U64::LessThan => 1, // returns one bool
            _ => 8,
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            U64::Add => Sum64::<F>::witness_size(),
            U64::Sub => Diff64::<F>::witness_size(),
            U64::Mul => Product64::<F>::witness_size(),
            U64::DivRem => DivRem64::<F>::witness_size(),
            U64::LessThan => IsLessThan64::<F>::witness_size(),
        }
    }

    fn require_size(&self) -> usize {
        match self {
            U64::Add => Sum64::<F>::num_requires(),
            U64::Sub => Diff64::<F>::num_requires(),
            U64::Mul => Product64::<F>::num_requires(),
            U64::DivRem => DivRem64::<F>::num_requires(),
            U64::LessThan => IsLessThan64::<F>::num_requires(),
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
        let bytes = &mut queries.bytes.context(nonce, requires);
        match self {
            U64::Add => {
                let mut add_witness = Sum64::<F>::default();
                let add = add_witness.populate(&in1, &in2, bytes);
                add.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::Sub => {
                let mut sub_witness = Diff64::<F>::default();
                let sub = sub_witness.populate(&in1, &in2, bytes);
                sub.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::Mul => {
                let mut mul_witness = Product64::<F>::default();
                let mul = mul_witness.populate(&in1, &in2, bytes);
                mul.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::DivRem => {
                let mut div_witness = DivRem64::<F>::default();
                let (div, rem) = div_witness.populate(&in1, &in2, bytes);
                div.to_le_bytes()
                    .into_iter()
                    .chain(rem.to_le_bytes())
                    .map(F::from_canonical_u8)
                    .collect()
            }
            U64::LessThan => {
                let mut lessthan_witness = IsLessThan64::<F>::default();
                let lessthan = lessthan_witness.populate_less_than(&in1, &in2, bytes);
                vec![F::from_bool(lessthan)]
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
                add.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::Sub => {
                let mut sub_witness = Diff64::<F>::default();
                let sub = sub_witness.populate(&in1, &in2, bytes);
                sub.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::Mul => {
                // TODO: Clean up the API and remove these hardcoded 16/8 values?
                //   This is here because Product64 contains the result, but the witness and output are separate
                let mut out = vec![F::zero(); 16];
                let mul_witness: &mut Product64<F> = out.as_mut_slice().borrow_mut();
                let mul = mul_witness.populate(&in1, &in2, bytes);
                witness.copy_from_slice(&out[8..16]);
                mul.to_le_bytes().map(F::from_canonical_u8).to_vec()
            }
            U64::DivRem => {
                let mut out = vec![F::zero(); DivRem64::<F>::witness_size()];
                let div_witness: &mut DivRem64<F> = out.as_mut_slice().borrow_mut();
                let (div, rem) = div_witness.populate(&in1, &in2, bytes);
                witness.copy_from_slice(&out);
                div.to_le_bytes()
                    .into_iter()
                    .chain(rem.to_le_bytes())
                    .map(F::from_canonical_u8)
                    .collect()
            }
            U64::LessThan => {
                // TODO: Clean up API, same as Mul case, but result is after the witness this time
                let mut out = vec![F::zero(); IsLessThan64::<F>::witness_size() + 1]; // + 1 for the output bool
                let lessthan_witness: &mut IsLessThan64<F> = out.as_mut_slice().borrow_mut();
                let lessthan = lessthan_witness.populate_less_than(&in1, &in2, bytes);
                witness.copy_from_slice(&out[0..IsLessThan64::<F>::witness_size()]);
                vec![F::from_bool(lessthan)]
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
                vec.extend(witness);
                let mul: &Product64<AB::Var> = vec.as_slice().borrow();
                mul.eval(builder, &in1, &in2, &mut air_record, is_real);
            }
            U64::DivRem => {
                let vec = witness.to_vec();
                let divrem: &DivRem64<AB::Var> = vec.as_slice().borrow();
                let (div, rem) = divrem.eval(builder, &in1, &in2, &mut air_record, is_real);
                for (div_limb, out_limb) in div.iter().zip(out[0..8].iter()) {
                    builder.assert_eq(*div_limb, *out_limb);
                }
                for (rem_limb, out_limb) in rem.iter().zip(out[8..16].iter()) {
                    builder.assert_eq(*rem_limb, *out_limb);
                }
            }
            U64::LessThan => {
                let mut vec = witness.to_vec();
                vec.extend(out);
                let lessthan: &IsLessThan64<AB::Var> = vec.as_slice().borrow();
                let res = lessthan.eval_less_than(builder, &in1, &in2, &mut air_record, is_real);
                builder.assert_bool(res);
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
            let d: [8] = extern_call(u64_mul, c, c);
            let e: [8] = extern_call(u64_mul, d, d);
            let f: [8] = extern_call(u64_mul, e, e);
            let g: [8] = extern_call(u64_mul, f, f);
            return g
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[mul_func], lurk_chip_map);

        let mul_chip = FuncChip::from_name("mul", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(2),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            //
            f(2),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
        ];
        let out = toplevel.execute_by_name("mul", args, &mut queries);
        assert_eq!(
            out.as_ref(),
            &[f(0), f(0), f(0), f(0), f(1), f(0), f(0), f(0)]
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

    #[test]
    fn u64_divrem_test() {
        sphinx_core::utils::setup_logger();

        let divrem_func = func!(
        fn divrem(a: [8], b: [8]): [16] {
            let (div: [8], rem: [8]) = extern_call(u64_divrem, a, b);
            return (div, rem)
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[divrem_func], lurk_chip_map);

        let divrem_chip = FuncChip::from_name("divrem", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(0),
            f(0),
            f(1),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            //
            f(7),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
        ];
        let out = toplevel.execute_by_name("divrem", args, &mut queries);
        assert_eq!(
            out.as_ref(),
            &[
                f(146),
                f(36),
                f(0),
                f(0),
                f(0),
                f(0),
                f(0),
                f(0),
                //
                f(2),
                f(0),
                f(0),
                f(0),
                f(0),
                f(0),
                f(0),
                f(0)
            ]
        );

        let lair_chips = build_lair_chip_vector(&divrem_chip);
        debug_chip_constraints_and_queries_with_sharding(&queries, &lair_chips, None);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&divrem_chip),
            queries.expect_public_values().len(),
        );

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        machine.debug_constraints(&pk, shard.clone());
    }

    #[test]
    fn u64_lessthan_test() {
        sphinx_core::utils::setup_logger();

        let lessthan_func = func!(
        fn lessthan(a: [8], b: [8]): [1] {
            let c = extern_call(u64_lessthan, a, b);
            return c
        });
        let lurk_chip_map = lurk_chip_map();
        let toplevel = Toplevel::new(&[lessthan_func], lurk_chip_map);

        let lessthan_chip = FuncChip::from_name("lessthan", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let f = F::from_canonical_usize;
        // Little endian
        let args = &[
            f(200),
            f(200),
            f(200),
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            //
            f(0),
            f(0),
            f(0),
            f(0),
            f(0),
            f(10),
            f(0),
            f(0),
        ];
        let out = toplevel.execute_by_name("lessthan", args, &mut queries);
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
