use crate::air::builder::{LookupBuilder, Relation};
use itertools::{chain, repeat_n, Itertools};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};
use sphinx_core::air::{EventLens, MachineAir, WithEvents};
use std::iter::zip;
use std::marker::PhantomData;
use std::ops::Deref;

use super::execute::{mem_index_from_len, MemMap, QueryRecord};

const MEMORY_TAG: u32 = 42;
pub struct MemoryRelation<Ptr, ValuesIter>(pub Ptr, pub ValuesIter);

impl<T, Ptr, IntoValuesIter, Value> Relation<T> for MemoryRelation<Ptr, IntoValuesIter>
where
    T: AbstractField,
    Ptr: Into<T>,
    IntoValuesIter: IntoIterator<Item = Value>,
    Value: Into<T>,
{
    fn values(self) -> impl IntoIterator<Item = T> {
        let Self(ptr, values_iter) = self;
        chain(
            [T::from_canonical_u32(MEMORY_TAG), ptr.into()],
            values_iter.into_iter().map(Into::into),
        )
    }
}

#[derive(Default)]
pub struct MemChip<F> {
    len: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> EventLens<MemChip<F>> for QueryRecord<F> {
    fn events(&self) -> <MemChip<F> as WithEvents<'_>>::Events {
        self.mem_queries.as_slice()
    }
}

impl<'a, F: Field> WithEvents<'a> for MemChip<F> {
    type Events = &'a [MemMap<F>];
}

impl<F: Field> MachineAir<F> for MemChip<F> {
    type Record = QueryRecord<F>;
    type Program = QueryRecord<F>;

    fn name(&self) -> String {
        format!("mem {}", self.len).to_string()
    }

    fn generate_trace<EL: EventLens<Self>>(
        &self,
        input: &EL,
        _output: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        let len = self.len;
        let mem_idx = mem_index_from_len(len);
        let mem = &input.events()[mem_idx];
        let width = self.width();

        let height = mem
            .values()
            .map(|&m| m as usize)
            .sum::<usize>()
            .next_power_of_two()
            .max(4);
        let mut rows = vec![F::zero(); height * width];

        let values = mem
            .iter()
            .enumerate()
            .flat_map(|(i, (args, &mult))| {
                // We skip the address 0 as to leave room for null pointers
                let ptr = F::from_canonical_usize(i + 1);
                let values: &[F] = args.deref();

                repeat_n((ptr, values), mult as usize)
            })
            .collect_vec();

        rows.par_chunks_mut(width)
            .zip(values)
            .for_each(|(row, (ptr, values))| {
                // is_real
                row[0] = F::one();
                // ptr
                row[1] = ptr;
                // values
                row[2..].copy_from_slice(values);
            });
        RowMajorMatrix::new(rows, width)
    }

    fn included(&self, _shard: &Self::Record) -> bool {
        true
    }
}

impl<AB> Air<AB> for MemChip<AB::F>
where
    AB: LookupBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &[AB::Var] = &main.row_slice(0);
        let next: &[AB::Var] = &main.row_slice(1);

        let (is_real, ptr_local, values_local) = (local[0], local[1], &local[2..]);
        let (is_real_next, ptr_next, values_next) = (next[0], next[1], &next[2..]);

        // is_real is 1 for all valid entries, then 0 for padding rows until the last row.
        builder.assert_bool(is_real);
        // is_real starts with one
        builder.when_first_row().assert_one(is_real);

        // all but the last rows where is_real = 1
        let is_real_transition = is_real_next * builder.is_transition();

        // if we are in a real transition, the current row should be real
        builder.when(is_real_transition.clone()).assert_one(is_real);

        // First valid pointer is 1
        builder.when_first_row().assert_one(ptr_local);

        // Next pointer is either the same, or increased by 1
        let is_next_ptr_diff = ptr_next - ptr_local;
        builder
            .when(is_real_transition.clone())
            .assert_bool(is_next_ptr_diff.clone());

        let is_next_prt_same = AB::Expr::one() - is_next_ptr_diff;

        for (&val_local, &val_next) in zip(values_local, values_next) {
            builder
                .when(is_real_transition.clone())
                .when(is_next_prt_same.clone())
                .assert_eq(val_local, val_next);
        }

        builder.send(
            MemoryRelation(ptr_local, values_local.iter().copied()),
            is_real,
        );
    }
}

impl<F: Sync> BaseAir<F> for MemChip<F> {
    /// is_real, Pointer, and arguments
    fn width(&self) -> usize {
        2 + self.len
    }
}

#[cfg(test)]
mod tests {
    use crate::air::debug::debug_constraints_collecting_queries;
    use crate::lair::hasher::LurkHasher;
    use crate::{
        func,
        lair::{chip::FuncChip, toplevel::Toplevel},
    };
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    use super::*;
    #[test]
    fn lair_memory_test() {
        let func_e = func!(
        fn test(): [2] {
            let one = 1;
            let two = 2;
            let three = 3;
            let ptr1 = store(one, two, three);
            let ptr2 = store(one, one, one);
            let (_x, y, _z) = load(ptr1);
            return (ptr2, y)
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let queries = &mut QueryRecord::new(&toplevel);
        let mut queries_out = QueryRecord::default();
        test_chip.execute([].into(), queries);
        let func_trace = test_chip.generate_trace(queries);

        let expected_trace = [
            // ptr2, y, mult, ptr1, ptr2, one, two, three, selector
            2, 2, 1, 1, 2, 1, 2, 3, 1, //
            0, 0, 0, 0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(func_trace.values, expected_trace);

        let mem_len = 3;
        let mem_chip = MemChip::<F> {
            len: mem_len,
            _marker: Default::default(),
        };
        let mem_trace = mem_chip.generate_trace(queries, &mut queries_out);

        let expected_trace = [
            // is_real, index, memory values
            1, 1, 1, 2, 3, // 1
            1, 1, 1, 2, 3, // 1
            1, 2, 1, 1, 1, // 2
            0, 0, 0, 0, 0, // dummy
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(mem_trace.values, expected_trace);

        let _ = debug_constraints_collecting_queries(&mem_chip, &[], &mem_trace);
    }

    use crate::lair::execute::QueryRecord;
    use p3_baby_bear::BabyBear;
    use sphinx_core::stark::{Chip, LocalProver, StarkGenericConfig, StarkMachine};
    use sphinx_core::utils::BabyBearPoseidon2;

    struct DummyChip;

    impl<AB: AirBuilder> Air<AB> for DummyChip {
        fn eval(&self, _builder: &mut AB) {}
    }

    impl<'a> WithEvents<'a> for DummyChip {
        type Events = ();
    }
    impl<F: Field> EventLens<DummyChip> for QueryRecord<F> {
        fn events(&self) -> <DummyChip as WithEvents<'_>>::Events {}
    }

    impl<F: Field> BaseAir<F> for DummyChip {
        fn width(&self) -> usize {
            1
        }
    }

    impl<F: Field> MachineAir<F> for DummyChip {
        type Record = QueryRecord<F>;
        type Program = QueryRecord<F>;

        fn name(&self) -> String {
            "Dummy".to_string()
        }

        fn generate_trace<EL: EventLens<Self>>(
            &self,
            _input: &EL,
            _output: &mut Self::Record,
        ) -> RowMajorMatrix<F> {
            RowMajorMatrix::new(vec![F::zero(); 32], 1)
        }

        fn included(&self, _shard: &Self::Record) -> bool {
            true
        }
        fn preprocessed_width(&self) -> usize {
            1
        }

        /// Generate the preprocessed trace given a specific program.
        fn generate_preprocessed_trace(
            &self,
            _program: &Self::Program,
        ) -> Option<RowMajorMatrix<F>> {
            Some(RowMajorMatrix::new(vec![F::zero(); 32], 1))
        }
    }

    #[test]
    fn test_chip() {
        type F = BabyBear;
        type H = LurkHasher;
        let func_e = func!(
        fn test(): [2] {
            let one = 1;
            let two = 2;
            let three = 3;
            let ptr1 = store(one, two, three);
            let ptr2 = store(one, one, one);
            let (_x, y, _z) = load(ptr1);
            return (ptr2, y)
        });
        let toplevel = Toplevel::<F, H>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        let program = QueryRecord::default();
        test_chip.execute([].into(), &mut queries);
        let _func_trace = test_chip.generate_trace(&queries);

        let mem_len = 3;
        let mem_chip = MemChip::<F> {
            len: mem_len,
            _marker: Default::default(),
        };
        let chip = Chip::new(mem_chip);

        // let chip2 =Chip::new(test_chip);

        let config = BabyBearPoseidon2::new();
        // TODO: StarkMachine only accepts a `Vec` of the same Chip, but we don't necessarily want to create the enum with the derive MachineAir trait
        //       Can we change the definition to use a dynamic array of chips?
        let machine = StarkMachine::new(config, vec![chip], 5);
        // let machine = StarkMachine::new(config, vec![chip, Chip::new(DummyChip{})], 5);
        // TODO: This fails because the machine expects at least one chip to have a preprocessed trace.
        let (pk, vk) = machine.setup(&program);
        let mut challenger_p = machine.config().challenger();
        let mut challenger_v = machine.config().challenger();
        let proof = machine.prove::<LocalProver<_, _>>(&pk, queries, &mut challenger_p);
        machine
            .verify(&vk, &proof, &mut challenger_v)
            .expect("proof verifies");
    }
}
