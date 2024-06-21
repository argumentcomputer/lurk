use itertools::{repeat_n, Itertools};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};
use sphinx_core::air::{EventLens, MachineAir, WithEvents};
use std::{iter::zip, marker::PhantomData};

use crate::air::builder::LookupBuilder;

use super::{
    execute::{mem_index_from_len, MemMap, QueryRecord},
    lair_chip::LairMachineProgram,
    relations::MemoryRelation,
};

#[derive(Default)]
pub struct MemChip<F> {
    len: usize,
    _p: PhantomData<F>,
}

impl<F> MemChip<F> {
    #[inline]
    pub fn new(len: usize) -> Self {
        Self {
            len,
            _p: PhantomData,
        }
    }

    pub fn generate_trace_parallel(&self, queries: &[MemMap<F>]) -> RowMajorMatrix<F>
    where
        F: Field,
    {
        let mem_idx = mem_index_from_len(self.len);
        let mem = &queries[mem_idx];
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
                repeat_n((ptr, args), mult as usize)
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
    type Program = LairMachineProgram;

    #[inline]
    fn name(&self) -> String {
        format!("{}-wide", self.len)
    }

    #[inline]
    fn generate_trace<EL: EventLens<Self>>(
        &self,
        input: &EL,
        _: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        self.generate_trace_parallel(input.events())
    }

    #[inline]
    fn included(&self, queries: &Self::Record) -> bool {
        queries.mem_queries[mem_index_from_len(self.len)]
            .values()
            .any(|mult| mult > &0)
    }

    #[inline]
    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}
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
    use crate::{
        func,
        lair::{func_chip::FuncChip, hasher::LurkHasher, toplevel::Toplevel},
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
        test_chip.execute([].into(), queries);
        let func_trace = test_chip.generate_trace_sequential(queries);

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
        let mem_chip = MemChip::new(mem_len);
        let mem_trace = mem_chip.generate_trace_parallel(&queries.mem_queries);

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
}
