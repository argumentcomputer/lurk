use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;
use sphinx_core::air::{EventLens, MachineAir, WithEvents};
use std::marker::PhantomData;

use crate::air::builder::{LookupBuilder, ProvideRecord};

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

        let height = mem.len().next_power_of_two().max(4); // TODO: Remove?

        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace
            .par_rows_mut()
            .zip(mem.par_iter())
            .enumerate()
            .for_each(|(i, (row, (args, callers_nonces)))| {
                let (_, last_nonce, _) = callers_nonces
                    .last()
                    .expect("Must have at least one caller");
                let last_count = callers_nonces.len();

                // is_real
                row[0] = F::one();
                // ptr: We skip the address 0 as to leave room for null pointers
                row[1] = F::from_canonical_usize(i + 1);
                // last_nonce
                row[2] = F::from_canonical_usize(*last_nonce);
                // last_count
                row[3] = F::from_canonical_usize(last_count);
                row[4..].copy_from_slice(args)
            });
        trace
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
    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}

    #[inline]
    fn included(&self, queries: &Self::Record) -> bool {
        queries.mem_queries[mem_index_from_len(self.len)]
            .values()
            .any(|set| !set.is_empty())
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

        let (is_real, ptr_local, last_nonce, last_count, values) =
            (local[0], local[1], local[2], local[3], &local[4..]);
        let (is_real_next, ptr_next) = (next[0], next[1]);

        // is_real is 1 for all valid entries, then 0 for padding rows until the last row.
        builder.assert_bool(is_real);

        // all but the last rows where is_real = 1
        let is_real_transition = is_real_next * builder.is_transition();

        // if we are in a real transition, the current row should be real
        builder.when(is_real_transition.clone()).assert_one(is_real);

        // First valid pointer is 1
        builder.when_first_row().when(is_real).assert_one(ptr_local);
        // Pointer increases by one
        builder
            .when(is_real_transition.clone())
            .assert_eq(ptr_local + AB::Expr::one(), ptr_next);

        builder.provide(
            MemoryRelation(ptr_local, values.iter().copied()),
            ProvideRecord {
                last_nonce,
                last_count,
            },
            is_real,
        );
    }
}

impl<F: Sync> BaseAir<F> for MemChip<F> {
    /// is_real, Pointer, last_nonce, last_count, and arguments
    fn width(&self) -> usize {
        4 + self.len
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
        toplevel.execute_by_name("test", &[], queries);
        let func_trace = test_chip.generate_trace_sequential(queries);

        #[rustfmt::skip]
        let expected_trace = [
            0, 1, 0, 0, 1, 2, 0, 0, 1, 1, 2, 3, 0, 1, 1006632961, 0, 1, 1,
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,          0, 0, 0, 0,
            2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,          0, 0, 0, 0,
            3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,          0, 0, 0, 0,
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(func_trace.values, expected_trace);

        let mem_len = 3;
        let mem_chip = MemChip::new(mem_len);
        let mem_trace = mem_chip.generate_trace_parallel(&queries.mem_queries);

        #[rustfmt::skip]
        let expected_trace = [
            1, 1, 0, 2, 1, 2, 3,
            1, 2, 0, 1, 1, 1, 1,
            0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0,
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(mem_trace.values, expected_trace);

        let _ = debug_constraints_collecting_queries(&mem_chip, &[], None, &mem_trace);
    }
}
