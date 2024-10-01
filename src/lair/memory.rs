use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;
use rayon::iter::{IndexedParallelIterator, ParallelIterator};
use std::marker::PhantomData;

use crate::air::builder::{LookupBuilder, ProvideRecord};

use super::{
    execute::{mem_index_from_len, Shard},
    relations::MemoryRelation,
};

#[derive(Default)]
pub struct MemChip<F> {
    pub(crate) len: usize,
    _p: PhantomData<F>,
}

impl<F: PrimeField32> MemChip<F> {
    #[inline]
    pub fn new(len: usize) -> Self {
        Self {
            len,
            _p: PhantomData,
        }
    }

    pub fn generate_trace(&self, shard: &Shard<'_, F>) -> RowMajorMatrix<F> {
        let record = &shard.queries().mem_queries;
        let mem_idx = mem_index_from_len(self.len);
        let mem = &record[mem_idx];
        let width = self.width();

        let height = mem.len().next_power_of_two().max(4); // TODO: Remove? loam#118

        // TODO: This snippet or equivalent is needed for memory sharding
        // let range = shard.get_mem_range(mem_index_from_len(self.len));
        // let non_dummy_height = range.len();
        // let height = non_dummy_height.next_power_of_two().max(4);

        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace
            .par_rows_mut()
            .zip(mem.par_iter())
            .enumerate()
            // TODO: This snippet or equivalent is needed for memory sharding
            // .skip(range.start)
            // .take(non_dummy_height)
            .for_each(|(i, (row, (args, mem_result)))| {
                let provide = mem_result.provide.into_provide();

                // is_real
                row[0] = F::one();
                // ptr: We skip the address 0 as to leave room for null pointers
                row[1] = F::from_canonical_usize(i + 1);
                // TODO: the ptr can be "duplicated" when sharding is involved: how do we deal with this?

                // last_nonce
                row[2] = provide.last_nonce;
                // last_count
                row[3] = provide.last_count;
                row[4..].copy_from_slice(args)
            });
        trace
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
    use crate::lair::execute::QueryRecord;
    use crate::{
        func,
        lair::{chipset::NoChip, func_chip::FuncChip, toplevel::Toplevel},
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);
        toplevel
            .execute_by_name("test", &[], &mut queries, None)
            .unwrap();
        let func_trace = test_chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = [
            0, 2, 2, 0, 1, 1, 0, 0, 1, 2, 0, 0, 1, 1, 2, 3, 0, 1, 1006632961, 1,
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(func_trace.values, expected_trace);

        let mem_len = 3;
        let mem_chip = MemChip::new(mem_len);
        let shard = Shard::new(&queries);
        let mem_trace = mem_chip.generate_trace(&shard);

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
