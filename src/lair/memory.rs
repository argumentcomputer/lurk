use crate::air::builder::LookupBuilder;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};
use std::iter::zip;

use super::execute::{mem_index_from_len, QueryRecord};

pub struct MemChip {
    len: usize,
}

impl<AB> Air<AB> for MemChip
where
    AB: AirBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &[AB::Var] = &main.row_slice(0);
        let next: &[AB::Var] = &main.row_slice(1);

        let (is_real, ptr_local, values_local) = (local[0], local[1], &local[2..]);
        let (is_real_next, ptr_next, values_next) = (next[0], next[1], &next[2..]);

        // is_real
        {
            builder.assert_bool(is_real);
            // is_real starts with one
            builder.when_first_row().assert_one(is_real);
            // if next is real, local is real
            builder
                .when_transition()
                .when(is_real_next)
                .assert_one(is_real);
            // last row must be padding
            // after this, is_real => is_transition
            builder.when_last_row().assert_zero(is_real);
        }

        // First valid pointer is 1
        builder.when_first_row().assert_one(ptr_local);
        // Then increases by 0 or 1
        let ptr_diff = ptr_next - ptr_local;
        builder.when(is_real).assert_bool(ptr_diff.clone());

        // ptr in first padding row must be the next unused index
        let is_last_real = is_real * (AB::Expr::one() - is_real_next);
        builder.when(is_last_real).assert_one(ptr_diff.clone());

        // write happens in the last duplication of the value
        let is_write = ptr_diff;
        let is_read = AB::Expr::one() - is_write.clone();

        for (&val_local, &val_next) in zip(values_local, values_next) {
            builder
                .when(is_real)
                .when(is_read.clone())
                .assert_eq(val_local, val_next);
        }

        const READ_TAG: u32 = 1;
        const WRITE_TAG: u32 = 2;

        let tag = AB::Expr::from_canonical_u32(READ_TAG) * is_read
            + AB::Expr::from_canonical_u32(WRITE_TAG) * is_write;

        // builder.when(is_real).send([tag, values_local]);
    }
}

impl<F: Sync> BaseAir<F> for MemChip {
    fn width(&self) -> usize {
        self.width()
    }
}

impl MemChip {
    /// is_real, Pointer, and arguments
    fn width(&self) -> usize {
        2 + self.len
    }

    pub fn generate_trace<F: Field>(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let len = self.len;
        let mem_idx = mem_index_from_len(len);
        let mem = &queries.mem_queries[mem_idx];
        let width = self.width();
        let height = mem.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        rows.chunks_mut(width).enumerate().for_each(|(i, row)| {
            // We skip the address 0 as to leave room for null pointers
            row[0] = F::from_canonical_usize(i + 1);
            if let Some((args, &mult)) = mem.get_index(i) {
                assert_eq!(args.len(), len);
                row[1] = F::from_canonical_u32(mult);
                args.iter().enumerate().for_each(|(j, arg)| {
                    row[j + 2] = *arg;
                });
            }
        });
        RowMajorMatrix::new(rows, width)
    }

    pub fn generate_trace_parallel<F: Field>(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let len = self.len;
        let mem_idx = mem_index_from_len(len);
        let mem = queries.mem_queries[mem_idx].iter().collect::<Vec<_>>();
        let width = self.width();
        let height = mem.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        rows.par_chunks_mut(width).enumerate().for_each(|(i, row)| {
            // We skip the address 0 as to leave room for null pointers
            row[0] = F::from_canonical_usize(i + 1);
            if let Some((args, &mult)) = mem.get(i) {
                assert_eq!(args.len(), len);
                row[1] = F::from_canonical_u32(mult);
                args.iter().enumerate().for_each(|(j, arg)| {
                    row[j + 2] = *arg;
                });
            }
        });
        RowMajorMatrix::new(rows, width)
    }
}

#[cfg(test)]
mod tests {
    use crate::air::debug::debug_constraints_collecting_queries;
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
        let toplevel = Toplevel::<F>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let queries = &mut QueryRecord::new(&toplevel);
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
        let mem_chip = MemChip { len: mem_len };
        let mem_trace = mem_chip.generate_trace(queries);

        let expected_trace = [
            // index, mult, memory values
            1, 2, 1, 2, 3, //
            2, 1, 1, 1, 1, //
            3, 0, 0, 0, 0, //
            4, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(mem_trace.values, expected_trace);

        let _ = debug_constraints_collecting_queries(&mem_chip, &[], &mem_trace);
    }
}
