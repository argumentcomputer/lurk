use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeField;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

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
        let (local, next) = (main.row_slice(0), main.row_slice(1));
        let local_ptr = local[0];
        let next_ptr = next[0];
        builder.when_transition().assert_one(next_ptr - local_ptr);
    }
}

impl<F: Sync> BaseAir<F> for MemChip {
    fn width(&self) -> usize {
        self.witdh()
    }
}

impl MemChip {
    /// Pointer, multiplicity and arguments
    fn witdh(&self) -> usize {
        2 + self.len
    }

    pub fn generate_trace<F: PrimeField>(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let len = self.len;
        let idx = mem_index_from_len(len).unwrap();
        let mem = &queries.mem_queries[idx];
        let width = self.witdh();
        let height = mem.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        rows.chunks_mut(width).enumerate().for_each(|(ptr, row)| {
            row[0] = F::from_canonical_usize(ptr);
            if let Some((args, &mult)) = mem.get_index(ptr) {
                assert_eq!(args.len(), len);
                row[1] = F::from_canonical_u32(mult);
                args.iter().enumerate().for_each(|(idx, arg)| {
                    row[idx + 2] = *arg;
                });
            }
        });
        RowMajorMatrix::new(rows, width)
    }

    pub fn generate_trace_parallel<F: PrimeField>(
        &self,
        queries: &QueryRecord<F>,
    ) -> RowMajorMatrix<F> {
        let len = self.len;
        let idx = mem_index_from_len(len).unwrap();
        let mem = queries.mem_queries[idx].iter().collect::<Vec<_>>();
        let width = self.witdh();
        let height = mem.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        rows.par_chunks_mut(width)
            .enumerate()
            .for_each(|(ptr, row)| {
                row[0] = F::from_canonical_usize(ptr);
                if let Some((args, &mult)) = mem.get(ptr) {
                    assert_eq!(args.len(), len);
                    row[1] = F::from_canonical_u32(mult);
                    args.iter().enumerate().for_each(|(idx, arg)| {
                        row[idx + 2] = *arg;
                    });
                }
            });
        RowMajorMatrix::new(rows, width)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lair::{chip::FuncChip, toplevel::Toplevel},
    };
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use wp1_core::{
        stark::StarkGenericConfig,
        utils::{uni_stark_prove as prove, uni_stark_verify as verify, BabyBearPoseidon2},
    };

    use super::*;
    #[test]
    fn lair_memory_test() {
        let func_e = func!(
        fn test(): 2 {
            let one = num(1);
            let two = num(2);
            let three = num(3);
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
            1, 2, 1, 0, 1, 1, 2, 3, 1, //
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
            0, 2, 1, 2, 3, //
            1, 1, 1, 1, 1, //
            2, 0, 0, 0, 0, //
            3, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(F::from_canonical_u32)
        .collect::<Vec<_>>();
        assert_eq!(mem_trace.values, expected_trace);

        let config = BabyBearPoseidon2::new();
        let challenger = &mut config.challenger();
        let proof = prove(&config, &mem_chip, challenger, mem_trace);
        let challenger = &mut config.challenger();
        verify(&config, &mem_chip, challenger, &proof).unwrap();
    }
}
