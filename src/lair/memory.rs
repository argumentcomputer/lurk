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
        // pointer, multiplicity and arguments
        2 + self.len
    }
}

impl MemChip {
    pub fn generate_trace<F: PrimeField>(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let len = self.len;
        let idx = mem_index_from_len(len).unwrap();
        let mem = &queries.mem_queries[idx];
        let width = 2 + len;
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
        // pointer, multiplicity and arguments
        let width = 2 + len;
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
            let ptr = store(one, two, three);
            let (_x, y, _z) = load(ptr);
            return (ptr, y)
        });
        let toplevel = Toplevel::<F>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let queries = &mut QueryRecord::new(&toplevel);
        test_chip.execute([].into(), queries);
        let mem_len = 3;
        let mem_chip = MemChip { len: mem_len };
        let mem_trace = mem_chip.generate_trace_parallel(queries);

        let config = BabyBearPoseidon2::new();
        let challenger = &mut config.challenger();
        let proof = prove(&config, &mem_chip, challenger, mem_trace);
        let challenger = &mut config.challenger();
        verify(&config, &mem_chip, challenger, &proof).unwrap();
    }
}
