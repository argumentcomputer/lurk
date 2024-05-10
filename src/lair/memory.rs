use p3_field::PrimeField;
use p3_matrix::dense::RowMajorMatrix;
use rayon::{
    iter::{IndexedParallelIterator, IntoParallelRefIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use super::execute::{mem_index_to_len, MemMap, QueryRecord};

impl<F: PrimeField + Ord> QueryRecord<F> {
    pub fn generate_mem_traces(&self) -> Vec<RowMajorMatrix<F>> {
        self.mem_queries
            .iter()
            .enumerate()
            .map(|(i, mem)| {
                let len = mem_index_to_len(i).unwrap();
                generate_mem_trace(mem, len)
            })
            .collect()
    }

    pub fn generate_mem_traces_parallel(&self) -> Vec<RowMajorMatrix<F>> {
        self.mem_queries
            .par_iter()
            .enumerate()
            .map(|(i, mem)| {
                let len = mem_index_to_len(i).unwrap();
                generate_mem_trace_parallel(mem, len)
            })
            .collect()
    }
}

fn generate_mem_trace<F: PrimeField + Ord>(mem: &MemMap<F>, len: usize) -> RowMajorMatrix<F> {
    // pointer, multiplicity and arguments
    let width = 2 + len;
    let height = mem.len().next_power_of_two().max(4);
    let mut rows = vec![F::zero(); height * width];

    for (ptr, (args, &mult)) in mem.iter().enumerate() {
        assert_eq!(args.len(), len);
        let mut idx = ptr * width;
        rows[idx] = F::from_canonical_usize(ptr);
        idx += 1;
        rows[idx] = F::from_canonical_u32(mult);
        args.iter().for_each(|arg| {
            idx += 1;
            rows[idx] = *arg;
        });
    }
    RowMajorMatrix::new(rows, width)
}

fn generate_mem_trace_parallel<F: PrimeField + Ord>(
    mem: &MemMap<F>,
    len: usize,
) -> RowMajorMatrix<F> {
    let mem = mem.iter().collect::<Vec<_>>();
    // pointer, multiplicity and arguments
    let width = 2 + len;
    let height = mem.len().next_power_of_two().max(4);
    let mut rows = vec![F::zero(); height * width];
    let non_dummies = &mut rows[0..mem.len() * width];
    non_dummies
        .par_chunks_mut(width)
        .enumerate()
        .for_each(|(ptr, row)| {
            let (args, &mult) = mem[ptr];
            assert_eq!(args.len(), len);
            let mut idx = 0;
            row[idx] = F::from_canonical_usize(ptr);
            idx += 1;
            row[idx] = F::from_canonical_u32(mult);
            args.iter().for_each(|arg| {
                idx += 1;
                row[idx] = *arg;
            });
        });
    RowMajorMatrix::new(rows, width)
}
