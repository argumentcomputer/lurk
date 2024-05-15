use itertools::Itertools;
use p3_field::{ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrix;
use rayon::iter::ParallelIterator;


/// List of multiplicities proved by a single `provide` interaction.
pub(crate) struct Multiplicities {
    // index of traces that made `require` calls
    traces: Vec<usize>,
    // counts[i][j] is the number of times provided[i] was requested in the trace
    // at index j
    // width = traces.len()
    // height = provided.height()
    counts: RowMajorMatrix<u32>,
}

impl Multiplicities {
    pub(crate) fn rlc<F: Field, EF: ExtensionField<F>>(&self, mu: EF) -> Vec<EF> {
        let mus = self
            .traces
            .iter()
            .map(|&trace_idx| mu.exp_u64(trace_idx as u64))
            .collect_vec();

        self.counts
            .par_row_slices()
            .map(|row| {
                row.iter()
                    .zip(mus.iter())
                    .map(|(&value, &mu)| mu * F::from_canonical_u32(value))
                    .sum()
            }).collect()
    }
}
