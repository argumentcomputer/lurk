use p3_matrix::dense::RowMajorMatrix;
pub mod air;
pub mod builder;
mod trace;

/// List of multiplicities proved by a single `provide` interaction.
pub struct Multiplicities {
    // index of traces that made `require` calls
    traces: Vec<usize>,
    // counts[i][j] is the number of times provided[i] was requested in the trace
    // at index j
    // width = traces.len()
    // height = provided.height()
    counts: RowMajorMatrix<u32>,
}
