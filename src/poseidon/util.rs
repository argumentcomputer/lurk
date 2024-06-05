use p3_field::{AbstractField, Field};
use p3_poseidon2::apply_mat4;
use std::iter::zip;

// Apply the MDS matrix to the external state.
pub(crate) fn matmul_exterior<F: Field>(state: &mut [F]) {
    let width = state.len();

    for state_chunk in state.chunks_exact_mut(4) {
        let state_chunk: &mut [F; 4] = state_chunk.try_into().unwrap();
        apply_mat4(state_chunk);
    }

    let mut sums = [F::zero(); 4];
    for state_chunk in state.chunks_exact(4) {
        let state_chunk: &[F; 4] = state_chunk.try_into().unwrap();
        for (sum, &v) in zip(sums.iter_mut(), state_chunk) {
            *sum += v;
        }
    }

    for i in 0..width {
        state[i] += sums[i % 4];
    }
}

// Apply the diffusion matrix to the internal state.
pub(crate) fn matmul_internal<AF: AbstractField>(
    state: &mut [AF],
    mat_internal_diag: impl IntoIterator<Item = AF>,
) {
    let sum: AF = state.iter().cloned().sum();
    for (state, diag) in zip(state.iter_mut(), mat_internal_diag) {
        *state *= diag + AF::neg_one();
        *state += sum.clone();
    }
}
