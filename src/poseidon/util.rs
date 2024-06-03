use p3_field::{AbstractField, Field};
use std::iter::zip;

// TODO: Make this public inside Plonky3 and import directly.
pub fn apply_m_4<AF>(x: &mut [AF])
where
    AF: AbstractField,
{
    let t01 = x[0].clone() + x[1].clone();
    let t23 = x[2].clone() + x[3].clone();
    let t0123 = t01.clone() + t23.clone();
    let t01123 = t0123.clone() + x[1].clone();
    let t01233 = t0123.clone() + x[3].clone();
    // The order here is important. Need to overwrite x[0] and x[2] after x[1] and x[3].
    x[3] = t01233.clone() + x[0].double(); // 3*x[0] + x[1] + x[2] + 2*x[3]
    x[1] = t01123.clone() + x[2].double(); // x[0] + 2*x[1] + 3*x[2] + x[3]
    x[0] = t01123 + t01; // 2*x[0] + 3*x[1] + x[2] + x[3]
    x[2] = t01233 + t23; // x[0] + x[1] + 2*x[2] + 3*x[3]
}

// Apply the MDS matrix to the external state.
pub(crate) fn matmul_exterior<F: Field>(state: &mut [F]) {
    let width = state.len();

    for state_chunk in state.chunks_exact_mut(4) {
        apply_m_4(state_chunk);
    }
    let sums = state
        .chunks_exact_mut(4)
        .fold([F::zero(); 4], |mut sums, chunk| {
            zip(sums.iter_mut(), chunk).for_each(|(s, &mut v)| *s += v);
            sums
        });

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
        *state *= diag + (-AF::one());
        *state += sum.clone();
    }
}
