use hybrid_array::{typenum::Unsigned, Array, ArraySize};
use p3_field::{AbstractField, Field};

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

pub(crate) fn matmul_generic<F, AF, WIDTH>(
    state: &mut [AF],
    mat_internal_diag_m_1: Array<F, WIDTH>,
) where
    F: Field,
    AF: AbstractField<F = F>,
    WIDTH: ArraySize,
{
    let sum: AF = state.iter().cloned().sum();
    for i in 0..<WIDTH as Unsigned>::USIZE {
        state[i] *= AF::from_f(mat_internal_diag_m_1[i]);
        state[i] += sum.clone();
    }
}
