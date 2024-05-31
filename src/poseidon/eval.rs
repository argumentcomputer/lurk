use super::constants::{FULL_RC_4_8, PART_RC_4_21};
use super::PoseidonConfig;
use super::{config::BabyBearConfig4, constants::MATRIX_DIAG_4_BABYBEAR};
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use p3_poseidon2::{DiffusionPermutation, Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

type F = BabyBear;

#[derive(Clone)]
pub struct Internal4Diffusion {}

impl Permutation<[F; 4]> for Internal4Diffusion {
    fn permute_mut(&self, input: &mut [F; 4]) {
        let sum: F = input.iter().map(|x| *x).sum();
        for i in 0..4 {
            input[i] = sum + (MATRIX_DIAG_4_BABYBEAR[i] + (-F::one())) * input[i];
        }
    }
}

impl DiffusionPermutation<BabyBear, 4> for Internal4Diffusion {}

fn hasher() -> Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, Internal4Diffusion, 4, 7> {
    let rounds_f = BabyBearConfig4::R_F;
    let rounds_p = BabyBearConfig4::R_P;

    let external_constants = FULL_RC_4_8.to_vec();
    let internal_constants = PART_RC_4_21.to_vec();

    let external_linear_layer = Poseidon2ExternalMatrixGeneral {};
    let internal_linear_layer = Internal4Diffusion {};

    Poseidon2::new(
        rounds_f,
        external_constants,
        external_linear_layer,
        rounds_p,
        internal_constants,
        internal_linear_layer,
    )
}

#[cfg(test)]
mod test {
    use p3_field::AbstractField;

    use super::*;

    #[test]
    fn test_hasher() {
        let blah = hasher();
        let input = [BabyBear::zero(); 4];
        let asdf = blah.permute(input);

        dbg!(asdf);
    }
}
