//! This module defines the out-of-circuit evaluation of the Poseidon hash function
use super::config::{BabyBearConfig4, PoseidonConfig};
use arc_swap::docs::internal;
use hybrid_array::ArraySize;
use p3_baby_bear::{BabyBear, DiffusionMatrixBabyBear};
use p3_field::{AbstractField, PrimeField};
use p3_poseidon2::{MDSMat4, MdsLightPermutation, Poseidon2};
use p3_symmetric::Permutation;

#[derive(Clone, Default)]
struct InternalDiag4 {}

impl Permutation<[BabyBear; 4]> for InternalDiag4 {
    fn permute_mut(&self, input: &mut [BabyBear; 4]) {
        todo!()
    }
}

impl BabyBearConfig4 {
    pub fn hasher(&self) -> Poseidon2<BabyBear, MDSMat4, InternalDiag4, 4, 7> {
        let rounds_f = Self::R_F;
        let external_constants: Vec<[BabyBear; 4]> = Self::full_round_constants()
            .into_iter()
            .map(|x| x.map(BabyBear::from_wrapped_u32).into())
            .collect::<Vec<_>>();
        let rounds_p = Self::R_P;
        let internal_constants: Vec<_> = Self::partial_round_constants()
            .into_iter()
            .map(BabyBear::from_wrapped_u32)
            .collect();

        todo!()
        // Complains BabyBear isn't a PrimeField but it is!!
        // Poseidon2::new(
        //     rounds_f,
        //     external_constants,
        //     MDSMat4,
        //     rounds_p,
        //     internal_constants,
        //     InternalDiag4::default(),
        // )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_hasher() {
        let config = BabyBearConfig4;
        let hasher = config.hasher();
        let blah = [BabyBear::from_wrapped_u32(0); 4];

        let tada = hasher.permute(&blah);
    }
}
