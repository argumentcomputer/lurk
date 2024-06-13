use std::marker::PhantomData;

use crate::poseidon::config::PoseidonConfig;

mod air;
pub mod columns;
pub mod trace;

/// A chip that implements addition for the opcode ADD.
pub struct Poseidon2WideChip<C: PoseidonConfig<WIDTH>, const WIDTH: usize> {
    _marker: PhantomData<C>,
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Default for Poseidon2WideChip<C, WIDTH> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod test {
    use std::ops::Sub;

    use super::Poseidon2WideChip;
    use crate::poseidon::config::*;

    use hybrid_array::{typenum::B1, ArraySize};
    use p3_field::AbstractField;
    use p3_symmetric::Permutation;

    fn test_trace_eq_hash_with<const WIDTH: usize, C: PoseidonConfig<WIDTH>>()
    where
        C::R_P: Sub<B1>,
        <<C as PoseidonConfig<WIDTH>>::R_P as Sub<B1>>::Output: ArraySize,
    {
        let chip = Poseidon2WideChip::<C, WIDTH>::default();
        let input: [C::F; WIDTH] = core::array::from_fn(C::F::from_canonical_usize);
        let hasher = C::hasher();

        let expected_output = hasher.permute(input);
        let (output, _trace) = chip.generate_trace(&[input]);

        assert_eq!(output[0], expected_output);
    }

    #[test]
    fn test_trace_eq_hash() {
        test_trace_eq_hash_with::<4, BabyBearConfig4>();
        test_trace_eq_hash_with::<8, BabyBearConfig8>();
        test_trace_eq_hash_with::<12, BabyBearConfig12>();
        test_trace_eq_hash_with::<16, BabyBearConfig16>();
        test_trace_eq_hash_with::<24, BabyBearConfig24>();
        test_trace_eq_hash_with::<40, BabyBearConfig40>();
    }

    fn test_air_constraints_with<const WIDTH: usize, C: PoseidonConfig<WIDTH>>() {}

    #[test]
    fn test_air_constraints() {
        test_air_constraints_with::<4, BabyBearConfig4>();
        test_air_constraints_with::<8, BabyBearConfig8>();
        test_air_constraints_with::<12, BabyBearConfig12>();
        test_air_constraints_with::<16, BabyBearConfig16>();
        test_air_constraints_with::<24, BabyBearConfig24>();
        test_air_constraints_with::<40, BabyBearConfig40>();
    }
}
