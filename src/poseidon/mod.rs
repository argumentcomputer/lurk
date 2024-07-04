//! This module defines a Poseidon2 chip that generates traces, verifies air constraints, and
//! supports hashing data outside of the circuit
//!

use std::marker::PhantomData;

use self::config::PoseidonConfig;

pub mod air;
pub mod columns;
pub mod config;
mod constants;
pub mod trace;
pub mod wide;

/// A chip that implements addition for the Poseidon2 permutation
pub struct Poseidon2Chip<C: PoseidonConfig<WIDTH>, const WIDTH: usize> {
    _marker: PhantomData<C>,
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Default for Poseidon2Chip<C, WIDTH> {
    fn default() -> Self {
        Self {
            _marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use core::array;

    use hybrid_array::typenum::Unsigned;
    use itertools::Itertools;
    use p3_field::{AbstractField, PrimeField32};
    use p3_matrix::Matrix;
    use p3_symmetric::Permutation;

    use crate::{
        air::debug::debug_constraints_collecting_queries, poseidon::config::BabyBearConfig16,
    };

    use super::{config::*, Poseidon2Chip};

    fn test_trace_eq_hash_with<const WIDTH: usize, C: PoseidonConfig<WIDTH>>() {
        let chip = Poseidon2Chip::<C, WIDTH>::default();
        let hasher = C::hasher();
        let input: [C::F; WIDTH] = array::from_fn(C::F::from_canonical_usize);

        let expected_output = hasher.permute(input).to_vec();

        let trace = chip.generate_trace(vec![input]);
        let output_row = trace.row(<<C as PoseidonConfig<WIDTH>>::R as Unsigned>::USIZE);
        let output = output_row.tail(WIDTH).collect::<Vec<_>>();

        assert_eq!(expected_output, output);
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

    fn test_air_constraints_with<const WIDTH: usize, C: PoseidonConfig<WIDTH>>()
    where
        C::F: PrimeField32,
    {
        let chip = Poseidon2Chip::<C, WIDTH>::default();
        let public_values: [C::F; WIDTH] = array::from_fn(C::F::from_canonical_usize);
        let main = chip.generate_trace(vec![public_values]);

        let _ = debug_constraints_collecting_queries(&chip, &public_values, None, &main);
    }

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
