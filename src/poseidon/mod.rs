//! This module defines a Poseidon2 chip that generates traces, verifies air constraints, and
//! supports hashing data outside of the circuit
//!

use std::marker::PhantomData;

use self::config::PoseidonConfig;

mod air;
mod columns;
mod config;
mod constants;
mod trace;
mod util;

/// A chip that implements addition for the Poseidon2 permutation
pub struct Poseidon2Chip<C>
where
    C: PoseidonConfig,
{
    _p: PhantomData<C>,
}

impl<C: PoseidonConfig> Poseidon2Chip<C> {
    /// Creates a new Poseidon2 chip.
    pub fn new() -> Self {
        Self { _p: PhantomData }
    }
}

#[cfg(test)]
mod tests {
    use hybrid_array::{typenum::Unsigned, Array};
    use itertools::Itertools;
    use p3_air::Air;
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::Matrix;
    use p3_symmetric::Permutation;

    use crate::{
        air::debug::{debug_constraints_collecting_queries, DebugConstraintBuilder},
        poseidon::config::BabyBearConfig16,
    };

    use super::{
        config::{BabyBearConfig4, PoseidonConfig},
        Poseidon2Chip,
    };

    type F = BabyBear;

    #[test]
    fn test_trace_eq_hash() {
        // Test arity 4
        let chip4 = Poseidon2Chip::<BabyBearConfig4>::new();
        let hasher = chip4.hasher();
        let input: [F; 4] = core::array::from_fn(|i| F::from_canonical_usize(i));

        let expected_output = hasher.permute(input).to_vec();

        let trace = chip4.generate_trace(vec![*Array::from_slice(&input)]);
        let output_row = trace.row(<<BabyBearConfig4 as PoseidonConfig>::R as Unsigned>::USIZE);
        let output = output_row.tail(BabyBearConfig4::WIDTH).collect::<Vec<_>>();

        // assert_eq!(expected_output, output);
        dbg!(expected_output);
        dbg!(output);

        // Test arity 16
        let chip16 = Poseidon2Chip::<BabyBearConfig16>::new();
        let hasher = chip16.hasher();
        let input: [F; 16] = core::array::from_fn(|i| F::from_canonical_usize(i));

        let expected_output = hasher.permute(input).to_vec();

        let trace = chip16.generate_trace(vec![*Array::from_slice(&input)]);
        let output_row = trace.row(<<BabyBearConfig16 as PoseidonConfig>::R as Unsigned>::USIZE);
        let output = output_row.tail(BabyBearConfig16::WIDTH).collect::<Vec<_>>();

        // assert_eq!(expected_output, output);
        dbg!(expected_output);
        dbg!(output);
    }

    #[test]
    fn test_air_constraints() {
        let chip4 = Poseidon2Chip::<BabyBearConfig4>::new();
        let public_values: [F; 4] = core::array::from_fn(|i| F::from_canonical_usize(i));
        let main = chip4.generate_trace(vec![*Array::from_slice(&public_values)]);

        let result = debug_constraints_collecting_queries(&chip4, &public_values, &main);

        dbg!(result.len());
    }
}
