use std::marker::PhantomData;
use crate::poseidon::config::PoseidonConfig;

mod air;
mod columns;
mod trace;

/// The width of the permutation.
pub const WIDTH: usize = 16;

pub const NUM_EXTERNAL_ROUNDS: usize = 8;
pub const NUM_INTERNAL_ROUNDS: usize = 13;
pub const NUM_ROUNDS: usize = NUM_EXTERNAL_ROUNDS + NUM_INTERNAL_ROUNDS;

/// A chip that implements addition for the opcode ADD.
#[derive(Default)]
pub struct Poseidon2WideChip<C: PoseidonConfig<WIDTH>, const WIDTH: usize> {
    _marker: PhantomData<C>,
}
