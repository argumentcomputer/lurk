use std::marker::PhantomData;

use crate::poseidon::config::PoseidonConfig;

mod air;
mod columns;
mod trace;

/// A chip that implements addition for the opcode ADD.
#[derive(Default)]
pub struct Poseidon2WideChip<C: PoseidonConfig<WIDTH>, const WIDTH: usize> {
    _marker: PhantomData<C>,
}
