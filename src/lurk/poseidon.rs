use crate::air::builder::{LookupBuilder, RequireRecord};
use crate::lair::chipset::Chipset;
use crate::poseidon::config::{InternalDiffusion, PoseidonConfig};
use crate::poseidon::wide::columns::Poseidon2Cols;
use hybrid_array::typenum::Sub1;
use hybrid_array::ArraySize;
use p3_air::AirBuilder;

use p3_field::AbstractField;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;
use std::borrow::{Borrow, BorrowMut};

const OUTPUT_SIZE: usize = 8;

#[derive(Clone)]
pub struct PoseidonChipset<C: PoseidonConfig<W>, const W: usize> {
    hasher: Poseidon2<C::F, Poseidon2ExternalMatrixGeneral, InternalDiffusion<C>, W, 7>,
}

impl<C: PoseidonConfig<W>, const W: usize> Default for PoseidonChipset<C, W> {
    fn default() -> Self {
        Self {
            hasher: C::hasher(),
        }
    }
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> PoseidonChipset<C, WIDTH> {
    pub fn hash(&self, preimg: &[C::F]) -> [C::F; OUTPUT_SIZE] {
        let mut state = [C::F::zero(); WIDTH];
        state.copy_from_slice(preimg);
        self.hasher.permute_mut(&mut state);

        let mut out = [C::F::zero(); OUTPUT_SIZE];
        out.copy_from_slice(&state[..OUTPUT_SIZE]);
        out
    }
}

impl<C: PoseidonConfig<WIDTH> + 'static, const WIDTH: usize> Chipset<C::F>
    for PoseidonChipset<C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    fn input_size(&self) -> usize {
        WIDTH
    }

    fn output_size(&self) -> usize {
        OUTPUT_SIZE
    }

    fn witness_size(&self) -> usize {
        OUTPUT_SIZE + Poseidon2Cols::<C::F, C, WIDTH>::num_cols()
    }

    fn require_size(&self) -> usize {
        0
    }

    fn execute_simple(&self, input: &[C::F]) -> Vec<C::F> {
        self.hasher.permute(input.try_into().unwrap())[..OUTPUT_SIZE].to_vec()
    }

    fn populate_witness(&self, input: &[C::F], witness: &mut [C::F]) -> Vec<C::F> {
        let (output, witness) = witness.split_at_mut(OUTPUT_SIZE);

        let cols: &mut Poseidon2Cols<C::F, C, WIDTH> = witness.borrow_mut();
        let result = cols.populate(input.try_into().unwrap());
        output.copy_from_slice(&result[0..OUTPUT_SIZE]);
        result.to_vec()
    }

    /// Given a witness of size `OUTPUT_SIZE + Poseidon2Cols::num_cols`,
    /// apply the Poseidon2 permutation over the input and compare the returned state,
    /// potentially truncating it to the image size.
    /// When is_real = 0, the output is unconstrained.
    fn eval<AB: AirBuilder<F = C::F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        input: Vec<AB::Expr>,
        witness: &[AB::Var],
        _nonce: AB::Expr,
        _requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        let (output, witness) = witness.split_at(OUTPUT_SIZE);

        let cols: &Poseidon2Cols<AB::Var, C, WIDTH> = witness.borrow();
        cols.eval(builder, input.try_into().unwrap(), output, is_real);

        output.iter().copied().map(Into::into).collect()
    }
}
