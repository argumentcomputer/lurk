use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{
    air::builder::{LookupBuilder, RequireRecord},
    lair::chipset::Chipset,
};

#[derive(Clone)]
pub struct ExtractSign<const NUM_ABS_BITS: u32>;

impl<const NUM_ABS_BITS: u32> ExtractSign<NUM_ABS_BITS> {
    fn abs_max(&self) -> u32 {
        1 << NUM_ABS_BITS
    }
}

impl<F: PrimeField32, const NUM_ABS_BITS: u32> Chipset<F> for ExtractSign<NUM_ABS_BITS> {
    fn input_size(&self) -> usize {
        1
    }

    fn output_size(&self) -> usize {
        2
    }

    fn witness_size(&self) -> usize {
        2
    }

    fn require_size(&self) -> usize {
        0
    }

    fn execute_simple(&self, input: &[F]) -> Vec<F> {
        let byte = input[0].as_canonical_u32();
        let abs_max = self.abs_max();
        let sign = F::from_canonical_u32(byte / abs_max);
        let rem = F::from_canonical_u32(byte % abs_max);
        vec![sign, rem]
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        let out = self.execute_simple(input);
        witness.copy_from_slice(&out);
        out
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        input: Vec<AB::Expr>,
        witness: &[AB::Var],
        _nonce: AB::Expr,
        _requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        let byte = input[0].clone();
        let (sign, rem) = (witness[0], witness[1]);
        let abs_max = F::from_canonical_u32(self.abs_max());
        builder.when(is_real.clone()).assert_bool(sign);
        // sign * abs_max + rem = byte
        builder.when(is_real).assert_eq(sign * abs_max + rem, byte);
        vec![sign.into(), rem.into()]
    }
}
