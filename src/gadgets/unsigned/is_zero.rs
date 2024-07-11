use crate::gadgets::unsigned::Word;
use hybrid_array::sizes::{U4, U8};
use hybrid_array::{Array, ArraySize};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use sphinx_derive::AlignedBorrow;
use std::iter::zip;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct IsZeroWitness<T, W: ArraySize> {
    inverses: Array<T, W>,
}

pub type IsZero64Witness<T> = IsZeroWitness<T, U8>;
pub type IsZero32Witness<T> = IsZeroWitness<T, U4>;

impl<F: Field, W: ArraySize> IsZeroWitness<F, W> {
    pub fn populate_is_zero(&mut self, word: &Word<u8, W>) -> bool {
        for (&limb, inv) in zip(word, self.inverses.iter_mut()) {
            if limb != 0 {
                *inv = F::from_canonical_u8(limb).inverse();
                return false;
            }
        }
        true
    }

    pub fn populate_is_equal(&mut self, word1: &Word<u8, W>, word2: &Word<u8, W>) -> bool {
        for ((&limb1, &limb2), inv) in zip(zip(word1, word2), self.inverses.iter_mut()) {
            if limb1 != limb2 {
                let diff = F::from_canonical_u8(limb1) - F::from_canonical_u8(limb2);
                *inv = diff.inverse();
                return false;
            }
        }
        true
    }
}

pub fn eval_is_zero<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    input: Word<impl Into<AB::Expr>, W>,
    is_zero: impl Into<AB::Expr>,
    witness: &IsZeroWitness<AB::Var, W>,
    is_real: impl Into<AB::Expr>,
) {
    let builder = &mut builder.when(is_real.into());

    let input = input.into();
    let is_zero = is_zero.into();

    builder.assert_bool(is_zero.clone());

    // If is_zero, all limbs are zero
    for i in &input {
        builder.when(is_zero.clone()).assert_zero(i.clone());
    }

    // Otherwise, there exist w such that 1 = ∑ w[i]*limb[i]
    let not_zero = is_zero - AB::F::one();
    let lc = zip(input, &witness.inverses)
        .map(|(i, &inv)| i * inv.into())
        .sum::<AB::Expr>();

    builder.when(not_zero).assert_one(lc);
}

pub fn eval_is_equal<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    is_equal: impl Into<AB::Expr>,
    witness: &IsZeroWitness<AB::Var, W>,
    is_real: impl Into<AB::Expr>,
) {
    let in1 = in1.into();
    let in2 = in2.into();
    let diff = Word::from_fn(|i| in1[i].clone() - in2[i].clone());
    eval_is_zero(builder, diff, is_equal, witness, is_real);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::GadgetAirBuilder;
    use crate::gadgets::unsigned::{Word32, Word64};
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;

    type F = BabyBear;

    fn test_is_zero<W: ArraySize>(input: Word<u8, W>, expected: bool) {
        let mut builder = GadgetAirBuilder::<F>::default();

        assert_eq!(input.is_zero(), expected);
        let mut witness = IsZeroWitness::<F, W>::default();

        let result = witness.populate_is_zero(&input);
        assert_eq!(result, expected);

        eval_is_zero(
            &mut builder,
            input.into_field::<F>(),
            F::from_bool(result),
            &witness,
            F::one(),
        );
    }
    fn test_is_equal<W: ArraySize>(in1: Word<u8, W>, in2: Word<u8, W>, expected: bool) {
        let mut builder = GadgetAirBuilder::<F>::default();

        assert_eq!(in1 == in2, expected);
        let mut witness = IsZeroWitness::<F, W>::default();

        let result = witness.populate_is_equal(&in1, &in2);
        assert_eq!(result, expected);

        eval_is_equal(
            &mut builder,
            (in1.into_field::<F>(), in2.into_field::<F>()),
            F::from_bool(result),
            &witness,
            F::one(),
        );
    }

    proptest! {

    #[test]
    fn test_is_zero_32(a: u32) {
        let r = a == 0;
        test_is_zero(Word32::from(a), r)
    }

    #[test]
    fn test_is_zero_64(a: u64) {
        let r = a == 0;
        test_is_zero(Word64::from(a), r)
    }

    #[test]
    fn test_is_equal_32(a: u32, b: u32) {
        let r = a == b;
        test_is_equal(Word32::from(a), Word32::from(b), r)
    }
    #[test]
    fn test_is_equal_64(a: u64, b: u64) {
        let r = a == b;
        test_is_equal(Word64::from(a), Word64::from(b), r)
    }

    }
}
