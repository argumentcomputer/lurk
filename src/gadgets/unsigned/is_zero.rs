use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use sphinx_derive::AlignedBorrow;
use std::iter::zip;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct IsZeroWitness<T> {
    inverses: [T; WORD_SIZE],
}

impl<F: Field> IsZeroWitness<F> {
    pub fn populate_is_zero(&mut self, word: Word<u8>) -> bool {
        for (limb, inv) in zip(word, self.inverses.iter_mut()) {
            if limb != 0 {
                *inv = F::from_canonical_u8(limb).inverse();
                return false;
            }
        }
        true
    }

    pub fn populate_is_equal(&mut self, word1: Word<u8>, word2: Word<u8>) -> bool {
        for ((limb1, limb2), inv) in zip(zip(word1, word2), self.inverses.iter_mut()) {
            if limb1 != limb2 {
                let diff = F::from_canonical_u8(limb1) - F::from_canonical_u8(limb2);
                *inv = diff.inverse();
                return false;
            }
        }
        true
    }
}

pub fn eval_is_zero<AB: AirBuilder>(
    builder: &mut AB,
    input: Word<impl Into<AB::Expr>>,
    is_zero: impl Into<AB::Expr>,
    witness: &IsZeroWitness<AB::Var>,
    is_real: impl Into<AB::Expr>,
) {
    let builder = &mut builder.when(is_real.into());

    let input = input.into();
    let is_zero = is_zero.into();

    builder.assert_bool(is_zero.clone());

    for i in &input {
        builder.when(is_zero.clone()).assert_zero(i.clone());
    }

    let lc = zip(input, witness.inverses)
        .map(|(i, inv)| i * inv.into())
        .sum::<AB::Expr>();

    builder.when_ne(is_zero, AB::F::one()).assert_one(lc);
}

pub fn eval_is_equal<AB: AirBuilder>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>>, Word<impl Into<AB::Expr>>),
    is_equal: impl Into<AB::Expr>,
    witness: &IsZeroWitness<AB::Var>,
    is_real: impl Into<AB::Expr>,
) {
    let in1 = in1.into();
    let in2 = in2.into();
    let diff = Word::from_fn(|i| in1[i].clone() - in2[i].clone());
    eval_is_zero(builder, diff, is_equal, witness, is_real);
}
