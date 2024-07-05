use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField32};
use std::iter::zip;

pub struct IsZeroWitness<T> {
    inverses: [T; WORD_SIZE],
}

impl<F: PrimeField32> IsZeroWitness<F> {
    pub fn populate(&mut self, word: Word<u8>) -> bool {
        for (limb, inv) in zip(word, self.inverses.iter_mut()) {
            if limb != 0 {
                *inv = F::from_canonical_u8(limb).inverse();
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
