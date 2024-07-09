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

    // If is_zero, all limbs are zero
    for i in &input {
        builder.when(is_zero.clone()).assert_zero(i.clone());
    }

    // Otherwise, there exist w such that 1 = ∑ w[i]*limb[i]
    let not_zero = is_zero - AB::F::one();
    let lc = zip(input, witness.inverses)
        .map(|(i, inv)| i * inv.into())
        .sum::<AB::Expr>();

    builder.when(not_zero).assert_one(lc);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::GadgetAirBuilder;
    use p3_baby_bear::BabyBear;
    #[test]
    fn test_is_zero() {
        type F = BabyBear;

        let inputs = [0u64, 1, 1 << 8, 1 << 16, 1 << 24, 1 << 63];

        for input in inputs {
            let word = Word(input.to_le_bytes());

            let mut witness = IsZeroWitness::<F>::default();
            let is_zero = witness.populate_is_zero(word);
            assert_eq!(is_zero, input == 0);

            let mut builder = GadgetAirBuilder::<F>::default();
            eval_is_zero(
                &mut builder,
                word.into_field::<F>(),
                F::from_bool(is_zero),
                &witness,
                F::one(),
            );
        }
    }

    #[test]
    fn test_is_equal() {
        type F = BabyBear;

        let inputs = [(0u64, 0u64), (4, 5), (1, 0), (0, 1)];

        for (lhs, rhs) in inputs {
            let word_l = Word(lhs.to_le_bytes());
            let word_r = Word(rhs.to_le_bytes());

            let mut witness = IsZeroWitness::<F>::default();
            let is_equal = witness.populate_is_equal(word_l, word_r);
            assert_eq!(is_equal, lhs == rhs);

            let mut builder = GadgetAirBuilder::<F>::default();
            eval_is_equal(
                &mut builder,
                (word_l.into_field::<F>(), word_r.into_field::<F>()),
                F::from_bool(is_equal),
                &witness,
                F::one(),
            );
        }
    }
}
