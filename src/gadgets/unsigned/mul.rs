use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use std::iter::zip;

pub struct MulWitness<T> {
    carry: [T; WORD_SIZE],
}

impl<F: AbstractField> MulWitness<F> {
    pub fn populate(&mut self, lhs: Word<u8>, rhs: Word<u8>) -> Word<u8> {
        let mut carry = 0u16;
        let mut result = Word::default();
        for k in 0..WORD_SIZE {
            let product = (0..k).fold(carry as u32, |acc, i| {
                let j = k - i;
                acc + u32::from(lhs[i]) * u32::from(rhs[j])
            });

            let [limb, carry_lo, carry_hi, null] = product.to_le_bytes();
            debug_assert_eq!(null, 0);

            carry = u16::from_le_bytes([carry_lo, carry_hi]);
            // TODO: Range check carry[i] is u16
            self.carry[k] = F::from_canonical_u16(carry);

            result[k] = limb
        }

        result
    }
}

pub fn eval_mut<AB: AirBuilder>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>>, Word<impl Into<AB::Expr>>),
    out: Word<impl Into<AB::Expr>>,
    witness: MulWitness<AB::Var>,
    is_real: impl Into<AB::Expr>,
) {
    let lhs = in1.into();
    let rhs = in2.into();
    let is_real = is_real.into();

    let base = AB::F::from_canonical_u16(256);

    let expected = zip(out, witness.carry).map(|(limb, carry)| limb.into() + carry.into() * base);

    let mut carry = AB::Expr::zero();
    for (k, expected) in expected.enumerate() {
        let product = (0..k).fold(carry, |acc, i| {
            let j = k - i;
            acc + lhs[i].clone() * rhs[j].clone()
        });

        carry = witness.carry[k].into();

        builder.when(is_real.clone()).assert_eq(expected, product);
    }

    // TODO: Range check carry[i] is u16
}
