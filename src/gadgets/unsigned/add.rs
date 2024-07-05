use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField32};
use std::array;
use std::iter::zip;

pub struct AddWitness<T> {
    carry: [T; WORD_SIZE - 1],
}

impl<F: PrimeField32> AddWitness<F> {
    pub fn populate(&mut self, in1: Word<u8>, in2: Word<u8>) -> Word<u8> {
        Word::default()
    }
}

pub fn eval_add<AB: AirBuilder>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>>, Word<impl Into<AB::Expr>>),
    out: Word<impl Into<AB::Expr>>,
    witness: &AddWitness<AB::Var>,
    is_real: impl Into<AB::Expr>,
) {
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();
    let carry = witness.carry;

    let base = AB::F::from_canonical_u16(256);

    let builder = &mut builder.when(is_real.clone());

    let overflow: [AB::Expr; WORD_SIZE] = array::from_fn(|i| {
        // For each limb, assert that difference between the carried result and the non-carried
        // result is either zero or the base.
        let overflow = if i == 0 {
            in1[i].clone() + in2[i].clone() - out[i].clone()
        } else {
            in1[i].clone() + in2[i].clone() - out[i].clone() + carry[i - 1]
        };
        // If overflow is non-zero, then it must be equal to 256
        builder
            .when(overflow.clone())
            .assert_eq(overflow.clone(), base);
        overflow
    });

    for (overflow, carry) in zip(overflow, carry) {
        // carry is either 0 or 1
        builder.assert_bool(carry);

        // overflow = 256 <=> carry = 1
        builder.when(overflow.clone()).assert_one(carry);
        builder.when(carry).assert_eq(overflow, base);
    }
}
