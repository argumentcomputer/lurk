use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use sphinx_derive::AlignedBorrow;
use std::iter::zip;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct AddWitness<T> {
    carry: [T; WORD_SIZE - 1],
}

impl<F: AbstractField> AddWitness<F> {
    pub fn populate(
        &mut self,
        in1: Word<u8>,
        in2: Word<u8>,
        record: &mut impl ByteRecord,
    ) -> Word<u8> {
        let mut result = Word::default();
        let mut carry_prev = 0u16;
        for (i, (in1, in2)) in zip(in1, in2).enumerate() {
            let [out, carry] = (u16::from(in1) + u16::from(in2) + carry_prev).to_le_bytes();
            result[i] = out;
            debug_assert!(carry == 0 || carry == 1);
            if carry == 1 && i < WORD_SIZE - 1 {
                self.carry[i] = F::one();
            }
            carry_prev = carry.into();
        }
        result.range_check(record);
        result
    }

    const fn num_requires() -> usize {
        WORD_SIZE / 2
    }
}

pub fn eval_add<AB: AirBuilder>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>>, Word<impl Into<AB::Expr>>),
    out: Word<impl Into<AB::Expr>>,
    witness: &AddWitness<AB::Var>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();

    let builder = &mut builder.when(is_real.clone());

    let base = AB::F::from_canonical_u16(256);
    let mut carry_prev = AB::Expr::zero();
    for i in 0..WORD_SIZE {
        let sum = in1[i].clone() + in2[i].clone() + carry_prev.clone();

        if i < WORD_SIZE - 1 {
            let carry = witness.carry[i];
            builder.assert_bool(carry);

            builder.assert_eq(sum, out[i].clone() + carry.into() * base);

            carry_prev = carry.into();
        } else {
            let diff = sum - out[i].clone();
            builder.when(diff.clone()).assert_eq(diff, base);
        }
    }

    record.range_check_u8_iter(out, is_real);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::builder::RequireRecord;
    use crate::gadgets::bytes::builder::BytesAirRecordWithContext;
    use crate::gadgets::bytes::record::BytesRecord;
    use crate::gadgets::debug::GadgetAirBuilder;
    use p3_baby_bear::BabyBear;

    #[test]
    fn test_add() {
        type F = BabyBear;

        let inputs = [
            (0u64, 0u64),
            (0u64, u64::MAX),
            (u64::MAX, 0u64),
            (1u64, u64::MAX),
            (u64::MAX, 1u64),
        ];
        let mut record = BytesRecord::default();

        for (i, (lhs, rhs)) in inputs.into_iter().enumerate() {
            let nonce = i as u32;
            let out = lhs.wrapping_add(rhs);
            let lhs = Word(lhs.to_le_bytes());
            let rhs = Word(rhs.to_le_bytes());
            let out_expected = Word(out.to_le_bytes());

            let mut witness = AddWitness::<F>::default();
            let mut requires = vec![RequireRecord::<F>::default(); AddWitness::<F>::num_requires()];
            let out = witness.populate(
                lhs,
                rhs,
                &mut record.with_context(nonce, requires.iter_mut()),
            );
            assert_eq!(out, out_expected);

            let mut air_record = BytesAirRecordWithContext::default();

            let mut builder = GadgetAirBuilder::<F>::default();
            eval_add(
                &mut builder,
                (lhs.into_field::<F>(), rhs.into_field::<F>()),
                out.into_field::<F>(),
                &witness,
                &mut air_record,
                F::one(),
            );
        }
    }
}
