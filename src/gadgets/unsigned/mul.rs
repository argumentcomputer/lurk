use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::{Word, WORD_SIZE};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use sphinx_derive::AlignedBorrow;
use std::iter::zip;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct MulWitness<T> {
    carry: [T; WORD_SIZE],
}

impl<F: AbstractField> MulWitness<F> {
    pub fn populate(
        &mut self,
        lhs: Word<u8>,
        rhs: Word<u8>,
        byte_record: &mut impl ByteRecord,
    ) -> Word<u8> {
        let mut carry = 0u16;
        let mut result = Word::default();
        for k in 0..WORD_SIZE {
            let product = (0..=k).fold(u32::from(carry), |acc, i| {
                let j = k - i;
                acc + u32::from(lhs[i]) * u32::from(rhs[j])
            });

            let [limb, carry_lo, carry_hi, null] = product.to_le_bytes();
            debug_assert_eq!(null, 0);

            carry = u16::from_le_bytes([carry_lo, carry_hi]);
            byte_record.range_check_u16(carry);
            self.carry[k] = F::from_canonical_u16(carry);

            result[k] = limb
        }
        byte_record.range_check_u8_iter(result);

        result
    }

    const fn num_requires() -> usize {
        WORD_SIZE // u16 carry checks
        + WORD_SIZE / 2 // range check output
    }
}

pub fn eval_mul<AB: AirBuilder>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>>, Word<impl Into<AB::Expr>>),
    out: Word<impl Into<AB::Expr>>,
    witness: &MulWitness<AB::Var>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    let lhs = in1.into();
    let rhs = in2.into();
    let out = out.into();
    let is_real = is_real.into();

    let base = AB::F::from_canonical_u16(256);

    let expected = zip(out.clone(), witness.carry).map(|(limb, carry)| limb + carry.into() * base);

    let mut carry = AB::Expr::zero();
    for (k, expected) in expected.enumerate() {
        let product = (0..=k).fold(carry, |acc, i| {
            let j = k - i;
            acc + lhs[i].clone() * rhs[j].clone()
        });

        carry = witness.carry[k].into();
        record.range_check_u16(carry.clone(), is_real.clone());

        builder.when(is_real.clone()).assert_eq(expected, product);
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
    fn test_mul() {
        type F = BabyBear;

        let inputs = [
            (0u64, 0u64),
            (0u64, 1u64),
            (1u64, 0u64),
            (1u64, 1u64),
            (0u64, u64::MAX),
            (1u64, u64::MAX),
            (u64::MAX, 0u64),
            (u64::MAX, 1u64),
            (0u64, u64::MAX),
            (1u64, u64::MAX),
            (u64::MAX, 0u64),
            (u64::MAX, 1u64),
            (2u64, u64::MAX),
            (u64::MAX, 2u64),
        ];

        let mut record = BytesRecord::default();

        for (i, (lhs, rhs)) in inputs.into_iter().enumerate() {
            let nonce = i as u32;
            let out = lhs.wrapping_mul(rhs);
            let lhs = Word(lhs.to_le_bytes());
            let rhs = Word(rhs.to_le_bytes());
            let out_expected = Word(out.to_le_bytes());

            let mut witness = MulWitness::<F>::default();
            let mut requires = vec![RequireRecord::<F>::default(); MulWitness::<F>::num_requires()];
            let out = witness.populate(
                lhs,
                rhs,
                &mut record.with_context(nonce, requires.iter_mut()),
            );
            assert_eq!(out, out_expected, "lhs: {:?}, rhs: {:?}", lhs, rhs);

            let mut builder = GadgetAirBuilder::<F>::default();
            let mut air_record = BytesAirRecordWithContext::default();
            eval_mul(
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
