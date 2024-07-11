use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use hybrid_array::sizes::{U4, U8};
use hybrid_array::{Array, ArraySize};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use sphinx_derive::AlignedBorrow;
use std::iter::zip;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct MulWitness<T, W: ArraySize> {
    carry: Array<T, W>,
}

pub type Mul64Witness<T> = MulWitness<T, U8>;
pub type Mul32Witness<T> = MulWitness<T, U4>;

impl<F: AbstractField, W: ArraySize> MulWitness<F, W> {
    pub fn populate(
        &mut self,
        lhs: &Word<u8, W>,
        rhs: &Word<u8, W>,
        byte_record: &mut impl ByteRecord,
    ) -> Word<u8, W> {
        let mut carry = 0u16;
        let mut result = Word::default();
        for k in 0..W::USIZE {
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
        byte_record.range_check_u8_iter(result.clone());

        result
    }

    const fn num_requires() -> usize {
        W::USIZE // u16 carry checks
        + W::USIZE / 2 // range check output
    }
}

pub fn eval_mul<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: Word<impl Into<AB::Expr>, W>,
    witness: &MulWitness<AB::Var, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    let lhs = in1.into();
    let rhs = in2.into();
    let out = out.into();
    let is_real = is_real.into();

    let base = AB::F::from_canonical_u16(256);

    let expected =
        zip(out.clone(), &witness.carry).map(|(limb, &carry)| limb + carry.into() * base);

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
    use crate::gadgets::unsigned::{Word32, Word64};
    use p3_baby_bear::BabyBear;
    use proptest::proptest;

    type F = BabyBear;

    fn test_mul<W: ArraySize>(in1: Word<u8, W>, in2: Word<u8, W>, expected: Word<u8, W>) {
        let mut record = BytesRecord::default();
        let mut builder = GadgetAirBuilder::<F>::default();
        let mut requires = vec![RequireRecord::<F>::default(); MulWitness::<F, W>::num_requires()];

        assert_eq!(in1.clone() * in2.clone(), expected.clone());
        let mut witness = MulWitness::<F, W>::default();

        let result = witness.populate(&in1, &in2, &mut record.with_context(0, requires.iter_mut()));
        assert_eq!(result, expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_mul(
            &mut builder,
            (in1.into_field::<F>(), in2.into_field::<F>()),
            result.into_field::<F>(),
            &witness,
            &mut air_record,
            F::one(),
        );

        air_record.check();
        // air_record.require_all(&mut builder, F::from_canonical_u32(nonce), requires);
    }

    proptest! {

    #[test]
    fn test_mul_32(a: u32, b: u32) {
        let c = a.wrapping_mul(b);
        test_mul(Word32::from(a), Word32::from(b), Word32::from(c))
    }

    #[test]
    fn test_mul_64(a: u64, b: u64) {
        let c = a.wrapping_mul(b);
        test_mul(Word64::from(a), Word64::from(b), Word64::from(c))
    }

    }
}
