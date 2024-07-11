use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use hybrid_array::sizes::{U4, U8};
use hybrid_array::typenum::{Sub1, B1};
use hybrid_array::{Array, ArraySize};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use std::iter::zip;
use std::ops::Sub;

#[derive(Clone, Default)]
#[repr(C)]
pub struct AddWitness<T, W: ArraySize + Sub<B1>>
where
    Sub1<W>: ArraySize,
{
    carry: Array<T, Sub1<W>>,
}

pub type Add64Witness<T> = AddWitness<T, U8>;
pub type Add32Witness<T> = AddWitness<T, U4>;

impl<F: AbstractField, W: ArraySize + Sub<B1>> AddWitness<F, W>
where
    Sub1<W>: ArraySize,
{
    fn populate_add_sub(&mut self, in1: &Word<u8, W>, in2: &Word<u8, W>) -> Word<u8, W> {
        let mut result = Word::default();
        let mut carry_prev = 0u16;
        for (i, (&in1, &in2)) in zip(in1, in2).enumerate() {
            let [out, carry] = (u16::from(in1) + u16::from(in2) + carry_prev).to_le_bytes();
            result[i] = out;
            debug_assert!(carry == 0 || carry == 1);
            if carry == 1 && i < W::USIZE - 1 {
                self.carry[i] = F::one();
            }
            carry_prev = carry.into();
        }
        result
    }

    pub fn populate_add(
        &mut self,
        in1: &Word<u8, W>,
        in2: &Word<u8, W>,
        record: &mut impl ByteRecord,
    ) -> Word<u8, W> {
        let result = self.populate_add_sub(in1, in2);
        record.range_check_u8_iter(result.clone());
        result
    }

    pub fn populate_sub(
        &mut self,
        in1: &Word<u8, W>,
        in2: &Word<u8, W>,
        record: &mut impl ByteRecord,
    ) -> Word<u8, W> {
        let result = in1.clone() - in2.clone();

        let in1_expected = self.populate_add_sub(in2, &result);
        debug_assert_eq!(*in1, in1_expected);
        record.range_check_u8_iter(result.clone());

        result
    }

    const fn num_requires() -> usize {
        W::USIZE / 2
    }
}

fn eval_add_sub<AB: AirBuilder, W: ArraySize + Sub<B1>>(
    builder: &mut AB,
    (in1, in2): (Word<AB::Expr, W>, Word<AB::Expr, W>),
    out: Word<AB::Expr, W>,
    witness: &AddWitness<AB::Var, W>,
    is_real: AB::Expr,
) where
    Sub1<W>: ArraySize,
{
    let builder = &mut builder.when(is_real);

    let base = AB::F::from_canonical_u16(256);
    let mut carry_prev = AB::Expr::zero();
    for (i, out) in out.into_iter().enumerate() {
        let sum = in1[i].clone() + in2[i].clone() + carry_prev.clone();

        if i < W::USIZE - 1 {
            let carry = witness.carry[i];
            builder.assert_bool(carry);

            builder.assert_eq(sum, out + carry.into() * base);

            carry_prev = carry.into();
        } else {
            let diff = sum - out;
            builder.when(diff.clone()).assert_eq(diff, base);
        }
    }
}

pub fn eval_add<AB: AirBuilder, W: ArraySize + Sub<B1>>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: Word<impl Into<AB::Expr>, W>,
    witness: &AddWitness<AB::Var, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) where
    Sub1<W>: ArraySize,
{
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();
    eval_add_sub(builder, (in1, in2), out.clone(), witness, is_real.clone());
    record.range_check_u8_iter(out, is_real);
}

pub fn eval_sub<AB: AirBuilder, W: ArraySize + Sub<B1>>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: Word<impl Into<AB::Expr>, W>,
    witness: &AddWitness<AB::Var, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) where
    Sub1<W>: ArraySize,
{
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();
    eval_add_sub(builder, (in2, out.clone()), in1, witness, is_real.clone());
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
    use proptest::prelude::*;

    type F = BabyBear;

    fn test_add<W: ArraySize + Sub<B1>>(in1: Word<u8, W>, in2: Word<u8, W>, expected: &Word<u8, W>)
    where
        Sub1<W>: ArraySize,
    {
        let mut record = BytesRecord::default();
        let mut builder = GadgetAirBuilder::<F>::default();
        let mut requires = vec![RequireRecord::<F>::default(); AddWitness::<F, W>::num_requires()];

        assert_eq!(in1.clone() + in2.clone(), *expected);
        let mut witness = AddWitness::<F, W>::default();

        let result =
            witness.populate_add(&in1, &in2, &mut record.with_context(0, requires.iter_mut()));
        assert_eq!(result, *expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_add(
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

    fn test_sub<W: ArraySize + Sub<B1>>(in1: Word<u8, W>, in2: Word<u8, W>, expected: &Word<u8, W>)
    where
        Sub1<W>: ArraySize,
    {
        let mut record = BytesRecord::default();
        let mut builder = GadgetAirBuilder::<F>::default();
        let mut requires = vec![RequireRecord::<F>::default(); AddWitness::<F, W>::num_requires()];

        assert_eq!(in1.clone() - in2.clone(), *expected);
        let mut witness = AddWitness::<F, W>::default();

        let result =
            witness.populate_sub(&in1, &in2, &mut record.with_context(0, requires.iter_mut()));
        assert_eq!(result, *expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_sub(
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
    fn test_add_32(a: u32, b: u32) {
        let c = a.wrapping_add(b);
        test_add(Word32::from(a), Word32::from(b), &Word32::from(c))
    }

    #[test]
    fn test_add_64(a: u64, b: u64) {
        let c = a.wrapping_add(b);
        test_add(Word64::from(a), Word64::from(b), &Word64::from(c))
    }

    #[test]
    fn test_sub_32(a: u32, b: u32) {
        let c = a.wrapping_sub(b);
        test_sub(Word32::from(a), Word32::from(b), &Word32::from(c))
    }

    #[test]
    fn test_sub_64(a: u64, b: u64) {
        let c = a.wrapping_sub(b);
        test_sub(Word64::from(a), Word64::from(b), &Word64::from(c))
    }

    }
}
