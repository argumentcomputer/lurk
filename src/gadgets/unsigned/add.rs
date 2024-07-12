use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use hybrid_array::typenum::{Sub1, B1};
use hybrid_array::ArraySize;
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use std::iter::zip;
use std::ops::Sub;

pub fn populate_add<W: ArraySize>(
    in1: Word<u8, W>,
    in2: Word<u8, W>,
    record: &mut impl ByteRecord,
) -> Word<u8, W> {
    let result = in1 + in2;
    record.range_check_u8_iter(result.clone());
    result
}

pub fn populate_sub<W: ArraySize>(
    in1: Word<u8, W>,
    in2: Word<u8, W>,
    record: &mut impl ByteRecord,
) -> Word<u8, W> {
    let result = in1 - in2;
    record.range_check_u8_iter(result.clone());
    result
}

pub const fn num_requires<W: ArraySize>() -> usize {
    W::USIZE / 2
}

fn eval_sum<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (in1, in2): (Word<AB::Expr, W>, Word<AB::Expr, W>),
    out: Word<AB::Expr, W>,
    is_real: AB::Expr,
) {
    let builder = &mut builder.when(is_real);

    let base_inv = AB::F::from_canonical_u16(256).inverse();

    let mut carry = AB::Expr::zero();
    for (out, (in1, in2)) in out.into_iter().zip(zip(in1, in2)) {
        let sum = carry + in1 + in2;

        // in1[i] + in2[i] + carry[i-1] = out[i] + 256 * carry[i]
        // carry[i] = (in1[i] + in2[i] + carry[i-1] - out[i]) * 256^{-1}
        carry = (sum - out) * base_inv;
        // if carry[i] == 0
        //   in1[i] + in2[i] + carry[i-1] == out[i]
        // else
        //   in1[i] + in2[i] + carry[i-1] == out[i] + 256
        builder.assert_bool(carry.clone());
    }
}

pub fn eval_add<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: Word<impl Into<AB::Expr>, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();
    record.range_check_u8_iter(out.clone(), is_real.clone());
    eval_sum(builder, (in1, in2), out, is_real);
}

pub fn eval_sub<AB: AirBuilder, W: ArraySize + Sub<B1>>(
    builder: &mut AB,
    (in1, in2): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: Word<impl Into<AB::Expr>, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) where
    Sub1<W>: ArraySize,
{
    let in1 = in1.into();
    let in2 = in2.into();
    let out = out.into();
    let is_real = is_real.into();
    record.range_check_u8_iter(out.clone(), is_real.clone());
    eval_sum(builder, (in2, out), in1, is_real);
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

    fn test_add<W: ArraySize>(in1: Word<u8, W>, in2: Word<u8, W>, expected: &Word<u8, W>) {
        let mut record = BytesRecord::default();
        let mut builder = GadgetAirBuilder::<F>::default();
        let mut requires = vec![RequireRecord::<F>::default(); num_requires::<W>()];

        assert_eq!(in1.clone() + in2.clone(), *expected);

        let result = populate_add(
            in1.clone(),
            in2.clone(),
            &mut record.with_context(0, requires.iter_mut()),
        );
        assert_eq!(result, *expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_add(
            &mut builder,
            (in1.into_field::<F>(), in2.into_field::<F>()),
            result.into_field::<F>(),
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
        let mut requires = vec![RequireRecord::<F>::default(); num_requires::<W>()];

        assert_eq!(in1.clone() - in2.clone(), *expected);

        let result = populate_sub(
            in1.clone(),
            in2.clone(),
            &mut record.with_context(0, requires.iter_mut()),
        );
        assert_eq!(result, *expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_sub(
            &mut builder,
            (in1.into_field::<F>(), in2.into_field::<F>()),
            result.into_field::<F>(),
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
