use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::{UncheckedWord, Word};
use itertools::izip;
use num_traits::ops::overflowing::{OverflowingAdd, OverflowingSub};
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use sphinx_derive::AlignedBorrow;
use std::marker::PhantomData;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct AddWitness<T, const W: usize>(PhantomData<(T, [(); W])>);

impl<Var, const W: usize> AddWitness<Var, W> {
    /// Constraints for checking that lhs + rhs = out, where the operands are assumed to be
    /// range checked little-endian unsigned integers.
    /// Returns a boolean carry flag indicating whether an overflow happened.
    pub fn assert_add<AB: AirBuilder<Var = Var>>(
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        out: Word<AB::Expr, W>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Expr {
        let is_real = is_real.into();

        let base_inv = AB::F::from_canonical_u16(256).inverse();

        let mut carry = AB::Expr::zero();
        for (out, in1, in2) in izip!(out, lhs, rhs) {
            let sum = carry + in1 + in2;

            // in1[i] + in2[i] + carry[i-1] = out[i] + 256 * carry[i]
            // carry[i] = (in1[i] + in2[i] + carry[i-1] - out[i]) * 256^{-1}
            carry = (sum - out) * base_inv;
            // if carry[i] == 0
            //   in1[i] + in2[i] + carry[i-1] == out[i]
            // else
            //   in1[i] + in2[i] + carry[i-1] == out[i] + 256
            builder.when(is_real.clone()).assert_bool(carry.clone());
        }
        carry
    }
}

/// Wrapper type for addition, which contains the witness and output of the computation.
#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct Sum<T, const W: usize> {
    result: UncheckedWord<T, W>,
}
pub type Sum64<T> = Sum<T, 8>;
pub type Sum32<T> = Sum<T, 4>;

impl<F: AbstractField, const W: usize> Sum<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord) -> U
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + OverflowingAdd,
    {
        let (out, _carry) = lhs.overflowing_add(rhs);
        self.result.assign_bytes(&out.to_le_bytes(), byte_record);
        out
    }
}

impl<Var, const W: usize> Sum<Var, W> {
    pub fn eval<AB>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> Word<AB::Var, W>
    where
        AB: AirBuilder<Var = Var>,
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        let result = self.result.into_checked(record, is_real.clone());

        AddWitness::<Var, W>::assert_add(builder, lhs, rhs, result.into(), is_real.clone());
        result
    }
}

impl<T, const W: usize> Sum<T, W> {
    pub const fn num_requires() -> usize {
        W / 2
    }
}

/// Wrapper type for subtraction, which contains the witness and output of the computation.
#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct Diff<T, const W: usize> {
    result: UncheckedWord<T, W>,
}

pub type Diff64<T> = Diff<T, 8>;
pub type Diff32<T> = Diff<T, 4>;

impl<F: AbstractField, const W: usize> Diff<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord) -> U
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + OverflowingSub,
    {
        let (out, _carry) = lhs.overflowing_sub(rhs);
        self.result.assign_bytes(&out.to_le_bytes(), byte_record);
        out
    }
}

impl<Var, const W: usize> Diff<Var, W> {
    pub fn eval<AB>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> Word<AB::Var, W>
    where
        AB: AirBuilder<Var = Var>,
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        let result = self.result.into_checked(record, is_real.clone());
        // result + rhs = lhs => lhs - rhs = result
        AddWitness::<Var, W>::assert_add(builder, result.into(), rhs, lhs, is_real.clone());
        result
    }
}

impl<T, const W: usize> Diff<T, W> {
    pub const fn num_requires() -> usize {
        W / 2
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;
    use std::fmt::Debug;

    type F = BabyBear;

    fn test_add_sub<
        const W: usize,
        U: ToBytes<Bytes = [u8; W]> + Unsigned + OverflowingAdd + OverflowingSub + Debug,
    >(
        lhs: U,
        rhs: U,
    ) {
        let record = &mut ByteRecordTester::default();

        let mut add_witness = Sum::<F, W>::default();
        let add = add_witness.populate(&lhs, &rhs, record);
        let (add_expected, _) = lhs.overflowing_add(&rhs);
        assert_eq!(add, add_expected);
        let add_f = add_witness.eval(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(&lhs),
            Word::<F, W>::from_unsigned(&rhs),
            &mut record.passing(Sum::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(add_f, Word::from_unsigned(&add));

        let mut sub_witness = Diff::<F, W>::default();
        let sub = sub_witness.populate(&lhs, &rhs, record);
        let (sub_expected, _) = lhs.overflowing_sub(&rhs);
        assert_eq!(sub, sub_expected);
        let sub_f = sub_witness.eval(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(&lhs),
            Word::<F, W>::from_unsigned(&rhs),
            &mut record.passing(Diff::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(sub_f, Word::from_unsigned(&sub));
    }

    proptest! {

    #[test]
    fn test_add_sub_32(a: u32, b: u32) {
        test_add_sub(a, b)
    }

    #[test]
    fn test_add_sub_64(a: u64, b: u64) {
        test_add_sub(a, b)
    }

    }
}
