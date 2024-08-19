use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::add::Diff;
use crate::gadgets::unsigned::cmp::CompareWitness;
use crate::gadgets::unsigned::is_zero::IsZeroWitness;
use crate::gadgets::unsigned::less_than::LessThanWitness;
use crate::gadgets::unsigned::mul::Product;
use crate::gadgets::unsigned::{UncheckedWord, Word};
use num_traits::ops::overflowing::OverflowingSub;
use num_traits::{FromBytes, ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::PrimeField;
use sphinx_derive::AlignedBorrow;
use std::cmp::Ordering;
use std::ops::Div;

#[derive(Clone, Default, AlignedBorrow)]
#[repr(C)]
pub struct DivRem<T, const W: usize> {
    b_non_zero: IsZeroWitness<T, W>,
    /// q = a // b
    q: UncheckedWord<T, W>,
    /// qb = q * b
    qb: Product<T, W>,
    /// r = a % b = a - q * b
    r: Diff<T, W>,
    /// is_r_lt_b = r < b
    r_lt_b: LessThanWitness<T, W>,
    /// is_qb_lte_a = qb <= a
    qb_cmp_a: CompareWitness<T, W>,
}

impl<F: PrimeField, const W: usize> DivRem<F, W> {
    pub fn populate<U>(&mut self, a: &U, b: &U, byte_record: &mut impl ByteRecord) -> (U, U)
    where
        U: ToBytes<Bytes = [u8; W]>
            + FromBytes<Bytes = [u8; W]>
            + Unsigned
            + Div
            + Copy
            + OverflowingSub
            + Ord,
    {
        // b != 0
        self.b_non_zero.populate_non_zero(b);

        // q = a // b
        let q = a.div(*b);
        self.q.assign_bytes(&q.to_le_bytes(), byte_record);

        let qb = self.qb.populate(&q, b, byte_record);
        // r = a - qb
        let r = self.r.populate(a, &qb, byte_record);
        // r < b
        self.r_lt_b.populate(&r, b, byte_record);
        // qb <= a
        let is_qb_lte_a = self.qb_cmp_a.populate(&qb, a, byte_record);
        assert!(matches!(is_qb_lte_a, Ordering::Less | Ordering::Equal));
        (q, r)
    }
}

impl<Var, const W: usize> DivRem<Var, W> {
    pub fn eval<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        a: &Word<AB::Expr, W>,
        b: &Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> (Word<AB::Var, W>, Word<AB::Var, W>)
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        // b != 0
        self.b_non_zero
            .assert_non_zero(builder, b.clone(), is_real.clone());

        // Following Jolt (https://eprint.iacr.org/2023/1217.pdf) 6.3
        // Assume a, b are range checked
        let q = self.q.into_checked(record, is_real.clone());

        // q * b
        let qb = self.qb.eval(builder, &q.into(), b, record, is_real.clone());

        // r = a - q * b
        let r = self
            .r
            .eval(builder, a.clone(), qb.into(), record, is_real.clone());

        // r < b
        self.r_lt_b
            .assert_less_than(builder, &r.into(), b, record, is_real.clone());

        // q * b <= a
        let qb_cmp_a = self
            .qb_cmp_a
            .eval(builder, &qb.into(), a, record, is_real.clone());
        builder
            .when(is_real.clone())
            .assert_one(qb_cmp_a.is_less_than_or_equal());
        (q, r)
    }
}
impl<T, const W: usize> DivRem<T, W> {
    pub const fn num_requires() -> usize {
        W / 2
            + Diff::<T, W>::num_requires()
            + Product::<T, W>::num_requires()
            + LessThanWitness::<T, W>::num_requires()
            + CompareWitness::<T, W>::num_requires()
    }

    pub const fn witness_size() -> usize {
        size_of::<DivRem<u8, W>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.q.0.clone().into_iter().chain(self.r.iter_result())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use expect_test::expect;
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use proptest::prelude::*;
    use std::fmt::Debug;

    type F = BabyBear;

    #[test]
    fn test_witness_size() {
        expect!["34"].assert_eq(&DivRem::<u8, 4>::witness_size().to_string());
        expect!["62"].assert_eq(&DivRem::<u8, 8>::witness_size().to_string());
    }
    #[test]
    fn test_num_requires() {
        expect!["12"].assert_eq(&DivRem::<u8, 4>::num_requires().to_string());
        expect!["22"].assert_eq(&DivRem::<u8, 8>::num_requires().to_string());
    }

    fn test_div_rem<
        const W: usize,
        U: ToBytes<Bytes = [u8; W]>
            + FromBytes<Bytes = [u8; W]>
            + Unsigned
            + Div
            + OverflowingSub
            + Copy
            + Debug
            + Ord,
    >(
        a: U,
        b: U,
    ) {
        if b.is_zero() {
            return;
        }
        let record = &mut ByteRecordTester::default();

        let mut witness = DivRem::<F, W>::default();
        let (q, r) = witness.populate(&a, &b, record);
        assert_eq!(b * q + r, a);
        assert!(r < b);
        assert!(q * b <= a);
        let (q_f, r_f) = witness.eval(
            &mut GadgetTester::passing(),
            &Word::<F, W>::from_unsigned(&a),
            &Word::<F, W>::from_unsigned(&b),
            &mut record.passing(DivRem::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(q_f, Word::from_unsigned(&q));
        assert_eq!(r_f, Word::from_unsigned(&r));
    }

    proptest! {

    #[test]
    fn test_div_rem_32(a: u32, b: u32) {
        test_div_rem::<4, _>(a, b);
    }

    #[test]
    fn test_div_rem_64(a: u64, b: u64) {
        test_div_rem::<8, _>(a, b);
    }

    }
}
