use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::add::AddWitness;
use crate::gadgets::unsigned::less_than::{IsLessThan, LessThanWitness};
use crate::gadgets::unsigned::mul::Product;
use crate::gadgets::unsigned::{UncheckedWord, Word};
use num_traits::{FromBytes, ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;
use std::ops::{Div, Rem};

#[derive(Clone, Default, AlignedBorrow)]
#[repr(C)]
pub struct DivRem<T, const W: usize> {
    /// q = a // b
    q: UncheckedWord<T, W>,
    /// r = a % b
    r: UncheckedWord<T, W>,
    /// qb = q * b
    qb: Product<T, W>,
    /// is_r_lt_b = r < b
    is_r_lt_b: LessThanWitness<T, W>,
    /// is_qb_lte_a = qb <= a
    is_qb_lte_a: IsLessThan<T, W>,
}

impl<F: PrimeField, const W: usize> DivRem<F, W> {
    pub fn populate<U>(&mut self, a: &U, b: &U, byte_record: &mut impl ByteRecord) -> (U, U)
    where
        U: ToBytes<Bytes = [u8; W]> + FromBytes<Bytes = [u8; W]> + Unsigned + Div + Rem + Copy,
    {
        let q = a.div(*b);
        let r = a.rem(*b);
        self.q.assign_bytes(&q.to_le_bytes(), byte_record);
        self.r.assign_bytes(&r.to_le_bytes(), byte_record);

        let qb = self.qb.populate(&q, b, byte_record);
        let is_r_lt_b = self.is_r_lt_b.populate(&r, b, byte_record);
        debug_assert!(is_r_lt_b);
        let is_qb_lte_a = self
            .is_qb_lte_a
            .populate_less_than_or_equal(&qb, a, byte_record);
        debug_assert!(is_qb_lte_a);
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
        // Following Jolt (https://eprint.iacr.org/2023/1217.pdf) 6.3
        // Assume a, b are range checked
        let q = self.q.into_checked(record, is_real.clone());
        let r = self.r.into_checked(record, is_real.clone());

        // q * b
        let qb = self.qb.eval(builder, &q.into(), b, record, is_real.clone());

        // a = q * b + r
        // we use sum to avoid the range check of a
        AddWitness::<Var, W>::assert_add(builder, qb.into(), r.into(), a.clone(), is_real.clone());

        // r < b
        let is_r_lt_b = AB::F::one();
        self.is_r_lt_b.assert_is_less_than(
            builder,
            &r.into(),
            b,
            is_r_lt_b,
            record,
            is_real.clone(),
        );

        // q * b <= a
        let is_qb_lte_a = self.is_qb_lte_a.eval_less_than_or_equal(
            builder,
            &qb.into(),
            a,
            record,
            is_real.clone(),
        );
        builder.when(is_real.clone()).assert_one(is_qb_lte_a);
        (q, r)
    }
}
impl<T, const W: usize> DivRem<T, W> {
    pub const fn num_requires() -> usize {
        2 * (W / 2)
            + Product::<T, W>::num_requires()
            + LessThanWitness::<T, W>::num_requires()
            + IsLessThan::<T, W>::num_requires()
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

    fn test_div_rem<
        const W: usize,
        U: ToBytes<Bytes = [u8; W]>
            + FromBytes<Bytes = [u8; W]>
            + Unsigned
            + Div
            + Rem
            + Copy
            + Debug
            + Ord,
    >(
        a: U,
        b: U,
    ) {
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
