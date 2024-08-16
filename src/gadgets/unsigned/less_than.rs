use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;
use std::array;
use std::iter::zip;

#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct LessThanWitness<T, const W: usize> {
    is_comp: [T; W],
    lhs_comp_limb: T,
    rhs_comp_limb: T,
}

impl<F: PrimeField, const W: usize> LessThanWitness<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord)
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + Ord,
    {
        assert!(lhs < rhs);
        let lhs = lhs.to_le_bytes();
        let rhs = rhs.to_le_bytes();
        // Iterate over limbs in reverse order
        for i in (0..W).rev() {
            // Stop at first unequal limb
            if lhs[i] != rhs[i] {
                self.is_comp[i] = F::one();
                self.lhs_comp_limb = F::from_canonical_u8(lhs[i]);
                self.rhs_comp_limb = F::from_canonical_u8(rhs[i]);

                byte_record.less_than(lhs[i], rhs[i]);
                return;
            }
        }
        unreachable!()
    }
}

impl<Var, const W: usize> LessThanWitness<Var, W> {
    /// Constraints for checking that is_less_than = (lhs < rhs), where the operands are assumed to be
    /// range checked little-endian unsigned integers.
    /// The `is_less_than` variable will always be boolean-checked since it a result of a lookup relation.
    /// Returns a boolean variable `is_equal = (lhs == rhs)`
    pub fn assert_less_than<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: &Word<AB::Expr, W>,
        rhs: &Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        let builder = &mut builder.when(is_real.clone());

        let mut is_equal = AB::Expr::zero();
        for i in 0..W {
            // Since is_equal starts at zero, we never need to compare the first limbs.
            // If they were equal, then all subsequent ones would be too,
            // and the assertion would fail.
            if i > 0 {
                builder
                    .when(is_equal.clone())
                    .assert_eq(lhs[i].clone(), rhs[i].clone());
            }

            // `is_comp` indicates whether this is the most significant non-equal limb pair
            let is_comp = self.is_comp[i];
            builder.assert_bool(is_comp);
            // Set the equality checking flag if this is the first non-equal limb pair
            is_equal += is_comp.into();
        }
        // Exactly one is_comp flag should have been set.
        builder.assert_one(is_equal.clone());

        // Ensure the limbs used for comparison are the ones selected by `is_comp`
        // Stores the most significant non-equal limbs
        let select_limb = |word: &Word<AB::Expr, W>| -> AB::Expr {
            zip(word, &self.is_comp)
                .map(|(limb, &flag)| limb.clone() * flag.into())
                .sum()
        };
        builder.assert_eq(select_limb(lhs), self.lhs_comp_limb);
        builder.assert_eq(select_limb(rhs), self.rhs_comp_limb);

        let is_less_than = AB::Expr::one();
        record.less_than(
            self.lhs_comp_limb,
            self.rhs_comp_limb,
            is_less_than,
            is_real,
        );
    }
}

impl<T, const W: usize> LessThanWitness<T, W> {
    pub const fn num_requires() -> usize {
        1
    }

    pub const fn witness_size() -> usize {
        size_of::<LessThanWitness<u8, W>>()
    }
}

impl<T: Default, const W: usize> Default for LessThanWitness<T, W> {
    fn default() -> Self {
        Self {
            is_comp: array::from_fn(|_| T::default()),
            lhs_comp_limb: T::default(),
            rhs_comp_limb: T::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use expect_test::expect;
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;

    type F = BabyBear;

    #[test]
    fn test_witness_size() {
        expect!["6"].assert_eq(&LessThanWitness::<u8, 4>::witness_size().to_string());
        expect!["10"].assert_eq(&LessThanWitness::<u8, 8>::witness_size().to_string());
    }

    #[test]
    fn test_num_requires() {
        expect!["1"].assert_eq(&LessThanWitness::<u8, 4>::num_requires().to_string());
        expect!["1"].assert_eq(&LessThanWitness::<u8, 8>::num_requires().to_string());
    }

    fn test_less_than<const W: usize, U: ToBytes<Bytes = [u8; W]> + Unsigned + Ord>(
        lhs: U,
        rhs: U,
    ) {
        let (lhs, rhs) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };

        let record = &mut ByteRecordTester::default();

        let mut lt_witness = LessThanWitness::<F, W>::default();
        lt_witness.populate(&lhs, &rhs, record);
        lt_witness.assert_less_than(
            &mut GadgetTester::passing(),
            &Word::<F, W>::from_unsigned(&lhs),
            &Word::<F, W>::from_unsigned(&rhs),
            &mut record.passing(LessThanWitness::<F, W>::num_requires()),
            F::one(),
        );
    }

    proptest! {

    #[test]
    fn test_less_than_32(a: u32, b: u32) {
        test_less_than::<4, _>(a, b);
    }

    #[test]
    fn test_less_than_64(a: u64, b: u64) {
        test_less_than::<8, _>(a, b);
    }

    }
}
