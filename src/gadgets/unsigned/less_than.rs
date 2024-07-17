use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;
use std::array;

#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct LessThanWitness<T, const W: usize> {
    is_comp: [T; W],
    lhs_comp_limb: T,
    rhs_comp_limb: T,
    diff_comp_inv: T,
}

impl<F: PrimeField, const W: usize> LessThanWitness<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord) -> bool
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned,
    {
        if lhs == rhs {
            byte_record.less_than(0, 0)
        } else {
            let lhs = lhs.to_le_bytes();
            let rhs = rhs.to_le_bytes();
            // Iterate over limbs in reverse order
            for i in (0..W).rev() {
                // Stop at first unequal limb
                if lhs[i] != rhs[i] {
                    self.is_comp[i] = F::one();
                    self.lhs_comp_limb = F::from_canonical_u8(lhs[i]);
                    self.rhs_comp_limb = F::from_canonical_u8(rhs[i]);
                    self.diff_comp_inv = (self.lhs_comp_limb - self.rhs_comp_limb).inverse();

                    return byte_record.less_than(lhs[i], rhs[i]);
                }
            }
            unreachable!()
        }
    }
}

impl<Var, const W: usize> LessThanWitness<Var, W> {
    /// Constraints for checking that is_less_than = (lhs < rhs), where the operands are assumed to be
    /// range checked little-endian unsigned integers.
    /// The `is_less_than` variable will always be boolean-checked since it a result of a lookup relation.
    /// Returns a boolean variable `is_equal = (lhs == rhs)`
    pub fn assert_is_less_than<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        is_less_than: impl Into<AB::Expr>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Expr
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_less_than = is_less_than.into();
        let is_real = is_real.into();

        let builder = &mut builder.when(is_real.clone());

        // Stores the most significant non-equal limbs
        let mut lhs_comp = AB::Expr::zero();
        let mut rhs_comp = AB::Expr::zero();

        // We start by assuming all limbs are equal.
        let mut is_equal = AB::Expr::one();

        // Iterate over the limbs in reverse order
        for i in (0..W).rev() {
            // `is_comp` indicates whether this is the most significant non-equal limb pair
            let is_comp = self.is_comp[i];
            builder.assert_bool(is_comp);

            // Select the current limbs for comparison
            lhs_comp += lhs[i].clone() * is_comp.into();
            rhs_comp += rhs[i].clone() * is_comp.into();

            // Unset the equality checking flag if this is the first non-equal limb pair
            is_equal -= is_comp.into();

            // If we have not yet encountered the non-equal limb pair, then the limbs should be equal
            builder
                .when(is_equal.clone())
                .assert_eq(lhs[i].clone(), rhs[i].clone());
        }
        // At most one limb pair is different
        builder.assert_bool(is_equal.clone());

        // Ensure the limbs used for comparison are the ones selected by `is_comp`
        builder.assert_eq(lhs_comp, self.lhs_comp_limb);
        builder.assert_eq(rhs_comp, self.rhs_comp_limb);

        // If the words are not equal, then the comparison limbs must be different,
        // so their difference must have an inverse.
        let diff_comp = self.lhs_comp_limb.into() - self.rhs_comp_limb.into();
        // Active if all the comparison flags were off
        let is_not_eq = AB::Expr::one() - is_equal.clone();
        // Is a comparison happened, the difference should be non-zero and we check the inverse.
        // Otherwise, the inverse is unconstrained and may be set to 0.
        builder.assert_eq(diff_comp * self.diff_comp_inv.into(), is_not_eq.clone());

        // Check the comparison of the `less_than` flag
        record.less_than(
            self.lhs_comp_limb,
            self.rhs_comp_limb,
            is_less_than,
            is_real,
        );

        // Return the `is_equal` flag, so we can compute `is_less_or_equal = is_less_than + is_equal.
        // If is_equal == 1, then both comparison limbs will be 0, so is_less_than will be 0
        // If is_less_than = 1, then is_equal will have been set by one of the comparison flags
        is_equal
    }
}

impl<T, const W: usize> LessThanWitness<T, W> {
    pub const fn num_requires() -> usize {
        1
    }
}

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct IsLessThan<T, const W: usize> {
    witness: LessThanWitness<T, W>,
    is_less_than: T,
}

impl<F: PrimeField, const W: usize> IsLessThan<F, W> {
    pub fn populate_less_than<U>(
        &mut self,
        lhs: &U,
        rhs: &U,
        byte_record: &mut impl ByteRecord,
    ) -> bool
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned,
    {
        let is_less_than = self.witness.populate(lhs, rhs, byte_record);
        self.is_less_than = F::from_bool(is_less_than);
        is_less_than
    }

    pub fn populate_less_than_or_equal<U>(
        &mut self,
        lhs: &U,
        rhs: &U,
        byte_record: &mut impl ByteRecord,
    ) -> bool
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned,
    {
        let is_equal = lhs == rhs;
        let is_less_than = self.populate_less_than(lhs, rhs, byte_record);
        is_less_than | is_equal
    }
}

impl<Var, const W: usize> IsLessThan<Var, W> {
    pub fn eval_less_than<AB>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Expr
    where
        AB: AirBuilder<Var = Var>,
        Var: Copy + Into<AB::Expr>,
    {
        self.witness
            .assert_is_less_than(builder, lhs, rhs, self.is_less_than, record, is_real);
        self.is_less_than.into()
    }

    pub fn eval_less_than_or_equal<AB>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Expr
    where
        AB: AirBuilder<Var = Var>,
        Var: Copy + Into<AB::Expr>,
    {
        let is_equal =
            self.witness
                .assert_is_less_than(builder, lhs, rhs, self.is_less_than, record, is_real);
        self.is_less_than.into() + is_equal
    }
}
impl<T, const W: usize> IsLessThan<T, W> {
    pub const fn num_requires() -> usize {
        1
    }
}

/// Asserts that `is_less_than = (lhs < rhs)` and returns `is_equal = (lhs == rhs)`

impl<T: Default, const W: usize> Default for LessThanWitness<T, W> {
    fn default() -> Self {
        Self {
            is_comp: array::from_fn(|_| T::default()),
            lhs_comp_limb: T::default(),
            rhs_comp_limb: T::default(),
            diff_comp_inv: T::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;

    type F = BabyBear;

    fn test_less_than<const W: usize, U: ToBytes<Bytes = [u8; W]> + Unsigned + PartialOrd>(
        lhs: U,
        rhs: U,
    ) {
        let (lhs, rhs) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };

        let record = &mut ByteRecordTester::default();

        let mut is_lt_witness = IsLessThan::<F, W>::default();
        let is_lt = is_lt_witness.populate_less_than(&lhs, &rhs, record);
        assert!(is_lt);
        let is_lt_f = is_lt_witness.eval_less_than(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(&lhs),
            Word::<F, W>::from_unsigned(&rhs),
            &mut record.passing(IsLessThan::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(is_lt_f, F::one());

        let is_lt = is_lt_witness.populate_less_than(&lhs, &rhs, record);
        assert!(is_lt);

        let is_gt = F::zero();
        let is_real = F::one();
        let is_not_real = F::zero();
        is_lt_witness.witness.assert_is_less_than(
            &mut GadgetTester::failing(),
            Word::<F, W>::from_unsigned(&lhs),
            Word::<F, W>::from_unsigned(&rhs),
            is_gt,
            &mut record.ignoring(),
            is_real,
        );

        is_lt_witness.witness.assert_is_less_than(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(&lhs),
            Word::<F, W>::from_unsigned(&rhs),
            is_gt,
            &mut record.ignoring(),
            is_not_real,
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
