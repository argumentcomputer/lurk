use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::cmp::{CompareResult, CompareWitness};
use crate::gadgets::unsigned::field::FieldToWord32;
use crate::lurk::zstore::DIGEST_SIZE;
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField32};
use sphinx_derive::AlignedBorrow;
use std::array;
use std::cmp::Ordering;
use std::iter::zip;

pub const WORD32_SIZE: usize = 4;

#[derive(Clone, Debug, AlignedBorrow)]
pub struct CommitmentCompareWitness<T> {
    is_comp: [T; DIGEST_SIZE],
    lhs_comp_limb: T,
    rhs_comp_limb: T,
    lhs_comp_word: FieldToWord32<T>,
    rhs_comp_word: FieldToWord32<T>,
    comp_witness: CompareWitness<T, WORD32_SIZE>,
    comp_diff_inv: T,
}

impl<F: PrimeField32> CommitmentCompareWitness<F> {
    pub fn populate(
        &mut self,
        lhs: &[F; DIGEST_SIZE],
        rhs: &[F; DIGEST_SIZE],
        byte_record: &mut impl ByteRecord,
    ) -> Ordering {
        // Iterate over the field elements in reverse order to find the most-significant different element
        for i in (0..DIGEST_SIZE).rev() {
            if lhs[i] != rhs[i] {
                self.is_comp[i] = F::one();
                self.lhs_comp_limb = lhs[i];
                self.rhs_comp_limb = rhs[i];
                self.comp_diff_inv = (self.lhs_comp_limb - self.rhs_comp_limb).inverse();
                let lhs_u32 = lhs[i].as_canonical_u32();
                let rhs_u32 = rhs[i].as_canonical_u32();
                self.lhs_comp_word.populate(&lhs_u32, byte_record);
                self.rhs_comp_word.populate(&rhs_u32, byte_record);
                return self.comp_witness.populate(&lhs_u32, &rhs_u32, byte_record);
            }
        }
        Ordering::Equal
    }
}

impl<Var> CommitmentCompareWitness<Var> {
    pub fn eval<AB: AirBuilder<Var = Var>>(
        &self,
        orig_builder: &mut AB,
        lhs: &[AB::Expr; DIGEST_SIZE],
        rhs: &[AB::Expr; DIGEST_SIZE],
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> CompareResult<AB::Expr>
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        let builder = &mut orig_builder.when(is_real.clone());

        // Iterate over limb pairs in reverse order, asserting they are equal until
        // we encounter a set `is_comp` flag.
        let mut is_equal = AB::Expr::one();
        for i in (0..DIGEST_SIZE).rev() {
            // `is_comp` indicates whether this is the most significant non-equal limb pair
            let is_comp = self.is_comp[i];
            builder.assert_bool(is_comp);
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
        // Stores the most significant non-equal limbs
        let select_limb = |digest: &[AB::Expr; DIGEST_SIZE]| -> AB::Expr {
            zip(digest, &self.is_comp)
                .map(|(limb, &flag)| limb.clone() * flag.into())
                .sum()
        };
        builder.assert_eq(select_limb(lhs), self.lhs_comp_limb);
        builder.assert_eq(select_limb(rhs), self.rhs_comp_limb);

        // If is_equal == 0, then we must ensure that the comparison limbs are actually different,
        // since this ensures `is_comp` actually selects the most-significant *different* bytes.
        // Otherwise, we would be able to set `is_comp[i]` to select equal limbs, which would
        // force `is_less_than = 0`.
        // Note that we could avoid this extra constraint if we just want an assertion that lhs<rhs,
        // since setting `is_less_than` as a constant equal to 1 ensures that the `lhs[i] != rhs[i]`
        let is_different = AB::Expr::one() - is_equal.clone();
        let comp_diff = self.lhs_comp_limb.into() - self.rhs_comp_limb;
        builder.assert_eq(comp_diff * self.comp_diff_inv, is_different.clone());

        // Convert the comparison limbs into their respective Word32s
        let lhs_word = self.lhs_comp_word.eval(
            orig_builder,
            &self.lhs_comp_limb.into(),
            record,
            is_real.clone(),
        );
        let rhs_word = self.rhs_comp_word.eval(
            orig_builder,
            &self.rhs_comp_limb.into(),
            record,
            is_real.clone(),
        );

        // Perform the actual comparison on each Word32 and return the result.
        let comp_result = self.comp_witness.eval(
            orig_builder,
            &lhs_word.into(),
            &rhs_word.into(),
            record,
            is_real.clone(),
        );

        // Assert that the field-element `is_equal` is equal to word-wise `comp_result.is_equal()`
        orig_builder
            .when(is_real)
            .assert_eq(is_equal.clone(), comp_result.is_equal());

        comp_result
    }
}

impl<T> CommitmentCompareWitness<T> {
    pub const fn num_requires() -> usize {
        FieldToWord32::<T>::num_requires() * 2 + CompareWitness::<T, WORD32_SIZE>::num_requires()
    }

    pub const fn witness_size() -> usize {
        size_of::<CommitmentCompareWitness<u8>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.comp_witness.iter_result()
    }
}
impl<T: Default> Default for CommitmentCompareWitness<T> {
    fn default() -> Self {
        Self {
            is_comp: array::from_fn(|_| T::default()),
            lhs_comp_limb: T::default(),
            rhs_comp_limb: T::default(),
            lhs_comp_word: Default::default(),
            rhs_comp_word: Default::default(),
            comp_witness: Default::default(),
            comp_diff_inv: T::default(),
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

    const BABYBEAR_MOD: u32 = 0x78000001;

    #[test]
    fn test_witness_size() {
        expect!["29"].assert_eq(&CommitmentCompareWitness::<u8>::witness_size().to_string());
    }

    #[test]
    fn test_num_requires() {
        expect!["7"].assert_eq(&CommitmentCompareWitness::<u8>::num_requires().to_string());
    }

    fn util_cmp(lhs: &[F; DIGEST_SIZE], rhs: &[F; DIGEST_SIZE]) -> Ordering {
        for i in (0..DIGEST_SIZE).rev() {
            if lhs[i] != rhs[i] {
                return lhs[i].cmp(&rhs[i]);
            }
        }
        Ordering::Equal
    }

    fn test_compare_inner(lhs: &[F; DIGEST_SIZE], rhs: &[F; DIGEST_SIZE]) {
        let cmp_expected = util_cmp(lhs, rhs);

        let record = &mut ByteRecordTester::default();

        let mut cmp_witness = CommitmentCompareWitness::<F>::default();
        let cmp = cmp_witness.populate(lhs, rhs, record);
        assert_eq!(cmp, cmp_expected);
        let cmp_f = cmp_witness.eval(
            &mut GadgetTester::passing(),
            lhs,
            rhs,
            &mut record.passing(CommitmentCompareWitness::<F>::num_requires()),
            F::one(),
        );
        match cmp {
            Ordering::Less => {
                assert_eq!(cmp_f.is_less_than(), F::one());
                assert_eq!(cmp_f.is_equal(), F::zero());
            }
            Ordering::Equal => {
                assert_eq!(cmp_f.is_less_than(), F::zero());
                assert_eq!(cmp_f.is_equal(), F::one());
            }
            Ordering::Greater => {
                assert_eq!(cmp_f.is_less_than(), F::zero());
                assert_eq!(cmp_f.is_equal(), F::zero());
            }
        }
    }

    proptest! {

    #[test]
    fn test_compare(
        lhs: [u32; DIGEST_SIZE],
        rhs: [u32; DIGEST_SIZE],
    ) {
        let lhs = lhs.map(F::from_canonical_u32);
        let rhs = rhs.map(F::from_canonical_u32);
        test_compare_inner(&lhs, &rhs);
    }

    }
}
