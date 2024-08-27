use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;
use std::array;
use std::cmp::Ordering;
use std::iter::zip;

#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct CompareWitness<T, const W: usize> {
    is_comp: [T; W],
    lhs_comp_limb: T,
    rhs_comp_limb: T,
    comp_diff_inv: T,
    is_less_than: T,
}

impl<F: PrimeField, const W: usize> CompareWitness<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord) -> Ordering
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + Ord,
    {
        let lhs = lhs.to_le_bytes();
        let rhs = rhs.to_le_bytes();
        // Iterate over limbs in reverse order to find the most-significant different byte8
        for i in (0..W).rev() {
            // Stop at first unequal limb
            if lhs[i] != rhs[i] {
                self.is_comp[i] = F::one();
                self.lhs_comp_limb = F::from_canonical_u8(lhs[i]);
                self.rhs_comp_limb = F::from_canonical_u8(rhs[i]);
                self.comp_diff_inv = (self.lhs_comp_limb - self.rhs_comp_limb).inverse();

                let is_less_than = byte_record.less_than(lhs[i], rhs[i]);
                self.is_less_than = F::from_bool(is_less_than);

                return lhs[i].cmp(&rhs[i]);
            }
        }
        byte_record.less_than(0, 0);
        Ordering::Equal
    }
}

impl<Var, const W: usize> CompareWitness<Var, W> {
    pub fn eval<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: &Word<AB::Expr, W>,
        rhs: &Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> CompareResult<AB::Expr>
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        let builder = &mut builder.when(is_real.clone());

        // Iterate over limb pairs in reverse order, asserting they are equal until
        // we encounter a set `is_comp` flag.
        let mut is_equal = AB::Expr::one();
        for i in (0..W).rev() {
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
        let select_limb = |word: &Word<AB::Expr, W>| -> AB::Expr {
            zip(word, &self.is_comp)
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

        record.less_than(
            self.lhs_comp_limb,
            self.rhs_comp_limb,
            self.is_less_than,
            is_real,
        );

        let is_less_than = self.is_less_than.into();
        // The sum `is_equal + is_less_than` is boolean (both flags cannot both be 1) because
        // if is_less_than == 1
        //   -> lhs_comp_limb < lhs_comp_limb
        //   -> (lhs_comp_limb, lhs_comp_limb) != (0, 0)
        //   -> ∃! i s.t. is_comp[i] = 1
        //   -> is_equal == 0
        // if is_equal == 1
        //   -> ∀i is_comp[i] = 0
        //   -> ∀i lhs[i] == rhs[i]
        //   -> {lhs, rhs}_comp_limb == 0
        //   -> is_less_than == 0
        CompareResult {
            is_less_than,
            is_equal,
        }
    }
}

impl<T, const W: usize> CompareWitness<T, W> {
    pub const fn num_requires() -> usize {
        1
    }

    pub const fn witness_size() -> usize {
        size_of::<CompareWitness<u8, W>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        [self.is_less_than.clone()]
    }
}
impl<T: Default, const W: usize> Default for CompareWitness<T, W> {
    fn default() -> Self {
        Self {
            is_comp: array::from_fn(|_| T::default()),
            lhs_comp_limb: T::default(),
            rhs_comp_limb: T::default(),
            comp_diff_inv: T::default(),
            is_less_than: T::default(),
        }
    }
}

pub struct CompareResult<E: AbstractField> {
    is_less_than: E,
    is_equal: E,
}

impl<E: AbstractField> CompareResult<E> {
    pub fn is_less_than(&self) -> E {
        self.is_less_than.clone()
    }

    pub fn is_equal(&self) -> E {
        self.is_equal.clone()
    }

    pub fn is_less_than_or_equal(&self) -> E {
        self.is_less_than() + self.is_equal()
    }

    pub fn is_greater_than(&self) -> E {
        E::one() - self.is_less_than_or_equal()
    }

    pub fn is_greater_than_or_equal(&self) -> E {
        E::one() - self.is_less_than()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;

    type F = BabyBear;

    fn test_compare<const W: usize, U: ToBytes<Bytes = [u8; W]> + Unsigned + Ord>(
        lhs: &U,
        rhs: &U,
    ) {
        let cmp_expected = lhs.cmp(rhs);

        let record = &mut ByteRecordTester::default();

        let mut cmp_witness = CompareWitness::<F, W>::default();
        let cmp = cmp_witness.populate(lhs, rhs, record);
        assert_eq!(cmp, cmp_expected);
        let cmp_f = cmp_witness.eval(
            &mut GadgetTester::passing(),
            &Word::<F, W>::from_unsigned(lhs),
            &Word::<F, W>::from_unsigned(rhs),
            &mut record.passing(CompareWitness::<F, W>::num_requires()),
            F::one(),
        );
        match cmp {
            Ordering::Less => {
                assert_eq!(cmp_f.is_less_than, F::one());
                assert_eq!(cmp_f.is_equal, F::zero());
            }
            Ordering::Equal => {
                assert_eq!(cmp_f.is_less_than, F::zero());
                assert_eq!(cmp_f.is_equal, F::one());
            }
            Ordering::Greater => {
                assert_eq!(cmp_f.is_less_than, F::zero());
                assert_eq!(cmp_f.is_equal, F::zero());
            }
        }
    }

    proptest! {

    #[test]
    fn test_compare_32(a: u32, b: u32) {
        test_compare::<4, _>(&a, &b);
    }

    #[test]
    fn test_compare_64(a: u64, b: u64) {
        test_compare::<8, _>(&a, &b);
    }

    }
}
