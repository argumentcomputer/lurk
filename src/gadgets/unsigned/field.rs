use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField32};
use sphinx_derive::AlignedBorrow;

use super::{UncheckedWord, Word32, WORD32_SIZE};

const BABYBEAR_MSB: u8 = 0x78;
const BABYBEAR_MOD: u32 = 0x78000001;

/// Witness variables for proving the equality between a field element and a u32
///
/// This implementation assumes BabyBear and is not generic over the base field
#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct FieldWitness<T> {
    is_msb_less_than: T,
}

impl<F: PrimeField32> FieldWitness<F> {
    pub fn populate<U>(&mut self, field: &U, byte_record: &mut impl ByteRecord) -> [u8; WORD32_SIZE]
    where
        U: ToBytes<Bytes = [u8; WORD32_SIZE]> + Unsigned + Ord,
    {
        let word_bytes = field.to_le_bytes();
        let word_u32 = u32::from_le_bytes(word_bytes);
        assert!(word_u32 < BABYBEAR_MOD, "Field element too large");

        let is_less_than = byte_record.less_than(word_bytes[WORD32_SIZE - 1], BABYBEAR_MSB);
        self.is_msb_less_than = F::from_bool(is_less_than);

        word_bytes
    }
}

impl<Var> FieldWitness<Var> {
    fn assert_eq<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        word: &Word32<AB::Expr>,
        field: &AB::Expr,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        let base = AB::F::from_canonical_u32(256);
        let babybear_msb = AB::F::from_canonical_u8(BABYBEAR_MSB);

        builder
            .when(is_real.clone())
            .assert_bool(self.is_msb_less_than);

        let mut recomposed_word = AB::Expr::zero();

        for i in (0..WORD32_SIZE).rev() {
            let limb = word[i].clone();
            recomposed_word = recomposed_word * base + limb;
        }

        builder
            .when(is_real.clone())
            .assert_eq(field.clone(), recomposed_word);

        // either the MSB is less than the BabyBear MSB
        record.less_than(
            word[WORD32_SIZE - 1].clone(),
            babybear_msb,
            self.is_msb_less_than,
            is_real.clone(),
        );

        // otherwise, the MSBs must be equal and every other byte must be zero
        let mut builder_when_eq =
            builder.when(is_real.clone() * (AB::Expr::one() - self.is_msb_less_than));

        builder_when_eq.assert_eq(word[WORD32_SIZE - 1].clone(), babybear_msb);
        for i in 0..(WORD32_SIZE - 1) {
            builder_when_eq.assert_eq(word[i].clone(), AB::Expr::zero());
        }
    }
}

impl<T> FieldWitness<T> {
    pub const fn num_requires() -> usize {
        1
    }

    pub const fn witness_size() -> usize {
        size_of::<FieldWitness<u8>>()
    }
}

impl<T: Default> Default for FieldWitness<T> {
    fn default() -> Self {
        Self {
            is_msb_less_than: Default::default(),
        }
    }
}

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct FieldToWord32<T> {
    witness: FieldWitness<T>,
    result: UncheckedWord<T, WORD32_SIZE>,
}

impl<F: PrimeField32> FieldToWord32<F> {
    pub fn populate<U>(&mut self, field: &U, byte_record: &mut impl ByteRecord)
    where
        U: ToBytes<Bytes = [u8; WORD32_SIZE]> + Unsigned + Ord,
    {
        let out = self.witness.populate(field, byte_record);
        self.result.assign_bytes(&out, byte_record);
    }
}

impl<Var> FieldToWord32<Var> {
    pub fn eval<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        field: &AB::Expr,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> Word32<AB::Var>
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        self.witness.assert_eq(
            builder,
            &self.result.into_unchecked().into(),
            field,
            record,
            is_real.clone(),
        );
        self.result.into_checked(record, is_real.clone())
    }
}

impl<T> FieldToWord32<T> {
    pub const fn num_requires() -> usize {
        FieldWitness::<T>::num_requires() + WORD32_SIZE / 2
    }

    pub const fn witness_size() -> usize {
        size_of::<FieldToWord32<u8>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.result.0.clone()
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
        expect!["1"].assert_eq(&FieldWitness::<u8>::witness_size().to_string());
        expect!["5"].assert_eq(&FieldToWord32::<u8>::witness_size().to_string());
    }

    #[test]
    fn test_num_requires() {
        expect!["1"].assert_eq(&FieldWitness::<u8>::num_requires().to_string());
        expect!["3"].assert_eq(&FieldToWord32::<u8>::num_requires().to_string());
    }

    fn test_field_inner(val_u32: u32) {
        let record = &mut ByteRecordTester::default();
        let mut witness = FieldWitness::<F>::default();
        let result_bytes = witness.populate(&val_u32, record);

        let result_u32 = u32::from_le_bytes(result_bytes);
        assert_eq!(val_u32, result_u32);
        let result = result_bytes.into_iter().map(F::from_canonical_u8).collect();
        let expected = Word32::from_unsigned(&val_u32);
        assert_eq!(result, expected);
        let val = F::from_canonical_u32(val_u32);

        let builder = &mut GadgetTester::<F>::passing();
        witness.assert_eq(
            builder,
            &result,
            &val,
            &mut record.passing(FieldWitness::<F>::num_requires()),
            F::one(),
        );

        let record = &mut ByteRecordTester::default();
        let mut full_witness = FieldToWord32::<F>::default();
        full_witness.populate(&val_u32, record);

        let builder = &mut GadgetTester::<F>::passing();
        let full_result = full_witness.eval(
            builder,
            &val,
            &mut record.passing(FieldToWord32::<F>::num_requires()),
            F::one(),
        );
        assert_eq!(full_result, result);
    }

    #[test]
    fn test_field_special() {
        test_field_inner(0);
        test_field_inner(BABYBEAR_MOD - 1);
    }

    proptest! {

    #[test]
    fn test_field_passing(val_u32 in 0u32..BABYBEAR_MOD) {
        test_field_inner(val_u32);
    }

    }
}
