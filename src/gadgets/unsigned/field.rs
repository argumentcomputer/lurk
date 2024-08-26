use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField32};
use sphinx_derive::AlignedBorrow;

use super::Word32;

const W: usize = 4;
const BABYBEAR_MSB: u8 = 0x78;

/// Witness variables for proving the equality between a field element and a u32
///
/// This implementation assumes BabyBear and is not generic over the base field
#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct FieldWitness<T> {
    is_msb_less_than: T,
}

impl<F: PrimeField32> FieldWitness<F> {
    pub fn populate<U>(&mut self, field: &U, byte_record: &mut impl ByteRecord) -> Word32<F>
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + Ord + std::fmt::Debug,
    {
        // TODO: assert that field fits in babybear -- constraints fail even without the assert however

        let word = Word32::from_unsigned(field);
        let word_bytes = field.to_le_bytes();

        let is_less_than = byte_record.less_than(word_bytes[W - 1], BABYBEAR_MSB);
        self.is_msb_less_than = F::from_bool(is_less_than);

        word
    }

    pub fn populate_uint<U>(&mut self, _uint: &Word32<F>, _byte_record: &mut impl ByteRecord) -> F
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned,
    {
        todo!()
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

        for i in (0..W).rev() {
            let limb = word[i].clone();
            recomposed_word = recomposed_word * base + limb;
        }

        builder
            .when(is_real.clone())
            .assert_eq(field.clone(), recomposed_word);

        // either the MSB is less than the BabyBear MSB
        record.less_than(
            word[W - 1].clone(),
            babybear_msb,
            self.is_msb_less_than,
            is_real.clone(),
        );

        // otherwise, the MSBs must be equal and every other byte must be zero
        let mut builder_when_eq =
            builder.when(is_real.clone() * (AB::Expr::one() - self.is_msb_less_than));

        builder_when_eq.assert_eq(word[W - 1].clone(), babybear_msb);
        for i in 0..(W - 1) {
            builder_when_eq.assert_eq(word[i].clone(), AB::Expr::zero());
        }

        // TODO: range check the word?
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
        expect!["1"].assert_eq(&FieldWitness::<u8>::witness_size().to_string());
    }

    #[test]
    fn test_num_requires() {
        expect!["1"].assert_eq(&FieldWitness::<u8>::witness_size().to_string());
    }

    fn test_field_inner(val_u32: u32, should_fail: bool) {
        // FIXME: why is this not failing for n > BABYBEAR_MOD
        let record = &mut ByteRecordTester::default();
        let builder = if should_fail {
            &mut GadgetTester::<F>::failing()
        } else {
            &mut GadgetTester::<F>::passing()
        };

        let mut witness = FieldWitness::<F>::default();

        let result: Word32<F> = witness.populate(&val_u32, record);
        let val = F::from_canonical_u32(val_u32);

        witness.assert_eq(
            builder,
            &result,
            &val,
            &mut record.passing(FieldWitness::<F>::num_requires()),
            F::one(),
        );

        let expected = Word32::from_unsigned(&val_u32);

        assert_eq!(result, expected);
    }

    #[test]
    fn test_field_special() {
        test_field_inner(0, false);
        test_field_inner(BABYBEAR_MOD - 1, false);
        test_field_inner(BABYBEAR_MOD, true);
        test_field_inner(BABYBEAR_MOD + 1, true);
        test_field_inner(u32::MAX, true);
    }

    proptest! {

    #[test]
    fn test_field_passing(val_u32 in 0u32..BABYBEAR_MOD) {
        test_field_inner(val_u32, false);
    }

    #[test]
    fn test_field_failing(val_u32 in BABYBEAR_MOD..u32::MAX) {
        test_field_inner(val_u32, true);
    }

    }
}
