use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::{UncheckedWord, Word};
use itertools::{enumerate, izip};
use num_traits::{FromBytes, ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use sphinx_derive::AlignedBorrow;
use std::array;

/// Witness variables for proving the correctness of a multiplication.
/// # Warning
/// Due to the lack of range-constraints over the output, it is recommended to use
/// `Product` instead.
#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct MulWitness<T, const W: usize> {
    carry: [T; W],
}

impl<F: AbstractField, const W: usize> MulWitness<F, W> {
    /// Populates a witness for checking the multiplication of two unsigned integers
    /// representable as arrays of little-endian bytes.
    /// The result is not range-constrained, as this allows the Air to reuse this witness
    /// for operations such as division, or simply checking the result against an existing value.
    fn populate<L: ToBytes, R: ToBytes>(
        &mut self,
        lhs: &L,
        rhs: &R,
        byte_record: &mut impl ByteRecord,
    ) -> [u8; W] {
        let lhs = lhs.to_le_bytes();
        let lhs = lhs.as_ref();
        let rhs = rhs.to_le_bytes();
        let rhs = rhs.as_ref();

        // Compute products[k] = ∑_{i + j = k} lhs[i] * rhs[j]
        let mut products: [u32; W] = array::from_fn(|_| 0);
        for (i, &l) in enumerate(lhs) {
            for (j, &r) in enumerate(rhs) {
                let k = i + j;
                if k < W {
                    products[k] += u32::from(l) * u32::from(r);
                }
            }
        }

        let mut carry = 0u16;
        let mut result: [u8; W] = array::from_fn(|_| 0);
        for k in 0..W {
            let out = products[k] + u32::from(carry);

            let [limb, carry_lo, carry_hi, null] = out.to_le_bytes();
            debug_assert_eq!(null, 0);

            carry = u16::from_le_bytes([carry_lo, carry_hi]);

            byte_record.range_check_u16(carry);
            self.carry[k] = F::from_canonical_u16(carry);

            result[k] = limb;
        }

        result
    }
}

impl<Var, const W: usize> MulWitness<Var, W> {
    /// Constraints for checking that lhs * rhs = out, where the operands are assumed to be
    /// range checked little-endian unsigned integers. The result is truncated to the number
    /// of limbs of the output.
    fn assert_mul<const W_L: usize, const W_R: usize, AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W_L>,
        rhs: Word<AB::Expr, W_R>,
        out: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        let base = AB::F::from_canonical_u16(256);

        let mut products: [AB::Expr; W] = array::from_fn(|_| AB::Expr::zero());
        for (i, lhs) in enumerate(&lhs) {
            for (j, rhs) in enumerate(&rhs) {
                let k = i + j;
                if k < W {
                    products[k] += lhs.clone() * rhs.clone();
                }
            }
        }

        let mut carry_prev = AB::Expr::zero();
        for (product, carry, limb) in izip!(products, self.carry, out) {
            record.range_check_u16(carry, is_real.clone());
            let out = limb + carry.into() * base;

            builder
                .when(is_real.clone())
                .assert_eq(product + carry_prev, out);
            carry_prev = carry.into();
        }
    }
}

impl<T, const W: usize> MulWitness<T, W> {
    pub const fn num_requires() -> usize {
        W // u16 carry checks
    }
}

impl<T: Default, const W: usize> Default for MulWitness<T, W> {
    fn default() -> Self {
        Self {
            carry: array::from_fn(|_| T::default()),
        }
    }
}

/// Wrapper type for multiplication, which contains the witness and output of the computation.
#[derive(Clone, Debug, Default, AlignedBorrow)]
pub struct Product<T, const W: usize> {
    witness: MulWitness<T, W>,
    result: UncheckedWord<T, W>,
}

impl<F: AbstractField, const W: usize> Product<F, W> {
    pub fn populate<U>(&mut self, lhs: &U, rhs: &U, byte_record: &mut impl ByteRecord) -> U
    where
        U: ToBytes<Bytes = [u8; W]> + FromBytes<Bytes = [u8; W]> + Unsigned,
    {
        let out = self.witness.populate(lhs, rhs, byte_record);
        self.result.assign_bytes(&out, byte_record);
        U::from_le_bytes(&out)
    }
}

impl<Var, const W: usize> Product<Var, W> {
    pub fn eval<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: Word<AB::Expr, W>,
        rhs: Word<AB::Expr, W>,
        record: &mut impl ByteAirRecord<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) -> Word<AB::Var, W>
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        self.witness.assert_mul(
            builder,
            lhs,
            rhs,
            self.result.as_unchecked(),
            record,
            is_real.clone(),
        );
        self.result.into_checked(record, is_real.clone())
    }
}

impl<T, const W: usize> Product<T, W> {
    pub const fn num_requires() -> usize {
        MulWitness::<T, W>::num_requires() + W / 2
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use num_traits::ops::overflowing::OverflowingMul;
    use num_traits::AsPrimitive;
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;
    use std::fmt::Debug;
    use std::iter::zip;

    type F = BabyBear;

    fn test_mul<
        const W_L: usize,
        const W_R: usize,
        const W_O: usize,
        L: ToBytes<Bytes = [u8; W_L]> + Unsigned + AsPrimitive<O>,
        R: ToBytes<Bytes = [u8; W_R]> + Unsigned + AsPrimitive<O>,
        O: ToBytes<Bytes = [u8; W_O]>
            + Unsigned
            + FromBytes<Bytes = [u8; W_O]>
            + OverflowingMul
            + Debug
            + 'static
            + Copy,
    >(
        lhs: L,
        rhs: R,
    ) {
        let record = &mut ByteRecordTester::default();
        let builder = &mut GadgetTester::<F>::passing();

        let mut witness = MulWitness::<F, W_O>::default();

        let result_bytes = witness.populate(&lhs, &rhs, record);
        let result = O::from_le_bytes(&result_bytes);

        witness.assert_mul(
            builder,
            Word::<F, W_L>::from_unsigned(&lhs),
            Word::<F, W_R>::from_unsigned(&rhs),
            Word::<F, W_O>::from_unsigned(&result),
            &mut record.passing(MulWitness::<F, W_O>::num_requires()),
            F::one(),
        );
        let (expected, _) = lhs.as_().overflowing_mul(&rhs.as_());
        assert_eq!(result, expected);
    }

    fn test_product<
        const W: usize,
        U: ToBytes<Bytes = [u8; W]> + FromBytes<Bytes = [u8; W]> + Unsigned + OverflowingMul + Debug,
    >(
        lhs: U,
        rhs: U,
    ) {
        let record = &mut ByteRecordTester::default();
        let builder = &mut GadgetTester::<F>::passing();

        let mut witness = Product::<F, W>::default();

        let result: U = witness.populate(&lhs, &rhs, record);

        let lhs_f = Word::<F, W>::from_unsigned(&lhs);
        let rhs_f = Word::<F, W>::from_unsigned(&rhs);
        let result_f = witness.eval(
            builder,
            lhs_f,
            rhs_f,
            &mut record.passing(Product::<F, W>::num_requires()),
            F::one(),
        );

        let (expected, _) = lhs.overflowing_mul(&rhs);
        assert_eq!(result, expected);
        for (r, e) in zip(result_f, expected.to_le_bytes()) {
            assert_eq!(r, F::from_canonical_u8(e));
        }
    }

    proptest! {

    #[test]
    fn test_mul_all(a_u64: u64, b_u64: u64) {
        let a_u32 = u32::try_from(a_u64 >> 32).unwrap();
        let b_u32 = u32::try_from(a_u64 >> 32).unwrap();

        // u64 x u64 -> u64
        test_mul::<8, 8, 8, u64, u64, u64>(a_u64, b_u64);
        // u32 x u32 -> u64
        test_mul::<4, 4, 8, u32, u32, u64>(a_u32, b_u32);
        // u64 x u32 -> u64
        test_mul::<8, 4, 8, u64, u32, u64>(a_u64, b_u32);
        // u64 x u32 -> u32
        test_mul::<8, 4, 4, u64, u32, u32>(a_u64, b_u32);

        test_product::<8, u64>(a_u64, b_u64);
        test_product::<4, u32>(a_u32, b_u32);
    }
    }

    #[test]
    fn test_mul_special() {
        // u64 x u64 -> u64
        test_mul::<8, 8, 8, u64, u64, u64>(0, 0);
        // u32 x u32 -> u64
        test_mul::<4, 4, 8, u32, u32, u64>(0, 0);
        // u64 x u32 -> u64
        test_mul::<8, 4, 8, u64, u32, u64>(0, 0);
        // u64 x u32 -> u32
        test_mul::<8, 4, 4, u64, u32, u32>(0, 0);

        let builder = &mut GadgetTester::<F>::passing();
        let record = &mut ByteRecordTester::default();
        let empty_witness = MulWitness::<F, 8>::default();
        let zero = Word::<F, 8>::from_unsigned(&0u64);
        let one = Word::<F, 8>::from_unsigned(&1u64);
        empty_witness.assert_mul(
            builder,
            zero,
            zero,
            one,
            &mut record.passing(MulWitness::<F, 8>::num_requires()),
            F::zero(),
        );
        let product = Product::<F, 8>::default();
        product.eval(
            builder,
            zero,
            one,
            &mut record.passing(Product::<F, 8>::num_requires()),
            F::zero(),
        );
    }
}
