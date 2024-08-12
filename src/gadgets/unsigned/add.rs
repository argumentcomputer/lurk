use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::{UncheckedWord, Word};
use itertools::{enumerate, izip};
use num_traits::ops::overflowing::{OverflowingAdd, OverflowingSub};
use num_traits::{ToBytes, Unsigned};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use sphinx_derive::AlignedBorrow;
use std::array;
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
        let builder = &mut builder.when(is_real);

        let base_inv = AB::F::from_canonical_u16(256).inverse();

        // Initialize carry[-1] = 0
        let mut carry = AB::Expr::zero();
        for (out, in1, in2) in izip!(out, lhs, rhs) {
            // We compute the overflowing sum of both limbs, adding the previous carry bit.
            //   sum[i] = in1[i] + in2[i] + carry[i-1]
            // Due to range checks, we know
            //   0 <= sum[i] <= 255 + 255 + 1 = 511,
            // since we can assume carry[i-1] is always boolean.
            let sum = in1 + in2 + carry;

            // We expect the output to equal
            //   out[i] = sum[i] % 256,
            // with quotient/remainder equation
            //   sum[i] = out[i] + carry[i] * 256.
            // The only possible value for carry[i] is 0 or 1,
            // since the right-hand side of the equation is at most 511 when carry[i] = 1.
            // We can therefore compute the carry bit as
            // carry[i] = (sum[i] - out[i])/256
            carry = (sum - out) * base_inv;

            // By constraining carry[i] to be boolean, we ensure the modular reduction was correct
            // if carry[i] = 0
            //   -> sum[i] = out[i] (since out[i] < 256, no overflow happened)
            // else
            //   -> sum[i] = out[i] + 256 (sum[i] must be >= 256, so an overflow occurred)
            builder.assert_bool(carry.clone());
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

    pub const fn witness_size() -> usize {
        size_of::<Sum<u8, W>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.result.0.clone()
    }
}

/// Wrapper type for subtraction, which contains the witness and output of the computation.
#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct Diff<T, const W: usize> {
    result: UncheckedWord<T, W>,
}

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

    pub const fn witness_size() -> usize {
        size_of::<Diff<u8, W>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.result.0.clone()
    }
}

#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct AddOne<T, const W: usize> {
    // inverses[i] = (result[i] - 256)^{-1}
    inverses: [T; W],
    result: [T; W],
}

impl<F: Field, const W: usize> AddOne<F, W> {
    pub fn populate<U>(&mut self, input: &U) -> U
    where
        U: ToBytes<Bytes = [u8; W]> + Unsigned + OverflowingAdd,
    {
        let (out, _carry) = input.overflowing_add(&U::one());
        let base = F::from_canonical_u16(256);

        for (i, out) in enumerate(out.to_le_bytes()) {
            let out = F::from_canonical_u8(out);
            // compute (out[i] - 256)^{-1} to prove out[i] != 256
            self.inverses[i] = (out - base).inverse();
            self.result[i] = out;
        }

        out
    }
}

impl<Var, const W: usize> AddOne<Var, W> {
    /// Returns a word equal to input + 1, along with a carry bit indicating whether an overflow
    /// occurred.
    ///
    /// # Detail
    /// We assume the input word is correctly range checked, and add 1 (defined as `carry[-1]`)
    /// We constrain
    ///   `output[i] + carry[i] * 256 = input[i] + carry[i-1]`
    /// Since `carry[i]` can only be boolean, the range of `output[i]` is `[0, ..., 256]`.
    /// To avoid range checks, we simply constrain `output[i] != 256` by providing an inverse.
    pub fn eval<AB>(
        &self,
        builder: &mut AB,
        input: Word<AB::Expr, W>,
        is_real: impl Into<AB::Expr>,
    ) -> (Word<AB::Var, W>, AB::Expr)
    where
        AB: AirBuilder<Var = Var>,
        Var: Copy + Into<AB::Expr>,
    {
        let builder = &mut builder.when(is_real);

        let base = AB::F::from_canonical_u16(256);
        let base_inv = base.inverse();

        // Initialize carry[-1] = 1
        let mut carry = AB::Expr::one();
        for (input, output, inverse) in izip!(input, self.result, self.inverses) {
            // We compute the overflowing sum of the limb and the previous carry bit.
            //   sum[i] = input[i] + carry[i-1]
            // Due to range checks, we know
            //   0 <= sum[i] <= 255 + 1 = 256,
            // since we can assume carry[i-1] is always boolean.
            let sum = input + carry;

            // We expect the output to equal
            //   out[i] = sum[i] % 256,
            // with quotient/remainder equation
            //   sum[i] = out[i] + carry[i] * 256.
            // We compute carry[i] from the given variables
            //   carry[i] = (sum[i] - out[i])/256,
            // and constrain carry[i] ∈ {0,1}.
            carry = (sum - output.into()) * base_inv;
            builder.assert_bool(carry.clone());

            // We can bound out[i] = sum[i] - carry[i] * 256 as follows
            // if carry[i] = 0
            //   -> out[i] = sum[i]
            //   -> out[i] ∈ [0, 255]
            // if carry[i] = 1
            //   -> out[i] = sum[i] - 256.
            // In the latter case, since sum[i] ∈ [0, 256], the same applies to out[i],
            // so need to assert that out[i] != 256.
            // We do so by showing that
            //   ∃ inverses[i] s.t. (out[i] - 256) * inverses[i] = 1
            let non_zero = output.into() - base;
            builder.assert_one(non_zero * inverse);
        }

        // We range constrain result manually by checking that none of
        // its limbs is 256
        let output = Word(self.result);
        (output, carry)
    }
}

impl<T, const W: usize> AddOne<T, W> {
    pub const fn num_requires() -> usize {
        0
    }

    pub const fn witness_size() -> usize {
        size_of::<AddOne<u8, W>>()
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = T>
    where
        T: Clone,
    {
        self.result.clone()
    }
}
impl<F: Default, const W: usize> Default for AddOne<F, W> {
    fn default() -> Self {
        Self {
            inverses: array::from_fn(|_| F::default()),
            result: array::from_fn(|_| F::default()),
        }
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
        lhs: &U,
        rhs: &U,
    ) {
        let record = &mut ByteRecordTester::default();

        let mut add_witness = Sum::<F, W>::default();
        let add = add_witness.populate(lhs, rhs, record);
        let (add_expected, _) = lhs.overflowing_add(rhs);
        assert_eq!(add, add_expected);
        let add_f = add_witness.eval(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(lhs),
            Word::<F, W>::from_unsigned(rhs),
            &mut record.passing(Sum::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(add_f, Word::from_unsigned(&add));

        let mut sub_witness = Diff::<F, W>::default();
        let sub = sub_witness.populate(lhs, rhs, record);
        let (sub_expected, _) = lhs.overflowing_sub(rhs);
        assert_eq!(sub, sub_expected);
        let sub_f = sub_witness.eval(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(lhs),
            Word::<F, W>::from_unsigned(rhs),
            &mut record.passing(Diff::<F, W>::num_requires()),
            F::one(),
        );
        assert_eq!(sub_f, Word::from_unsigned(&sub));
    }

    fn test_add_one<
        const W: usize,
        U: ToBytes<Bytes = [u8; W]> + Unsigned + OverflowingAdd + OverflowingSub + Debug,
    >(
        input: &U,
    ) {
        let mut add_one_witness = AddOne::<F, W>::default();
        let out = add_one_witness.populate(input);
        let (out_expected, carry_expected) = input.overflowing_add(&U::one());
        assert_eq!(out, out_expected);
        let (out_f, carry_f) = add_one_witness.eval(
            &mut GadgetTester::passing(),
            Word::<F, W>::from_unsigned(input),
            F::one(),
        );
        assert_eq!(out_f, Word::from_unsigned(&out));
        assert_eq!(carry_f, F::from_bool(carry_expected));
    }

    proptest! {

    #[test]
    fn test_add_sub_32(a: u32, b: u32) {
        test_add_sub(&a, &b)
    }

    #[test]
    fn test_add_sub_64(a: u64, b: u64) {
        test_add_sub(&a, &b)
    }

    #[test]
    fn test_add_one_32(a: u32) {
        test_add_one(&a)
    }

    #[test]
    fn test_add_one_64(a: u64) {
        test_add_one(&a)
    }

    }
}
