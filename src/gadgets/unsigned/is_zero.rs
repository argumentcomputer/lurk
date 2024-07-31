use crate::gadgets::unsigned::Word;
use itertools::enumerate;
use num_traits::{ToBytes, Zero};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use sphinx_derive::AlignedBorrow;
use std::array;
use std::iter::zip;

#[derive(Clone, Debug, AlignedBorrow)]
#[repr(C)]
pub struct IsZeroWitness<T, const W: usize> {
    inverses: [T; W],
}

impl<F: Field, const W: usize> IsZeroWitness<F, W> {
    pub fn populate_non_zero<U>(&mut self, input: &U)
    where
        U: ToBytes<Bytes = [u8; W]> + Zero,
    {
        for (i, limb) in enumerate(input.to_le_bytes()) {
            if !limb.is_zero() {
                self.inverses[i] = F::from_canonical_u8(limb).inverse();
                return;
            }
        }
        panic!("expected input to be non-zero")
    }

    pub fn populate_not_equal<U>(&mut self, lhs: &U, rhs: &U)
    where
        U: ToBytes<Bytes = [u8; W]> + PartialEq,
    {
        for (i, (lhs, rhs)) in enumerate(zip(lhs.to_le_bytes(), rhs.to_le_bytes())) {
            if lhs != rhs {
                self.inverses[i] =
                    (F::from_canonical_u8(lhs) - F::from_canonical_u8(rhs)).inverse();
                return;
            }
        }
        panic!("expected inputs to be different")
    }
}

impl<Var, const W: usize> IsZeroWitness<Var, W> {
    /// Constraints for checking that input != 0, where the operands are assumed to be
    /// range checked little-endian unsigned integers, or boolean.
    pub fn assert_non_zero<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        input: Word<AB::Expr, W>,
        is_real: impl Into<AB::Expr>,
    ) where
        Var: Copy + Into<AB::Expr>,
    {
        let builder = &mut builder.when(is_real);

        let mut lc = AB::Expr::zero();
        for (input, inverse) in zip(input, self.inverses) {
            lc += input * inverse;
        }

        // Otherwise, there exist w such that 1 = ∑ w[i]*limb[i]
        builder.assert_one(lc);
    }

    /// Constraints for checking that is_zero = (lhs == rhs), where the operands are assumed to be
    /// range checked little-endian unsigned integers, or boolean.
    pub fn assert_is_zero<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        input: &[AB::Expr; W],
        is_zero: impl Into<AB::Expr>,
        is_real: impl Into<AB::Expr>,
    ) where
        Var: Copy + Into<AB::Expr>,
    {
        let builder = &mut builder.when(is_real);
        let is_zero = is_zero.into();

        let mut lc = AB::Expr::zero();
        for (input, inverse) in zip(input, self.inverses) {
            // If is_zero, all limbs are zero
            builder.when(is_zero.clone()).assert_zero(input.clone());

            lc += input.clone() * inverse;
        }

        // Otherwise, there exist w such that 1 = ∑ w[i]*limb[i]
        let not_zero = AB::Expr::one() - is_zero;
        builder.assert_eq(lc, not_zero);
    }
}

impl<T: Default, const W: usize> Default for IsZeroWitness<T, W> {
    fn default() -> Self {
        Self {
            inverses: array::from_fn(|_| T::default()),
        }
    }
}

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct IsZeroOrEqual<T, const W: usize> {
    witness: IsZeroWitness<T, W>,
    result: T,
}

pub type IsZero<T, const W: usize> = IsZeroOrEqual<T, W>;
pub type IsEqual<T, const W: usize> = IsZeroOrEqual<T, W>;

impl<F: Field, const W: usize> IsZeroOrEqual<F, W> {
    pub fn populate_is_zero<U>(&mut self, input: &U) -> bool
    where
        U: ToBytes<Bytes = [u8; W]> + Zero,
    {
        if input.is_zero() {
            self.result = F::one();
            true
        } else {
            self.witness.populate_non_zero(input);
            false
        }
    }

    pub fn populate_is_equal<U>(&mut self, lhs: &U, rhs: &U) -> bool
    where
        U: ToBytes<Bytes = [u8; W]> + PartialEq,
    {
        if lhs == rhs {
            self.result = F::one();
            true
        } else {
            self.witness.populate_not_equal(lhs, rhs);
            false
        }
    }

    pub const fn witness_size() -> usize {
        size_of::<IsZeroOrEqual<u8, W>>()
    }

    pub const fn num_requires() -> usize {
        0
    }

    pub fn iter_result(&self) -> impl IntoIterator<Item = F>
    where
        F: Clone,
    {
        [self.result]
    }
}

impl<Var, const W: usize> IsZeroOrEqual<Var, W> {
    pub fn eval_is_zero<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        input: &Word<AB::Expr, W>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Var
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        let is_zero = self.result;
        builder.when(is_real.clone()).assert_bool(is_zero);
        self.witness
            .assert_is_zero(builder, &input.0, is_zero, is_real);
        is_zero
    }

    pub fn eval_is_equal<AB: AirBuilder<Var = Var>>(
        &self,
        builder: &mut AB,
        lhs: &Word<AB::Expr, W>,
        rhs: &Word<AB::Expr, W>,
        is_real: impl Into<AB::Expr>,
    ) -> AB::Var
    where
        Var: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        let is_equal = self.result;
        builder.when(is_real.clone()).assert_bool(is_equal);

        let input = array::from_fn(|i| lhs[i].clone() - rhs[i].clone());
        self.witness
            .assert_is_zero(builder, &input, is_equal, is_real);
        is_equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::GadgetTester;
    use num_traits::Unsigned;
    use p3_baby_bear::BabyBear;
    use proptest::prelude::*;

    type F = BabyBear;

    fn test_non_zero<const W: usize, U: ToBytes<Bytes = [u8; W]> + Unsigned>(input: &U) {
        let mut witness = IsZero::<F, W>::default();
        let is_zero = witness.populate_is_zero(input);
        assert_eq!(is_zero, input.is_zero());

        let is_zero_f = witness.eval_is_zero(
            &mut GadgetTester::passing(),
            &Word::<F, W>::from_unsigned(input),
            F::one(),
        );
        assert_eq!(is_zero_f, F::from_bool(is_zero));

        if !is_zero {
            witness.eval_is_zero(
                &mut GadgetTester::passing(),
                &Word::<F, W>::zero(),
                F::zero(),
            );
            witness.eval_is_zero(
                &mut GadgetTester::failing(),
                &Word::<F, W>::zero(),
                F::one(),
            );
        }
    }
    fn test_is_diff<const W: usize, U: ToBytes<Bytes = [u8; W]> + Unsigned>(lhs: &U, rhs: &U) {
        let mut witness = IsEqual::<F, W>::default();
        let is_equal = witness.populate_is_equal(lhs, rhs);
        assert_eq!(is_equal, lhs == rhs);

        let is_equal_f = witness.eval_is_equal(
            &mut GadgetTester::passing(),
            &Word::<F, W>::from_unsigned(lhs),
            &Word::<F, W>::from_unsigned(rhs),
            F::one(),
        );
        assert_eq!(is_equal_f, F::from_bool(is_equal));

        if !is_equal {
            witness.eval_is_equal(
                &mut GadgetTester::passing(),
                &Word::<F, W>::zero(),
                &Word::<F, W>::zero(),
                F::zero(),
            );
        }
    }

    #[test]
    fn test_is_zero() {
        let mut witness = IsZero::<F, 8>::default();
        let is_zero = witness.populate_is_zero(&0u64);
        assert!(is_zero);

        let is_zero_f = witness.eval_is_zero(
            &mut GadgetTester::passing(),
            &Word::<F, 8>::zero(),
            F::one(),
        );
        assert_eq!(is_zero_f, F::one());
    }

    proptest! {

    #[test]
    fn test_non_zero_prop(a: u64) {
        test_non_zero::<8, _>(&a);
        test_non_zero::<4, _>(&u32::try_from(a>>32).unwrap());
    }

    }
}
