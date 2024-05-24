use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::rc::Rc;

use crate::air::symbolic::variable::Variable;
use p3_field::{AbstractField, Field};

/// An expression over `SymbolicVariable`s.
#[derive(Clone, Debug)]
pub enum Expression<F: Field> {
    Variable(Variable<F>),
    Identity,
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
    Sub {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
    Neg {
        x: Rc<Self>,
        degree_multiple: usize,
    },
    Mul {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
}

impl<F: Field> Expression<F> {
    /// Returns the multiple of `n` (the trace length) in this expression's degree.
    pub const fn degree_multiple(&self) -> usize {
        match self {
            Expression::Variable(v) => v.degree_multiple(),
            Expression::IsFirstRow | Expression::IsLastRow => 1,
            Expression::Identity | Expression::IsTransition | Expression::Constant(_) => 0,
            Expression::Add {
                degree_multiple, ..
            }
            | Expression::Sub {
                degree_multiple, ..
            }
            | Expression::Neg {
                degree_multiple, ..
            }
            | Expression::Mul {
                degree_multiple, ..
            } => *degree_multiple,
        }
    }
}

impl<F: Field> Default for Expression<F> {
    fn default() -> Self {
        Self::Constant(F::zero())
    }
}

impl<F: Field> From<F> for Expression<F> {
    fn from(value: F) -> Self {
        Self::Constant(value)
    }
}

impl<F: Field> AbstractField for Expression<F> {
    type F = F;

    fn zero() -> Self {
        Self::Constant(F::zero())
    }
    fn one() -> Self {
        Self::Constant(F::one())
    }
    fn two() -> Self {
        Self::Constant(F::two())
    }
    fn neg_one() -> Self {
        Self::Constant(F::neg_one())
    }

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_bool(b: bool) -> Self {
        Self::Constant(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::Constant(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::Constant(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::Constant(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::Constant(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::Constant(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::Constant(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::Constant(F::from_wrapped_u64(n))
    }

    fn generator() -> Self {
        Self::Constant(F::generator())
    }
}

impl<F: Field> Add for Expression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let degree_multiple = self.degree_multiple().max(rhs.degree_multiple());
        Self::Add {
            x: Rc::new(self),
            y: Rc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Add<F> for Expression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        self + Self::from(rhs)
    }
}

impl<F: Field> AddAssign for Expression<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: Field> AddAssign<F> for Expression<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::from(rhs);
    }
}

impl<F: Field> Sum for Expression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::zero())
    }
}

impl<F: Field> Sum<F> for Expression<F> {
    fn sum<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl<F: Field> Sub for Expression<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let degree_multiple = self.degree_multiple().max(rhs.degree_multiple());
        Self::Sub {
            x: Rc::new(self),
            y: Rc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Sub<F> for Expression<F> {
    type Output = Self;

    fn sub(self, rhs: F) -> Self {
        self - Self::from(rhs)
    }
}

impl<F: Field> SubAssign for Expression<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: Field> SubAssign<F> for Expression<F> {
    fn sub_assign(&mut self, rhs: F) {
        *self -= Self::from(rhs);
    }
}

impl<F: Field> Neg for Expression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        let degree_multiple = self.degree_multiple();
        Self::Neg {
            x: Rc::new(self),
            degree_multiple,
        }
    }
}

impl<F: Field> Mul for Expression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        let degree_multiple = self.degree_multiple() + rhs.degree_multiple();
        Self::Mul {
            x: Rc::new(self),
            y: Rc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Mul<F> for Expression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
    }
}

impl<F: Field> MulAssign for Expression<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: Field> MulAssign<F> for Expression<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::from(rhs);
    }
}

impl<F: Field> Product for Expression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::one())
    }
}

impl<F: Field> Product<F> for Expression<F> {
    fn product<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
    }
}
