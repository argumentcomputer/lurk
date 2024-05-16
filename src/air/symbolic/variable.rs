use core::marker::PhantomData;
use core::ops::{Add, Mul, Sub};

use crate::air::symbolic::expression::Expression;
use p3_field::Field;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Entry {
    Preprocessed { offset: usize },
    Main { offset: usize },
    Permutation { offset: usize },
    Public,
    Challenge,
}

/// A variable within the evaluation window, i.e. a column in either the local or next row.
#[derive(Copy, Clone, Debug)]
pub struct Variable<F: Field> {
    pub entry: Entry,
    pub index: usize,
    _phantom: PhantomData<F>,
}

impl<F: Field> Variable<F> {
    pub const fn new(entry: Entry, index: usize) -> Self {
        Self {
            entry,
            index,
            _phantom: PhantomData,
        }
    }

    pub const fn degree_multiple(&self) -> usize {
        match self.entry {
            Entry::Preprocessed { .. } | Entry::Main { .. } | Entry::Permutation { .. } => 1,
            Entry::Public | Entry::Challenge => 0,
        }
    }
}

impl<F: Field> From<Variable<F>> for Expression<F> {
    fn from(value: Variable<F>) -> Self {
        Expression::Variable(value)
    }
}

impl<F: Field> Add for Variable<F> {
    type Output = Expression<F>;

    fn add(self, rhs: Self) -> Self::Output {
        Expression::from(self) + Expression::from(rhs)
    }
}

impl<F: Field> Add<F> for Variable<F> {
    type Output = Expression<F>;

    fn add(self, rhs: F) -> Self::Output {
        Expression::from(self) + Expression::from(rhs)
    }
}

impl<F: Field> Add<Expression<F>> for Variable<F> {
    type Output = Expression<F>;

    fn add(self, rhs: Expression<F>) -> Self::Output {
        Expression::from(self) + rhs
    }
}

impl<F: Field> Add<Variable<F>> for Expression<F> {
    type Output = Self;

    fn add(self, rhs: Variable<F>) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: Field> Sub for Variable<F> {
    type Output = Expression<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        Expression::from(self) - Expression::from(rhs)
    }
}

impl<F: Field> Sub<F> for Variable<F> {
    type Output = Expression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        Expression::from(self) - Expression::from(rhs)
    }
}

impl<F: Field> Sub<Expression<F>> for Variable<F> {
    type Output = Expression<F>;

    fn sub(self, rhs: Expression<F>) -> Self::Output {
        Expression::from(self) - rhs
    }
}

impl<F: Field> Sub<Variable<F>> for Expression<F> {
    type Output = Self;

    fn sub(self, rhs: Variable<F>) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: Field> Mul for Variable<F> {
    type Output = Expression<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        Expression::from(self) * Expression::from(rhs)
    }
}

impl<F: Field> Mul<F> for Variable<F> {
    type Output = Expression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        Expression::from(self) * Expression::from(rhs)
    }
}

impl<F: Field> Mul<Expression<F>> for Variable<F> {
    type Output = Expression<F>;

    fn mul(self, rhs: Expression<F>) -> Self::Output {
        Expression::from(self) * rhs
    }
}

impl<F: Field> Mul<Variable<F>> for Expression<F> {
    type Output = Self;

    fn mul(self, rhs: Variable<F>) -> Self::Output {
        self * Self::from(rhs)
    }
}
