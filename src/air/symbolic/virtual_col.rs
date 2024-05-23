use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::variable::Entry;
use p3_field::{AbstractField, Field};
use std::fmt::Debug;
use std::ops::{Add, Mul, Neg, Sub};
use std::rc::Rc;

/// An affine function over columns in a PAIR.
#[derive(Clone, Debug, PartialEq)]
pub struct PairColLC<F: Field> {
    column_weights: Vec<(PairCol, F)>,
    constant: F,
}

#[derive(Debug)]
pub enum Error {
    NotAffine,
    ContainsSelector,
    ScaledIdentity,
}

impl<F: Field> TryFrom<Expression<F>> for PairColLC<F> {
    type Error = Error;

    fn try_from(value: Expression<F>) -> Result<Self, Self::Error> {
        let lc = match value {
            Expression::Variable(v) => {
                let col = match v.entry {
                    Entry::Preprocessed { offset: 0 } => PairCol::Preprocessed(v.index),
                    Entry::Main { offset: 0 } => PairCol::Main(v.index),
                    _ => return Err(Error::NotAffine),
                };
                Self {
                    column_weights: vec![(col, F::one())],
                    constant: F::zero(),
                }
            }
            Expression::Constant(c) => Self {
                column_weights: vec![],
                constant: c,
            },
            Expression::Add { x, y, .. } => {
                let x: Self = Rc::unwrap_or_clone(x).try_into()?;
                let y: Self = Rc::unwrap_or_clone(y).try_into()?;
                x + y
            }
            Expression::Sub { x, y, .. } => {
                let x: Self = Rc::unwrap_or_clone(x).try_into()?;
                let y: Self = Rc::unwrap_or_clone(y).try_into()?;
                x - y
            }
            Expression::Neg { x, .. } => {
                let x: Self = Rc::unwrap_or_clone(x).try_into()?;
                -x
            }

            Expression::Mul { x, y, .. } => {
                let x: Self = Rc::unwrap_or_clone(x).try_into()?;
                let y: Self = Rc::unwrap_or_clone(y).try_into()?;

                match (x.column_weights.len(), y.column_weights.len()) {
                    (0, _) => y * x.constant,
                    (_, 0) => x * y.constant,
                    // "Can only construct PairColLC from affine expressions"
                    (_, _) => {
                        return Err(Error::NotAffine);
                    }
                }
            }
            Expression::Identity => Self {
                column_weights: vec![(PairCol::Identity, F::one())],
                constant: F::zero(),
            },
            Expression::IsFirstRow | Expression::IsLastRow | Expression::IsTransition => {
                return Err(Error::ContainsSelector)
            }
        };

        lc.simplify()
    }
}

/// A column in a PAIR, i.e. either a preprocessed column or a main trace column.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum PairCol {
    Identity,
    Preprocessed(usize),
    Main(usize),
}

impl PairCol {
    pub fn get<E: Clone, V: Copy + Into<E>>(
        &self,
        identity: &E,
        preprocessed: &[V],
        main: &[V],
    ) -> E {
        match self {
            // TODO: Fix
            PairCol::Identity => identity.clone(),
            PairCol::Preprocessed(i) => preprocessed[*i].into(),
            PairCol::Main(i) => main[*i].into(),
        }
    }
}

impl<F: Field> PairColLC<F> {
    fn simplify(mut self) -> Result<Self, Error> {
        self.column_weights.retain(|(_, w)| !w.is_zero());
        self.column_weights.sort_by(|(c1, _), (c2, _)| c1.cmp(c2));

        if self
            .column_weights
            .iter()
            .find(|(c, w)| matches!(c, PairCol::Identity) && !w.is_one())
            .is_some()
        {
            Err(Error::ScaledIdentity)
        } else {
            Ok(self)
        }
    }

    // TODO: Handle PairCol::Identity
    pub fn apply<Expr, Var>(&self, identity: &Expr, preprocessed: &[Var], main: &[Var]) -> Expr
    where
        F: Into<Expr>,
        Expr: AbstractField + Mul<F, Output = Expr>,
        Var: Into<Expr> + Copy,
    {
        let mut result = self.constant.into();
        for (column, weight) in self.column_weights.iter() {
            result += column.get(identity, preprocessed, main) * weight.clone();
        }
        result
    }
}

impl<F: Field> Add for PairColLC<F> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        for (c_r, w_r) in rhs.column_weights {
            if let Some((_, w_l)) = self.column_weights.iter_mut().find(|(c_l, _)| *c_l == c_r) {
                *w_l += w_r
            } else {
                self.column_weights.push((c_r, w_r))
            }
        }
        self.constant += rhs.constant;
        self
    }
}

impl<F: Field> Neg for PairColLC<F> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        self.column_weights.iter_mut().for_each(|(_, w)| {
            *w = -*w;
        });
        self.constant = -self.constant;
        self
    }
}

impl<F: Field> Sub for PairColLC<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl<F: Field> Mul<F> for PairColLC<F> {
    type Output = Self;

    fn mul(mut self, rhs: F) -> Self::Output {
        self.column_weights.iter_mut().for_each(|(_, w)| {
            *w *= rhs;
        });
        self.constant *= rhs;
        self
    }
}
