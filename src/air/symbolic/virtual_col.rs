use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::variable::Entry;
use itertools::chain;
use p3_field::{AbstractField, Field};
use std::ops::Mul;
use std::rc::Rc;

/// An affine function over columns in a PAIR.
#[derive(Clone, Debug)]
pub struct VirtualPairCol<F: Field> {
    column_weights: Vec<(PairCol, F)>,
    constant: F,
}

// TODO: Replace with `TryFrom`
impl<F: Field> From<Expression<F>> for VirtualPairCol<F> {
    fn from(value: Expression<F>) -> Self {
        assert!(value.degree_multiple() <= 1);
        match value {
            Expression::Variable(v) => {
                let col = match v.entry {
                    Entry::Preprocessed { offset: 0 } => PairCol::Preprocessed(v.index),
                    Entry::Main { offset: 0 } => PairCol::Main(v.index),
                    _ => panic!(),
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
                let (x, y) = (Rc::unwrap_or_clone(x), Rc::unwrap_or_clone(y));
                let Self {
                    column_weights: cols_l,
                    constant: c_l,
                } = x.into();
                let Self {
                    column_weights: cols_r,
                    constant: c_r,
                } = y.into();

                let column_weights = chain(cols_l, cols_r).collect();
                let constant = c_l + c_r;
                Self {
                    column_weights,
                    constant,
                }
            }
            Expression::Sub { x, y, .. } => {
                let (x, y) = (Rc::unwrap_or_clone(x), Rc::unwrap_or_clone(y));
                let Self {
                    column_weights: cols_l,
                    constant: c_l,
                } = x.into();
                let Self {
                    column_weights: cols_r,
                    constant: c_r,
                } = y.into();

                let neg_cols_r = cols_r.into_iter().map(|(c, w)| (c, -w));

                Self {
                    column_weights: chain(cols_l, neg_cols_r).collect(),
                    constant: c_l - c_r,
                }
            }
            Expression::Neg { x, .. } => {
                let x = Rc::unwrap_or_clone(x);
                let Self {
                    column_weights: cols,
                    constant: c,
                } = x.into();

                let neg_cols = cols.into_iter().map(|(c, w)| (c, -w));
                Self {
                    column_weights: neg_cols.collect(),
                    constant: -c,
                }
            }

            Expression::Mul { x, y, .. } => {
                let (x, y) = (Rc::unwrap_or_clone(x), Rc::unwrap_or_clone(y));
                let Self {
                    column_weights: cols_l,
                    constant: c_l,
                } = x.into();
                let Self {
                    column_weights: cols_r,
                    constant: c_r,
                } = y.into();

                assert!(
                    !(!cols_l.is_empty() && !cols_r.is_empty()),
                    "Not an affine expression"
                );

                let cols_l_c_r = cols_l.into_iter().map(|(c, w)| (c, w * c_r));
                let cols_r_c_l = cols_r.into_iter().map(|(c, w)| (c, w * c_l));

                Self {
                    column_weights: chain(cols_l_c_r, cols_r_c_l).collect(),
                    constant: c_l * c_r,
                }
            }
            Expression::Identity
            | Expression::IsFirstRow
            | Expression::IsLastRow
            | Expression::IsTransition => {
                panic!()
            }
        }
    }
}

/// A column in a PAIR, i.e. either a preprocessed column or a main trace column.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum PairCol {
    Preprocessed(usize),
    Main(usize),
}

impl PairCol {
    pub const fn get<T: Copy>(&self, preprocessed: &[T], main: &[T]) -> T {
        match self {
            PairCol::Preprocessed(i) => preprocessed[*i],
            PairCol::Main(i) => main[*i],
        }
    }
}

impl<F: Field> VirtualPairCol<F> {
    pub fn apply<Expr, Var>(&self, preprocessed: &[Var], main: &[Var]) -> Expr
    where
        F: Into<Expr>,
        Expr: AbstractField + Mul<F, Output = Expr>,
        Var: Into<Expr> + Copy,
    {
        let mut result = self.constant.into();
        for (column, weight) in self.column_weights.iter() {
            result += column.get(preprocessed, main).into() * *weight;
        }
        result
    }
}
