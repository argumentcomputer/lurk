mod builder;
mod expression;
mod variable;
mod virtual_col;

use crate::air::symbolic::expression::Expression;
use itertools::enumerate;
use std::iter::zip;
use std::ops::Mul;

use crate::air::symbolic::virtual_col::VirtualPairCol;
use p3_field::{AbstractExtensionField, AbstractField, Field};


#[derive(Clone)]
pub(crate) struct Interaction<F: Field> {
    pub(crate) values: Vec<VirtualPairCol<F>>,
    pub(crate) is_real: VirtualPairCol<F>,
}

impl<F: Field> Interaction<F> {
    pub fn apply<Expr, ExprEF, Var, Challenge>(
        &self,
        preprocessed: &[Var],
        main: &[Var],
        r: &Challenge,
        gamma_powers: &[Challenge],
    ) -> ExprEF
    where
        F: Into<Expr>,
        Expr: AbstractField + Mul<F, Output = Expr>,
        ExprEF: AbstractExtensionField<Expr>,
        Var: Into<Expr> + Copy,
        Challenge: Into<ExprEF> + Copy,
    {
        let mut result: ExprEF = (*r).into();

        for (i, (v_i, gamma_i)) in enumerate(zip(&self.values, gamma_powers)) {
            let gamma: ExprEF = (*gamma_i).into();
            let v: Expr = v_i.apply(preprocessed, main);
            if i == 0 {
                result += v;
            } else {
                result += gamma * v;
            }
        }
        result
    }
}

#[derive(Default, Clone)]
pub(crate) struct SymbolicAir<F: Field> {
    pub(crate) constraints: Vec<Expression<F>>,
    pub(crate) requires: Vec<Interaction<F>>,
    pub(crate) provides: Vec<Interaction<F>>,
}
