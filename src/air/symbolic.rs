mod builder;
mod expression;
mod variable;
mod virtual_col;

use crate::air::symbolic::builder::SymbolicAirBuilder;
use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::virtual_col::PairColLC;
use p3_air::Air;
use p3_field::Field;

#[derive(Clone)]
pub struct Interaction<F: Field> {
    pub(crate) values: Vec<PairColLC<F>>,
    pub(crate) is_real: Option<PairColLC<F>>,
}

impl<F: Field> Interaction<F> {
    pub fn num_entries(&self) -> usize {
        self.values.len()
    }
}

#[derive(Default, Clone)]
pub struct SymbolicAir<F: Field> {
    pub constraints: Vec<Expression<F>>,
    pub requires: Vec<Interaction<F>>,
    pub provides: Vec<Interaction<F>>,
}

impl<F: Field> SymbolicAir<F> {
    pub fn new<A: Air<SymbolicAirBuilder<F>>>(
        air: &A,
        num_public_values: usize,
        preprocessed_width: usize,
        main_width: usize,
    ) -> Self {
        let mut builder = SymbolicAirBuilder::new(num_public_values, preprocessed_width, main_width);
        air.eval(&mut builder);
        builder.air
    }
}
