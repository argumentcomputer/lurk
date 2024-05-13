mod builder;
mod variable;
mod expression;
mod lookup;

use crate::air::builder::LairBuilder;

use p3_air::AirBuilder;
use p3_field::Field;
use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::lookup::Interaction;

#[derive( Default, Clone)]
struct SymbolicAir<F: Field> {
    constraints: Vec<Expression<F>>,
    requires: Vec<Interaction<Expression<F>>>,
    provides: Vec<Interaction<Expression<F>>>,
}

