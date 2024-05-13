use crate::air::builder::{LairBuilder, Relation};

use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::lookup::Interaction;
use crate::air::symbolic::variable::{Entry, Variable};
use crate::air::symbolic::SymbolicAir;
use itertools::Itertools;
use p3_air::{AirBuilder, AirBuilderWithPublicValues, PairBuilder};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;

/// A builder for the lookup table interactions.
struct SymbolicAirBuilder<F: Field> {
    main: RowMajorMatrix<Variable<F>>,
    preprocessed: RowMajorMatrix<Variable<F>>,
    public_values: Vec<Variable<F>>,
    air: SymbolicAir<F>,
}

impl<F: Field> SymbolicAirBuilder<F> {
    #[allow(dead_code)]
    fn new(main_width: usize, preprocessed_width: usize, public_values_width: usize) -> Self {
        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width).map(move |column| Variable::new(Entry::Main { offset }, column))
            })
            .collect();

        let preprocessed_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width)
                    .map(move |column| Variable::new(Entry::Preprocessed { offset }, column))
            })
            .collect();

        let public_values = (0..public_values_width)
            .into_iter()
            .map(|i| Variable::new(Entry::Public, i))
            .collect_vec();

        Self {
            main: RowMajorMatrix::new(main_values, main_width),
            preprocessed: RowMajorMatrix::new(preprocessed_values, preprocessed_width),
            public_values,
            air: Default::default(),
        }
    }
}

impl<F: Field> AirBuilder for SymbolicAirBuilder<F> {
    type F = F;
    type Expr = Expression<F>;
    type Var = Variable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        Expression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        Expression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            Expression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let constraint = x.into();
        self.air.constraints.push(constraint)
    }
}
impl<F: Field> AirBuilderWithPublicValues for SymbolicAirBuilder<F> {
    type PublicVar = Variable<F>;
    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F: Field> PairBuilder for SymbolicAirBuilder<F> {
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F: Field> LairBuilder for SymbolicAirBuilder<F> {
    fn trace_index(&self) -> Self::Expr {
        // TODO: Need to modify `SymbolicExpression` to add this case
        panic!()
    }

    fn row_index(&self) -> Self::Expr {
        // TODO: Need to modify `SymbolicExpression` to add this case
        panic!()
    }
    fn require(&mut self, relation: impl Relation<Self::Expr>, is_real: impl Into<Self::Expr>) {
        let values = relation.values().into_iter().map(Into::into).collect();
        self.air.requires.push(Interaction::required(
            values,
            is_real.into(),
        ))
    }

    fn provide(&mut self, relation: impl Relation<Self::Expr>) {
        let values = relation.values().into_iter().map(Into::into).collect();
        self.air
            .provides
            .push(Interaction::provided(values))
    }
}
