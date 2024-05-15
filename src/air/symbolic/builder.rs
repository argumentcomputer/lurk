use crate::air::builder::{AirBuilderExt, LookupBuilder, Relation};
use crate::air::symbolic::expression::Expression;
use crate::air::symbolic::variable::{Entry, Variable};
use crate::air::symbolic::virtual_col::VirtualPairCol;
use crate::air::symbolic::{Interaction, SymbolicAir};
use p3_air::AirBuilder;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;

/// A builder for the lookup table interactions.
struct SymbolicAirBuilder<F: Field> {
    preprocessed: RowMajorMatrix<Variable<F>>,
    main: RowMajorMatrix<Variable<F>>,
    air: SymbolicAir<F>,
}

impl<F: Field> SymbolicAirBuilder<F> {
    #[allow(dead_code)]
    fn new(preprocessed_width: usize, main_width: usize) -> Self {
        let preprocessed_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width)
                    .map(move |column| Variable::new(Entry::Preprocessed { offset }, column))
            })
            .collect();

        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width).map(move |column| Variable::new(Entry::Main { offset }, column))
            })
            .collect();

        Self {
            preprocessed: RowMajorMatrix::new(preprocessed_values, preprocessed_width),
            main: RowMajorMatrix::new(main_values, main_width),
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

impl<F: Field> AirBuilderExt for SymbolicAirBuilder<F> {
    fn row_index(&self) -> Self::Expr {
        Expression::Identity
    }
}

impl<F: Field> LookupBuilder for SymbolicAirBuilder<F> {
    fn require<R, I>(&mut self, relation: R, is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>,
    {
        let values = relation
            .values()
            .into_iter()
            .map(|v| VirtualPairCol::from(v))
            .collect();
        let is_real = VirtualPairCol::from(is_real.into());
        self.air.requires.push(Interaction { values, is_real })
    }

    fn provide<R, I>(&mut self, relation: R, is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>,
    {
        let values = relation
            .values()
            .into_iter()
            .map(|v| VirtualPairCol::from(v))
            .collect();
        let is_real =VirtualPairCol::from(is_real.into());
        self.air.provides.push(Interaction { values, is_real })
    }
}
