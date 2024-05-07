use p3_air::AirBuilder;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{Entry, SymbolicExpression, SymbolicVariable};

use crate::{Interaction, LookupAirBuilder};

/// A builder for the lookup table interactions.
struct SymbolicBuilder<F: Field> {
    main: RowMajorMatrix<SymbolicVariable<F>>,
    constraints: Vec<SymbolicExpression<F>>,
    interactions: Vec<Interaction<SymbolicExpression<F>>>,
}

impl<F: Field> LookupAirBuilder<SymbolicExpression<F>> for SymbolicBuilder<F> {
    fn require<V: Into<SymbolicExpression<F>>, R: Into<SymbolicExpression<F>>>(
        &mut self,
        values: impl IntoIterator<Item = V>,
        is_real: R,
    ) {
        self.interactions
            .push(Interaction::required(values, is_real))
    }

    fn provide<V: Into<SymbolicExpression<F>>, M: Into<SymbolicExpression<F>>>(
        &mut self,
        values: impl IntoIterator<Item = V>,
        multiplicity: M,
    ) {
        self.interactions
            .push(Interaction::provided(values, multiplicity))
    }
}

impl<F: Field> SymbolicBuilder<F> {
    /// Creates a new `InteractionBuilder` with the given width.
    #[allow(dead_code)]
    fn new(main_width: usize) -> Self {
        let main_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..main_width)
                    .map(move |column| SymbolicVariable::new(Entry::Main { offset }, column))
            })
            .collect();

        Self {
            main: RowMajorMatrix::new(main_values, main_width),
            constraints: vec![],
            interactions: vec![],
        }
    }
}

impl<F: Field> AirBuilder for SymbolicBuilder<F> {
    type F = F;
    type Expr = SymbolicExpression<F>;
    type Var = SymbolicVariable<F>;
    type M = RowMajorMatrix<Self::Var>;

    fn main(&self) -> Self::M {
        self.main.clone()
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let constraint = x.into();
        self.constraints.push(constraint)
    }
}
