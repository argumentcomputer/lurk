use crate::air::builder::{AirBuilderExt, LairBuilder, LookupBuilder, QueryType, Relation};
use p3_air::{Air, AirBuilder};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use p3_matrix::Matrix;

type LocalRowView<'a, F> = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;

pub struct Query<F> {
    query_type: QueryType,
    values: Vec<F>,
}

/// Check the `air` constraints over a given `main` trace.
pub fn debug_constraints_collecting_interactions<
    F: Field,
    A: for<'a> Air<DebugConstraintBuilder<'a, F>>,
    M: Matrix<F>,
>(
    air: &A,
    main: &M,
) -> Vec<Query<F>> {
    let height = main.height();

    (0..height)
        .flat_map(|row| {
            let row_next = (row + 1) % height;

            let main_local = &main.row_slice(row);
            let main_next = &main.row_slice(row_next);

            let main = VerticalPair::new(
                RowMajorMatrixView::new_row(main_local),
                RowMajorMatrixView::new_row(main_next),
            );

            let mut builder = DebugConstraintBuilder::new(main, row, height);

            air.eval(&mut builder);

            builder.queries
        })
        .collect()
}

/// A builder for debugging constraints.
pub struct DebugConstraintBuilder<'a, F> {
    main: LocalRowView<'a, F>,
    row: usize,
    height: usize,
    queries: Vec<Query<F>>,
}

impl<'a, F: Field> LairBuilder for DebugConstraintBuilder<'a, F> {}

impl<'a, F: Field> DebugConstraintBuilder<'a, F> {
    #[inline]
    fn new(main: LocalRowView<'a, F>, row: usize, height: usize) -> Self {
        Self {
            main,
            row,
            height,
            queries: vec![],
        }
    }

    #[inline]
    fn debug_constraint(&self, x: F, y: F) {
        if x != y {
            let backtrace = std::backtrace::Backtrace::force_capture();
            eprintln!(
                "constraint failed at row {}: {:?} != {:?}\n{}",
                self.row, x, y, backtrace
            );
            panic!();
        }
    }
}

impl<'a, F: Field> LookupBuilder for DebugConstraintBuilder<'a, F> {
    fn query(
        &mut self,
        query_type: QueryType,
        relation: impl Relation<Self::Expr>,
        is_real: Option<Self::Expr>,
    ) {
        if let Some(is_real) = is_real {
            let is_real: F = is_real.into();
            if is_real.is_zero() {
                return;
            }
        }

        let values = relation.values().into_iter().collect();
        self.queries.push(Query { query_type, values });
    }
}

impl<'a, F: Field> AirBuilderExt for DebugConstraintBuilder<'a, F> {
    fn trace_index(&self) -> Self::Expr {
        // TODO: fix
        Self::Expr::zero()
    }

    fn row_index(&self) -> Self::Expr {
        // TODO: roots of unity
        Self::Expr::from_canonical_usize(self.row)
    }
}

impl<'a, F: Field> AirBuilder for DebugConstraintBuilder<'a, F> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = LocalRowView<'a, F>;

    fn main(&self) -> Self::M {
        self.main
    }

    fn is_first_row(&self) -> Self::Expr {
        F::from_bool(self.row == 0)
    }

    fn is_last_row(&self) -> Self::Expr {
        F::from_bool(self.row == self.height - 1)
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            F::from_bool(self.row != self.height - 1)
        } else {
            panic!("only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.debug_constraint(x.into(), F::zero());
    }

    fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) {
        self.debug_constraint(x.into(), F::one());
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        self.debug_constraint(x.into(), y.into());
    }

    /// Assert that `x` is a boolean, i.e. either 0 or 1.
    fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) {
        let x = x.into();
        if x != F::zero() && x != F::one() {
            let backtrace = std::backtrace::Backtrace::force_capture();
            eprintln!(
                "constraint failed at row {}: {:?} is not a bool\n{}",
                self.row, x, backtrace
            );
            panic!();
        }
    }
}
