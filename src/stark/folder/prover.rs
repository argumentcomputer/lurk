use crate::air::builder::{
    AirBuilderExt, FilteredLookupBuilder, LairBuilder, Relation,
};
use crate::air::symbolic::Interaction;
use crate::stark::config::{StarkGenericConfig, Val};
use p3_air::{AirBuilder, ExtensionBuilder, PairBuilder};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use crate::lookup::air::eval_logup_constraints;
use crate::lookup::builder::LogupBuilder;

type FolderView<'a, F: Field> = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;

// pub fn folder_view<'a, F: Field>(matrix: &'a RowMajorMatrix< F>, index: usize) -> FolderView<'a, F> {
//
//     let i_local = index;
//     let i_next = (index + 1) % matrix.height();
//
//     let row_local: &'a [F] =  &(*matrix.row_slice(i_local));
//     let row_local = RowMajorMatrixView::<'a, F>::new_row(row_local);
//     let row_next = RowMajorMatrixView::new_row(&(*matrix.row_slice(i_next)));
//     VerticalPair::new(row_local, row_next)
// }

#[derive(Debug)]
pub struct ProverConstraintFolder<'a, SC: StarkGenericConfig> {
    pub preprocessed: FolderView<'a, Val<SC>>,
    pub main: FolderView<'a, Val<SC>>,
    pub multiplicities: FolderView<'a, SC::Challenge>,
    pub permutations: FolderView<'a, SC::Challenge>,
    pub logup_sum: SC::Challenge,
    pub logup_z_trace: SC::Challenge,
    pub logup_r: SC::Challenge,
    pub logup_gammas: Vec<SC::Challenge>,
    pub identity: Val<SC>,
    pub is_first_row: Val<SC>,
    pub is_last_row: Val<SC>,
    pub is_transition: Val<SC>,
    pub alpha: SC::Challenge,
    pub accumulator: SC::Challenge,
}

impl<'a, SC: StarkGenericConfig> ProverConstraintFolder<'a, SC> {
    fn eval_permutations(
        &mut self,
        requires: &[Interaction<Val<SC>>],
        provides: &[Interaction<Val<SC>>],
    ) {
        eval_logup_constraints(self, requires, provides)
    }
}

impl<'a, SC: StarkGenericConfig> LairBuilder for ProverConstraintFolder<'a, SC> {}

impl<'a, SC: StarkGenericConfig> LogupBuilder for ProverConstraintFolder<'a, SC> {
    type MP = FolderView<'a, SC::Challenge>;

    type RandomVar = SC::Challenge;

    fn logup_challenge_z_trace(&self) -> Self::RandomVar {
        self.logup_z_trace
    }

    fn logup_challenge_r(&self) -> Self::RandomVar {
        self.logup_r
    }

    fn logup_challenge_gammas(&self) -> &[Self::RandomVar] {
        &self.logup_gammas
    }

    fn logup_sum(&self) -> Self::ExprEF {
        self.logup_sum
    }

    fn multiplicities(&self) -> Self::MP {
        self.multiplicities
    }

    fn permutation(&self) -> Self::MP {
        self.permutations
    }
}

impl<'a, SC: StarkGenericConfig> FilteredLookupBuilder for ProverConstraintFolder<'a, SC> {
    fn filtered_require(
        &mut self,
        _relation: impl Relation<Self::Expr>,
        _is_real: Option<Self::Expr>,
    ) {
    }

    fn filtered_provide(
        &mut self,
        _relation: impl Relation<Self::Expr>,
        _is_real: Option<Self::Expr>,
    ) {
    }
}

impl<'a, SC: StarkGenericConfig> AirBuilder for ProverConstraintFolder<'a, SC> {
    type F = Val<SC>;
    type Expr = Val<SC>;
    type Var = Val<SC>;
    type M = FolderView<'a, Val<SC>>;

    fn main(&self) -> Self::M {
        self.main
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            self.is_transition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let x: Val<SC> = x.into();
        self.accumulator *= self.alpha;
        self.accumulator += x;
    }
}

impl<'a, SC: StarkGenericConfig> ExtensionBuilder for ProverConstraintFolder<'a, SC> {
    type EF = SC::Challenge;

    type ExprEF = SC::Challenge;

    type VarEF = SC::Challenge;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        let x: SC::Challenge = x.into();
        self.accumulator *= self.alpha;
        self.accumulator += x;
    }
}

impl<'a, SC: StarkGenericConfig> AirBuilderExt for ProverConstraintFolder<'a, SC> {
    fn trace_index(&self) -> Self::Expr {
        todo!()
    }

    fn row_index(&self) -> Self::Expr {
        self.identity
    }
}

impl<'a, SC: StarkGenericConfig> PairBuilder for ProverConstraintFolder<'a, SC> {
    fn preprocessed(&self) -> Self::M {
        self.preprocessed
    }
}
