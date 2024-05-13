use crate::air::TracePointer;
use p3_air::{AirBuilder, FilteredAirBuilder};

// TODO: Do we want to make `require` and `provide` take a Relation?
pub(crate) trait Relation<T> {
    // fn tag?
    fn values(&self) -> impl IntoIterator<Item = T>;
}

pub trait LairBuilder: AirBuilder {
    fn trace_index(&self) -> Self::Expr;

    fn row_index(&self) -> Self::Expr;

    fn local_pointer(&self) -> TracePointer<Self::Expr> {
        TracePointer::new(self.trace_index(), self.row_index())
    }

    fn require(&mut self, relation: impl Relation<Self::Expr>, is_real: impl Into<Self::Expr>);
    fn provide(&mut self, relation: impl Relation<Self::Expr>);
}

impl<'a,  AB: LairBuilder> LairBuilder for FilteredAirBuilder<'a, AB> {
    fn trace_index(&self) -> Self::Expr {
        self.inner.trace_index()
    }

    fn row_index(&self) -> Self::Expr {
        self.inner.row_index()
    }

    fn require(&mut self, relation: impl Relation<Self::Expr>, is_real: impl Into<Self::Expr>) {
        self.inner.require(relation, is_real)
    }
    fn provide(&mut self, relation: impl Relation<Self::Expr>) {
        self.inner.provide(relation)
    }
}
