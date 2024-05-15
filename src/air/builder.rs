use crate::air::TracePointer;
use p3_air::{
    AirBuilder, FilteredAirBuilder,
};
use p3_field::AbstractField;

/// For example, if we have a ROM with 8 words, then we could create a relation as
///
/// ```
/// struct MemoryRelation<F: Field> {
///     addr: TracePointer<F>,
///     values: [F; 8],
/// }
/// ```
/// then the `values()` implementation would return
///  `[Expr::from_canonical_u32(MEMORY_TAG), addr.trace.into(), addr.index.into(), values.map(Into)]`
pub(crate) trait Relation<T> {
    fn values(&self) -> impl IntoIterator<Item = T>;
}

pub trait AirBuilderExt: AirBuilder {
    /// Returns the constant index of the current trace being proved
    /// Defaults to 0
    fn trace_index(&self) -> Self::Expr {
        Self::Expr::zero()
    }

    /// Return a unique expression for the current row. When using a univariate PCS, this is given
    /// as the i-th root of unity, since the column it would correspond to would be the
    /// interpolations of the identity.
    fn row_index(&self) -> Self::Expr;

    fn local_pointer(&self) -> TracePointer<Self::Expr> {
        TracePointer::new(self.trace_index(), self.row_index())
    }
}

pub trait LookupBuilder: AirBuilder {
    fn require<R, I>(&mut self, relation: R, is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>;
    fn provide<R, I>(&mut self, relation: R, is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>;
}

pub trait LairBuilder: AirBuilder + LookupBuilder + AirBuilderExt {}
impl<'a, AB: AirBuilderExt> AirBuilderExt for FilteredAirBuilder<'a, AB> {
    fn trace_index(&self) -> Self::Expr {
        self.inner.trace_index()
    }

    fn row_index(&self) -> Self::Expr {
        self.inner.row_index()
    }
}

impl<'a, AB: LairBuilder> LairBuilder for FilteredAirBuilder<'a, AB> {}

impl<'a, AB: LookupBuilder> LookupBuilder for FilteredAirBuilder<'a, AB> {
    fn require<R, I>(&mut self, _relation: R, _is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>,
    {
        panic!("lookups should be called without `when`")
    }
    fn provide<R, I>(&mut self, _relation: R, _is_real: I)
    where
        R: Relation<Self::Expr>,
        I: Into<Self::Expr>,
    {
        panic!("lookups should be called without `when`")
    }
}
