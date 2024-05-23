use p3_air::{AirBuilder, FilteredAirBuilder};
use p3_field::AbstractField;

/// Tagged tuple describing an element of a relation
///
/// # Example
/// If we have a ROM with 8 words, then we could create a relation as
///
/// ```
/// struct MemoryRelation<F: Field> {
///     addr: TracePointer<F>,
///     values: [F; 8],
/// }
/// ```
/// then the `values()` implementation would return
///  `[Expr::from_canonical_u32(MEMORY_TAG), addr.trace.into(), addr.index.into(), values.map(Into)]`
pub trait Relation<T> {
    fn values(self) -> impl IntoIterator<Item = T>;
}

/// Default implementation to allow `[AB::Var; N]` and `[AB::Expr; N]` to implement `Relation`.
impl<T, I: Into<T>, II: IntoIterator<Item = I>> Relation<T> for II {
    fn values(self) -> impl IntoIterator<Item = T> {
        self.into_iter().map(Into::into)
    }
}

pub trait LairBuilder: AirBuilder + LookupBuilder + AirBuilderExt {}

/// Extension of [`AirBuilder`] for creating [`Pointer`]s
pub trait AirBuilderExt: AirBuilder {
    /// Returns the constant index of the current trace being proved
    /// Defaults to 0
    fn trace_index(&self) -> usize;

    /// Return a unique expression for the current row. When using a univariate PCS, this is given
    /// as the i-th root of unity, since the column it would correspond to would be the
    /// interpolations of the identity.
    /// Note that arithmetic is NOT supported on row indices.
    fn row_index(&self) -> Self::Expr;
}

pub enum QueryType {
    Require,
    RequireOnce,
    Provide,
    ProvideOnce,
}

/// TODO: The `once` calls are not fully supported, and deferred to their multi-use counterparts.
pub trait LookupBuilder: AirBuilder {
    /// Generic query that to be added to the global lookup argument.
    /// Note: is_real_bool must be a boolean.
    fn query(
        &mut self,
        query_type: QueryType,
        relation: impl Relation<Self::Expr>,
        is_real_bool: Option<Self::Expr>,
    );

    /// Provide a query that can be required multiple times.
    fn provide(&mut self, relation: impl Relation<Self::Expr>) {
        self.query(QueryType::Provide, relation, None);
    }

    /// Provide a query that will be required exactly once.
    fn provide_once(&mut self, relation: impl Relation<Self::Expr>) {
        self.query(QueryType::Provide, relation, None);
    }

    /// Require a query that has been provided.
    fn require(&mut self, relation: impl Relation<Self::Expr>) {
        self.query(QueryType::Require, relation, None);
    }

    /// Require a query that has been provided for single use.
    fn require_once(&mut self, relation: impl Relation<Self::Expr>) {
        self.query(QueryType::Require, relation, None);
    }
}

impl<'a, AB: LookupBuilder> LookupBuilder for FilteredAirBuilder<'a, AB> {
    fn query(
        &mut self,
        query_type: QueryType,
        relation: impl Relation<Self::Expr>,
        is_real: Option<Self::Expr>,
    ) {
        // TODO: This requires FilteredAirBuilder.condition to be made public
        // let condition = if let Some(is_real) = is_real {
        //     is_real * self.condition.clone()
        // } else {
        //     self.condition.clone()
        // };
        let condition = is_real.unwrap_or(Self::Expr::one());
        self.inner.query(query_type, relation, Some(condition))
    }
}
