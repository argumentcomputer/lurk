use p3_air::AirBuilder;

pub trait Relation<T> {
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
    fn values(&self) -> impl IntoIterator<Item = T>;
}

pub trait LairBuilder: AirBuilder + LookupBuilder + AirBuilderExt {}

/// Extension of [`AirBuilder`] for creating [`Pointer`]s
pub trait AirBuilderExt: AirBuilder {
    /// Returns the constant index of the current trace being proved
    /// Defaults to 0
    fn trace_index(&self) -> Self::Expr;

    /// Return a unique expression for the current row. When using a univariate PCS, this is given
    /// as the i-th root of unity, since the column it would correspond to would be the
    /// interpolations of the identity.
    fn row_index(&self) -> Self::Expr;
}

pub trait LookupBuilder: AirBuilder {
    fn provide(&mut self, relation: impl Relation<Self::Expr>) {
        self.filtered_provide(relation, None)
    }
    fn require(&mut self, relation: impl Relation<Self::Expr>) {
        self.filtered_require(relation, None)
    }

    fn filtered_provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real: Option<Self::Expr>,
    );

    fn filtered_require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real: Option<Self::Expr>,
    );
}

// TODO: This would be a nice improvement since we could call
//       `builder.when(condition).require(relation)`.
//       This requires `FilteredAirBuilder` to make `condition` public.
// impl <'a, AB: LookupBuilder> LookupBuilder for FilteredAirBuilder<'a, AB> {
//     fn provide(&mut self, relation: impl Relation<Self::Expr>) {
//         self.inner.filtered_provide(relation, Some(self.condition.clone()))
//     }
//
//     fn require(&mut self, relation: impl Relation<Self::Expr>) {
//         self.inner.filtered_require(relation, Some(self.condition.clone()))
//     }
//
//     fn filtered_provide(&mut self, _relation: impl Relation<Self::Expr>, _is_real: Option<Self::Expr>) {
//         panic!("filtered_provide should not be called after `when`")
//     }
//
//     fn filtered_require(&mut self, relation: impl Relation<Self::Expr>, is_real: Option<Self::Expr>) {
//         panic!("filtered_require should not be called after `when`")
//     }
// }
