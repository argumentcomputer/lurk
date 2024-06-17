use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use sphinx_core::air::{AirInteraction, MessageBuilder};
use sphinx_core::lookup::InteractionKind;

/// Tagged tuple describing an element of a relation
///
/// # Example
/// If we have a ROM with 8 words, then we could create a relation as
///
/// struct MemoryRelation<F: Field> {
///     addr: TracePointer<F>,
///     values: [F; 8],
/// }
///
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

pub trait LairBuilder: AirBuilder + LookupBuilder + AirBuilderWithPublicValues {}

pub enum QueryType {
    Receive,
    Send,
    Provide,
    Require,
}

/// TODO: The `once` calls are not fully supported, and deferred to their multi-use counterparts.
pub trait LookupBuilder: AirBuilder {
    /// Generic query that to be added to the global lookup argument.
    /// Note: is_real_bool must be a boolean.
    fn query(
        &mut self,
        query_type: QueryType,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    );

    /// Receive a query (once) that has been sent in another part of the program.
    fn receive(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        self.query(QueryType::Receive, relation, is_real_bool);
    }

    /// Send a query (once) to another part of the program.
    fn send(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>) {
        self.query(QueryType::Send, relation, is_real_bool);
    }

    /// Provide a query that can be required multiple times.
    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        self.query(QueryType::Provide, relation, is_real_bool);
    }

    /// Require a query that has been provided.
    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        self.query(QueryType::Require, relation, is_real_bool);
    }
}

// impl<'a, AB: LookupBuilder> LookupBuilder for FilteredAirBuilder<'a, AB> {
//     fn query(
//         &mut self,
//         query_type: QueryType,
//         relation: impl Relation<Self::Expr>,
//         is_real: Option<Self::Expr>,
//     ) {
//         // // TODO: This requires FilteredAirBuilder.condition to be made public
//         // let condition = if let Some(is_real) = is_real {
//         //     is_real * self.condition().clone()
//         // } else {
//         //     self.condition().clone()
//         // };
//         // self.inner.query(query_type, relation, Some(condition))
//         self.inner.query(query_type, relation, is_real)
//     }
// }

impl<AB: AirBuilder + MessageBuilder<AirInteraction<AB::Expr>>> LookupBuilder for AB {
    fn query(
        &mut self,
        query_type: QueryType,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();
        match query_type {
            QueryType::Receive => {
                <Self as MessageBuilder<AirInteraction<Self::Expr>>>::receive(
                    self,
                    AirInteraction::new(
                        relation.values().into_iter().collect(),
                        is_real,
                        InteractionKind::Program,
                    ),
                );
            }
            QueryType::Send => {
                <Self as MessageBuilder<AirInteraction<Self::Expr>>>::send(
                    self,
                    AirInteraction::new(
                        relation.values().into_iter().collect(),
                        is_real,
                        InteractionKind::Program,
                    ),
                );
            }
            QueryType::Provide => {
                <Self as MessageBuilder<AirInteraction<Self::Expr>>>::receive(
                    self,
                    AirInteraction::new(
                        relation.values().into_iter().collect(),
                        is_real,
                        InteractionKind::Program,
                    ),
                );
            }
            QueryType::Require => {
                <Self as MessageBuilder<AirInteraction<Self::Expr>>>::receive(
                    self,
                    AirInteraction::new(
                        relation.values().into_iter().collect(),
                        is_real,
                        InteractionKind::Program,
                    ),
                );
            }
        }
    }
}
