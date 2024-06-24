use itertools::chain;
use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use p3_field::AbstractField;
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
    /// Provide a query that can be required multiple times.
    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: ProvideRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    );

    /// Require a query that has been provided.
    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: RequireRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    );
}

impl<AB: AirBuilder + MessageBuilder<AirInteraction<AB::Expr>>> LookupBuilder for AB {
    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: ProvideRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();

        let ProvideRecord {
            last_nonce,
            last_count,
        } = record;

        let values: Vec<_> = relation.values().into_iter().collect();

        self.receive(AirInteraction {
            values: chain([last_nonce, last_count], values.clone()).collect(),
            multiplicity: is_real.clone(),
            kind: InteractionKind::Memory,
        });
        self.send(AirInteraction {
            values: chain([nonce.into(), AB::Expr::zero()], values).collect(),
            multiplicity: is_real.clone(),
            kind: InteractionKind::Memory,
        })
    }

    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: RequireRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();

        let RequireRecord {
            prev_nonce,
            prev_count,
            count_inv,
        } = record;

        let count = prev_count.clone() + AB::Expr::one();

        self.when(is_real.clone())
            .assert_one(count.clone() * count_inv);

        let values: Vec<_> = relation.values().into_iter().collect();

        self.receive(AirInteraction {
            values: chain([prev_nonce, prev_count], values.clone()).collect(),
            multiplicity: is_real.clone(),
            kind: InteractionKind::Memory,
        });
        self.send(AirInteraction {
            values: chain([nonce.into(), count], values).collect(),
            multiplicity: is_real.clone(),
            kind: InteractionKind::Memory,
        })
    }
}

pub struct RequireRecord<E> {
    pub prev_nonce: E,
    pub prev_count: E,
    pub count_inv: E,
}

pub struct ProvideRecord<E> {
    pub last_nonce: E,
    pub last_count: E,
}
