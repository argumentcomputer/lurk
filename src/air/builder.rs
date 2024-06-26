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
    // Read a
    fn receive(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>);

    fn send(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>);

    /// Provide a query that can be required multiple times.
    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: ProvideRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();

        // Witness values corresponding to the nonce/row and final count used by the
        // last require access.
        let ProvideRecord {
            last_nonce,
            last_count,
        } = record;

        let values: Vec<_> = relation.values().into_iter().collect();

        // Read the query written by the final require access.
        self.receive(
            chain([last_nonce, last_count], values.clone()),
            is_real.clone(),
        );
        // Write it back with a counter initialized to 0, to be read by the first require access.
        self.send(
            chain([nonce.into(), Self::Expr::zero()], values),
            is_real.clone(),
        );
    }

    /// Require a query that has been provided.
    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        nonce: Self::Var,
        record: RequireRecord<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        let is_real = is_real_bool.into();

        // Witness values used when writing the query to the set in the previous access.
        let RequireRecord {
            prev_nonce,
            prev_count,
            count_inv,
        } = record;

        // The count to be written through this access.
        let count = prev_count.clone() + Self::Expr::one();

        // Ensure that we are not writing back a query with a count = 0.
        self.when(is_real.clone())
            .assert_one(count.clone() * count_inv);

        let values: Vec<_> = relation.values().into_iter().collect();

        // Read the query from the set with the provided nonce and count
        self.receive(
            chain([prev_nonce, prev_count], values.clone()),
            is_real.clone(),
        );
        // Write it back with the updated count and current nonce/row value.
        self.send(chain([nonce.into(), count], values), is_real.clone());
    }
}

impl<AB: AirBuilder + MessageBuilder<AirInteraction<AB::Expr>>> LookupBuilder for AB {
    fn receive(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        <Self as MessageBuilder<AirInteraction<AB::Expr>>>::receive(
            self,
            AirInteraction {
                values: relation.values().into_iter().collect(),
                multiplicity: is_real_bool.into(),
                kind: InteractionKind::Memory,
            },
        )
    }

    fn send(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>) {
        <Self as MessageBuilder<AirInteraction<AB::Expr>>>::send(
            self,
            AirInteraction {
                values: relation.values().into_iter().collect(),
                multiplicity: is_real_bool.into(),
                kind: InteractionKind::Memory,
            },
        )
    }
}

/// A [RequireRecord] contains witness values
#[derive(Copy, Clone, Default, Debug)]
#[repr(C)]
pub struct RequireRecord<E> {
    /// The `nonce` is the row in the trace where the previous access occurred.
    pub prev_nonce: E,
    /// The `count`
    /// May be zero when the previous access was `provide`, or for padding when `is_real = 0`.
    pub prev_count: E,
    /// Inverse of `count = prev_count + 1`, proving that `count` is non-zero.
    /// May be zero when `is_real = 0`
    pub count_inv: E,
}

#[derive(Copy, Clone, Default, Debug)]
#[repr(C)]
pub struct ProvideRecord<E> {
    /// The `nonce` is the row in the trace where the last `require` access occurred.
    pub last_nonce: E,
    /// The `count` written by the final `require` access, also sometimes referred to as the
    /// "multiplicity" of the query.
    pub last_count: E,
}
