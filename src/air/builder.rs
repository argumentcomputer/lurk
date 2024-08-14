use itertools::chain;
use p3_air::{AirBuilder, AirBuilderWithPublicValues};
use p3_field::{AbstractField, PrimeField};
use sphinx_core::air::{AirInteraction, MessageBuilder};
use sphinx_core::lookup::InteractionKind;
use sphinx_derive::AlignedBorrow;

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

/// TODO: The `once` calls are not fully supported, and deferred to their multi-use counterparts.
pub trait LookupBuilder: AirBuilder {
    // TODO comment
    // Read a
    fn receive(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>);

    fn send(&mut self, relation: impl Relation<Self::Expr>, is_real_bool: impl Into<Self::Expr>);

    /// Provide a query that can be required multiple times.
    fn provide(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        // Write it back with the updated count and current nonce/row value.
        self.send(relation, is_real_bool);
    }

    /// Require a query that has been provided.
    fn require(
        &mut self,
        relation: impl Relation<Self::Expr>,
        is_real_bool: impl Into<Self::Expr>,
    ) {
        // Write it back with the updated count and current nonce/row value.
        self.send(relation, is_real_bool);
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

#[derive(Copy, Clone, Default, Debug, Eq, PartialEq)]
pub struct Record {
    pub nonce: u32,
    pub count: u32,
}

impl Record {
    /// Updates the provide record and returns the require record
    pub fn new_lookup(&mut self, nonce: u32) -> Record {
        let require = *self;
        self.nonce = nonce;
        self.count += 1;
        require
    }

    pub fn into_provide<F: PrimeField>(self) -> ProvideRecord<F> {
        let last_nonce = F::from_canonical_u32(self.nonce);
        let last_count = F::from_canonical_u32(self.count);
        ProvideRecord {
            last_count,
            last_nonce,
        }
    }

    pub fn into_require<F: PrimeField>(self) -> RequireRecord<F> {
        let prev_nonce = F::from_canonical_u32(self.nonce);
        let prev_count = F::from_canonical_u32(self.count);
        let count_inv = (prev_count + F::one()).inverse();
        RequireRecord {
            prev_nonce,
            prev_count,
            count_inv,
        }
    }
}

/// A [RequireRecord] contains witness values
#[derive(Copy, Clone, Default, Debug, AlignedBorrow)]
#[repr(C)]
pub struct RequireRecord<T> {
    /// The `nonce` is the row in the trace where the previous access occurred.
    pub prev_nonce: T,
    /// The `count`
    /// May be zero when the previous access was `provide`, or for padding when `is_real = 0`.
    pub prev_count: T,
    /// Inverse of `count = prev_count + 1`, proving that `count` is non-zero.
    /// May be zero when `is_real = 0`
    pub count_inv: T,
}

impl<F: PrimeField> RequireRecord<F> {
    pub fn populate(&mut self, record: Record) {
        self.prev_nonce = F::from_canonical_u32(record.nonce);
        self.prev_count = F::from_canonical_u32(record.count);
        self.count_inv = (self.prev_count + F::one()).inverse()
    }

    pub fn populate_and_update(&mut self, nonce: u32, record: &mut Record) {
        self.populate(*record);
        record.nonce = nonce;
        record.count += 1;
    }
}

#[derive(Copy, Clone, Default, Debug, AlignedBorrow)]
#[repr(C)]
pub struct ProvideRecord<T> {
    /// The `nonce` is the row in the trace where the last `require` access occurred.
    pub last_nonce: T,
    /// The `count` written by the final `require` access, also sometimes referred to as the
    /// "multiplicity" of the query.
    pub last_count: T,
}

impl<F: PrimeField> ProvideRecord<F> {
    pub fn populate(&mut self, record: Record) {
        self.last_count = F::from_canonical_u32(record.count);
        self.last_nonce = F::from_canonical_u32(record.nonce);
    }
}
