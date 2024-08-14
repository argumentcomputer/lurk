use crate::air::builder::{LookupBuilder, RequireRecord};
use crate::gadgets::bytes::relation::ByteRelation;
use crate::gadgets::bytes::ByteAirRecord;
use itertools::zip_eq;
use p3_field::{AbstractField, PrimeField32};

/// A struct meant to implement ByteAirRecord.
///
/// # Detail
/// When evaluating the Air constraints, we simply log all the requested byte relations
/// in this struct.
///
/// Note that in the context of Sphinx, this structure will only be used when initializing the
/// prover, since the constraints will first be evaluated by the `SymbolicAirBuilder` to gather
/// all the lookup interactions. During proving and specifically quotient evaluation,
/// the Air constraints should run using `ByteAirRecord` where all operations are no-ops.
#[derive(Clone, Debug, Default)]
pub struct BytesAirRecordWithContext<F> {
    // [(Relation, IsReal)]
    records: Vec<(ByteRelation<F>, F)>,
}

impl<F: AbstractField> BytesAirRecordWithContext<F> {
    /// Once the row has been evaluated, and all byte relations recorded into this struct,
    /// the chip must provide an iterator of mutable references to the `RequireRecord`s that
    /// will be sent to the lookup argument.
    pub fn require_all<AB: LookupBuilder<Expr = F>, R: Into<AB::Expr>>(
        self,
        builder: &mut AB,
        nonce: impl Into<AB::Expr>,
        requires: impl IntoIterator<Item = RequireRecord<R>>,
    ) {
        let nonce = nonce.into();
        for ((relation, is_real), record) in zip_eq(self.records, requires) {
            builder.require(relation, is_real);
        }
    }

    pub fn check(&self)
    where
        F: PrimeField32,
    {
        for (relation, is_real) in &self.records {
            if is_real.is_zero() {
                continue;
            }
            assert!(is_real.is_one());
            relation.check();
        }
    }
}

impl<F: AbstractField> ByteAirRecord<F> for BytesAirRecordWithContext<F> {
    fn range_check_u8_pair(&mut self, i1: impl Into<F>, i2: impl Into<F>, is_real: impl Into<F>) {
        self.records
            .push((ByteRelation::range_u8_pair(i1, i2), is_real.into()))
    }

    fn range_check_u16(&mut self, i: impl Into<F>, is_real: impl Into<F>) {
        self.records
            .push((ByteRelation::range_u16(i), is_real.into()))
    }

    fn less_than(
        &mut self,
        i1: impl Into<F>,
        i2: impl Into<F>,
        r: impl Into<F>,
        is_real: impl Into<F>,
    ) {
        self.records
            .push((ByteRelation::less_than(i1, i2, r), is_real.into()))
    }

    fn and(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.records
            .push((ByteRelation::and(i1, i2, r), is_real.into()))
    }

    fn xor(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.records
            .push((ByteRelation::xor(i1, i2, r), is_real.into()))
    }

    fn or(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.records
            .push((ByteRelation::or(i1, i2, r), is_real.into()))
    }
}
