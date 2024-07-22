use crate::air::builder::{Record, RequireRecord};
use crate::gadgets::bytes::{ByteInput, ByteRecord};
use p3_field::PrimeField;
use std::collections::BTreeMap;

/// Contains all Byte operation records that happened during an execution.
/// For each type of event, we record the nonce at which this event happened.
/// In order to modify this record, use `with_context` and provide an iterator of
/// mutable references to the `RequireRecord`s.
///
/// # Detail
/// Records are indexed by the input byte pair, so that we only store records for inputs
/// that were actually requested.  
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BytesRecord {
    // Maps input bytes to a list of records for each potential operation that could've been
    records: BTreeMap<ByteInput, BytesInputRecord>,
}

/// Temporary wrapper around `BytesRecord` which implements `ByteRecord`.
///
/// # Detail
///
/// Since the ByteRecord API does not make any assumptions about any additional "context"
/// that may be needed to securely use the lookup argument when looking up byte results,
/// we store this extra context in this struct and implement the trait over it.
///
/// It contains the nonce for the event, as well as a pre-allocated list of `RequireRecords` that
/// will be populated with the correct witness data.
///
/// # Panics
///
/// This structure implements `Drop` and asserts that the list of `RequireRecords` was fully
/// consumed. This ensures the correct number of records are populated.
pub struct ByteRecordWithContext<'a, 'b, F, I>
where
    F: 'static,
    I: Iterator<Item = &'b mut RequireRecord<F>>,
{
    nonce: u32,
    record: &'a mut BytesRecord,
    requires: I,
}

pub struct BytesRecordWithContext<'a> {
    pub nonce: u32,
    pub requires: &'a mut Vec<Record>,
    pub record: &'a mut BytesRecord,
}

/// For a given input byte pair, this structure records the nonce and count of the accesses to
/// the specific operations.
///
/// # Detail
///
/// It is assumed that all byte operations are performed sequentially,
/// so we therefore know in advance when all the `require` calls are happening.
/// Moreover, the `provide` records are populated afterward, so we only need to keep track of the
/// last access. This is a small optimization that avoids having to maintain a list of
/// all the nonces used throughout the computation.
///
/// We take advantage of the fact that the default record with `(nonce, count) = (0, 0)`  
/// represents the record of an event which was never required. Therefore, the default
/// state of this struct is valid.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BytesInputRecord {
    pub(crate) range_u8: Record,
    pub(crate) range_u16: Record,
    pub(crate) less_than: Record,
    pub(crate) and: Record,
    pub(crate) xor: Record,
    pub(crate) or: Record,
    pub(crate) msb: Record,
}

impl BytesInputRecord {
    /// Returns an iterator of all the records
    pub fn iter_records(&self) -> impl IntoIterator<Item = Record> {
        [
            self.range_u8,
            self.range_u16,
            self.less_than,
            self.and,
            self.xor,
            self.or,
            self.msb,
        ]
    }
}

impl BytesRecord {
    /// Add context (nonce and `RequireRecords`) to a given `ByteInputRecord` to be passed along
    /// to a witness's `populate` function.
    pub fn with_context<'a, 'b, F, II>(
        &'a mut self,
        nonce: u32,
        requires: II,
    ) -> ByteRecordWithContext<'a, 'b, F, II::IntoIter>
    where
        F: 'b,
        II: IntoIterator<Item = &'b mut RequireRecord<F>>,
    {
        ByteRecordWithContext {
            nonce,
            record: self,
            requires: requires.into_iter(),
        }
    }

    pub fn context<'a>(
        &'a mut self,
        nonce: u32,
        requires: &'a mut Vec<Record>,
    ) -> BytesRecordWithContext<'a> {
        BytesRecordWithContext {
            nonce,
            record: self,
            requires,
        }
    }

    fn get_mut(&mut self, input: ByteInput) -> &mut BytesInputRecord {
        self.records.entry(input).or_default()
    }

    pub fn get(&self, input: ByteInput) -> Option<&BytesInputRecord> {
        self.records.get(&input)
    }

    pub fn is_empty(&self) -> bool {
        self.records.is_empty()
    }
}

impl<'a> ByteRecord for BytesRecordWithContext<'a> {
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        let input = ByteInput::from_u8_pair(i1, i2);
        let range_u8 = &mut self.record.get_mut(input).range_u8;
        let require = range_u8.new_lookup(self.nonce);
        self.requires.push(require);
    }

    fn range_check_u16(&mut self, i: u16) {
        let input = ByteInput::from_u16(i);
        let range_u16 = &mut self.record.get_mut(input).range_u16;
        let require = range_u16.new_lookup(self.nonce);
        self.requires.push(require);
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::from_u8_pair(i1, i2);
        let less_than = &mut self.record.get_mut(input).less_than;
        let require = less_than.new_lookup(self.nonce);
        self.requires.push(require);
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let and = &mut self.record.get_mut(input).and;
        let require = and.new_lookup(self.nonce);
        self.requires.push(require);
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let xor = &mut self.record.get_mut(input).xor;
        let require = xor.new_lookup(self.nonce);
        self.requires.push(require);
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let or = &mut self.record.get_mut(input).or;
        let require = or.new_lookup(self.nonce);
        self.requires.push(require);
        input.or()
    }

    fn msb(&mut self, i: u8) -> bool {
        let input = ByteInput::from_u8(i);
        let msb = &mut self.record.get_mut(input).msb;
        let require = msb.new_lookup(self.nonce);
        self.requires.push(require);
        input.msb()
    }
}

/// Implement ByteRecord such that each operation will populate the `RequireRecords` with the
/// appropriate nonce.
///
/// # Detail
/// For each type of event, we
/// - Get the records for the index of the byte operation in the ByteChip, or default initialize it.
/// - Populate the next available `RequireRecord` using the record we have stored.
/// - Update the stored record with the nonce for this access.
impl<'a, 'b, F, I> ByteRecord for ByteRecordWithContext<'a, 'b, F, I>
where
    F: 'static + PrimeField,
    I: Iterator<Item = &'b mut RequireRecord<F>>,
{
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        let input = ByteInput::from_u8_pair(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.range_u8;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
    }

    fn range_check_u16(&mut self, i: u16) {
        let input = ByteInput::from_u16(i);
        let records = self.record.get_mut(input);
        let record = &mut records.range_u16;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::from_u8_pair(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.less_than;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.and;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.xor;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.or;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.or()
    }

    fn msb(&mut self, i: u8) -> bool {
        let input = ByteInput::from_u8(i);
        let records = self.record.get_mut(input);
        let record = &mut records.msb;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.msb()
    }
}

// Implement drop to ensure the witness generation always passes the right number of RequireRecord
impl<'a, 'b, F, I> Drop for ByteRecordWithContext<'a, 'b, F, I>
where
    F: 'static,
    I: Iterator<Item = &'b mut RequireRecord<F>>,
{
    fn drop(&mut self) {
        assert!(
            self.requires.next().is_none(),
            "Too many `require` were given"
        )
    }
}
