use crate::air::builder::Record;
use crate::gadgets::bytes::{ByteInput, ByteRecord};
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
    pub(crate) records: BTreeMap<ByteInput, BytesInputRecord>,
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
pub struct ByteRecordWithContext<'a> {
    pub nonce: u32,
    pub requires: &'a mut Vec<Record>,
    pub record: &'a mut BytesRecord,
    pub query_index: usize,
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
        ]
    }

    /// Returns a mutable iterator of all the records
    pub fn iter_mut_records(&mut self) -> impl IntoIterator<Item = &mut Record> {
        [
            &mut self.range_u8,
            &mut self.range_u16,
            &mut self.less_than,
            &mut self.and,
            &mut self.xor,
            &mut self.or,
        ]
    }
}

impl BytesRecord {
    /// Add context (nonce and `RequireRecords`) to a given `ByteInputRecord` to be passed along
    /// to a witness's `populate` function.
    pub fn context<'a>(
        &'a mut self,
        nonce: u32,
        query_index: usize,
        requires: &'a mut Vec<Record>,
    ) -> ByteRecordWithContext<'a> {
        ByteRecordWithContext {
            nonce,
            record: self,
            requires,
            query_index,
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

    pub fn clear(&mut self) {
        self.records.clear()
    }
}

/// Implement ByteRecord by recording all the required events
///
/// # Detail
/// For each type of event, we
/// - Get the records for the index of the byte operation in the ByteChip, or default initialize it.
/// - Populate the next available `RequireRecord` using the record we have stored.
/// - Update the stored record with the nonce for this access.
impl ByteRecord for ByteRecordWithContext<'_> {
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        let input = ByteInput::from_u8_pair(i1, i2);
        let index = self.query_index;
        let range_u8 = &mut self.record.get_mut(input).range_u8;
        let require = range_u8.new_lookup(self.nonce, index);
        self.requires.push(require);
    }

    fn range_check_u16(&mut self, i: u16) {
        let input = ByteInput::from_u16(i);
        let index = self.query_index;
        let range_u16 = &mut self.record.get_mut(input).range_u16;
        let require = range_u16.new_lookup(self.nonce, index);
        self.requires.push(require);
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::from_u8_pair(i1, i2);
        let index = self.query_index;
        let less_than = &mut self.record.get_mut(input).less_than;
        let require = less_than.new_lookup(self.nonce, index);
        self.requires.push(require);
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let index = self.query_index;
        let and = &mut self.record.get_mut(input).and;
        let require = and.new_lookup(self.nonce, index);
        self.requires.push(require);
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let index = self.query_index;
        let xor = &mut self.record.get_mut(input).xor;
        let require = xor.new_lookup(self.nonce, index);
        self.requires.push(require);
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let index = self.query_index;
        let or = &mut self.record.get_mut(input).or;
        let require = or.new_lookup(self.nonce, index);
        self.requires.push(require);
        input.or()
    }
}

// Dummy record for when you do not want to record anything
pub struct DummyBytesRecord;

impl ByteRecord for DummyBytesRecord {
    fn range_check_u8_pair(&mut self, _: u8, _: u8) {}

    fn range_check_u16(&mut self, _: u16) {}

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::from_u8_pair(i1, i2);
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        input.or()
    }
}
