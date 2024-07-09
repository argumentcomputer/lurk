use crate::air::builder::{Record, RequireRecord};
use crate::gadgets::bytes::{ByteInput, ByteRecord};
use p3_field::PrimeField;
use std::collections::BTreeMap;

/// Contains all Byte operation records that happened during an execution.
/// For each type of event, we record the nonce at which this event happened.
/// In order to modify this record, use `with_context` and provide an iterator of
/// mutable references to the `RequireRecord`s.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BytesRecord {
    records: BTreeMap<ByteInput, BytesInputRecord>,
}

/// Temporary wrapper around `BytesRecord` which implements `ByteRecord`.
///
pub struct ByteRecordWithContext<'a, 'b, F, I>
where
    F: 'static,
    I: Iterator<Item = &'b mut RequireRecord<F>>,
{
    nonce: u32,
    record: &'a mut BytesRecord,
    requires: I,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct BytesInputRecord {
    pub(crate) range_u8: Record,
    pub(crate) range_u16: Record,
    pub(crate) less_then: Record,
    pub(crate) and: Record,
    pub(crate) xor: Record,
    pub(crate) or: Record,
    pub(crate) msb: Record,
}

impl BytesInputRecord {
    pub fn iter_records(&self) -> impl IntoIterator<Item = Record> {
        [
            self.range_u8,
            self.range_u16,
            self.less_then,
            self.and,
            self.xor,
            self.or,
            self.msb,
        ]
    }
}

impl BytesRecord {
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

impl<'a, 'b, F, I> ByteRecord for ByteRecordWithContext<'a, 'b, F, I>
where
    F: 'static + PrimeField,
    I: Iterator<Item = &'b mut RequireRecord<F>>,
{
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.range_u8;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
    }

    fn range_check_u16(&mut self, i: u16) {
        let [i1, i2] = i.to_le_bytes();
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.range_u16;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.less_then;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.and;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.xor;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.get_mut(input);
        let record = &mut records.or;
        let require = self.requires.next().expect("not enough requires records");
        require.populate_and_update(self.nonce, record);
        input.or()
    }

    fn msb(&mut self, i: u8) -> bool {
        let input = ByteInput::new(i, 0);
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
