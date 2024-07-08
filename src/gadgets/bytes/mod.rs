mod trace;

use std::collections::BTreeMap;

#[derive(Copy, Clone, Debug, Default, Ord, PartialOrd, Eq, PartialEq)]
pub struct ByteInput(u16);

impl ByteInput {
    #[inline]
    pub fn new(i1: u8, i2: u8) -> Self {
        Self(u16::from_le_bytes([i1, i2]))
    }

    #[inline]

    pub fn range_u8_pair(&self) -> (u8, u8) {
        let [i1, i2] = self.0.to_le_bytes();
        (i1, i2)
    }

    #[inline]
    pub fn range_u16(&self) -> u16 {
        self.0
    }

    #[inline]
    pub fn less_than(&self) -> bool {
        let [i1, i2] = self.0.to_le_bytes();
        i1 < i2
    }

    #[inline]
    pub fn and(&self) -> u8 {
        let [i1, i2] = self.0.to_le_bytes();
        i1 & i2
    }

    #[inline]
    pub fn xor(&self) -> u8 {
        let [i1, i2] = self.0.to_le_bytes();
        i1 ^ i2
    }

    #[inline]
    pub fn or(&self) -> u8 {
        let [i1, i2] = self.0.to_le_bytes();
        i1 | i2
    }

    #[inline]
    pub fn msb(&self) -> bool {
        let [i1, i2] = self.0.to_le_bytes();
        debug_assert_eq!(i2, 0);
        (i1 >> 7) == 1
    }
}

pub trait ByteRecord {
    fn range_check_u8(&mut self, i: u8) {
        self.range_check_u8_pair(i, 0);
    }
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8);
    fn range_check_u8_iter(&mut self, iter: impl IntoIterator<Item = u8>) {
        let mut iter = iter.into_iter();
        while let Some(i1) = iter.next() {
            let i2 = iter.next().unwrap_or(0);
            self.range_check_u8_pair(i1, i2)
        }
    }
    fn range_check_u16(&mut self, i: u16);

    fn less_than(&mut self, i1: u8, i2: u8) -> bool;
    fn and(&mut self, i1: u8, i2: u8) -> u8;
    fn xor(&mut self, i1: u8, i2: u8) -> u8;
    fn or(&mut self, i1: u8, i2: u8) -> u8;
    fn msb(&mut self, i: u8) -> bool;
}

#[derive(Copy, Clone, Debug, Default)]
pub struct ByteInputRecord {
    nonce: u32,
}

#[derive(Debug, Default)]
pub struct NonceByteRecord {
    range_u8: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    range_u16: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    less_then: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    and: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    xor: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    or: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
    msb: BTreeMap<ByteInput, Vec<ByteInputRecord>>,
}

impl NonceByteRecord {
    pub fn with_nonce(&mut self, nonce: u32) -> ByteRecordWithContext {
        ByteRecordWithContext {
            nonce,
            record: self,
        }
    }
}

pub struct ByteRecordWithContext<'a> {
    nonce: u32,
    record: &'a mut NonceByteRecord,
}

impl<'a> ByteRecord for ByteRecordWithContext<'a> {
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        let input = ByteInput::new(i1, i2);
        let records = self.record.range_u8.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
    }

    fn range_check_u16(&mut self, i: u16) {
        let [i1, i2] = i.to_le_bytes();
        let input = ByteInput::new(i1, i2);
        let records = self.record.range_u16.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::new(i1, i2);
        let records = self.record.less_then.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
        input.less_than()
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.and.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
        input.and()
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.xor.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
        input.xor()
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::new(i1, i2);
        let records = self.record.or.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
        input.or()
    }

    fn msb(&mut self, i: u8) -> bool {
        let input = ByteInput::new(i, 0);
        let records = self.record.msb.entry(input).or_default();
        records.push(ByteInputRecord { nonce: self.nonce });
        input.msb()
    }
}
