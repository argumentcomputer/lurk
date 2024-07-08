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

pub struct ContextByteRecord<C> {
    range_u8: BTreeMap<ByteInput, C>,
    range_u16: BTreeMap<ByteInput, C>,
    less_then: BTreeMap<ByteInput, C>,
    and: BTreeMap<ByteInput, C>,
    xor: BTreeMap<ByteInput, C>,
    or: BTreeMap<ByteInput, C>,
    msb: BTreeMap<ByteInput, C>,
}

pub trait ByteRecord {
    type Context;
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

pub struct ByteRecordWithContext<'a, CI, C> {
    context_item: CI,
    record: &'a mut ContextByteRecord<C>,
}

pub struct ByteInputRecord {
    prev_nonce: u32,
    prev_count: u32,
}

pub struct ByteInputRowRecord {
    range_u8_pair: ByteInputRecord,
    range_u16: ByteInputRecord,
    less_than: ByteInputRecord,
    and: ByteInputRecord,
    xor: ByteInputRecord,
    or: ByteInputRecord,
    msb: ByteInputRecord,
}
