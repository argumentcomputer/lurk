use p3_field::{AbstractField, PrimeField32};
use std::num::TryFromIntError;

pub mod builder;
pub mod record;
mod relation;
pub mod trace;

/// A generic input for a byte relation, used as index in a record of required relations,
/// and can compute the expected result of an operation applied to the input.
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

impl<F: PrimeField32> TryFrom<(F, F)> for ByteInput {
    type Error = TryFromIntError;

    fn try_from(value: (F, F)) -> Result<Self, Self::Error> {
        let (i1, i2) = value;
        let i1 = u8::try_from(i1.as_canonical_u32())?;
        let i2 = u8::try_from(i2.as_canonical_u32())?;
        Ok(Self(u16::from_le_bytes([i1, i2])))
    }
}

/// A ByteRecord is passed a mutable reference to a witness generation subroutine,
/// and records all the relations that were required in order to validate the correctness
/// of the witness.
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

/// A ByteAirRecord is passed as mutable reference to a function that evaluates the Air constraints
/// for a witness, in a given row. The main chip will initialize this structure at the start of
/// `Air::eval`, and perform any necessary bookkeeping to ensure the relations are added to a
/// lookup argument.  
pub trait ByteAirRecord<F: AbstractField> {
    fn range_check_u8(&mut self, i: impl Into<F>, is_real: impl Into<F>) {
        self.range_check_u8_pair(i, F::default(), is_real);
    }
    fn range_check_u8_pair(&mut self, i1: impl Into<F>, i2: impl Into<F>, is_real: impl Into<F>);
    fn range_check_u8_iter<IT: Into<F>>(
        &mut self,
        iter: impl IntoIterator<Item = IT>,
        is_real: impl Into<F>,
    ) {
        let is_real = is_real.into();
        let mut iter = iter.into_iter();
        while let Some(i1) = iter.next() {
            let i2 = iter.next().map(Into::into).unwrap_or_default();
            self.range_check_u8_pair(i1, i2, is_real.clone())
        }
    }
    fn range_check_u16(&mut self, i: impl Into<F>, is_real: impl Into<F>);

    fn less_than(
        &mut self,
        i1: impl Into<F>,
        i2: impl Into<F>,
        r: impl Into<F>,
        is_real: impl Into<F>,
    );
    fn and(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>);
    fn xor(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>);
    fn or(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>);
    fn msb(&mut self, i: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>);
}
