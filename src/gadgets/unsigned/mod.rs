use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use core::slice;
use num_traits::{ToBytes, Unsigned};
use p3_field::AbstractField;
use std::array;
use std::fmt::Debug;
use std::iter::zip;
use std::ops::{Index, IndexMut};

pub mod add;
pub mod div_rem;
pub mod is_zero;
pub mod less_than;
pub mod mul;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(C)]
pub struct Word<T, const W: usize>([T; W]);

pub type Word32<T> = Word<T, 4>;
pub type Word64<T> = Word<T, 8>;

impl<T, const W: usize> Word<T, W> {
    #[inline]
    pub fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Self(array::from_fn(cb))
    }

    #[inline]
    pub fn map<F, O>(self, f: F) -> Word<O, W>
    where
        F: FnMut(T) -> O,
    {
        Word(self.0.map(f))
    }

    #[inline]
    pub fn into<U>(self) -> Word<U, W>
    where
        T: Into<U>,
    {
        self.map(Into::into)
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &'_ mut T> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn into_array(self) -> [T; W] {
        self.0
    }
}

//
// Conversion
//

impl<F: AbstractField, const W: usize> Word<F, W> {
    #[inline]
    pub fn zero() -> Self {
        Self(array::from_fn(|_| F::zero()))
    }

    #[inline]
    pub fn one() -> Self {
        Self(array::from_fn(
            |i| {
                if i == 0 {
                    F::one()
                } else {
                    F::zero()
                }
            },
        ))
    }

    pub fn from_unsigned<U: ToBytes<Bytes = [u8; W]> + Unsigned>(u: &U) -> Self {
        Self(u.to_le_bytes().map(F::from_canonical_u8))
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(C)]
pub struct UncheckedWord<T, const W: usize>([T; W]);

impl<F: Default, const W: usize> Default for UncheckedWord<F, W> {
    fn default() -> Self {
        Self(array::from_fn(|_| F::default()))
    }
}

impl<F: AbstractField, const W: usize> UncheckedWord<F, W> {
    pub fn assign_bytes(&mut self, bytes: &[u8], record: &mut impl ByteRecord) {
        assert_eq!(bytes.len(), W);
        for (limb, &byte) in zip(self.0.iter_mut(), bytes) {
            *limb = F::from_canonical_u8(byte);
        }
        record.range_check_u8_iter(bytes.iter().copied());
    }
}

impl<Var, const W: usize> UncheckedWord<Var, W> {
    pub fn into_checked<Expr: AbstractField>(
        self,
        record: &mut impl ByteAirRecord<Expr>,
        is_real: impl Into<Expr>,
    ) -> Word<Var, W>
    where
        Var: Copy + Into<Expr>,
    {
        record.range_check_u8_iter(self.0.iter().copied(), is_real);
        Word(self.0)
    }

    pub fn as_unchecked<Expr: AbstractField>(&self) -> Word<Expr, W>
    where
        Var: Copy + Into<Expr>,
    {
        Word(self.0.map(Into::into))
    }
}

//
// Iterator
//

impl<T, const W: usize> IntoIterator for Word<T, W> {
    type Item = T;
    type IntoIter = array::IntoIter<T, W>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, const W: usize> IntoIterator for &'a Word<T, W> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T, const W: usize> IntoIterator for &'a mut Word<T, W> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T, I, const W: usize> Index<I> for Word<T, W>
where
    [T]: Index<I>,
{
    type Output = <[T] as Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T, I, const W: usize> IndexMut<I> for Word<T, W>
where
    [T]: IndexMut<I>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl<T, const W: usize> AsRef<[T]> for Word<T, W> {
    fn as_ref(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T: Default, const W: usize> Default for Word<T, W> {
    fn default() -> Self {
        Self(array::from_fn(|_| T::default()))
    }
}
