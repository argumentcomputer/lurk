use p3_field::AbstractField;
use std::ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign};
use std::{array, slice};

pub mod add;
mod bitwise;
pub mod is_zero;
pub mod mul;

pub const WORD_SIZE: usize = 8;

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
#[repr(C)]
pub struct Word<T>([T; WORD_SIZE]);

impl Add for Word<u8> {
    type Output = Word<u8>;

    fn add(self, rhs: Self) -> Self::Output {
        let lhs = u64::from_le_bytes(self.0);
        let rhs = u64::from_le_bytes(rhs.0);
        let out = lhs + rhs;
        Self(out.to_le_bytes())
    }
}

impl AddAssign for Word<u8> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Mul for Word<u8> {
    type Output = Word<u8>;

    fn mul(self, rhs: Self) -> Self::Output {
        let lhs = u64::from_le_bytes(self.0);
        let rhs = u64::from_le_bytes(rhs.0);
        let out = lhs * rhs;
        Self(out.to_le_bytes())
    }
}

impl MulAssign for Word<u8> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<T> Word<T> {
    #[inline]
    pub fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Self(array::from_fn(cb))
    }

    #[inline]
    pub fn map<F, O>(self, f: F) -> Word<O>
    where
        F: FnMut(T) -> O,
    {
        Word(self.0.map(f))
    }

    #[inline]
    pub fn into<U>(self) -> Word<U>
    where
        T: Into<U>,
    {
        self.map(Into::into)
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl Word<u8> {
    #[inline]
    pub fn into_field<F: AbstractField>(self) -> Word<F> {
        self.map(F::from_canonical_u8)
    }
}

impl<T> IntoIterator for Word<T> {
    type Item = T;
    type IntoIter = array::IntoIter<T, WORD_SIZE>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Word<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T, I> Index<I> for Word<T>
where
    [T]: Index<I>,
{
    type Output = <[T] as Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T, I> IndexMut<I> for Word<T>
where
    [T]: IndexMut<I>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl<T> AsRef<[T]> for Word<T> {
    fn as_ref(&self) -> &[T] {
        self.0.as_slice()
    }
}
