use hybrid_array::sizes::{U4, U8};
use hybrid_array::{Array, ArraySize};
use p3_field::AbstractField;
use std::cmp::Ordering;
use std::fmt::{Debug, Formatter, Pointer};
use std::ops::{Add, AddAssign, Index, IndexMut, Mul, MulAssign, Sub, SubAssign};

pub mod add;
pub mod is_zero;
mod less_than;
pub mod mul;

#[derive(Clone, Default)]
#[repr(C)]
pub struct Word<T, W: ArraySize>(Array<T, W>);

pub type Word32<T> = Word<T, U4>;
pub type Word64<T> = Word<T, U8>;

impl<T, W: ArraySize> Word<T, W> {
    #[inline]
    pub fn from_fn<F>(cb: F) -> Self
    where
        F: FnMut(usize) -> T,
    {
        Self(Array::from_fn(cb))
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
}

impl<T: Default, W: ArraySize> Word<T, W> {
    #[inline]
    pub fn zero() -> Self {
        Self::default()
    }

    #[inline]
    pub fn is_zero(&self) -> bool
    where
        T: PartialEq,
    {
        self.0.iter().all(|limb| limb.eq(&T::default()))
    }
}

//
// Conversion
//

impl<W: ArraySize> Word<u8, W> {
    #[inline]
    pub fn into_field<F: AbstractField>(self) -> Word<F, W> {
        self.map(F::from_canonical_u8)
    }
}

impl From<Word64<u8>> for u64 {
    fn from(value: Word64<u8>) -> Self {
        Self::from_le_bytes(value.0.into())
    }
}

impl From<Word32<u8>> for u32 {
    fn from(value: Word32<u8>) -> Self {
        Self::from_le_bytes(value.0.into())
    }
}

impl From<u64> for Word64<u8> {
    fn from(value: u64) -> Self {
        Self(value.to_le_bytes().into())
    }
}

impl From<u32> for Word32<u8> {
    fn from(value: u32) -> Self {
        Self(value.to_le_bytes().into())
    }
}

impl<T: Default> From<Word32<T>> for Word64<T> {
    fn from(mut value: Word<T, U4>) -> Self {
        let mut limbs = Self::default();
        limbs.0[..4].swap_with_slice(&mut value.0);
        limbs
    }
}

impl<T, W, const N: usize> From<[T; N]> for Word<T, W>
where
    W: ArraySize<ArrayType<T> = [T; N]>,
{
    fn from(value: [T; N]) -> Self {
        Self(value.into())
    }
}

//
// Arithmetic Ops
//

impl<W: ArraySize> Add for Word<u8, W> {
    type Output = Word<u8, W>;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<W: ArraySize> AddAssign for Word<u8, W> {
    fn add_assign(&mut self, rhs: Self) {
        let mut carry = false;
        for (limb_l, &limb_r) in self.0.iter_mut().zip(rhs.0.iter()) {
            let (sum, overflow1) = limb_l.overflowing_add(limb_r);
            let (sum, overflow2) = sum.overflowing_add(u8::from(carry));
            *limb_l = sum;
            carry = overflow1 || overflow2;
        }
    }
}

impl<W: ArraySize> Sub for Word<u8, W> {
    type Output = Word<u8, W>;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<W: ArraySize> SubAssign for Word<u8, W> {
    fn sub_assign(&mut self, rhs: Self) {
        let mut borrow = false;
        for (limb_l, &limb_r) in self.0.iter_mut().zip(rhs.0.iter()) {
            let (diff, underflow1) = limb_l.overflowing_sub(limb_r);
            let (diff, underflow2) = diff.overflowing_sub(u8::from(borrow));
            *limb_l = diff;
            borrow = underflow1 || underflow2;
        }
    }
}

impl<W: ArraySize> Mul for Word<u8, W> {
    type Output = Word<u8, W>;

    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<W: ArraySize> MulAssign for Word<u8, W> {
    fn mul_assign(&mut self, rhs: Self) {
        let mut result = Self::default();

        for i in 0..W::USIZE {
            let mut carry = 0u16;
            for j in 0..(W::USIZE - i) {
                let product = u16::from(self.0[i]) * u16::from(rhs.0[j]);
                let sum = product + u16::from(result.0[i + j]) + carry;
                result.0[i + j] = sum as u8;
                carry = sum >> 8;
            }
        }

        *self = result;
    }
}

//
// Iterator
//

impl<T, W: ArraySize> IntoIterator for Word<T, W> {
    type Item = T;
    type IntoIter = <Array<T, W> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T, W: ArraySize> IntoIterator for &'a Word<T, W> {
    type Item = &'a T;
    type IntoIter = <&'a Array<T, W> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T, I, W: ArraySize> Index<I> for Word<T, W>
where
    [T]: Index<I>,
{
    type Output = <[T] as Index<I>>::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        self.0.index(index)
    }
}

impl<T, I, W: ArraySize> IndexMut<I> for Word<T, W>
where
    [T]: IndexMut<I>,
{
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        self.0.index_mut(index)
    }
}

impl<T, W: ArraySize> AsRef<[T]> for Word<T, W> {
    fn as_ref(&self) -> &[T] {
        self.0.as_slice()
    }
}

impl<T, W: ArraySize> Debug for Word<T, W> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.as_slice().fmt(f)
    }
}

impl<T: PartialEq, W: ArraySize> PartialEq for Word<T, W> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}

impl<T: Eq, W: ArraySize> Eq for Word<T, W> {}

impl<W: ArraySize> PartialOrd for Word<u8, W> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<W: ArraySize> Ord for Word<u8, W> {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..W::USIZE).rev() {
            match u8::cmp(&self[i], &other[i]) {
                Ordering::Equal => continue,
                ord => return ord,
            }
        }
        Ordering::Equal
    }
}
