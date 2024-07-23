use crate::air::builder::Relation;
use crate::gadgets::bytes::ByteInput;
use itertools::chain;
use p3_field::{AbstractField, PrimeField32};

/// Domain separation tag used to differentiate the provide/require relation for bytes
const BYTE_TAG: u8 = 3;

/// A byte relation which can be required by Air constraints.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ByteRelation<T> {
    RangeU8Pair { i1: T, i2: T },
    RangeU16 { i: T },
    LessThan { i1: T, i2: T, less_than: T },
    And { i1: T, i2: T, and: T },
    Xor { i1: T, i2: T, xor: T },
    Or { i1: T, i2: T, or: T },
    Msb { i: T, msb: T, dummy: T },
}

impl<T> ByteRelation<T> {
    pub fn range_u8(i: impl Into<T>) -> Self
    where
        T: Default,
    {
        Self::range_u8_pair(i, T::default())
    }

    pub fn range_u8_pair(i1: impl Into<T>, i2: impl Into<T>) -> Self {
        Self::RangeU8Pair {
            i1: i1.into(),
            i2: i2.into(),
        }
    }

    pub fn range_u16(i: impl Into<T>) -> Self {
        Self::RangeU16 { i: i.into() }
    }

    pub fn less_than(i1: impl Into<T>, i2: impl Into<T>, r: impl Into<T>) -> Self {
        Self::LessThan {
            i1: i1.into(),
            i2: i2.into(),
            less_than: r.into(),
        }
    }

    pub fn and(i1: impl Into<T>, i2: impl Into<T>, r: impl Into<T>) -> Self {
        Self::And {
            i1: i1.into(),
            i2: i2.into(),
            and: r.into(),
        }
    }

    pub fn xor(i1: impl Into<T>, i2: impl Into<T>, r: impl Into<T>) -> Self {
        Self::Xor {
            i1: i1.into(),
            i2: i2.into(),
            xor: r.into(),
        }
    }

    pub fn or(i1: impl Into<T>, i2: impl Into<T>, r: impl Into<T>) -> Self {
        Self::Or {
            i1: i1.into(),
            i2: i2.into(),
            or: r.into(),
        }
    }

    pub fn msb(i: impl Into<T>, r: impl Into<T>, d: impl Into<T>) -> Self {
        Self::Msb {
            i: i.into(),
            msb: r.into(),
            dummy: d.into(),
        }
    }

    /// Domain separation tag for differentiating different byte operations.
    pub fn tag(&self) -> u8 {
        match self {
            Self::RangeU8Pair { .. } => 1,
            Self::RangeU16 { .. } => 2,
            Self::LessThan { .. } => 3,
            Self::And { .. } => 4,
            Self::Xor { .. } => 5,
            Self::Or { .. } => 6,
            Self::Msb { .. } => 7,
        }
    }

    /// Panics if the relation is not valid.
    pub fn check(&self)
    where
        T: PrimeField32,
    {
        match self {
            ByteRelation::RangeU8Pair { i1, i2 } => {
                ByteInput::try_from((*i1, *i2)).expect("input is not byte");
            }
            ByteRelation::RangeU16 { i } => {
                u16::try_from(i.as_canonical_u32()).expect("i should be u16");
            }
            ByteRelation::LessThan { i1, i2, less_than } => {
                let input = ByteInput::try_from((*i1, *i2)).expect("input is not byte");
                let r = less_than.as_canonical_u32();
                assert!(r <= 1);
                assert_eq!(input.less_than(), r == 1);
            }
            ByteRelation::And { i1, i2, and } => {
                let input = ByteInput::try_from((*i1, *i2)).expect("input is not byte");
                let r = u8::try_from(and.as_canonical_u32()).expect("and should be u8");
                assert_eq!(input.and(), r);
            }
            ByteRelation::Xor { i1, i2, xor } => {
                let input = ByteInput::try_from((*i1, *i2)).expect("input is not byte");
                let r = u8::try_from(xor.as_canonical_u32()).expect("xor should be u8");
                assert_eq!(input.xor(), r);
            }
            ByteRelation::Or { i1, i2, or } => {
                let input = ByteInput::try_from((*i1, *i2)).expect("input is not byte");
                let r = u8::try_from(or.as_canonical_u32()).expect("or should be u8");
                assert_eq!(input.or(), r);
            }
            ByteRelation::Msb { i, msb, .. } => {
                let input = ByteInput::try_from((*i, T::zero())).expect("input is not byte");
                let r = msb.as_canonical_u32();
                assert!(r <= 1);
                assert_eq!(input.msb(), r == 1);
            }
        }
    }
}

/// Implement Relation for the lookup argument
impl<F: AbstractField> Relation<F> for ByteRelation<F> {
    fn values(self) -> impl IntoIterator<Item = F> {
        let relation_tag = F::from_canonical_u8(BYTE_TAG);
        let operation_tag = F::from_canonical_u8(self.tag());
        let relation = match self {
            ByteRelation::RangeU8Pair { i1, i2 } => vec![i1, i2],
            ByteRelation::RangeU16 { i } => vec![i],
            ByteRelation::LessThan { i1, i2, less_than } => vec![i1, i2, less_than],
            ByteRelation::And { i1, i2, and } => vec![i1, i2, and],
            ByteRelation::Xor { i1, i2, xor } => vec![i1, i2, xor],
            ByteRelation::Or { i1, i2, or } => vec![i1, i2, or],
            ByteRelation::Msb { i, msb, dummy } => vec![i, msb, dummy],
        };
        chain([relation_tag, operation_tag], relation)
    }
}
