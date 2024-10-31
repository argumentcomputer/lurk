use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_field::{AbstractField, PrimeField32};
use serde::{Deserialize, Serialize};
use strum::{EnumCount, EnumIter};

#[repr(u32)]
#[derive(
    Debug,
    Clone,
    Copy,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Serialize,
    Deserialize,
    FromPrimitive,
    EnumCount,
    EnumIter,
)]
pub enum Tag {
    U64 = 0,
    I64,
    I63, // OCaml ints
    Num,
    BigNum,
    Comm,
    Char,
    Str,
    Key,
    Fun,
    Builtin,
    Coroutine,
    Sym,
    Cons,
    Env,
    Fix,
    Err,
}

impl Tag {
    #[inline]
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    #[inline]
    pub fn from_field<F: PrimeField32>(f: &F) -> Tag {
        Tag::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a Tag")
    }
}

impl From<Tag> for i32 {
    fn from(item: Tag) -> Self {
        item as u32 as i32
    }
}

#[cfg(test)]
mod test {
    use crate::lurk::tag::Tag;
    use num_traits::FromPrimitive;
    use p3_baby_bear::BabyBear;
    use p3_field::PrimeField32;
    use strum::{EnumCount, IntoEnumIterator};

    #[test]
    fn test_strum() {
        assert_eq!(15, Tag::COUNT);
        assert_eq!(Tag::COUNT, Tag::iter().count());
    }

    #[test]
    fn test_tag_index_roundtrip() {
        for tag in Tag::iter() {
            let f = tag.to_field::<BabyBear>();
            let u = f.as_canonical_u32();
            assert_eq!(Some(tag), Tag::from_u32(u));
        }
    }
}
