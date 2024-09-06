use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_field::{AbstractField, PrimeField32};
use serde::{Deserialize, Serialize};

#[repr(u32)]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, FromPrimitive,
)]
pub enum Tag {
    U64 = 2, // 0 and 1 are reserved for nil and t inside the vm
    Num,
    BigNum,
    Comm,
    Char,
    Str,
    Key,
    Fun,
    Builtin,
    Sym,
    Cons,
    Env,
    Thunk,
    Err,
    Nil, // delete me
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

    pub fn count() -> usize {
        14
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

    #[test]
    fn test_tag_index_roundtrip() {
        for tag in [
            Tag::Cons,
            Tag::Sym,
            Tag::Fun,
            Tag::Num,
            Tag::Str,
            Tag::Char,
            Tag::Comm,
            Tag::U64,
            Tag::Key,
            Tag::Env,
            Tag::Err,
            Tag::Thunk,
            Tag::Builtin,
            Tag::BigNum,
        ] {
            let f = tag.to_field::<BabyBear>();
            let u = f.as_canonical_u32();
            assert_eq!(Some(tag), Tag::from_u32(u));
        }
    }
}
