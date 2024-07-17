use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_field::{AbstractField, PrimeField32};
use serde::{Deserialize, Serialize};

#[repr(u32)]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, FromPrimitive,
)]
pub enum Tag {
    Nil = 0,
    Cons,
    Sym,
    Fun,
    Num,
    Str,
    Char,
    Comm,
    U64,
    Key,
    Env,
    Err,
    Thunk,
    Builtin,
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
