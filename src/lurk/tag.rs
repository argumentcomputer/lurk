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
        13
    }
}

impl TryFrom<usize> for Tag {
    type Error = &'static str;

    fn try_from(n: usize) -> Result<Self, Self::Error> {
        match n {
            0 => Ok(Self::Nil),
            1 => Ok(Self::Cons),
            2 => Ok(Self::Sym),
            3 => Ok(Self::Fun),
            4 => Ok(Self::Num),
            5 => Ok(Self::Str),
            6 => Ok(Self::Char),
            7 => Ok(Self::Comm),
            8 => Ok(Self::U64),
            9 => Ok(Self::Key),
            10 => Ok(Self::Env),
            11 => Ok(Self::Err),
            12 => Ok(Self::Thunk),
            13 => Ok(Self::Builtin),
            _ => Err("invalid tag index"),
        }
    }
}
