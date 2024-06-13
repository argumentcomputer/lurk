use p3_field::AbstractField;
use serde::{Deserialize, Serialize};

#[repr(u32)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
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
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u16(self as u16)
    }
}
