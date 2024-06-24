use p3_field::AbstractField;

pub const EXPR_TAG_INIT: u16 = 0b0000_0000_0000_0000;

#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tag {
    Nil = EXPR_TAG_INIT,
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
