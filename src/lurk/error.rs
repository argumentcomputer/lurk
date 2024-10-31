use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_field::{AbstractField, PrimeField32};

#[derive(Clone, Copy, FromPrimitive, Debug)]
#[repr(u32)]
pub enum EvalErr {
    UnboundVar = 0,
    InvalidForm,
    IllegalBindingVar,
    ApplyNonFunc,
    ParamsNotList,
    ParamNotSymbol,
    ParamInvalidRest,
    ArgsNotList,
    InvalidArg,
    DivByZero,
    NotEnv,
    NotChar,
    NotCons,
    NotString,
    NotInt,
    NotBigNum,
    CantOpen,
    CantCastToChar,
    CantCastToU64,
    CantCastToBigNum,
    CantCastToComm,
    Todo,
}

impl EvalErr {
    pub(crate) fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    pub(crate) fn from_field<F: PrimeField32>(f: &F) -> Self {
        Self::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a EvalErr")
    }
}
