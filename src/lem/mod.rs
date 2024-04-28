pub mod bytecode;
pub mod execute;
pub mod expr;
mod macros;
pub mod map;
pub mod toplevel;
pub mod trace;

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Name(pub &'static str);

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[inline]
#[allow(dead_code)]
pub(crate) fn field_from_i32<F: p3_field::AbstractField>(i: i32) -> F {
    if i < 0 {
        -F::from_canonical_u32((-i).try_into().unwrap())
    } else {
        F::from_canonical_u32(i.try_into().unwrap())
    }
}

pub type List<T> = Box<[T]>;

pub type Limb<C, V> = (C, List<V>);
