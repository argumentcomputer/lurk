use p3_field::Field;

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

#[allow(dead_code)]
pub(crate) fn field_from_u32<F: Field>(f: u32) -> F {
    F::from_canonical_u32(f)
}

pub type List<T> = Box<[T]>;
