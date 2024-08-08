// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]
use std::cmp::Ordering;

use ascent::Lattice;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField32};

use crate::lurk::state::LURK_PACKAGE_SYMBOLS_NAMES;
use crate::lurk::tag::Tag;
use crate::lurk::zstore::{self, lurk_zstore, ZPtr, ZStore};

mod allocation;
mod distilled_evaluation;
mod evaluation;
mod memory;

pub type LE = BabyBear;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Num(LE);

#[derive(Clone, Copy, Debug, Ord, PartialEq, Eq, Hash)]
struct LEWrap(LE);

impl PartialOrd for LEWrap {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0
            .as_canonical_u32()
            .partial_cmp(&other.0.as_canonical_u32())
    }
}

impl Lattice for LEWrap {
    fn meet_mut(&mut self, other: Self) -> bool {
        let changed = *self > other;
        if changed {
            *self = other;
        }
        changed
    }
    fn join_mut(&mut self, other: Self) -> bool {
        let changed = *self < other;
        if changed {
            *self = other;
        }
        changed
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Ptr(pub LE, pub LE);

impl Ptr {
    fn nil() -> Self {
        // nil is zeroth element in the nil-typed table.
        Self(Tag::Nil.elt(), LE::from_canonical_u32(0))
    }

    fn t() -> Self {
        let addr = lurk_sym_index("t").unwrap();
        Self(Tag::Builtin.elt(), LE::from_canonical_u32(addr as u32))
    }

    fn f(val: LE) -> Self {
        Self(Tag::Num.elt(), val)
    }
    fn is_num(&self) -> bool {
        self.0 == Tag::Num.elt()
    }
    fn is_cons(&self) -> bool {
        self.0 == Tag::Cons.elt()
    }
    fn is_nil(&self) -> bool {
        // TODO: should we also check value?
        self.0 == Tag::Nil.elt()
    }
    fn is_sym(&self) -> bool {
        self.0 == Tag::Sym.elt()
    }

    fn is_builtin(&self) -> bool {
        self.0 == Tag::Builtin.elt()
    }

    fn is_fun(&self) -> bool {
        self.0 == Tag::Fun.elt()
    }
    fn is_thunk(&self) -> bool {
        self.0 == Tag::Thunk.elt()
    }
    fn is_err(&self) -> bool {
        self.0 == Tag::Err.elt()
    }

    pub fn tag(&self) -> Tag {
        Tag::from_field(&self.0)
    }

    pub fn wide_tag(&self) -> Wide {
        Wide::widen(self.0)
    }

    pub fn is_eq(&self, other: &Ptr) -> PtrEq {
        if self == other {
            // The pointers are actually equal
            PtrEq::Equal
        } else if self.tag() != other.tag() {
            // The pointers' tags are not equal, and thus the pointers must not be equal
            PtrEq::NotEqual
        } else {
            // The pointers' addresses are not equal, must check for deep equality
            PtrEq::DontKnow
        }
    }
}

/// Possible ways two pointer can be "equal" to each other
#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum PtrEq {
    Equal = 0,
    NotEqual,
    DontKnow,
}

impl Lattice for PtrEq {
    fn meet_mut(&mut self, other: Self) -> bool {
        let changed = *self > other;
        if changed {
            *self = other;
        }
        changed
    }
    fn join_mut(&mut self, other: Self) -> bool {
        let changed = *self < other;
        if changed {
            *self = other;
        }
        changed
    }
}


#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Wide(pub [LE; 8]);

impl Wide {
    pub fn widen(elt: LE) -> Self {
        let mut v = [LE::zero(); 8];
        v[0] = elt;
        Wide(v)
    }

    pub fn f(&self) -> LE {
        //        assert_eq!(&[0, 0, 0, 0, 0, 0, 0], &self.0[1..]);
        self.0[0]
    }

    pub fn from_slice(elts: &[LE]) -> Self {
        let mut v = [LE::zero(); 8];
        v.copy_from_slice(elts);
        Wide(v)
    }
}

impl From<&Num> for Wide {
    fn from(f: &Num) -> Self {
        Wide::widen(f.0)
    }
}
impl From<Num> for Wide {
    fn from(f: Num) -> Self {
        (&f).into()
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct WidePtr(pub Wide, pub Wide);

impl WidePtr {
    fn nil() -> Self {
        // FIXME: cache, don't do expensive read repeatedly.
        let zstore = &mut lurk_zstore();
        let ZPtr { tag, digest } = zstore.intern_nil();
        Self(Wide::widen(tag.elt()), Wide(digest))
    }

    fn empty_env() -> Self {
        Self::nil()
    }

    fn to_zptr(&self) -> ZPtr<LE> {
        ZPtr {
            tag: Tag::from_field(&self.0.f()),
            digest: self.1 .0,
        }
    }
}

impl From<&Num> for WidePtr {
    fn from(f: &Num) -> Self {
        WidePtr(Tag::Num.value(), f.into())
    }
}

impl From<Num> for WidePtr {
    fn from(f: Num) -> Self {
        (&f).into()
    }
}

// TODO: This can use a hashtable lookup, or could even be known at compile-time (but how to make that non-brittle since iter() is not const?).
pub(crate) fn lurk_sym_index(name: &str) -> Option<usize> {
    LURK_PACKAGE_SYMBOLS_NAMES
        .iter()
        .filter(|name| **name != "nil")
        .position(|s| *s == name)
}
