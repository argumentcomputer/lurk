// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]
use std::cmp::Ordering;

use allocation::Allocator;
use ascent::Lattice;
use memory::{Memory, VPtr, VirtualMemory};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField32};
use rustc_hash::FxHashMap;

use crate::lurk::chipset::LurkChip;
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

    /// make this const
    fn buitin(op: &str) -> Self {
        let addr = lurk_sym_index(op).unwrap();
        Self(Tag::Builtin.elt(), LE::from_canonical_u32(addr as u32))
    }

    /// make this const
    fn t() -> Self {
        Self::buitin("t")
    }

    /// make this const
    fn eq() -> Self {
        Self::buitin("eq")
    }

    /// make this const
    fn cons() -> Self {
        Self::buitin("cons")
    }

    /// make this const
    fn car() -> Self {
        Self::buitin("car")
    }

    /// make this const
    fn cdr() -> Self {
        Self::buitin("cdr")
    }

    /// make this const
    fn quote() -> Self {
        Self::buitin("quote")
    }

    /// make this const
    fn atom() -> Self {
        Self::buitin("atom")
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
            match self.tag() {
                // unless the pointers are immediate values
                Tag::Num | Tag::Err => {
                    if self.1 == other.1 {
                        PtrEq::Equal
                    } else {
                        PtrEq::NotEqual
                    }
                }
                _ => PtrEq::DontKnow,
            }
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

    fn tag(&self) -> Tag {
        Tag::from_field(&self.0.f())
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

/// TODO: Figure out how to organize the relationships between the types here correctly.
/// Also is this even needed if there's going to be exactly one Loam program? (Maybe that's wrong.)
trait LoamProgram {
    fn allocator(&self) -> &Allocator;
    fn allocator_mut(&mut self) -> &mut Allocator;

    fn ptr_value(&self) -> &Vec<(Ptr, Wide)>;
    fn cons_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)>;
    fn fun_rel(&self) -> &Vec<(Ptr, Ptr, Ptr, Ptr)>;
    fn thunk_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)>;

    fn alloc_addr(&mut self, tag: LE, initial_addr: LE) -> LE {
        self.allocator_mut().alloc_addr(tag, initial_addr)
    }

    fn import_zstore(&mut self, zstore: &ZStore<LE, LurkChip>) {
        self.allocator_mut().import_zstore(zstore)
    }

    fn unhash4(&mut self, digest: &Wide) -> [Wide; 4] {
        self.allocator_mut().unhash4(digest)
    }

    fn hash4(&mut self, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        self.allocator_mut().hash4(a, b, c, d)
    }

    fn unhash6(&mut self, digest: &Wide) -> [Wide; 6] {
        self.allocator_mut().unhash6(digest)
    }

    fn hash6(&mut self, a: Wide, b: Wide, c: Wide, d: Wide, e: Wide, f: Wide) -> Wide {
        self.allocator_mut().hash6(a, b, c, d, e, f)
    }

    fn export_memory(&self) -> VirtualMemory {
        let ptr_value = self
            .ptr_value()
            .iter()
            .map(|(ptr, wide)| (VPtr(*ptr), *wide))
            .collect();

        let cons_mem = self
            .cons_rel()
            .iter()
            .map(|(car, cdr, cons)| (VPtr(*cons), (VPtr(*car), VPtr(*cdr))))
            .collect();
        let fun_mem = self
            .fun_rel()
            .iter()
            .map(|(args, body, closed_env, fun)| {
                (VPtr(*fun), (VPtr(*args), VPtr(*body), VPtr(*closed_env)))
            })
            .collect();
        let thunk_mem = self
            .thunk_rel()
            .iter()
            .map(|(body, closed_env, thunk)| (VPtr(*thunk), (VPtr(*body), VPtr(*closed_env))))
            .collect();

        VirtualMemory {
            ptr_value,
            cons_mem,
            fun_mem,
            thunk_mem,
        }
    }
}

// TODO: This can use a hashtable lookup, or could even be known at compile-time (but how to make that non-brittle since iter() is not const?).
pub(crate) fn lurk_sym_index(name: &str) -> Option<usize> {
    LURK_PACKAGE_SYMBOLS_NAMES
        .iter()
        .filter(|name| **name != "nil")
        .position(|s| *s == name)
}
