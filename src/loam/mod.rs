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

/// TODO: Figure out how to organize the relationships between the types here correctly.
/// Also is this even needed if there's going to be exactly one Loam program? (Maybe that's wrong.)
trait LoamProgram {
    fn allocator(&self) -> &Allocator;
    fn allocator_mut(&mut self) -> &mut Allocator;
    fn zstore(&self) -> &ZStore<LE, LurkChip>;
    fn zstore_mut(&mut self) -> &mut ZStore<LE, LurkChip>;

    fn ptr_value(&self) -> &Vec<(Ptr, Wide)>;
    fn cons_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)>;
    fn fun_rel(&self) -> &Vec<(Ptr, Ptr, Ptr, Ptr)>;
    fn thunk_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)>;
    fn num_mem(&self) -> &Vec<(Ptr,)>;

    fn alloc_addr(&mut self, tag: LE, initial_addr: LE) -> LE {
        self.allocator_mut().alloc_addr(tag, initial_addr)
    }

    fn unhash4(&mut self, tag: LE, digest: Wide) -> [Wide; 4] {
        let zptr = ZPtr {
            tag: Tag::from_field(&tag),
            digest: digest.0,
        };
        let (a, b) = self.zstore_mut().fetch_tuple2(&zptr);
        [
            Wide::widen(a.tag.elt()),
            Wide(a.digest),
            Wide::widen(b.tag.elt()),
            Wide(b.digest),
        ]
    }

    fn hash4(&mut self, tag: LE, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        let a_zptr = ZPtr {
            tag: Tag::from_field(&a.f()),
            digest: b.0,
        };
        let b_zptr = ZPtr {
            tag: Tag::from_field(&c.f()),
            digest: d.0,
        };
        let zptr = self
            .zstore_mut()
            .intern_tuple2(Tag::from_field(&tag), a_zptr, b_zptr);
        Wide(zptr.digest)
    }

    fn unhash6(&mut self, tag: LE, digest: Wide) -> [Wide; 6] {
        let zptr = ZPtr {
            tag: Tag::from_field(&tag),
            digest: digest.0,
        };
        let (a, b, c) = self.zstore_mut().fetch_tuple3(&zptr);
        [
            a.tag.value(),
            Wide(a.digest),
            b.tag.value(),
            Wide(b.digest),
            c.tag.value(),
            Wide(c.digest),
        ]
    }

    fn hash6(&mut self, tag: LE, a: Wide, b: Wide, c: Wide, d: Wide, e: Wide, f: Wide) -> Wide {
        let a_zptr = ZPtr {
            tag: Tag::from_field(&a.f()),
            digest: b.0,
        };
        let b_zptr = ZPtr {
            tag: Tag::from_field(&c.f()),
            digest: d.0,
        };
        let c_zptr = ZPtr {
            tag: Tag::from_field(&e.f()),
            digest: f.0,
        };
        let zptr = self
            .zstore_mut()
            .intern_tuple3(Tag::from_field(&tag), a_zptr, b_zptr, c_zptr);
        Wide(zptr.digest)
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

        let num_mem = self.num_mem().iter().map(|(num,)| (VPtr(*num),)).collect();

        VirtualMemory {
            ptr_value,
            cons_mem,
            fun_mem,
            thunk_mem,
            num_mem,
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
