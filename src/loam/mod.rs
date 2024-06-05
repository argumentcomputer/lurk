use std::cmp::Ordering;

use ascent::Lattice;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField32};

mod allocation;
mod evaluation;

use allocation::allocator;

pub type LE = BabyBear;

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Tag {
    F,
    Cons,
    Nil,
    Sym,
    Fun,
    Err,
}

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
    fn meet(self, other: Self) -> Self {
        self.min(other)
    }
    fn join(self, other: Self) -> Self {
        self.max(other)
    }
}

trait Elemental {
    fn elt(&self) -> LE;
}

trait Valuable {
    fn value(&self) -> Wide;
}

trait Tagged {
    fn tag(&self) -> Tag;
}

impl<T: Elemental> Valuable for T {
    fn value(&self) -> Wide {
        Wide::widen(self.elt())
    }
}

impl Elemental for Tag {
    fn elt(&self) -> LE {
        LE::from_canonical_u32(match self {
            Self::F => 0,
            Self::Cons => 1,
            Self::Nil => 2,
            Self::Sym => 3,
            Self::Fun => 4,
            Self::Err => 5,
        })
    }
}

impl Tag {
    pub fn tag_wide_relation() -> Vec<(LE, Wide)> {
        (0..=4)
            .map(|i| {
                let tag = Tag::from(i);
                (tag.elt(), tag.value())
            })
            .collect()
    }
}

impl From<usize> for Tag {
    fn from(n: usize) -> Self {
        [Self::F, Self::Cons, Self::Nil, Self::Sym, Self::Err][n]
    }
}

impl From<&F> for Tag {
    fn from(f: &F) -> Self {
        Self::F
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct F(pub LE);

impl Elemental for F {
    fn elt(&self) -> LE {
        self.0
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Ptr(pub LE, pub LE);

impl Ptr {
    fn nil() -> Self {
        Self(Tag::Nil.elt(), LE::from_canonical_u32(0))
    }
    fn f(val: LE) -> Self {
        Self(Tag::F.elt(), val)
    }
    fn is_f(&self) -> bool {
        self.0 == Tag::F.elt()
    }
    fn is_cons(&self) -> bool {
        self.0 == Tag::Cons.elt()
    }
    fn is_nil(&self) -> bool {
        self.0 == Tag::Nil.elt()
    }
    fn is_sym(&self) -> bool {
        self.0 == Tag::Sym.elt()
    }
    fn is_fun(&self) -> bool {
        self.0 == Tag::Fun.elt()
    }
    fn is_err(&self) -> bool {
        self.0 == Tag::Err.elt()
    }
}

impl From<&F> for Ptr {
    fn from(f: &F) -> Self {
        Self(Tag::F.elt(), f.0)
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
}

impl From<&F> for Wide {
    fn from(f: &F) -> Self {
        Wide::widen(f.0)
    }
}
impl From<F> for Wide {
    fn from(f: F) -> Self {
        (&f).into()
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct WidePtr(pub Wide, pub Wide);

impl WidePtr {
    fn nil() -> Self {
        Self(Tag::Nil.value(), Wide::widen(LE::from_canonical_u32(0)))
    }
}

impl From<&F> for WidePtr {
    fn from(f: &F) -> Self {
        WidePtr(Tag::F.value(), f.into())
    }
}

impl From<F> for WidePtr {
    fn from(f: F) -> Self {
        (&f).into()
    }
}

impl<T: Valuable + Tagged> From<&T> for WidePtr {
    fn from(t: &T) -> Self {
        Self(t.tag().value(), t.value())
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Sym {
    Char(char),
    Opaque(Wide),
}

const BUILT_IN_CHAR_SYMS: [char; 6] = ['+', '-', '*', '/', 'l', 'f'];

impl Sym {
    fn built_in() -> Vec<Self> {
        BUILT_IN_CHAR_SYMS.iter().map(|c| Self::Char(*c)).collect()
    }

    fn built_in_count() -> usize {
        BUILT_IN_CHAR_SYMS.len()
    }
}

impl Valuable for Sym {
    fn value(&self) -> Wide {
        match self {
            Self::Char(char) => Wide::widen(LE::from_canonical_u32((*char).into())),
            Self::Opaque(value) => *value,
        }
    }
}

impl Tagged for Sym {
    fn tag(&self) -> Tag {
        Tag::Sym
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Cons {
    car: WidePtr,
    cdr: WidePtr,
}

impl Valuable for Cons {
    // Morally, this should need to take an Allocator argument, so this trait structure will need to be reworked when
    // Allocator becomes explicit.
    fn value(&self) -> Wide {
        allocator().hash4(self.car.0, self.car.1, self.cdr.0, self.cdr.1)
    }
}

impl Tagged for Cons {
    fn tag(&self) -> Tag {
        Tag::Cons
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Sexp {
    F(F),
    Sym(Sym),
    Cons(Cons),
    Nil,
}

impl Sexp {
    pub fn sym(c: char) -> Self {
        Self::Sym(Sym::Char(c))
    }
    pub fn f(f: LE) -> Self {
        Self::F(F(f))
    }

    pub fn list(elts: Vec<Sexp>) -> Self {
        Self::Cons(Cons::list_x(elts))
    }

    pub fn car(&self) -> Option<WidePtr> {
        match self {
            Self::Cons(cons) => Some(cons.car),
            _ => None,
        }
    }
    pub fn cdr(&self) -> Option<WidePtr> {
        match self {
            Self::Cons(cons) => Some(cons.cdr),
            _ => None,
        }
    }
}

impl Valuable for Sexp {
    fn value(&self) -> Wide {
        match self {
            Self::F(f) => f.value(),
            Self::Sym(sym) => sym.value(),
            Self::Cons(cons) => cons.value(),
            Self::Nil => Wide::widen(LE::from_canonical_u32(0)),
        }
    }
}

impl Tagged for Sexp {
    fn tag(&self) -> Tag {
        match self {
            Self::F(f) => Tag::F,
            Self::Sym(sym) => Tag::Sym,
            Self::Cons(cons) => Tag::Cons,
            Self::Nil => Tag::Nil,
        }
    }
}

impl Cons {
    fn bind(var: WidePtr, val: WidePtr, env: WidePtr) -> WidePtr {
        let binding = Cons { car: var, cdr: val };
        WidePtr::from(&Cons {
            car: WidePtr::from(&binding),
            cdr: env,
        })
    }

    fn list(elts: Vec<Sexp>) -> WidePtr {
        elts.iter().rev().fold(WidePtr::nil(), |acc, elt| {
            WidePtr::from(&Cons {
                car: WidePtr::from(elt),
                cdr: acc,
            })
        })
    }

    fn list_x(elts: Vec<Sexp>) -> Self {
        let mut result = None;
        elts.iter().rev().fold(WidePtr::nil(), |acc, elt| {
            result = Some(Cons {
                car: WidePtr::from(elt),
                cdr: acc,
            });
            WidePtr::from(&result.unwrap().clone())
        });
        result.unwrap()
    }
}

pub struct TypeError {}

impl TryFrom<WidePtr> for Cons {
    type Error = TypeError;

    fn try_from(p: WidePtr) -> Result<Self, Self::Error> {
        if p.0 == Tag::Cons.value() {
            if let Some([car_tag, car_value, cdr_tag, cdr_value]) = allocator().unhash4(&p.1) {
                Ok(Cons {
                    car: WidePtr(car_tag, car_value),
                    cdr: WidePtr(cdr_tag, cdr_value),
                })
            } else {
                Err(TypeError {})
            }
        } else {
            Err(TypeError {})
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cons_list() {
        let l = Cons::list(vec![
            Sexp::Sym(Sym::Char('+')),
            Sexp::F(F(LE::from_canonical_u32(1))),
            Sexp::F(F(LE::from_canonical_u32(2))),
        ]);

        assert_eq!(
            WidePtr(
                Wide([
                    LE::one(),
                    LE::zero(),
                    LE::zero(),
                    LE::zero(),
                    LE::zero(),
                    LE::zero(),
                    LE::zero(),
                    LE::zero(),
                ]),
                Wide([
                    LE::from_canonical_u32(1317489235),
                    LE::from_canonical_u32(988355858),
                    LE::from_canonical_u32(377021789),
                    LE::from_canonical_u32(1625298703),
                    LE::from_canonical_u32(1385378477),
                    LE::from_canonical_u32(297630406),
                    LE::from_canonical_u32(739282074),
                    LE::from_canonical_u32(37715763)
                ]),
            ),
            l
        );
    }
}
