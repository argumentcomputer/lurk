mod allocation;
mod evaluation;

use allocation::allocator;

pub type LE = u32;

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Tag {
    F,
    Cons,
    Nil,
    Sym,
    Err,
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
        match self {
            Self::F => 0,
            Self::Cons => 1,
            Self::Nil => 2,
            Self::Sym => 3,
            Self::Err => 4,
        }
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
        Self(Tag::Nil.elt(), 0)
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
    pub const fn widen(elt: LE) -> Wide {
        let mut v = [0u32; 8];
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
        Self(Tag::Nil.value(), Wide::widen(0))
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

const BUILT_IN_CHAR_SYMS: [char; 4] = ['+', '-', '*', '/'];

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
            Self::Char(char) => Wide::widen((*char).into()),
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
}

impl Valuable for Sexp {
    fn value(&self) -> Wide {
        match self {
            Self::F(f) => f.value(),
            Self::Sym(sym) => sym.value(),
            Self::Cons(cons) => cons.value(),
            Self::Nil => Wide::widen(0),
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
            Sexp::F(F(1)),
            Sexp::F(F(2)),
        ]);

        assert_eq!(
            WidePtr(
                Wide([1, 0, 0, 0, 0, 0, 0, 0]),
                Wide([
                    3864046529, 430932103, 4182774374, 1056266594, 3890674019, 2613686248,
                    848015655, 4249421387
                ])
            ),
            l
        );
    }
}
