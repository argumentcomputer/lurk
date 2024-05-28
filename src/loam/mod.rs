mod allocation;
mod evaluation;

pub type LE = u32;

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Tag {
    F,
    Cons,
    Nil,
    Sym,
    Cont,
    Err,
}

trait Elemental {
    fn elt(&self) -> LE;

    fn wide(&self) -> Wide {
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
            Self::Cont => 4,
            Self::Err => 5,
        }
    }
}

impl Tag {
    pub fn tag_wide_relation() -> Vec<(LE, Wide)> {
        (0..=5)
            .map(|i| {
                let tag = Tag::from(i);
                (tag.elt(), tag.wide())
            })
            .collect()
    }
}

impl From<usize> for Tag {
    fn from(n: usize) -> Self {
        [
            Self::F,
            Self::Cons,
            Self::Nil,
            Self::Sym,
            Self::Cont,
            Self::Err,
        ][n]
    }
}

impl From<&F> for Tag {
    fn from(f: &F) -> Self {
        Self::F
    }
}

impl From<&Cont> for Tag {
    fn from(cont: &Cont) -> Self {
        Self::Cont
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct F(pub LE);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Ptr(pub LE, pub LE);

impl Ptr {
    fn nil() -> Self {
        Self(Tag::Nil.elt(), 0)
    }
    fn f(val: LE) -> Self {
        Self(Tag::F.elt(), val)
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

impl From<Cont> for Wide {
    fn from(cont: Cont) -> Self {
        (&cont).into()
    }
}
impl From<&Cont> for Wide {
    fn from(cont: &Cont) -> Self {
        let simple = match cont {
            Cont::Outermost => 0,
            Cont::Terminal => 1,
            Cont::Error => 2,
        };
        Wide::widen(simple)
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct WidePtr(pub Wide, pub Wide);

impl WidePtr {
    fn nil() -> Self {
        Self(Tag::Nil.wide(), Wide::widen(0))
    }
}

impl From<&F> for WidePtr {
    fn from(f: &F) -> Self {
        WidePtr(Tag::F.wide(), f.into())
    }
}

impl From<F> for WidePtr {
    fn from(f: F) -> Self {
        (&f).into()
    }
}

impl From<&Cont> for WidePtr {
    fn from(cont: &Cont) -> Self {
        WidePtr(Tag::Cont.wide(), cont.wide())
    }
}

impl From<Cont> for WidePtr {
    fn from(cont: Cont) -> Self {
        (&cont).into()
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Cont {
    Outermost,
    Terminal,
    Error,
}

impl Elemental for Cont {
    fn elt(&self) -> LE {
        match self {
            Self::Outermost => 0,
            Self::Terminal => 1,
            Self::Error => 2,
        }
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct CEK<T> {
    expr: T,
    env: T,
    cont: T, // for simplicity, let continuations be first-class data. make it an error to evaluate one, though.
}

pub enum Sym {
    Char(char),
}

impl Elemental for Sym {
    fn elt(&self) -> LE {
        match self {
            Self::Char(char) => (*char).into(),
        }
    }
}
