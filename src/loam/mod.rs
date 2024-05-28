mod allocation;
mod evaluation;

pub type LE = u32;

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub enum Tag {
    F,
    Cons,
    Sym,
    Cont,
    Err,
}

impl Tag {
    pub fn elt(&self) -> LE {
        match self {
            Self::F => 0,
            Self::Cons => 1,
            Self::Sym => 2,
            Self::Cont => 3,
            Self::Err => 4,
        }
    }

    pub fn wide(&self) -> Wide {
        Wide::widen(self.elt())
    }
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct F(pub LE);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct Ptr(pub LE, pub LE);

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

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct WidePtr(pub Wide, pub Wide);
