use super::{map::Map, Limb, List, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Inv(usize),
    Pol(List<Limb<F, usize>>),
    // index, arguments
    // u32 is used here to reduce the size of Op<F> on 64 bit machines
    Call(u32, List<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block<F> {
    pub ops: List<Op<F>>,
    pub ctrl: Ctrl<F>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ctrl<F> {
    Match(usize, Cases<F>),
    If(usize, Box<Block<F>>, Box<Block<F>>),
    Return(List<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<F> {
    pub branches: Map<F, Block<F>>,
    pub default: Option<Box<Block<F>>>,
}

impl<F: Ord> Cases<F> {
    #[inline]
    pub fn match_case(&self, f: &F) -> Option<&Block<F>> {
        self.branches.get(f).or(self.default.as_deref())
    }

    pub fn get_index(&self, idx: usize) -> Option<&Block<F>> {
        if let Some((_, b)) = self.branches.get_index(idx) {
            Some(b)
        } else {
            self.default.as_deref()
        }
    }

    pub fn get_index_of(&self, f: &F) -> Option<usize> {
        self.branches
            .get_index_of(f)
            .or_else(|| self.default.as_ref().map(|_| self.branches.size()))
    }

    pub fn default_index(&self) -> usize {
        self.branches.size()
    }
}

impl<F> Cases<F> {
    pub fn size(&self) -> usize {
        let inc = if self.default.is_some() { 1 } else { 0 };
        self.branches.size() + inc
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Func<F> {
    pub(crate) name: Name,
    pub(crate) index: usize,
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) body: Block<F>,
}
