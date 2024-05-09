use super::{map::Map, List, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Inv(usize),
    // index, arguments
    Call(usize, List<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block<F> {
    pub(crate) ops: List<Op<F>>,
    pub(crate) ctrl: Ctrl<F>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ctrl<F> {
    Match(usize, Cases<F>),
    If(usize, Box<Block<F>>, Box<Block<F>>),
    // a unique return identifier, for selectors
    Return(usize, List<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<F> {
    pub(crate) branches: Map<F, Block<F>>,
    pub(crate) default: Option<Box<Block<F>>>,
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

impl<F: Ord> Func<F> {
    #[inline]
    pub fn name(&self) -> Name {
        self.name
    }

    #[inline]
    pub fn body(&self) -> &Block<F> {
        &self.body
    }

    #[inline]
    pub fn input_size(&self) -> usize {
        self.input_size
    }

    #[inline]
    pub fn output_size(&self) -> usize {
        self.output_size
    }
}
