use super::{map::Map, List, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Inv(usize),
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Func<F> {
    pub(crate) name: Name,
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) body: Block<F>,
}
