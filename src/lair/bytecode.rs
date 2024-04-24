use super::{map::Map, Name};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    Const(F),
    Add(usize, usize),
    Sub(usize, usize),
    Mul(usize, usize),
    Div(usize, usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block<F> {
    pub ops: Vec<Op<F>>,
    pub ctrl: Ctrl<F>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ctrl<F> {
    Match(usize, Cases<F>),
    If(usize, Box<Block<F>>, Box<Block<F>>),
    Return(Vec<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<F> {
    pub branches: Map<F, Block<F>>,
    pub default: Option<Box<Block<F>>>,
}

impl<F: Ord> Cases<F> {
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
