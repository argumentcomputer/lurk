use super::{map::Map, Name};

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Var(pub &'static str);

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpE<F> {
    Const(Var, F),
    Add(Var, Var, Var),
    Sub(Var, Var, Var),
    Mul(Var, Var, Var),
    Div(Var, Var, Var),
    Call(Vec<Var>, Name, Vec<Var>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockE<F> {
    pub ops: Vec<OpE<F>>,
    pub ctrl: CtrlE<F>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CtrlE<F> {
    Match(Var, CasesE<F>),
    If(Var, Box<BlockE<F>>, Box<BlockE<F>>),
    Return(Vec<Var>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesE<F> {
    pub branches: Map<F, BlockE<F>>,
    pub default: Option<Box<BlockE<F>>>,
}

impl<F: Ord> CasesE<F> {
    pub fn match_case(&self, f: &F) -> Option<&BlockE<F>> {
        self.branches.get(f).or(self.default.as_deref())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuncE<F> {
    pub name: Name,
    pub input_params: Vec<Var>,
    pub output_size: usize,
    pub body: BlockE<F>,
}
