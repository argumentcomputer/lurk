//! Defines a frontend for Lair using named references for variables and functions.

use super::{map::Map, List, Name};

/// The type for variable references
#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Var(pub &'static str);

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Interface for basic Lair operations
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpE<F> {
    /// `Const(var, x)` binds `var` to the constant `x`
    Const(Var, F),
    /// `Add(x, y, z)` binds `x` to the sum of the bindings of `y` and `z`
    Add(Var, Var, Var),
    /// `Sub(x, y, z)` binds `x` to the subtraction of the bindings of `y` and `z`
    Sub(Var, Var, Var),
    /// `Mul(x, y, z)` binds `x` to the multiplication of the bindings of `y` and `z`
    Mul(Var, Var, Var),
    /// `Div(x, y, z)` binds `x` to the division of the bindings of `y` and `z`
    ///
    /// Note: it's compiled to the multiplication of `x` by the inverse of `z`
    Div(Var, Var, Var),
    /// `Inv(x, y)` binds `x` to the inversion of the binding of `y`
    Inv(Var, Var),
    /// `Call([x, ...], foo, [y, ...])` binds `x, ...` to the output of `foo`
    /// when applied to the arguments `y, ...`
    Call(List<Var>, Name, List<Var>),
    /// `Store(x, [y, ...])` binds `x` to a pointer to `[y, ...]`
    Store(Var, List<Var>),
    /// `Load([x, ...], y)` binds `[x, ...]` to the values that is pointed by `y`
    Load(List<Var>, Var),
}

/// A "code block" containing a sequence of operators and a control node to be
/// executed afterwards
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockE<F> {
    pub ops: List<OpE<F>>,
    pub ctrl: CtrlE<F>,
}

/// Encodes the logical flow of a Lair program
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CtrlE<F> {
    /// `Match(x, cases)` matches on `x` in order to decide which case to execute
    Match(Var, CasesE<F>),
    /// `If(b, t, f)` executes block `f` if `b` is zero and `t` otherwise
    If(Var, Box<BlockE<F>>, Box<BlockE<F>>),
    /// Contains the variables whose bindings will construct the output of the
    /// block
    Return(List<Var>),
}

/// Represents the cases for `CtrlE::Match`, containing the branches for successfull
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesE<F> {
    pub branches: Map<F, BlockE<F>>,
    pub default: Option<Box<BlockE<F>>>,
}

/// Abstraction for a Lair function, which has a name, the input variables, the
/// size (arity) of the output and, of course, its body (encoded as a block).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuncE<F> {
    pub name: Name,
    pub input_params: List<Var>,
    pub output_size: usize,
    pub body: BlockE<F>,
}
