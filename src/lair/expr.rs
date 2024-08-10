//! Defines a frontend for Lair using named references for variables and functions.

use super::{List, Name};

/// The type for variable references
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Var {
    pub name: &'static str,
    pub size: usize,
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", &self.name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VarList(List<Var>);

impl VarList {
    #[inline]
    pub fn total_size(&self) -> usize {
        self.0.iter().map(|var| var.size).sum()
    }

    #[inline]
    pub fn as_slice(&self) -> &[Var] {
        &self.0
    }

    #[inline]
    pub fn iter(&self) -> core::slice::Iter<'_, Var> {
        self.as_slice().iter()
    }
}

impl<const N: usize> From<[Var; N]> for VarList {
    fn from(value: [Var; N]) -> Self {
        Self(value.into())
    }
}

/// Interface for basic Lair operations
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpE<F> {
    /// `AssertEq(x, y)` makes sure `x` is equal to `y`
    AssertEq(Var, Var),
    /// `AssertNe(x, y)` makes sure `x` is unequal to `y`
    AssertNe(Var, Var),
    /// `Contains(x, y)` makes sure an array `x` contains the value `y`
    Contains(Var, Var),
    /// `Const(var, x)` binds `var` to the constant `x`
    Const(Var, F),
    /// `Array(var, arr)` binds `var` to the constant array `arr`
    Array(Var, List<F>),
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
    /// `Not(x, y)` binds `x` to `y == 0`
    Not(Var, Var),
    /// `Not(x, y, z)` binds `x` to `y == z`
    Eq(Var, Var, Var),
    /// `Call([x, ...], foo, [y, ...])` binds `x, ...` to the output of `foo`
    /// when applied to the arguments `y, ...`
    Call(VarList, Name, VarList),
    /// `PreImg([x, ...], foo, [y, ...])` binds `x, ...` to the latest preimage
    /// (beware of non-injectivity) of `foo` when called with arguments `y, ...`
    PreImg(VarList, Name, VarList),
    /// `Store(x, [y, ...])` binds `x` to a pointer to `[y, ...]`
    Store(Var, VarList),
    /// `Load([x, ...], y)` binds `[x, ...]` to the values that is pointed by `y`
    Load(VarList, Var),
    /// `Slice([x, ...], [y, ...])` matches the pattern `[x, ...]` against the values
    /// formed by `[y, ...]`
    Slice(VarList, VarList),
    /// `ExternCall([x, ...], foo, [y, ...])` binds `x, ...` to the output of extern
    /// chip `foo` when applied to the arguments `y, ...`
    ExternCall(VarList, Name, VarList),
    /// `Debug(s)` emits debug message `s`
    Debug(&'static str),
    Print(Var),
    /// `RangeU8([x, ...])` makes sure `[x, ...]` are all U8 elements
    RangeU8(VarList),
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
    /// `Match(x, cases)` matches on `x` in order to decide which case to execute.
    /// The list collects all the values that map to the same branch
    Match(Var, CasesE<List<F>, F>),
    /// `MatchMany(x, cases)` matches on array `x` in order to decide which case to execute
    MatchMany(Var, CasesE<List<F>, F>),
    /// `If(b, t, f)` executes block `f` if `b` is zero and `t` otherwise
    If(Var, Box<BlockE<F>>, Box<BlockE<F>>),
    /// Contains the variables whose bindings will construct the output of the
    /// block
    Return(VarList),
}

/// Represents the cases for `CtrlE::Match`, containing the branches for successfull
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesE<K, F> {
    pub branches: Vec<(K, BlockE<F>)>,
    pub default: Option<Box<BlockE<F>>>,
}

/// Abstraction for a Lair function, which has a name, the input variables, the
/// size (arity) of the output and, of course, its body (encoded as a block).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuncE<F> {
    pub name: Name,
    pub invertible: bool,
    pub input_params: VarList,
    pub output_size: usize,
    pub body: BlockE<F>,
}
