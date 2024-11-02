//! Lair's IR, which uses named references for variables and functions.

use std::fmt::Debug;

use itertools::Itertools;

use super::{List, Name};

/// The type for variable references
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Var {
    pub name: Ident,
    pub size: usize,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub enum Ident {
    User(&'static str),
    Internal(usize),
}

impl Var {
    pub fn atom(name: &'static str) -> Self {
        Self {
            name: Ident::User(name),
            size: 1,
        }
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.size == 1 {
            write!(f, "{}", self.name)
        } else {
            write!(f, "{}: [{}]", self.name, self.size)
        }
    }
}

impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ident::User(n) => write!(f, "{}", n),
            Ident::Internal(n) => write!(f, "${}", n),
        }
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

    fn var_list_str(&self) -> String {
        self.iter().map(|v| format!("{v}")).join(", ")
    }
}

impl std::fmt::Display for VarList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = self.var_list_str();
        if self.as_slice().len() == 1 {
            write!(f, "{}", s)
        } else {
            write!(f, "({})", s)
        }
    }
}

impl<const N: usize> From<[Var; N]> for VarList {
    fn from(value: [Var; N]) -> Self {
        Self(value.into())
    }
}

impl From<Vec<Var>> for VarList {
    fn from(value: Vec<Var>) -> Self {
        Self(value.into())
    }
}

/// Interface for basic Lair operations
#[allow(clippy::type_complexity)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum OpE<F> {
    /// `AssertEq(x, y, fmt)` makes sure `x` is equal to `y`. If `fmt` is `Some`,
    /// use it to format an error message and bail at runtime instead of panicking
    /// when `x` is not equal to `y`
    AssertEq(Var, Var, Option<fn(&[F], &[F]) -> String>),
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
    /// `PreImg([x, ...], foo, [y, ...], fmt)` binds `x, ...` to the latest preimage
    /// (beware of non-injectivity) of `foo` when called with arguments `y, ...`.
    /// If `fmt` is `Some`, use it to format an error message and bail at runtime
    /// instead of panicking when the preimage is not available
    PreImg(VarList, Name, VarList, Option<fn(&[F]) -> String>),
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
    /// `Emit([x, ...])` pushes `x, ...` to `QueryRecord::emitted` during execution
    Emit(VarList),
    /// `RangeU8([x, ...])` makes sure `[x, ...]` are all U8 elements
    RangeU8(VarList),
    /// `Breakpoint` adds a breakpoint mark in the debug trace
    Breakpoint,
    /// `Debug(s)` emits debug message `s`
    Debug(&'static str),
}

/// A "code block" containing a sequence of operators and a control node to be
/// executed afterwards
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BlockE<F> {
    pub ops: List<OpE<F>>,
    pub ctrl: CtrlE<F>,
}

impl<F> BlockE<F> {
    #[inline]
    pub fn no_op(ctrl: CtrlE<F>) -> Self {
        Self {
            ops: [].into(),
            ctrl,
        }
    }
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

impl<F> CtrlE<F> {
    #[inline]
    pub fn return_vars<const N: usize>(vars: [Var; N]) -> Self {
        Self::Return(vars.into())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum CaseType {
    Constrained,
    Unconstrained,
}

/// Represents the cases for `CtrlE::Match`, containing the branches for successful
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CasesE<K, F> {
    pub branches: Vec<(K, BlockE<F>, CaseType)>,
    pub default: Option<(Box<BlockE<F>>, CaseType)>,
}

impl<K, F> CasesE<K, F> {
    #[inline]
    pub fn no_default(branches: Vec<(K, BlockE<F>, CaseType)>) -> Self {
        Self {
            branches,
            default: None,
        }
    }
}

/// Abstraction for a Lair function, which has a name, the input variables, the
/// size (arity) of the output and, of course, its body (encoded as a block).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FuncE<F> {
    pub name: Name,
    pub invertible: bool,
    pub partial: bool,
    pub input_params: VarList,
    pub output_size: usize,
    pub body: BlockE<F>,
}

impl<F: Debug> OpE<F> {
    pub fn pretty(&self) -> String {
        match self {
            OpE::AssertEq(x, y, _) => {
                format!("assert_eq!({x}, {y})")
            }
            OpE::AssertNe(x, y) => {
                format!("assert_ne!({x}, {y})")
            }
            OpE::Contains(x, y) => {
                format!("contains!({x}, {y})")
            }
            OpE::Const(x, c) => {
                format!("let {x} = {:?};", c)
            }
            OpE::Array(x, cs) => {
                format!("let {x} = Array({:?});", cs)
            }
            OpE::Add(x, y, z) => {
                format!("let {x} = add({y}, {z});")
            }
            OpE::Sub(x, y, z) => {
                format!("let {x} = sub({y}, {z});")
            }
            OpE::Mul(x, y, z) => {
                format!("let {x} = mul({y}, {z});")
            }
            OpE::Div(x, y, z) => {
                format!("let {x} = div({y}, {z});")
            }
            OpE::Inv(x, y) => {
                format!("let {x} = inv({y});")
            }
            OpE::Not(x, y) => {
                format!("let {x} = not({y});")
            }
            OpE::Eq(x, y, z) => {
                format!("let {x} = eq({y}, {z});")
            }
            OpE::Call(xs, n, ys) => {
                format!("let {xs} = call({n}, {});", ys.var_list_str())
            }
            OpE::PreImg(xs, n, ys, _) => {
                format!("let {xs} = preimg({n}, {});", ys.var_list_str())
            }
            OpE::Store(x, ys) => {
                format!("let {x} = store({});", ys.var_list_str())
            }
            OpE::Load(xs, y) => {
                format!("let {xs} = load({y});")
            }
            OpE::Slice(xs, ys) => {
                format!("let {xs} = {ys};")
            }
            OpE::ExternCall(xs, n, ys) => {
                format!("let {xs} = extern_call({n}, {});", ys.var_list_str())
            }
            OpE::Emit(xs) => {
                format!("emit({})", xs.var_list_str())
            }
            OpE::RangeU8(xs) => {
                format!("range_u8!({})", xs.var_list_str())
            }
            OpE::Breakpoint => "breakpoint".into(),
            OpE::Debug(s) => {
                format!("debug!({s})")
            }
        }
    }
}
