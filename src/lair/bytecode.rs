//! `bytecode` is the representation of Lair programs that's actually executed
//! and used for trace generation and arithmetization.
//!
//! References are index-based, thought of as positions in a stack from a stack
//! machine.

use super::{map::Map, List, Name};

/// The type for Lair operations
#[allow(clippy::type_complexity)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
    /// `AssertEq(x, y, fmt)` makes sure `x` is equal to `y`. If `fmt` is `Some`,
    /// use it to format an error message and bail at runtime instead of panicking
    /// when `x` is not equal to `y`
    AssertEq(List<usize>, List<usize>, Option<fn(&[F], &[F]) -> String>),
    /// `AssertNe(x, y)` makes sure `x` is unequal to `y`
    AssertNe(List<usize>, List<usize>),
    /// `Contains(x, y)` makes sure an array `x` contains the value `y`
    Contains(List<usize>, usize),
    /// `Const(x)` pushes `x` to the stack
    Const(F),
    /// `Add(i, j)` pushes `stack[i] + stack[j]` to the stack
    Add(usize, usize),
    /// `Sub(i, j)` pushes `stack[i] - stack[j]` to the stack
    Sub(usize, usize),
    /// `Mul(i, j)` pushes `stack[i] * stack[j]` to the stack
    Mul(usize, usize),
    /// `Inv(i)` pushes `1 / stack[i]` to the stack
    Inv(usize),
    /// `Not(i)` pushes `stack[i] == 0` to the stack
    Not(usize),
    /// `Call(i, [a, b, ...])` extends the stack with the output of the function
    /// at index `i` in the toplevel when applied to the arguments at positions
    /// `[a, b, ...]` in the stack
    Call(usize, List<usize>),
    /// `PreImg(i, [a, b, ...], fmt)` extends the stack with the latest preimage
    /// (beware of non-injectivity) of the function of index `i` when called with
    /// arguments at positions `[a, b, ...]` in the stack. If `fmt` is `Some`,
    /// use it to format an error message and bail at runtime instead of panicking
    /// when the preimage is not available
    PreImg(usize, List<usize>, Option<fn(&[F]) -> String>),
    /// `Store([y, ...])` pushes the pointer to `[y, ...]` to the stack
    Store(List<usize>),
    /// `Load(len, y)` extends the stack with the `len` values that is pointed by `y`
    Load(usize, usize),
    /// `ExternCall(i, [a, b, ...])` extends the stack with the output of the extern
    /// chip at index `i` in the toplevel when applied to the arguments at positions
    /// `[a, b, ...]` in the stack
    ExternCall(usize, List<usize>),
    /// `Emit([x, ...])` pushes `x, ...` to`QueryRecord::emitted` during execution
    Emit(List<usize>),
    /// `RangeU8(xs)` makes sure `xs` is a list of only U8 elements
    RangeU8(List<usize>),
    /// `Breakpoint` adds a breakpoint mark in the debug trace
    Breakpoint,
    /// `Debug(s)` emits debug message `s`
    Debug(&'static str),
}

/// A "code block" containing a sequence of operators and a control node to be
/// executed afterwards
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block<F> {
    pub(crate) ops: List<Op<F>>,
    pub(crate) ctrl: Ctrl<F>,
    pub(crate) return_idents: List<usize>,
}

/// Encodes the logical flow of a Lair program
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Ctrl<F> {
    /// `Choose(x, cases)` non-deterministically chooses which case to execute based on a value `x`
    /// It works by mapping field elements into indices of the list of unique branches.
    Choose(usize, Cases<F, usize>, List<Block<F>>),
    /// `ChooseMany(x, cases)` non-deterministically chooses which case to execute based on an array `x`
    ChooseMany(List<usize>, Cases<List<F>, Block<F>>),
    /// Contains the variables whose bindings will construct the output of the
    /// block. The first `usize` is an unique identifier, representing the
    /// selector used for arithmetization
    Return(usize, List<usize>),
}

/// Represents the cases for `Ctrl::Match`, containing the branches for successful
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<K, B> {
    pub(crate) branches: Map<K, B>,
    pub(crate) default: Option<Box<B>>,
}

impl<K: Ord, B> Cases<K, B> {
    /// Returns the block mapped from key `f`
    #[inline]
    pub fn match_case(&self, k: &K) -> Option<&B> {
        self.branches.get(k).or(self.default.as_deref())
    }

    /// Returns the block at a given index
    #[inline]
    pub fn get_index(&self, idx: usize) -> Option<&B> {
        self.branches
            .get_index(idx)
            .map(|(_, b)| b)
            .or(self.default.as_deref())
    }

    /// Returns the block index given its respective matching key. If there's no
    /// match, returns the size of `branches`, assuming that's the index of the
    /// default block
    #[inline]
    pub fn get_index_of(&self, k: &K) -> Option<usize> {
        self.branches
            .get_index_of(k)
            .or_else(|| self.default.as_ref().map(|_| self.branches.size()))
    }
}

impl<K, B> Cases<K, B> {
    /// Returns the size of `branches`, assuming that's the index of the default
    /// block
    #[inline]
    pub fn default_index(&self) -> usize {
        self.branches.size()
    }

    /// Returns the number of blocks including the default one
    pub fn size(&self) -> usize {
        let inc = if self.default.is_some() { 1 } else { 0 };
        self.branches.size() + inc
    }
}

/// Abstraction for a Lair function, which has a name, the index in the toplevel,
/// the size of the input and output and, of course, its body (encoded as a block).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Func<F> {
    pub(crate) name: Name,
    pub(crate) invertible: bool,
    pub(crate) partial: bool,
    pub(crate) index: usize,
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) body: Block<F>,
}

impl<F> Func<F> {
    /// Getter for the name
    #[inline]
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// Getter for the body block
    #[inline]
    pub fn body(&self) -> &Block<F> {
        &self.body
    }

    /// Getter for the input size
    #[inline]
    pub fn input_size(&self) -> usize {
        self.input_size
    }

    /// Getter for the output size
    #[inline]
    pub fn output_size(&self) -> usize {
        self.output_size
    }

    /// Getter for the index
    #[inline]
    pub fn index(&self) -> usize {
        self.index
    }
}
