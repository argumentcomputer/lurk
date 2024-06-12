//! `bytecode` is the representation of Lair programs that's actually executed
//! and used for trace generation and arithmetization.
//!
//! References are index-based, thought of as positions in a stack from a stack
//! machine.

use super::{map::Map, List, Name};

/// The type for Lair operations
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Op<F> {
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
    /// `PreImg(i, [a, b, ...])` extends the stack with the preimage of the function
    /// of index `i` on the arguments at positions `[a, b, ...]` in the stack
    PreImg(usize, List<usize>),
    /// `Store([y, ...])` pushes to the stack the pointer to `[y, ...]`
    Store(List<usize>),
    /// `Load(len, y)` extends the stack with the `len` values that is pointed by `y`
    Load(usize, usize),
    /// `Hash([x, ...])` extends the stack with the hash of `x, ...`
    Hash(List<usize>),
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
    /// `Match(x, cases)` matches on `x` in order to decide which case to execute
    Match(usize, Cases<F, F>),
    /// `MatchMany(x, cases)` matches on array `x` in order to decide which case to execute
    MatchMany(List<usize>, Cases<List<F>, F>),
    /// `If(b, t, f)` executes block `f` if `stack[b]` is zero and `t` otherwise
    If(usize, Box<Block<F>>, Box<Block<F>>),
    /// `IfMany(bs, t, f)` executes block `f` if `bs` is a zero array and `t` otherwise
    IfMany(List<usize>, Box<Block<F>>, Box<Block<F>>),
    /// Contains the variables whose bindings will construct the output of the
    /// block. The first `usize` is an unique identifier, representing the
    /// selector used for arithmetization
    Return(usize, List<usize>),
}

/// Represents the cases for `Ctrl::Match`, containing the branches for successfull
/// matches and an optional default case in case there's no match. Each code path
/// is encoded as its own block
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Cases<K, F> {
    pub(crate) branches: Map<K, Block<F>>,
    pub(crate) default: Option<Box<Block<F>>>,
}

impl<K: Ord, F> Cases<K, F> {
    /// Returns the block mapped from key `f`
    #[inline]
    pub fn match_case(&self, k: &K) -> Option<&Block<F>> {
        self.branches.get(k).or(self.default.as_deref())
    }

    /// Returns the block at a given index
    #[inline]
    pub fn get_index(&self, idx: usize) -> Option<&Block<F>> {
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

impl<K, F> Cases<K, F> {
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
    pub(crate) index: usize,
    pub(crate) input_size: usize,
    pub(crate) output_size: usize,
    pub(crate) body: Block<F>,
}

impl<F> Func<F> {
    /// Getter for the name
    #[inline]
    pub fn name(&self) -> Name {
        self.name
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
}
