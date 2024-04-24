use match_opt::match_opt;

/// An ergonomic pair type for tagged pointer semantics
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct GPtr<T, V> {
    pub tag: T,
    pub val: V,
}

impl<T, V> GPtr<T, V> {
    #[inline]
    pub fn new(tag: T, val: V) -> Self {
        Self { tag, val }
    }

    #[inline]
    pub fn tag(&self) -> &T {
        &self.tag
    }

    #[inline]
    pub fn val(&self) -> &V {
        &self.val
    }

    #[inline]
    pub fn parts(&self) -> (&T, &V) {
        let Self { tag, val } = self;
        (tag, val)
    }

    #[inline]
    pub fn into_parts(self) -> (T, V) {
        let Self { tag, val } = self;
        (tag, val)
    }
}

/// Encoding for pointer children that are stored in index-based data structures
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IVal {
    /// Holds the index of leaf data
    Atom(usize),
    /// Holds the index of two children
    Tuple2(usize),
    /// Holds the index of three children
    Tuple3(usize),
    /// Holds the index of four children
    Tuple4(usize),
    /// Similar to `Tuple3`, but ignores the tags of the first and third children
    /// for content-addressing
    Compact(usize),
}

impl IVal {
    #[inline]
    pub fn is_atom(&self) -> bool {
        matches!(self, IVal::Atom(_))
    }

    #[inline]
    pub fn is_compound(&self) -> bool {
        !self.is_atom()
    }

    #[inline]
    pub fn get_atom_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Atom(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple2_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple2(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple3_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple3(idx) => *idx)
    }

    #[inline]
    pub fn get_tuple4_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Tuple4(idx) => *idx)
    }

    #[inline]
    pub fn get_compact_idx(&self) -> Option<usize> {
        match_opt!(self, IVal::Compact(idx) => *idx)
    }
}

/// A `GPtr` that is generic on the `tag` type and uses `IVal` as the `val` type
pub type IPtr<T> = GPtr<T, IVal>;
