use crate::lair::{chipset::NoChip, expr::FuncE, FxIndexMap, Name};

use super::symbol::Symbol;

/// Carries the coroutine implementation as a Lair function and informs its
/// characteristics
pub struct Coroutine<F> {
    /// The arity of the coroutine in Lurk code. For example, `my-coroutine` in
    /// `(my-coroutine a b)` has `lurk_arity` 2.
    pub lurk_arity: usize,
    /// Whether the Lair function should take the reduction environment as a
    /// parameter
    pub uses_env: bool,
    /// The actual implementation of the coroutine. The Lair function must have
    /// arity equal `2 * lurk_arity + usize::from(uses_env)`. That's because
    /// each Lurk argument has a tag and a value and then the environment, if
    /// requested, is provided as the last argument. Additionally, the Lair
    /// function must have output size 2: a tag and a value.
    pub func_expr: FuncE<F>,
}

/// A `Lang` specifies how to extend Lurk with custom coroutines and gadgets.
///
/// Each coroutine is called, in Lurk, by the symbol associated with it. The
/// precise behavior is implemented as a Lair function, which can further call
/// custom gadgets by their names.
///
/// Important:
/// * Coroutine symbols must not conflict with Lurk's native symbols from the
///   `.lurk` and `.lurk.builtin` packages
/// * The names of the Lair functions must not conflict with the names of
///   native Lair functions' from Lurk's `Toplevel`
/// * The gadget names must not conflict with native gadget names from Lurk's
///   `Chipset`
pub struct Lang<F, C> {
    coroutines: FxIndexMap<Symbol, Coroutine<F>>,
    gadgets: FxIndexMap<Name, C>,
}

impl<F, C> Lang<F, C> {
    #[inline]
    pub fn new<
        IF: IntoIterator<Item = (Symbol, Coroutine<F>)>,
        IC: IntoIterator<Item = (Name, C)>,
    >(
        coroutines: IF,
        gadgets: IC,
    ) -> Self {
        Self {
            coroutines: coroutines.into_iter().collect(),
            gadgets: gadgets.into_iter().collect(),
        }
    }

    #[inline]
    pub fn into_parts(self) -> (FxIndexMap<Symbol, Coroutine<F>>, FxIndexMap<Name, C>) {
        let Self {
            coroutines,
            gadgets,
        } = self;
        (coroutines, gadgets)
    }

    #[inline]
    pub fn coroutines(&self) -> &FxIndexMap<Symbol, Coroutine<F>> {
        &self.coroutines
    }
}

impl<F> Lang<F, NoChip> {
    #[inline]
    pub fn empty() -> Lang<F, NoChip> {
        Lang {
            coroutines: FxIndexMap::default(),
            gadgets: FxIndexMap::default(),
        }
    }
}
