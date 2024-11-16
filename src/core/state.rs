#![deny(missing_docs)]

//! This module implements an abstraction for the Lurk state, which changes as
//! Lurk code is evaluated

use anyhow::{bail, Result};
use once_cell::sync::OnceCell;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::symbol::Symbol;

use super::package::{Package, SymbolRef};

/// Keeps track of the current package for symbol resolution when reading and printing
#[derive(Debug)]
pub struct State {
    current_package: SymbolRef,
    symbol_packages: HashMap<SymbolRef, Package>,
}

/// Alias for `Rc<RefCell<State>>`
pub type StateRcCell = Rc<RefCell<State>>;

impl State {
    /// Wraps a state with `Rc<RefCell<...>>`
    #[inline]
    pub fn rccell(self) -> StateRcCell {
        Rc::new(RefCell::new(self))
    }

    /// Creates a new state with a given package as the current one
    pub fn new_with_package(package: Package) -> Self {
        let current_package = package.name().clone();
        let mut symbol_packages = HashMap::default();
        symbol_packages.insert(current_package.clone(), package);
        Self {
            current_package,
            symbol_packages,
        }
    }

    /// Adds a package to a state
    pub fn add_package(&mut self, package: Package) {
        self.symbol_packages.insert(package.name().clone(), package);
    }

    /// Retrieves a package by its name
    pub fn get_package(&self, package_name: &Symbol) -> Option<&Package> {
        self.symbol_packages.get(package_name)
    }

    /// Sets the current package of the state
    pub fn set_current_package(&mut self, package_name: SymbolRef) -> Result<()> {
        if self.symbol_packages.contains_key(&package_name) {
            self.current_package = package_name;
            Ok(())
        } else {
            bail!("Package {package_name} not found")
        }
    }

    /// Returns the name of the current package
    #[inline]
    pub const fn get_current_package_name(&self) -> &SymbolRef {
        &self.current_package
    }

    /// Returns a reference to the current package
    pub fn get_current_package(&self) -> &Package {
        self.symbol_packages
            .get(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    /// Returns a mutable reference to the current package
    fn get_current_package_mut(&mut self) -> &mut Package {
        self.symbol_packages
            .get_mut(&self.current_package)
            .expect("current package must be in the hashmap")
    }

    /// Returns the resolved (fully-qualified) symbol given a symbol name
    pub fn resolve(&self, symbol_name: &str) -> Option<&SymbolRef> {
        self.get_current_package().resolve(symbol_name)
    }

    /// Interns a symbol into the current package
    pub fn intern<A: AsRef<str>>(&mut self, symbol_name: A) -> SymbolRef {
        self.get_current_package_mut()
            .intern(String::from(symbol_name.as_ref()))
    }

    /// Imports a set of symbols to the current package
    pub fn import(&mut self, symbols: &[SymbolRef]) -> Result<()> {
        self.get_current_package_mut().import(symbols)
    }

    /// Imports all symbols from a certain package
    pub fn use_package(&mut self, package: &Package) -> Result<()> {
        self.get_current_package_mut().use_package(package)
    }

    /// Formats a symbol to string w.r.t. the current package
    pub fn fmt_to_string(&self, symbol: &Symbol) -> String {
        self.get_current_package().fmt_to_string(symbol)
    }

    /// Sequentially intern a symbol into the potentially nested packages according
    /// to its path
    fn intern_fold<A: AsRef<str>, I: IntoIterator<Item = A>>(
        &mut self,
        init: SymbolRef,
        path: I,
        create_unknown_packages: bool,
    ) -> Result<SymbolRef> {
        path.into_iter()
            .try_fold(init, |acc, s| match self.symbol_packages.get_mut(&acc) {
                Some(package) => Ok(package.intern(String::from(s.as_ref()))),
                None => {
                    if create_unknown_packages {
                        let mut package = Package::new(acc);
                        let symbol = package.intern(String::from(s.as_ref()));
                        self.add_package(package);
                        Ok(symbol)
                    } else {
                        bail!("Package {acc} not found")
                    }
                }
            })
    }

    /// Call `intern_fold` w.r.t. the root package
    #[inline]
    pub fn intern_path<A: AsRef<str>, I: IntoIterator<Item = A>>(
        &mut self,
        path: I,
        keyword: bool,
        create_unknown_packages: bool,
    ) -> Result<SymbolRef> {
        self.intern_fold(Symbol::root(keyword).into(), path, create_unknown_packages)
    }

    /// Call `intern_path` with `create_unknown_packages = true`
    #[inline]
    pub fn intern_path_infallible<A: AsRef<str>, I: IntoIterator<Item = A>>(
        &mut self,
        path: I,
        keyword: bool,
    ) -> SymbolRef {
        self.intern_path(path, keyword, true)
            .expect("Can't fail if unknown packages are created")
    }

    /// Call `intern_fold` w.r.t. the current package
    #[inline]
    pub fn intern_relative_path<A: AsRef<str>, I: IntoIterator<Item = A>>(
        &mut self,
        path: I,
        create_unknown_packages: bool,
    ) -> Result<SymbolRef> {
        self.intern_fold(self.current_package.clone(), path, create_unknown_packages)
    }

    /// Call `intern_relative_path` with `create_unknown_packages = true`
    #[inline]
    pub fn intern_relative_path_infallible<A: AsRef<str>, I: IntoIterator<Item = A>>(
        &mut self,
        path: I,
    ) -> SymbolRef {
        self.intern_relative_path(path, true)
            .expect("Can't fail if unknown packages are created")
    }

    /// Initiates the Lurk state with the appropriate structure of packages
    pub fn init_lurk_state() -> Self {
        let mut root_package = Package::new(SymbolRef::new(Symbol::root_sym()));

        // bootstrap the keyword package
        let keyword_package = Package::new(SymbolRef::new(Symbol::root_key()));

        // bootstrap the lurk package
        let mut lurk_package = Package::new(root_package.intern(LURK_PACKAGE_NAME));
        for symbol_name in LURK_SYMBOLS {
            lurk_package.intern(symbol_name);
        }

        // bootstrap the builtin package
        let mut builtin_package = Package::new(lurk_package.intern(BUILTIN_PACKAGE_NAME));
        for symbol_name in BUILTIN_SYMBOLS {
            builtin_package.intern(symbol_name);
        }

        // bootstrap the meta package
        let mut meta_package = Package::new(lurk_package.intern(META_PACKAGE_NAME));
        for symbol_name in META_SYMBOLS {
            meta_package.intern(symbol_name);
        }

        // bootstrap the user package
        let mut user_package = Package::new(root_package.intern(USER_PACKAGE_NAME));
        user_package
            .use_package(&lurk_package)
            .expect("all symbols in the lurk package are importable");
        user_package
            .use_package(&builtin_package)
            .expect("all symbols in the builtin package are importable");

        // initiate the state with the lurk user package then add the others
        let mut state = Self::new_with_package(user_package);
        state.add_package(root_package);
        state.add_package(keyword_package);
        state.add_package(lurk_package);
        state.add_package(builtin_package);
        state.add_package(meta_package);
        state
    }
}

impl Default for State {
    fn default() -> Self {
        Self {
            current_package: SymbolRef::new(Symbol::root_sym()),
            symbol_packages: Default::default(),
        }
    }
}

/// Returns the symbol in the `.lurk` package given the symbol name
#[inline]
pub fn lurk_sym(name: &str) -> Symbol {
    Symbol::sym(&[LURK_PACKAGE_NAME, name])
}

/// Returns the symbol in the `.lurk.builtin` package given the symbol name
#[inline]
pub fn builtin_sym(name: &str) -> Symbol {
    Symbol::sym(&[LURK_PACKAGE_NAME, BUILTIN_PACKAGE_NAME, name])
}

/// Returns the symbol in the `.lurk.meta` package given the symbol name
#[inline]
pub fn meta_sym(name: &str) -> Symbol {
    Symbol::sym(&[LURK_PACKAGE_NAME, META_PACKAGE_NAME, name])
}

/// Returns the symbol corresponding to the name of the meta package
#[inline]
pub fn meta_package_symbol() -> Symbol {
    lurk_sym(META_PACKAGE_NAME)
}

/// Returns the symbol in the user package given the symbol name
#[inline]
pub fn user_sym(name: &str) -> Symbol {
    Symbol::sym(&[USER_PACKAGE_NAME, name])
}

static INITIAL_LURK_STATE_CELL: OnceCell<State> = OnceCell::new();

/// Returns a shared reference to the initial Lurk state
pub fn initial_lurk_state() -> &'static State {
    INITIAL_LURK_STATE_CELL.get_or_init(State::init_lurk_state)
}

const LURK_PACKAGE_NAME: &str = "lurk";
const BUILTIN_PACKAGE_NAME: &str = "builtin";
const META_PACKAGE_NAME: &str = "meta";
const USER_PACKAGE_NAME: &str = "lurk-user";

pub(crate) const LURK_SYMBOLS: [&str; 3] = ["nil", "t", "&rest"];

pub(crate) const BUILTIN_SYMBOLS: [&str; 43] = [
    "atom",
    "apply",
    "begin",
    "car",
    "cdr",
    "char",
    "commit",
    "comm",
    "bignum",
    "cons",
    "empty-env",
    "current-env",
    "bind",
    "env",
    "emit",
    "eval",
    "eq",
    "eqq",
    "type-eq",
    "type-eqq",
    "hide",
    "if",
    "lambda",
    "let",
    "letrec",
    "u64",
    "open",
    "quote",
    "secret",
    "strcons",
    "list",
    "+",
    "-",
    "*",
    "/",
    "%",
    "=",
    "<",
    ">",
    "<=",
    ">=",
    "breakpoint",
    "fail",
];

pub(crate) const META_SYMBOLS: [&str; 44] = [
    "def",
    "defq",
    "defrec",
    "update",
    "load",
    "assert",
    "assert-eq",
    "assert-emitted",
    "assert-error",
    "debug",
    "hide",
    "rand",
    "commit",
    "open",
    "clear",
    "set-env",
    "erase-from-env",
    "prove",
    "verify",
    "defpackage",
    "import",
    "in-package",
    "help",
    "call",
    "chain",
    "transition",
    "inspect",
    "dump-expr",
    "load-expr",
    "defprotocol",
    "prove-protocol",
    "verify-protocol",
    "microchain-set-info",
    "microchain-get-info",
    "microchain-start",
    "microchain-get-genesis",
    "microchain-get-state",
    "microchain-transition",
    "microchain-verify",
    "scope",
    "scope-pop",
    "scope-store",
    "load-ocaml",
    "load-ocaml-expr",
];
