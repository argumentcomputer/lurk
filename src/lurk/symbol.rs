use anyhow::{bail, Result};
use serde::{Deserialize, Serialize};
use std::fmt;

pub static LURK_WHITESPACE: [char; 27] = [
    '\u{0009}', '\u{000A}', '\u{000B}', '\u{000C}', '\u{000D}', '\u{0020}', '\u{0085}', '\u{200E}',
    '\u{200F}', '\u{2028}', '\u{2029}', '\u{20A0}', '\u{1680}', '\u{2000}', '\u{2001}', '\u{2002}',
    '\u{2003}', '\u{2004}', '\u{2005}', '\u{2006}', '\u{2007}', '\u{2008}', '\u{2009}', '\u{200A}',
    '\u{202F}', '\u{205F}', '\u{3000}',
];

pub(crate) const KEYWORD_MARKER: char = ':';
pub(crate) const SYM_SEPARATOR: char = '.';
pub(crate) const SYM_MARKER: char = '.';
pub(crate) const ESCAPE_CHARS: &str = "|(){}[],.:;'\\\"";

#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Serialize, Deserialize, Hash, Ord)]
/// Type for hierarchical symbol names.
pub struct Symbol {
    path: Vec<String>,
    keyword: bool,
}

impl Symbol {
    #[inline]
    pub fn path(&self) -> &[String] {
        &self.path
    }

    #[inline]
    pub const fn is_keyword(&self) -> bool {
        self.keyword
    }

    #[inline]
    pub const fn root(keyword: bool) -> Self {
        Self {
            path: vec![],
            keyword,
        }
    }

    /// Creates a new `Symbol` with an empty path.
    #[inline]
    pub fn root_sym() -> Self {
        Self::root(false)
    }

    /// Creates a new `Symbol` with an empty path.
    #[inline]
    pub fn root_key() -> Self {
        Self::root(true)
    }

    #[inline]
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    /// Returns true if the `Symbol` is the root symbol
    #[inline]
    pub fn is_root_sym(&self) -> bool {
        self.is_root() && !self.keyword
    }

    #[inline]
    pub fn is_root_key(&self) -> bool {
        self.is_root() && self.keyword
    }

    pub fn new<A: AsRef<str>>(path: &[A], keyword: bool) -> Self {
        Self {
            path: path.iter().map(|x| String::from(x.as_ref())).collect(),
            keyword,
        }
    }

    pub fn new_from_vec(path: Vec<String>, keyword: bool) -> Self {
        Self { path, keyword }
    }

    #[inline]
    pub fn sym<A: AsRef<str>>(path: &[A]) -> Self {
        Self::new(path, false)
    }

    #[inline]
    pub fn key<A: AsRef<str>>(path: &[A]) -> Self {
        Self::new(path, true)
    }

    #[inline]
    pub fn sym_from_vec(path: Vec<String>) -> Self {
        Self::new_from_vec(path, false)
    }

    #[inline]
    pub fn key_from_vec(path: Vec<String>) -> Self {
        Self::new_from_vec(path, true)
    }

    #[inline]
    pub fn set_as_keyword(&mut self) {
        self.keyword = true;
    }

    /// Creates a new Symbol with the path extended by the given vector of path segments.
    pub fn extend<A: AsRef<str>>(&self, child: &[A]) -> Self {
        let mut path = Vec::with_capacity(self.path.len() + child.len());
        for elt in self.path.iter() {
            path.push(elt.clone());
        }
        for elt in child.iter() {
            path.push(String::from(elt.as_ref()));
        }
        Self {
            path,
            keyword: self.keyword,
        }
    }

    pub fn has_parent(&self, parent: &Symbol) -> bool {
        // parent paths can't be longer than child paths
        if self.path.len() < parent.path.len() {
            false
        } else {
            // zip returns an iterator only as long as the shortest path,
            // in this case the parent
            self.path
                .iter()
                .zip(parent.path.iter())
                .all(|(a, b)| a == b)
        }
    }

    pub fn as_child(&self, parent: &Symbol) -> Option<Symbol> {
        // parent paths can't be longer than child paths
        if self.path.len() < parent.path.len() {
            None
        } else {
            let keyword = parent.keyword;
            let mut parent = parent.path.iter();
            let mut child = self.path.iter().peekable();

            // peek if there's more in the child path
            while child.peek().is_some() {
                // if there's more in the parent path, step through both together
                if let Some(next_parent) = parent.next() {
                    let next_child = child.next().unwrap();
                    // the parent path has to be a prefix of the child path
                    if next_child != next_parent {
                        return None;
                    }
                // if there's no more parent path
                } else {
                    let path = child.cloned().collect();
                    // return the remaining child path
                    return Some(Symbol { path, keyword });
                }
            }
            // only reachable if self == parent
            Some(Symbol {
                path: vec![],
                keyword,
            })
        }
    }

    pub fn is_whitespace(c: char) -> bool {
        LURK_WHITESPACE.iter().any(|x| *x == c)
    }

    pub fn fmt_path_component_to_string(xs: &str) -> String {
        let mut res = String::new();
        for x in xs.chars() {
            if ESCAPE_CHARS.chars().any(|c| c == x) {
                res.push_str(&format!("\\{x}"));
            } else if Self::is_whitespace(x) {
                res.push_str(&format!("{}", x.escape_unicode()));
            } else {
                res.push(x)
            }
        }
        res
    }

    pub fn fmt_path_to_string(&self) -> String {
        let mut res = String::new();
        let mut iter = self.path.iter().peekable();
        while let Some(next) = iter.next() {
            res.push_str(&Self::fmt_path_component_to_string(next));
            if iter.peek().is_some() || next.is_empty() {
                res.push('.');
            }
        }
        res
    }

    pub fn prints_as_absolute(&self) -> bool {
        if self.path.is_empty() {
            false
        } else {
            let head = &self.path[0];
            head.is_empty()
                || head.starts_with([
                    '~', '#', '1', '2', '3', '4', '5', '6', '7', '8', '9', '0', '.', ':', '[', ']',
                    '(', ')', '{', '}', '"', '\\',
                ])
                || head.starts_with("-1")
                || head.starts_with("-2")
                || head.starts_with("-3")
                || head.starts_with("-4")
                || head.starts_with("-5")
                || head.starts_with("-6")
                || head.starts_with("-7")
                || head.starts_with("-8")
                || head.starts_with("-9")
                || head.starts_with("-0")
                || head.starts_with(char::is_whitespace)
                || head.starts_with(char::is_control)
        }
    }

    pub fn direct_parent(&self) -> Option<Symbol> {
        if self.is_root() {
            None
        } else {
            Some(Self {
                // drop the last component of the path
                path: self.path[0..self.path.len() - 1].to_vec(),
                keyword: self.keyword,
            })
        }
    }

    pub fn direct_child(&self, child: &str) -> Symbol {
        let mut path = self.path.clone();
        path.push(child.into());
        Self {
            path,
            keyword: self.keyword,
        }
    }

    pub fn name(&self) -> Result<&str> {
        if self.is_root() {
            bail!("Root symbols don't have names")
        } else {
            Ok(&self.path[self.path.len() - 1])
        }
    }

    pub fn fmt_to_string(&self) -> String {
        if self.is_keyword() {
            if self.is_root() {
                "~:()".into()
            } else {
                format!(":{}", &self.fmt_path_to_string())
            }
        } else if self.is_root() {
            "~()".into()
        } else {
            format!(".{}", &self.fmt_path_to_string())
        }
    }

    // todo
    // /// Attempts to parse and intern a `Symbol` from a string
    // pub fn interned<A: AsRef<str>>(input: A, state: StateRcCell) -> Result<SymbolRef> {
    //     use crate::{parser::syntax::parse_symbol, syntax::Syntax};
    //     use halo2curves::bn256::Fr; // could be any other field
    //     use nom::Parser;
    //     match parse_symbol::<Fr>(state, true).parse(input.as_ref().into()) {
    //         Ok((_, Syntax::Symbol(_, symbol))) => Ok(symbol),
    //         Ok(_) => Err(anyhow!("Input didn't parse to a symbol")),
    //         Err(e) => Err(anyhow!(e.to_string())),
    //     }
    // }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.fmt_to_string())
    }
}

#[macro_export]
macro_rules! sym {
    [$( $x:expr ),*] => {
        {
            let temp_vec = vec![ $( $x.to_string() ),* ];
            $crate::symbol::Symbol::sym(&temp_vec)
        }
    };
}
