use p3_field::PrimeField;
use std::fmt;

use super::big_num::field_elts_to_biguint;
use super::package::SymbolRef;
use super::parser::position::Pos;
use super::zstore::DIGEST_SIZE;

/// Lurk's syntax for parsing
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Syntax<F> {
    /// An element of the finite field `F`: 1n, 0xffn
    Num(Pos, F),
    /// A u64 integer: 1, 0xff, 1u64, 0xffu64
    U64(Pos, u64),
    /// A i64 integer: -1, -0xff, 1i64, 0xffi64, -1i64, -0xffi64
    I64(Pos, bool, u64),
    /// A big numeric type stored in little-endian
    BigNum(Pos, [F; DIGEST_SIZE]),
    /// A hierarchical symbol: foo, foo.bar.baz or keyword :foo
    Symbol(Pos, SymbolRef),
    /// A string literal: "foobar", "foo\nbar"
    String(Pos, String),
    /// A character literal: 'A', 'λ'
    Char(Pos, char),
    /// A quoted expression: 'a, '(1 2)
    Quote(Pos, Box<Syntax<F>>),
    /// A nil-terminated cons-list of expressions: (1 2 3)
    List(Pos, Vec<Syntax<F>>),
    /// An improper cons-list of expressions: (1 2 . 3)
    Improper(Pos, Vec<Syntax<F>>, Box<Syntax<F>>),
}

impl<F> Syntax<F> {
    /// Retrieves the `Pos` attribute
    pub fn get_pos(&self) -> &Pos {
        match self {
            Self::Num(pos, _)
            | Self::U64(pos, _)
            | Self::I64(pos, ..)
            | Self::BigNum(pos, _)
            | Self::Symbol(pos, _)
            | Self::String(pos, _)
            | Self::Char(pos, _)
            | Self::Quote(pos, _)
            | Self::List(pos, _)
            | Self::Improper(pos, ..) => pos,
        }
    }
}

impl<F: fmt::Display + PrimeField> fmt::Display for Syntax<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Num(_, x) => write!(f, "{x}"),
            Self::U64(_, x) => write!(f, "{x}u64"),
            Self::I64(_, sign, x) => write!(f, "{}{x}i64", if *sign { "-" } else { "" }),
            Self::BigNum(_, c) => write!(f, "#{:#x}", field_elts_to_biguint(c)),
            Self::Symbol(_, x) => write!(f, "{x}"),
            Self::String(_, x) => write!(f, "\"{}\"", x.escape_default()),
            Self::Char(_, x) => {
                if *x == '(' || *x == ')' {
                    write!(f, "'\\{x}'")
                } else {
                    write!(f, "'{}'", x.escape_default())
                }
            }
            Self::Quote(_, x) => write!(f, "'{x}"),
            Self::List(_, xs) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{x} ")?,
                        None => write!(f, "{x}")?,
                    }
                }
                write!(f, ")")
            }
            Self::Improper(_, xs, end) => {
                let mut iter = xs.iter().peekable();
                write!(f, "(")?;
                while let Some(x) = iter.next() {
                    match iter.peek() {
                        Some(_) => write!(f, "{x} ")?,
                        None => write!(f, "{} . {}", x, *end)?,
                    }
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::lurk::{parser::syntax::parse_syntax, state::State};

    #[test]
    fn test_digest() {
        let state = State::init_lurk_state().rccell();
        let (rest, syn) = parse_syntax::<BabyBear>(state.clone(), false, false)(
            "#0x123456789ABCDEFEDCBA98765432123456789ABCDEFEDCBA98765432123456".into(),
        )
        .unwrap();
        assert!(rest.is_empty());
        assert_eq!(
            format!("{syn}"),
            "#0x123456789abcdefedcba98765432123456789abcdefedcba98765432123456"
        );

        let (rest, syn) =
            parse_syntax::<BabyBear>(state, false, false)("#0x000000000000000000123456789".into())
                .unwrap();
        assert!(rest.is_empty());
        assert_eq!(format!("{syn}"), "#0x123456789");
    }
}
