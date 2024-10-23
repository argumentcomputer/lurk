use std::{
    cmp::Ordering,
    fmt::{self, Write},
    num::ParseIntError,
    string::String,
};

use nom::{error::ErrorKind, AsBytes, Err, IResult, InputLength};
use num_bigint::BigUint;

use crate::lurk::parser::{base, Span};

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum ParseErrorKind {
    InvalidBase16EscapeSequence(String, Option<ParseIntError>),
    InvalidBaseEncoding(base::LitBase),
    NumError(String),
    DigestLiteralTooBig(BigUint),
    UnknownBaseCode,
    ParseIntErr(ParseIntError),
    InvalidChar(String),
    Nom(ErrorKind),
    InterningError(String),
    Custom(String),
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBase16EscapeSequence(seq, _) => {
                write!(f, "Unknown base 16 string escape sequence {seq}.")
            }
            Self::ParseIntErr(e) => {
                write!(f, "Error parsing number: {e}")
            }
            Self::Custom(e) => {
                write!(f, "Error: {e}")
            }
            e => write!(f, "internal parser error {e:?}"),
        }
    }
}

impl ParseErrorKind {
    pub fn is_nom_err(&self) -> bool {
        matches!(self, Self::Nom(_))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub struct ParseError<I: AsBytes> {
    pub input: I,
    pub expected: Option<&'static str>,
    pub errors: Vec<ParseErrorKind>,
}

impl<I: AsBytes> ParseError<I> {
    pub fn new(input: I, error: ParseErrorKind) -> Self {
        ParseError {
            input,
            expected: None,
            errors: vec![error],
        }
    }

    pub fn throw<A>(input: I, e: ParseErrorKind) -> IResult<I, A, Self> {
        Err(Err::Error(ParseError::new(input, e)))
    }

    pub fn opt<A>(opt: Option<A>, input: I, error: ParseErrorKind) -> IResult<I, A, Self> {
        match opt {
            Some(a) => Ok((input, a)),
            None => Err(Err::Error(ParseError::new(input, error))),
        }
    }

    pub fn res<A, E, Fun: Fn(E) -> ParseErrorKind>(
        res: Result<A, E>,
        input: I,
        f: Fun,
    ) -> IResult<I, A, Self> {
        match res {
            Ok(a) => Ok((input, a)),
            Err(e) => Err(Err::Error(ParseError::new(input, f(e)))),
        }
    }
}

impl<'a> fmt::Display for ParseError<Span<'a>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut res = String::new();

        writeln!(
            &mut res,
            "at line {}:{}",
            self.input.location_line(),
            self.input.get_column()
        )?;
        let line = String::from_utf8_lossy(self.input.get_line_beginning());

        writeln!(&mut res, "{} | {}", self.input.location_line(), line)?;

        let cols = format!("{} | ", self.input.location_line()).len() + self.input.get_column();
        for _ in 0..(cols - 1) {
            write!(&mut res, " ")?;
        }
        writeln!(&mut res, "^")?;

        if let Some(exp) = self.expected {
            writeln!(&mut res, "Expected {exp}")?;
        }

        let mut errs = self.errors.iter().filter(|x| !x.is_nom_err()).peekable();
        // TODO: Better handling of Nom errors, such as by using nom_supreme:
        // https://docs.rs/nom-supreme/latest/nom_supreme/ or similar
        if errs.peek().is_none() {
            writeln!(&mut res, "Internal parser error")?;
        } else {
            writeln!(&mut res, "Reported errors:")?;
            for kind in errs {
                writeln!(&mut res, "- {kind}")?;
            }
        }

        write!(f, "{res}")
    }
}

impl<I: AsBytes> nom::error::ParseError<I> for ParseError<I>
where
    I: InputLength,
{
    fn from_error_kind(input: I, kind: ErrorKind) -> Self {
        ParseError::new(input, ParseErrorKind::Nom(kind))
    }

    fn append(input: I, kind: ErrorKind, mut other: Self) -> Self {
        match input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => ParseError::new(input, ParseErrorKind::Nom(kind)),
            Ordering::Equal => {
                other.errors.push(ParseErrorKind::Nom(kind));
                other
            }
            Ordering::Greater => other,
        }
    }

    fn or(self, mut other: Self) -> Self {
        match self.input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => self,
            Ordering::Equal => {
                for x in self.errors {
                    other.errors.push(x);
                }
                other
            }
            Ordering::Greater => other,
        }
    }
}

impl<I: AsBytes> nom::error::ContextError<I> for ParseError<I>
where
    I: InputLength,
{
    fn add_context(input: I, ctx: &'static str, other: Self) -> Self {
        match input.input_len().cmp(&other.input.input_len()) {
            Ordering::Less => ParseError {
                input,
                expected: Some(ctx),
                errors: vec![],
            },
            Ordering::Equal => match other.expected {
                None => ParseError {
                    input,
                    expected: Some(ctx),
                    errors: other.errors,
                },
                _ => other,
            },
            Ordering::Greater => other,
        }
    }
}

pub fn map_parse_err<I: AsBytes, A, Fun: Fn(ParseError<I>) -> ParseError<I>>(
    x: IResult<I, A, ParseError<I>>,
    f: Fun,
) -> IResult<I, A, ParseError<I>> {
    x.map_err(|e| match e {
        Err::Incomplete(n) => Err::Incomplete(n),
        Err::Error(e) => Err::Error(f(e)),
        Err::Failure(e) => Err::Failure(f(e)),
    })
}
