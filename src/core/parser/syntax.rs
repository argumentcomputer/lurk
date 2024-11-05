use anyhow::{bail, Result};
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till},
    character::complete::{anychar, char, multispace0, multispace1, none_of},
    combinator::{eof, opt, peek, success, value},
    multi::{many0, many_till, separated_list1},
    sequence::{delimited, preceded, terminated},
    Parser,
};
use nom_locate::LocatedSpan;
use num_bigint::BigUint;
use p3_field::Field;

use crate::core::{
    package::SymbolRef,
    parser::{
        base,
        error::{ParseError, ParseErrorKind},
        position::Pos,
        string, ParseResult, Span,
    },
    state::{meta_package_symbol, StateRcCell},
    symbol,
    syntax::Syntax,
    zstore::DIGEST_SIZE,
};

fn parse_line_comment(i: Span<'_>) -> ParseResult<'_, Span<'_>> {
    let (i, _) = tag(";")(i)?;
    let (i, com) = take_till(|c| c == '\n')(i)?;
    Ok((i, com))
}

pub fn parse_space(i: Span<'_>) -> ParseResult<'_, Vec<Span<'_>>> {
    let (i, _) = multispace0(i)?;
    let (i, com) = many0(terminated(parse_line_comment, alt((multispace1, eof))))(i)?;
    Ok((i, com))
}

fn parse_symbol_limb(escape: &'static str) -> impl Fn(Span<'_>) -> ParseResult<'_, String> {
    move |from: Span<'_>| {
        let (i, s) = alt((
            string::parse_string_inner1(symbol::SYM_SEPARATOR, false, escape),
            delimited(
                tag("|"),
                string::parse_string_inner1('|', true, "|"),
                tag("|"),
            ),
            value(String::from(""), peek(tag("."))),
        ))(from)?;
        Ok((i, s))
    }
}

fn parse_symbol_limb_raw(escape: &'static str) -> impl Fn(Span<'_>) -> ParseResult<'_, String> {
    move |from: Span<'_>| {
        let (i, s) = alt((
            string::parse_string_inner1(' ', false, escape),
            delimited(
                tag("|"),
                string::parse_string_inner1('|', true, "|"),
                tag("|"),
            ),
            value(String::from(""), peek(tag("."))),
        ))(from)?;
        Ok((i, s))
    }
}

fn parse_symbol_limbs() -> impl Fn(Span<'_>) -> ParseResult<'_, Vec<String>> {
    move |from: Span<'_>| {
        let (i, path) = separated_list1(
            char(symbol::SYM_SEPARATOR),
            parse_symbol_limb(symbol::ESCAPE_CHARS),
        )(from)?;
        let (upto, _) = opt(tag("."))(i)?;
        Ok((upto, path))
    }
}

fn intern_path<'a>(
    state: &StateRcCell,
    upto: LocatedSpan<&'a str>,
    path: &[String],
    keyword: Option<bool>,
    create_unknown_packages: bool,
) -> ParseResult<'a, SymbolRef> {
    use nom::Err::Failure;
    match keyword {
        Some(keyword) => state
            .borrow_mut()
            .intern_path(path, keyword, create_unknown_packages),
        None => state
            .borrow_mut()
            .intern_relative_path(path, create_unknown_packages),
    }
    .map(|symbol| (upto, symbol))
    .map_err(|e| {
        Failure(ParseError::new(
            upto,
            ParseErrorKind::InterningError(format!("{e}")),
        ))
    })
}

fn parse_absolute_symbol(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, SymbolRef> {
    move |from: Span<'_>| {
        let (i, is_key) = alt((
            value(false, char(symbol::SYM_MARKER)),
            value(true, char(symbol::KEYWORD_MARKER)),
        ))(from)?;
        let (upto, path) = parse_symbol_limbs()(i)?;
        intern_path(&state, upto, &path, Some(is_key), create_unknown_packages)
    }
}

fn parse_relative_symbol(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = peek(none_of(",~#(){}[]1234567890."))(from)?;
        let (upto, path) = parse_symbol_limbs()(i)?;
        intern_path(&state, upto, &path, None, create_unknown_packages)
    }
}

fn parse_raw_symbol(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = tag("~(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_symbol_limb_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        intern_path(&state, upto, &path, Some(false), create_unknown_packages)
    }
}

fn parse_raw_keyword(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, SymbolRef> {
    move |from: Span<'_>| {
        let (i, _) = tag("~:(")(from)?;
        let (i, mut path) = many0(preceded(parse_space, parse_symbol_limb_raw("|()")))(i)?;
        let (upto, _) = many_till(parse_space, tag(")"))(i)?;
        path.reverse();
        intern_path(&state, upto, &path, Some(true), create_unknown_packages)
    }
}

/// relative: foo.bar
/// absolute: .foo.bar.baz, :foo.bar (escaped limbs: .|foo|.|bar|.|baz|)
/// raw: ~(foo bar baz) = .baz.bar.foo
/// raw keyword: ~:(foo bar) = :bar.foo
fn parse_symbol(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, SymbolRef> {
    move |from: Span<'_>| {
        let (upto, sym) = alt((
            parse_relative_symbol(state.clone(), create_unknown_packages),
            parse_absolute_symbol(state.clone(), create_unknown_packages),
            parse_raw_symbol(state.clone(), create_unknown_packages),
            parse_raw_keyword(state.clone(), create_unknown_packages),
        ))(from)?;
        Ok((upto, sym))
    }
}

fn parse_symbol_syntax<F>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (upto, sym) = parse_symbol(state.clone(), create_unknown_packages)(from)?;
        Ok((upto, Syntax::Symbol(Pos::from_upto(from, upto), sym)))
    }
}

fn parse_numeric_suffix() -> impl Fn(Span<'_>) -> ParseResult<'_, Span<'_>> {
    move |from: Span<'_>| {
        let (upto, suffix) = alt((
            tag("u8"),
            tag("u16"),
            tag("u32"),
            tag("u64"),
            tag("u128"),
            tag("i8"),
            tag("i16"),
            tag("i32"),
            tag("i64"),
            tag("i128"),
            tag("n"),
        ))(from)?;
        Ok((upto, suffix))
    }
}

fn parse_numeric<F: Field>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, neg) = opt(tag("-"))(from)?;
        let (i, base) = alt((
            preceded(tag("0"), base::parse_litbase_code()),
            success(base::LitBase::Dec),
        ))(i)?;
        let (i, digits) = base::parse_litbase_digits(base)(i)?;
        // when more uint types are supported we can do:
        let (upto, suffix) = opt(parse_numeric_suffix())(i)?;
        let suffix = suffix.map(|x| *x.fragment());
        match suffix {
            Some("n") => {
                // Field elements
                let (_, be_bytes) = be_bytes_from_digits(base, &digits, i)?;
                let f = f_from_be_bytes::<F>(&be_bytes);
                let num = f;
                let mut tmp = F::zero();
                if neg.is_some() {
                    tmp -= num;
                } else {
                    tmp = num;
                }
                let pos = Pos::from_upto(from, upto);
                Ok((upto, Syntax::Num(pos, tmp)))
            }
            // when more uint types are supported we can do:
            #[allow(clippy::unnested_or_patterns)]
            Some("u8") | Some("u16") | Some("u32") | Some("u128") | Some("i8") | Some("i16")
            | Some("i32") | Some("i128") => {
                let suffix = suffix.unwrap();
                ParseError::throw(
                    from,
                    ParseErrorKind::Custom(format!("Numeric suffix {suffix} not yet supported")),
                )
            }
            Some("i64") => {
                let (_, x) =
                    ParseError::res(u64::from_str_radix(&digits, base.radix()), from, |e| {
                        ParseErrorKind::ParseIntErr(e)
                    })?;
                let pos = Pos::from_upto(from, upto);
                Ok((upto, Syntax::I64(pos, neg.is_some(), x)))
            }
            None | Some("u64") => {
                let (_, x) =
                    ParseError::res(u64::from_str_radix(&digits, base.radix()), from, |e| {
                        ParseErrorKind::ParseIntErr(e)
                    })?;
                let pos = Pos::from_upto(from, upto);
                if neg.is_some() {
                    Ok((upto, Syntax::I64(pos, neg.is_some(), x)))
                } else {
                    Ok((upto, Syntax::U64(pos, x)))
                }
            }
            _ => unreachable!("implementation error in parse_nat"),
        }
    }
}

fn parse_prefixed_hex_digest<F: Field>(
    prefix: &'static str,
    digest_size: usize,
) -> impl Fn(Span<'_>) -> ParseResult<'_, (Pos, Vec<F>)> {
    move |from: Span<'_>| {
        let (i, _) = tag(prefix)(from)?;
        let (i, digits) = base::parse_litbase_digits(base::LitBase::Hex)(i)?;
        let (i, be_bytes) = be_bytes_from_digits(base::LitBase::Hex, &digits, i)?;
        let mut num = BigUint::from_bytes_be(&be_bytes);
        let mut res = Vec::with_capacity(digest_size); // This is stored in little-endian
        for _ in 0..digest_size {
            let rem = &num % F::order();
            res.push(F::from_canonical_u32(rem.try_into().unwrap()));
            num /= F::order();
        }
        if num != BigUint::ZERO {
            ParseError::throw(
                from,
                ParseErrorKind::DigestLiteralTooBig(BigUint::from_bytes_be(&be_bytes)),
            )
        } else {
            let pos = Pos::from_upto(from, i);
            Ok((i, (pos, res)))
        }
    }
}

fn parse_big_num<F: Field>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, (pos, res)) = parse_prefixed_hex_digest("#0x", DIGEST_SIZE)(from)?;
        Ok((i, Syntax::BigNum(pos, res.try_into().unwrap())))
    }
}

fn parse_comm<F: Field>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, (pos, res)) = parse_prefixed_hex_digest("#c0x", DIGEST_SIZE)(from)?;
        Ok((i, Syntax::Comm(pos, res.try_into().unwrap())))
    }
}

fn be_bytes_from_digits<'a>(
    base: base::LitBase,
    digits: &str,
    i: Span<'a>,
) -> ParseResult<'a, Vec<u8>> {
    let (i, bytes) = match base_x::decode(base.base_digits(), digits) {
        Ok(bytes) => Ok((i, bytes)),
        Err(_) => Err(nom::Err::Error(ParseError::new(
            i,
            ParseErrorKind::InvalidBaseEncoding(base),
        ))),
    }?;
    Ok((i, bytes))
}

fn f_from_be_bytes<F: Field>(bs: &[u8]) -> F {
    let mut res = F::zero();
    let mut bs = bs.iter().peekable();
    while let Some(b) = bs.next() {
        let b = F::from_canonical_u8(*b);
        if bs.peek().is_none() {
            res.add_assign(b)
        } else {
            res.add_assign(b);
            res.mul_assign(F::from_canonical_u16(256u16));
        }
    }
    res
}

fn parse_string<F>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (upto, s) = string::parse_string('"')(from)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::String(pos, s)))
    }
}

// hash syntax for chars
fn parse_hash_char<F>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    |from: Span<'_>| {
        let (i, _) = tag("#\\")(from)?;
        let (upto, c) = alt((string::parse_unicode(), anychar))(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::Char(pos, c)))
    }
}

fn parse_char<F>() -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("'")(from)?;
        let (i, s) = string::parse_string_inner1('\'', true, "()'")(i)?;
        // FIXME(#342): '(' does not parse, do we need () in the `must_escape` above
        let (upto, _) = tag("'")(i)?;
        let mut chars: Vec<char> = s.chars().collect();
        if chars.len() == 1 {
            let c = chars.pop().unwrap();
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Char(pos, c)))
        } else {
            ParseError::throw(from, ParseErrorKind::InvalidChar(s))
        }
    }
}

fn parse_list<F: Field>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("(")(from)?;
        let (i, xs) = many0(preceded(
            parse_space,
            parse_syntax(state.clone(), create_unknown_packages),
        ))(i)?;
        let (i, end) = opt(preceded(
            preceded(parse_space, tag(".")),
            preceded(
                parse_space,
                parse_syntax(state.clone(), create_unknown_packages),
            ),
        ))(i)?;
        let (i, _) = parse_space(i)?;
        let (upto, _) = tag(")")(i)?;
        let pos = Pos::from_upto(from, upto);
        if let Some(end) = end {
            Ok((upto, Syntax::Improper(pos, xs, Box::new(end))))
        } else {
            Ok((upto, Syntax::List(pos, xs)))
        }
    }
}

fn parse_meta<F: Field>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        let (i, _) = tag("!(")(from)?;

        // parse the head symbol in the meta package
        let saved_package = state.borrow().get_current_package_name().clone();
        state
            .borrow_mut()
            .set_current_package(meta_package_symbol().into())
            .expect("meta package is not available");
        let (i, sym) = preceded(
            parse_space,
            parse_symbol(state.clone(), create_unknown_packages),
        )(i)?;
        // then recover the previous package
        state
            .borrow_mut()
            .set_current_package(saved_package)
            .expect("previous package is not available");

        let (i, args) = many0(preceded(
            parse_space,
            parse_syntax(state.clone(), create_unknown_packages),
        ))(i)?;

        let (i, _) = parse_space(i)?;
        let (upto, _) = tag(")")(i)?;
        let pos = Pos::from_upto(from, upto);
        Ok((upto, Syntax::Meta(pos, sym, args)))
    }
}

fn parse_char_or_quote<F: Field>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        if let (i, Some(c)) = opt(parse_char())(from)? {
            Ok((i, c))
        } else {
            let (i, _) = tag("'")(from)?;
            let (upto, s) = parse_syntax(state.clone(), create_unknown_packages)(i)?;
            let pos = Pos::from_upto(from, upto);
            Ok((upto, Syntax::Quote(pos, Box::new(s))))
        }
    }
}

fn parse_syntax<F: Field>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Syntax<F>> {
    move |from: Span<'_>| {
        alt((
            parse_list(state.clone(), create_unknown_packages),
            parse_meta(state.clone(), create_unknown_packages),
            parse_numeric(),
            parse_comm(),
            parse_big_num(),
            parse_symbol_syntax(state.clone(), create_unknown_packages),
            parse_string(),
            parse_char_or_quote(state.clone(), create_unknown_packages),
            parse_hash_char(),
        ))(from)
    }
}

pub fn parse_syntax_eof<F: Field>(
    state: StateRcCell,
    create_unknown_packages: bool,
) -> impl Fn(Span<'_>) -> ParseResult<'_, Option<Syntax<F>>> {
    move |from: Span<'_>| {
        if let (_, Some(_)) = opt(eof)(from)? {
            // end of file
            return Ok((from, None));
        }
        let (end, syntax) = parse_syntax(state.clone(), create_unknown_packages)(from)?;
        Ok((end, Some(syntax)))
    }
}

pub fn parse<F: Field>(
    input: Span<'_>,
    state: StateRcCell,
    create_unknown_packages: bool,
) -> Result<Option<(Span<'_>, Syntax<F>)>> {
    match preceded(
        parse_space,
        parse_syntax_eof(state, create_unknown_packages),
    )
    .parse(input)
    {
        Err(e) => bail!(format!("{e}")),
        Ok((_, None)) => Ok(None),
        Ok((rest, Some(syn))) => Ok(Some((rest, syn))),
    }
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::core::{parser::syntax::parse_syntax, state::State};

    #[test]
    fn test_digest() {
        let state = State::init_lurk_state().rccell();
        let (rest, syn) = parse_syntax::<BabyBear>(state.clone(), false)(
            "#0x123456789ABCDEFEDCBA98765432123456789ABCDEFEDCBA98765432123456".into(),
        )
        .unwrap();
        assert!(rest.is_empty());
        assert_eq!(
            format!("{syn}"),
            "#0x123456789abcdefedcba98765432123456789abcdefedcba98765432123456"
        );

        let (rest, syn) =
            parse_syntax::<BabyBear>(state, false)("#0x000000000000000000123456789".into())
                .unwrap();
        assert!(rest.is_empty());
        assert_eq!(format!("{syn}"), "#0x123456789");
    }
}
