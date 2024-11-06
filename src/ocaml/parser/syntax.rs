use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, anychar, digit1, multispace0, multispace1},
    combinator::{opt, peek},
    multi::{many0, many1, many_till},
    number::complete::double,
    sequence::{delimited, pair, preceded},
};

use crate::{
    core::parser::{
        base,
        error::{ParseError, ParseErrorKind},
        position::Pos,
        string, ParseResult, Span,
    },
    ocaml::syntax::LambdaSyntax,
};

fn parse_ident(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    // see https://ocaml.org/manual/5.2/lex.html#sss:lex:identifiers
    // in the lambda IR, identifiers get appended an additional '/XXX' numerical suffix for disambiguation
    // for globals/modules, the '!' character is used as well
    // for match/switch statements, '*' is added, and sometimes used as a prefix
    let (i, init) = alt((alpha1, tag("*")))(from)?;
    let (i, ident) = many0(alt((
        alpha1,
        digit1,
        tag("_"),
        tag("'"),
        tag("/"),
        tag("!"),
        tag("*"),
    )))(i)?;
    let ident = [init]
        .into_iter()
        .chain(ident)
        .fold(String::new(), |mut r, s| {
            r.push_str(s.fragment());
            r
        });
    Ok((i, LambdaSyntax::Ident(Pos::from_upto(from, i), ident)))
}

fn parse_numeric(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, _) = opt(parse_int)(from)?;
    if i.fragment().starts_with(".")
        || i.fragment().starts_with("e")
        || i.fragment().starts_with("E")
    {
        parse_float(from)
    } else {
        parse_int(from)
    }
}

fn parse_float(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (upto, f) = double(from)?;
    Ok((upto, LambdaSyntax::Float(Pos::from_upto(from, upto), f)))
}

fn parse_int(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, neg) = opt(tag("-"))(from)?;
    // NOTE: As far as I can tell, ocamlc only outputs integers in decimal format, e.g. 0x123 is output at 291
    let (upto, digits) = base::parse_litbase_digits(base::LitBase::Dec)(i)?;

    let (_, x) = ParseError::res(digits.parse::<u64>(), from, |e| {
        ParseErrorKind::ParseIntErr(e)
    })?;
    let pos = Pos::from_upto(from, upto);

    Ok((upto, LambdaSyntax::Int(pos, neg.is_some(), x)))
}

fn parse_string(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (upto, s) = string::parse_string('"')(from)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, LambdaSyntax::String(pos, s)))
}

fn parse_char(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, _) = tag("'")(from)?;
    let (i, s) = string::parse_string_inner1('\'', true, "'")(i)?;
    let (upto, _) = tag("'")(i)?;
    let mut chars: Vec<char> = s.chars().collect();
    if chars.len() == 1 {
        let c = chars.pop().unwrap();
        let pos = Pos::from_upto(from, upto);
        Ok((upto, LambdaSyntax::Char(pos, c)))
    } else {
        ParseError::throw(from, ParseErrorKind::InvalidChar(s))
    }
}

fn parse_record(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, id) = delimited(tag("["), digit1, tag(":"))(from)?;
    let (_, id) = ParseError::res(id.parse::<u64>(), from, ParseErrorKind::ParseIntErr)?;
    let (i, xs) = many0(parse_syntax)(i)?;
    let (upto, _) = tag("]")(i)?;
    let pos = Pos::from_upto(from, upto);
    Ok((upto, LambdaSyntax::Record(pos, id, xs)))
}

fn peek_for_fallback(from: Span<'_>) -> ParseResult<'_, ()> {
    // when reading fallback literals, only separators are () and spaces
    let (i, _) = peek(alt((tag("("), tag(")"), multispace1)))(from)?;
    Ok((i, ()))
}

fn parse_fallback_literal(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, (head_chars, _)) = many_till(anychar, peek_for_fallback)(from)?;
    let head = head_chars.into_iter().fold(String::new(), |mut s, c| {
        s.push(c);
        s
    });
    if head.is_empty() {
        return ParseError::throw(
            from,
            ParseErrorKind::OCaml("Invalid fallback literal".into()),
        );
    }
    let pos = Pos::from_upto(from, i);
    Ok((i, LambdaSyntax::FallbackLiteral(pos, head)))
}

fn parse_let_binding(from: Span<'_>) -> ParseResult<'_, (LambdaSyntax, LambdaSyntax)> {
    let (i, ident) = preceded(multispace0, parse_ident)(from)?;
    let (i, _eq) = preceded(multispace1, parse_fallback_literal)(i)?;
    let (i, val) = preceded(multispace0, parse_syntax)(i)?;
    Ok((i, (ident, val)))
}

fn parse_letrec_binding(from: Span<'_>) -> ParseResult<'_, (LambdaSyntax, LambdaSyntax)> {
    let (i, ident) = preceded(multispace0, parse_ident)(from)?;
    let (i, val) = preceded(multispace0, parse_syntax)(i)?;
    Ok((i, (ident, val)))
}

fn parse_function_arg(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, ident) = preceded(multispace0, parse_ident)(from)?;
    // consume and ignore the "[int]" annotations
    let (i, _) = opt(tag("[int]"))(i)?;
    Ok((i, ident))
}

fn parse_primitive_sexp(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    let (i, _) = tag("(")(from)?;

    let (i, (head_chars, _)) = many_till(anychar, peek_for_fallback)(i)?;
    let head = head_chars.into_iter().fold(String::new(), |mut s, c| {
        s.push(c);
        s
    });
    if head.is_empty() {
        return ParseError::throw(
            from,
            ParseErrorKind::OCaml("Invalid head of S-expression".into()),
        );
    }

    match head.as_str() {
        "setglobal" => {
            let (i, ident) = preceded(multispace1, parse_ident)(i)?;
            let (i, val) = preceded(multispace1, parse_syntax)(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Setglobal(pos, ident.into(), val.into())))
        }
        "seq" => {
            let (i, xs) = many1(preceded(multispace0, parse_syntax))(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Seq(pos, xs)))
        }
        "makeblock" => {
            let (i, id_digits) =
                preceded(multispace1, base::parse_litbase_digits(base::LitBase::Dec))(i)?;
            let (_, id) = ParseError::res(id_digits.parse::<u64>(), from, |e| {
                ParseErrorKind::ParseIntErr(e)
            })?;
            let (i, xs) = many0(preceded(multispace0, parse_syntax))(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Makeblock(pos, id, xs)))
        }
        "let" => {
            let (i, bindings) = delimited(
                pair(multispace1, tag("(")),
                many1(preceded(multispace0, parse_let_binding)),
                tag(")"),
            )(i)?;
            let (i, body) = preceded(multispace0, parse_syntax)(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Let(pos, bindings, body.into())))
        }
        "letrec" => {
            let (i, bindings) = delimited(
                pair(multispace1, tag("(")),
                many1(preceded(multispace0, parse_letrec_binding)),
                tag(")"),
            )(i)?;
            let (i, body) = preceded(multispace0, parse_syntax)(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Letrec(pos, bindings, body.into())))
        }
        "function" => {
            let (i, args) = many0(preceded(multispace0, parse_function_arg))(i)?;
            let (i, body) = preceded(
                alt((
                    delimited(multispace1, tag(": int"), multispace1),
                    multispace1,
                )),
                parse_syntax,
            )(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Function(pos, args, body.into())))
        }
        "apply" => {
            let (i, func) = preceded(multispace1, parse_syntax)(i)?;
            let (i, args) = many1(preceded(multispace0, parse_syntax))(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::Apply(pos, func.into(), args)))
        }
        _ => {
            // parse as a placeholder fallback s-expression
            let (i, tail) = many0(preceded(
                multispace0,
                alt((parse_syntax, preceded(multispace0, parse_fallback_literal))),
            ))(i)?;
            let (i, _) = preceded(multispace0, tag(")"))(i)?;
            let pos = Pos::from_upto(from, i);
            Ok((i, LambdaSyntax::FallbackPrimitive(pos, head, tail)))
        }
    }
}

pub fn parse_syntax(from: Span<'_>) -> ParseResult<'_, LambdaSyntax> {
    delimited(
        multispace0,
        alt((
            parse_primitive_sexp,
            parse_ident,
            parse_numeric,
            parse_string,
            parse_char,
            parse_record,
        )),
        multispace0,
    )(from)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_parser(input: &str, expected: Option<LambdaSyntax>) {
        let span = Span::new(input);
        let (rest, res) = parse_syntax(span).unwrap();
        assert!(rest.is_empty());
        if let Some(expected) = expected {
            assert_eq!(res, expected);
        }
    }

    macro_rules! test {
        ($test_func:ident, $input_str:expr) => {
            #[test]
            fn $test_func() {
                test_parser($input_str, None)
            }
        };
        ($test_func:ident, $input_str:expr, $expected_cloj:expr) => {
            #[test]
            fn $test_func() {
                let placeholder_span = Span::new("");
                let p = Pos::from_upto(placeholder_span, placeholder_span);
                let expected = ($expected_cloj)(p);
                test_parser($input_str, Some(expected))
            }
        };
    }

    // test file generated by ocamlc 4.14.2 on `tests/mastermind.ml`
    test!(test_mastermind, include_str!("tests/mastermind.ir"));

    test!(test_int, "123", |p| LambdaSyntax::Int(p, false, 123));
    test!(test_int2, "-123", |p| LambdaSyntax::Int(p, true, 123));
    test!(test_float, "123.456", |p| LambdaSyntax::Float(p, 123.456));
    test!(test_float2, "-123.456", |p| LambdaSyntax::Float(
        p, -123.456
    ));
    test!(test_float3, "1.0e-5", |p| LambdaSyntax::Float(p, 1.0e-5));
    test!(test_float4, "1.0E-5", |p| LambdaSyntax::Float(p, 1.0e-5));
    test!(test_float5, "1e-5", |p| LambdaSyntax::Float(p, 1e-5));
    test!(test_float6, "1E-5", |p| LambdaSyntax::Float(p, 1e-5));
    test!(test_float7, "1.0e5", |p| LambdaSyntax::Float(p, 1.0e5));
    test!(test_float8, "1e5", |p| LambdaSyntax::Float(p, 1e5));
    test!(test_float9, "5.", |p| LambdaSyntax::Float(p, 5.));
    test!(test_float10, "-5.", |p| LambdaSyntax::Float(p, -5.));
    test!(test_ident, "abc'ABC123_/!*", |p| LambdaSyntax::Ident(
        p,
        "abc'ABC123_/!*".into()
    ));
    test!(test_ident2, "  Data!\n", |p| LambdaSyntax::Ident(
        p,
        "Data!".into()
    ));
    test!(test_char, "'a'", |p| LambdaSyntax::Char(p, 'a'));
    test!(test_char2, r"'\n'", |p| LambdaSyntax::Char(p, '\n'));
    test!(test_char3, r"'\''", |p| LambdaSyntax::Char(p, '\''));
    test!(
        test_string,
        "\"abc def () 123 -- #$%^!@*&_+=-\\\\|\"",
        |p| { LambdaSyntax::String(p, "abc def () 123 -- #$%^!@*&_+=-\\|".into()) }
    );
    test!(test_record, "[0: 0]", |p| LambdaSyntax::Record(
        p,
        0,
        vec![LambdaSyntax::Int(p, false, 0)],
    ));
    test!(test_record2, "[123: abc [456: 7.89] 'd']", |p| {
        LambdaSyntax::Record(
            p,
            123,
            vec![
                LambdaSyntax::Ident(p, "abc".into()),
                LambdaSyntax::Record(p, 456, vec![LambdaSyntax::Float(p, 7.89)]),
                LambdaSyntax::Char(p, 'd'),
            ],
        )
    });
    test!(test_fallback, "(fallback)", |p| {
        LambdaSyntax::FallbackPrimitive(p, "fallback".into(), vec![])
    });
    test!(test_fallback2, "(fallback\n(fallback 123))", |p| {
        LambdaSyntax::FallbackPrimitive(
            p,
            "fallback".into(),
            vec![LambdaSyntax::FallbackPrimitive(
                p,
                "fallback".into(),
                vec![LambdaSyntax::Int(p, false, 123)],
            )],
        )
    });
    test!(test_fallback3, "(int,*,*)", |p| {
        LambdaSyntax::FallbackPrimitive(p, "int,*,*".into(), vec![])
    });
    test!(test_fallback4, "(!= 1 1)", |p| {
        LambdaSyntax::FallbackPrimitive(
            p,
            "!=".into(),
            vec![
                LambdaSyntax::Int(p, false, 1),
                LambdaSyntax::Int(p, false, 1),
            ],
        )
    });
    test!(test_fallback5, "(*match*/273)", |p| {
        LambdaSyntax::FallbackPrimitive(p, "*match*/273".into(), vec![])
    });
    test!(test_fallback6, "(asdf *match*/273)", |p| {
        LambdaSyntax::FallbackPrimitive(
            p,
            "asdf".into(),
            vec![LambdaSyntax::Ident(p, "*match*/273".into())],
        )
    });
    test!(test_setglobal, "(setglobal Abc! 123)", |p| {
        LambdaSyntax::Setglobal(
            p,
            LambdaSyntax::Ident(p, "Abc!".into()).into(),
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function1, "(function 123)", |p| {
        LambdaSyntax::Function(p, vec![], LambdaSyntax::Int(p, false, 123).into())
    });
    test!(test_function2, "(function x 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![LambdaSyntax::Ident(p, "x".into())],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function3, "(function x/123 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![LambdaSyntax::Ident(p, "x/123".into())],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function4, "(function x/123 y/456 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![
                LambdaSyntax::Ident(p, "x/123".into()),
                LambdaSyntax::Ident(p, "y/456".into()),
            ],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function5, "(function : int 123)", |p| {
        LambdaSyntax::Function(p, vec![], LambdaSyntax::Int(p, false, 123).into())
    });
    test!(test_function6, "(function x[int] 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![LambdaSyntax::Ident(p, "x".into())],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function7, "(function x[int] : int 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![LambdaSyntax::Ident(p, "x".into())],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
    test!(test_function8, "(function x/123[int] : int 123)", |p| {
        LambdaSyntax::Function(
            p,
            vec![LambdaSyntax::Ident(p, "x/123".into())],
            LambdaSyntax::Int(p, false, 123).into(),
        )
    });
}
