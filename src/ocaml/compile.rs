use std::{fs, process::Command};

use anyhow::{anyhow, bail, Result};
use camino::Utf8Path;
use nom::Parser;
use p3_field::Field;
use tempfile::tempdir;

use crate::{
    core::{
        parser::Span,
        state::{builtin_sym, user_sym, StateRcCell, BUILTIN_SYMBOLS},
        zstore::{ZPtr, ZStore},
    },
    lair::chipset::Chipset,
    ocaml::parser::syntax::parse_syntax,
};

use super::syntax::LambdaSyntax;

/// Compiles and transforms a file into its corresponding Lurk program.
pub fn compile_and_transform_single_file<F: Field, C1: Chipset<F>>(
    zstore: &mut ZStore<F, C1>,
    state: &StateRcCell,
    file_path: &Utf8Path,
) -> Result<ZPtr<F>> {
    let lambda_ir = compile_single_file(file_path)?;
    let (rest, lambda) = parse_syntax
        .parse(Span::new(&lambda_ir))
        .expect("Lambda IR failed to parse");
    assert!(rest.is_empty(), "Lambda parsing failure");
    let zptr = transform_lambda_program(zstore, state, &lambda)?;
    Ok(zptr)
}

/// Compiles a single file with `ocamlc` and returns the resulting lambda IR.
pub fn compile_single_file(orig_path: &Utf8Path) -> Result<String> {
    let file_contents = fs::read_to_string(orig_path)?;
    let file_name = orig_path
        .file_name()
        .ok_or(anyhow!("Invalid file name: {}", orig_path))?;
    compile_single_file_contents(file_contents.as_str(), file_name)
}

/// Compiles a single file with `ocamlc` and returns the resulting lambda IR.
///
/// This writes the data to a temporary file in a temporary directory, runs
/// `ocamlc -dlambda -dno-unique-ids -warn-error +a -c <file>` and captures the stderr.
/// The flags ensure that the code compiles with no warnings, since the lambda IR is
/// output to stderr alongside any warnings/errors. `-c` inhibits the final link step,
/// and `-dno-unique-ids` removes the unique suffix added to identifiers.
pub fn compile_single_file_contents(source: &str, file_name: &str) -> Result<String> {
    // create a temporary directory because ocamlc generates .cmi and .cmo files
    let file_dir = tempdir()?;
    let file_path = file_dir.path().join(file_name);
    file_path
        .extension()
        .ok_or_else(|| anyhow!("Filenames must end in .ml: {}", file_name))?;
    let file_path = Utf8Path::from_path(&file_path)
        .ok_or_else(|| anyhow!("Invalid temporary path: {}", file_path.display()))?;
    fs::write(file_path, source)?;
    // because the compiler outputs the lambda IR from `-dlambda` on stderr,
    // if there are any warnings it would be caught in the output
    // below we turn all warnings into errors, but we could also
    // silence all warnings with ``-w -a``
    let output = Command::new("ocamlc")
        .args([
            "-dlambda",        // output lambda IR
            "-dno-unique-ids", // this disables the unique suffixes
            "-warn-error",     // set all warnings as errors
            "+a",
            "-c", // compile only (don't generate executable)
            file_path.as_str(),
        ])
        .current_dir(&file_dir)
        .output()?;
    let stderr = String::from_utf8(output.stderr)?;
    if !output.status.success() {
        bail!("Compilation failed: {}", stderr)
    } else {
        Ok(stderr)
    }
}

/// Compiles a full "program" from `LambdaSyntax` into its corresponding Lurk data form.
///
/// This adds a wrapper with helper functions used by the transformed code.
pub fn transform_lambda_program<F: Field, C1: Chipset<F>>(
    zstore: &mut ZStore<F, C1>,
    state: &StateRcCell,
    expr: &LambdaSyntax,
) -> Result<ZPtr<F>> {
    // TODO: we only want to include the helpers that are actually used -- for now these are always added for every program
    let eq = zstore.intern_symbol_no_lang(&builtin_sym("eq"));
    let not_eq = zstore.intern_symbol_no_lang(&state.borrow_mut().intern("!="));
    let lambda = zstore.intern_symbol_no_lang(&builtin_sym("lambda"));
    let arg_a = zstore.intern_symbol_no_lang(&state.borrow_mut().intern("a"));
    let arg_b = zstore.intern_symbol_no_lang(&state.borrow_mut().intern("b"));
    let bin_args = zstore.intern_list([arg_a, arg_b]);
    let if_ = zstore.intern_symbol_no_lang(&builtin_sym("if"));
    let eq_cond = zstore.intern_list([eq, arg_a, arg_b]);
    let t = *zstore.t();
    let nil = *zstore.nil();
    let not_eq_body = zstore.intern_list([if_, eq_cond, nil, t]);
    let not_eq_lambda = zstore.intern_list([lambda, bin_args, not_eq_body]);
    let not_eq_bind = zstore.intern_list([not_eq, not_eq_lambda]);

    let bindings = zstore.intern_list([not_eq_bind]);

    let let_ = zstore.intern_symbol_no_lang(&builtin_sym("let"));

    let result = transform_lambda(zstore, state, expr)?;

    Ok(zstore.intern_list([let_, bindings, result]))
}

/// Transforms a `LambdaSyntax` into its corresponding Lurk data form.
fn transform_lambda<F: Field, C1: Chipset<F>>(
    zstore: &mut ZStore<F, C1>,
    state: &StateRcCell,
    expr: &LambdaSyntax,
) -> Result<ZPtr<F>> {
    let out = match expr {
        LambdaSyntax::Ident(_, sym) => {
            let sym = state.borrow_mut().intern(sym);
            zstore.intern_symbol_no_lang(&sym)
        }
        LambdaSyntax::Int(_, sign, i) => {
            // TODO: output i63s
            if *sign {
                let minus = zstore.intern_symbol_no_lang(&builtin_sym("-"));
                let zero = zstore.intern_u64(0);
                let i = zstore.intern_u64(*i);
                zstore.intern_list([minus, zero, i])
            } else {
                zstore.intern_u64(*i)
            }
        }
        LambdaSyntax::Float(_, _) => {
            // We do not support floats, but emit a `(fail)` so we still generate something
            let fail = zstore.intern_symbol_no_lang(&builtin_sym("fail"));
            zstore.intern_list([fail])
        }
        LambdaSyntax::Char(_, c) => zstore.intern_char(*c),
        LambdaSyntax::String(_, s) => zstore.intern_string(s),
        LambdaSyntax::Setglobal(_, _id, val) => transform_lambda(zstore, state, val)?,
        LambdaSyntax::Seq(_, xs) => {
            let xs = xs
                .iter()
                .map(|x| transform_lambda(zstore, state, x))
                .collect::<Result<Vec<_>>>()?;
            let begin = zstore.intern_symbol_no_lang(&builtin_sym("begin"));
            let mut l = vec![begin];
            l.extend(xs);
            zstore.intern_list(l)
        }
        LambdaSyntax::Record(_, id, xs) | LambdaSyntax::Makeblock(_, id, xs) => {
            let xs = xs
                .iter()
                .map(|x| transform_lambda(zstore, state, x))
                .collect::<Result<Vec<_>>>()?;
            let list = zstore.intern_symbol_no_lang(&builtin_sym("list"));
            let id = zstore.intern_u64(*id);
            let mut l = vec![list, id];
            l.extend(xs);
            zstore.intern_list(l)
        }
        LambdaSyntax::Let(_, binds, body) | LambdaSyntax::Letrec(_, binds, body) => {
            let head = match expr {
                LambdaSyntax::Let(_, _, _) => zstore.intern_symbol_no_lang(&builtin_sym("let")),
                LambdaSyntax::Letrec(_, _, _) => {
                    zstore.intern_symbol_no_lang(&builtin_sym("letrec"))
                }
                _ => unreachable!(),
            };
            let binds = binds
                .iter()
                .map(|(var, val)| {
                    let var = transform_lambda(zstore, state, var)?;
                    let val = transform_lambda(zstore, state, val)?;
                    let res = zstore.intern_list([var, val]);
                    Ok(res)
                })
                .collect::<Result<Vec<_>>>()?;
            let binds = zstore.intern_list(binds);
            let body = transform_lambda(zstore, state, body)?;
            zstore.intern_list([head, binds, body])
        }
        LambdaSyntax::Function(_, args, body) => {
            let args = args
                .iter()
                .map(|x| transform_lambda(zstore, state, x))
                .collect::<Result<Vec<_>>>()?;
            let args = zstore.intern_list(args);
            let body = transform_lambda(zstore, state, body)?;
            let lambda = zstore.intern_symbol_no_lang(&builtin_sym("lambda"));
            zstore.intern_list([lambda, args, body])
        }
        LambdaSyntax::Apply(_, func, args) => {
            let func = transform_lambda(zstore, state, func)?;
            let args = args
                .iter()
                .map(|x| transform_lambda(zstore, state, x))
                .collect::<Result<Vec<_>>>()?;
            let mut l = vec![func];
            l.extend(args);
            zstore.intern_list(l)
        }

        LambdaSyntax::FallbackPrimitive(_, prim, args) => {
            let args = args
                .iter()
                .map(|a| transform_lambda(zstore, state, a))
                .collect::<Result<Vec<_>>>()?;
            // TODO: placeholder for primitives, might want to refactor this
            // more complex primitives
            let prim = match prim.as_str() {
                "==" => "eq", // NOTE: using `eq` since `==` can be used for non-integers too
                "mod" => "%",
                _ => prim,
            };
            let prim = if BUILTIN_SYMBOLS.contains(&prim) {
                builtin_sym(prim) // this transparently handles + - etc
            } else {
                user_sym(prim)
            };
            let prim = zstore.intern_symbol_no_lang(&prim);
            let mut l = vec![prim];
            l.extend(args);
            zstore.intern_list(l)
        }
        LambdaSyntax::FallbackLiteral(_, lit) => {
            let mut lit = user_sym(lit);
            lit.set_as_keyword();
            zstore.intern_symbol_no_lang(&lit)
        }
    };
    Ok(out)
}
