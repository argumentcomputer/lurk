use anyhow::{bail, Result};
use camino::Utf8Path;
use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sphinx_core::stark::StarkGenericConfig;
use std::{
    io::{Read, Write},
    net::{TcpListener, TcpStream},
};

use crate::{
    lair::{chipset::Chipset, lair_chip::LairMachineProgram},
    lurk::{
        big_num::field_elts_to_biguint,
        cli::{
            paths::{commits_dir, proofs_dir},
            proofs::{get_verifier_version, IOProof},
            repl::Repl,
        },
        package::{Package, SymbolRef},
        state::builtin_sym,
        tag::Tag,
        zstore::{ZPtr, DIGEST_SIZE},
    },
};

use super::{
    comm_data::CommData,
    debug::debug_mode,
    lurk_data::LurkData,
    proofs::{CallableData, ChainProof, ProtocolProof},
};

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) struct MetaCmd<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> {
    name: &'static str,
    summary: &'static str,
    format: &'static str,
    info: &'static [&'static str],
    example: &'static [&'static str],
    pub(crate) run:
        fn(repl: &mut Repl<F, C1, C2>, args: &ZPtr<F>, file_path: &Utf8Path) -> Result<()>,
}

pub(crate) type MetaCmdsMap<F, C1, C2> = FxHashMap<&'static str, MetaCmd<F, C1, C2>>;

impl<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> MetaCmd<F, C1, C2> {
    const ASSERT: Self = Self {
        name: "assert",
        summary: "Asserts that an expression doesn't reduce to nil.",
        format: "!(assert <expr>)",
        info: &[],
        example: &["!(assert t)", "!(assert (eq 3 (+ 1 2)))"],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            if &result == repl.zstore.nil() {
                eprintln!("assert failed. {} evaluates to nil", repl.fmt(&expr));
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_EQ: Self = Self {
        name: "assert-eq",
        summary: "Assert that two expressions evaluate to the same value.",
        format: "!(assert-eq <expr1> <expr2>)",
        info: &[],
        example: &["!(assert-eq 3 (+ 1 2))"],
        run: |repl, args, _path| {
            let (&expr1, &expr2) = repl.peek2(args)?;
            let (result1, _) = repl.reduce_aux(&expr1)?;
            if result1.tag == Tag::Err {
                bail!("LHS reduction error: {}", repl.fmt(&result1));
            }
            let (result2, _) = repl.reduce_aux(&expr2)?;
            if result2.tag == Tag::Err {
                bail!("RHS reduction error: {}", repl.fmt(&result2));
            }
            if result1 != result2 {
                repl.memoize_dag(result1.tag, &result1.digest);
                repl.memoize_dag(result2.tag, &result2.digest);
                eprintln!(
                    "assert-eq failed. {} ≠ {}",
                    repl.fmt(&result1),
                    repl.fmt(&result2)
                );
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_ERROR: Self = Self {
        name: "assert-error",
        summary: "Assert that a evaluation of <expr> fails.",
        format: "!(assert-error <expr>)",
        info: &[],
        example: &["!(assert-error (1 1))"],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag != Tag::Err {
                eprintln!(
                    "assert-error failed. {} doesn't result on evaluation error.",
                    repl.fmt(&expr)
                );
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_EMITTED: Self = Self {
        name: "assert-emitted",
        summary: "Asserts that the evaluation of an expr emits expected values",
        format: "!(assert-emitted <expr> <expr>)",
        info: &[
            "Asserts that the list of values in the first <expr> are emitted by",
            "the reduction of the second <expr>.",
        ],
        example: &["!(assert-emitted '(1 2) (begin (emit 1) (emit 2)))"],
        run: |repl, args, _path| {
            let (&expected_expr, &expr) = repl.peek2(args)?;
            let (expected, _) = repl.reduce_aux(&expected_expr)?;
            let (result, emitted) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            let emitted = repl.zstore.intern_list(emitted);
            if expected != emitted {
                repl.memoize_dag(expected.tag, &expected.digest);
                // DAG for `emitted` has already been memoized
                eprintln!(
                    "assert-emitted failed. Expected {} but got {}",
                    repl.fmt(&expected),
                    repl.fmt(&emitted)
                );
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const DEBUG: Self = Self {
        name: "debug",
        summary: "Enters the debug mode for a reduction",
        format: "!(debug <expr>?)",
        info: &[
            "There are three kinds of lines shown in debug mode:",
            " ?<d>: <e>       - at depth <d>, <e> will be evaluated",
            "  <d>: <e> ↦ <r> - at depth <d>, <e> evaluated to <r>",
            " !<d>: <e> ↦ <r> - at depth <d>, <e> evaluated to <r> (memoized)",
            "You can use the following keys to navigate:",
            " ↓            - next line",
            " ↑            - previous line",
            " →            - line for the next entry in the same depth",
            " ←            - line for the previous entry in the same depth",
            " ^↓/PgDn      - scroll down",
            " ^↑/PgUp      - scroll up",
            " ^→/Space     - next breakpoint",
            " ^←/Backspace - previous breakpoint",
            " Home         - first line",
            " End          - last line",
            " Esc/q        - quit debug mode",
        ],
        example: &["(+ 1 1)", "!(debug)", "!(debug (+ 1 1))"],
        run: |repl, args, _path| {
            if args != repl.zstore.nil() {
                let expr = *repl.peek1(args)?;
                let result = repl.handle_non_meta(&expr, None);
                debug_mode(&repl.format_debug_data())?;
                result.map(|_| ())
            } else {
                debug_mode(&repl.format_debug_data())
            }
        },
    };

    const LOAD: Self = Self {
        name: "load",
        summary: "Load Lurk expressions from a file.",
        format: "!(load <string>)",
        info: &[],
        example: &["!(load \"my_file.lurk\")"],
        run: |repl, args, path| {
            let file_name_zptr = repl.peek1(args)?;
            if file_name_zptr.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let file_name = repl.zstore.fetch_string(file_name_zptr);
            repl.load_file(&path.join(file_name), false)
        },
    };

    const DEF: Self = Self {
        name: "def",
        summary: "Extends env with a non-recursive binding.",
        format: "!(def <symbol> <value>)",
        info: &[
            "Gets macroexpanded to (let ((<symbol> <value>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        example: &["!(def foo (lambda () 123))"],
        run: |repl, args, _path| {
            let (&sym, _) = repl.peek2(args)?;
            let let_ = repl
                .zstore
                .intern_symbol(&builtin_sym("let"), &repl.lang_symbols);
            let bindings = repl.zstore.intern_list([*args]);
            let current_env = repl
                .zstore
                .intern_symbol(&builtin_sym("current-env"), &repl.lang_symbols);
            let current_env_call = repl.zstore.intern_list([current_env]);
            let expr = repl.zstore.intern_list([let_, bindings, current_env_call]);
            let (output, _) = repl.reduce_aux(&expr)?;
            if output.tag != Tag::Env {
                bail!("Reduction resulted in {}", repl.fmt(&output));
            }
            repl.env = output;
            println!("{}", repl.fmt(&sym));
            Ok(())
        },
    };

    const DEFREC: Self = Self {
        name: "defrec",
        summary: "Extends env with a recursive binding.",
        format: "!(defrec <symbol> <value>)",
        info: &[
            "Gets macroexpanded to (letrec ((<symbol> <value>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        example: &[
            "!(defrec sum (lambda (l) (if (eq l nil) 0 (+ (car l) (sum (cdr l))))))",
            "(sum '(1 2 3))",
        ],
        run: |repl, args, _path| {
            let (&sym, _) = repl.peek2(args)?;
            let letrec = repl
                .zstore
                .intern_symbol(&builtin_sym("letrec"), &repl.lang_symbols);
            let bindings = repl.zstore.intern_list([*args]);
            let current_env = repl
                .zstore
                .intern_symbol(&builtin_sym("current-env"), &repl.lang_symbols);
            let current_env_call = repl.zstore.intern_list([current_env]);
            let expr = repl
                .zstore
                .intern_list([letrec, bindings, current_env_call]);
            let (output, _) = repl.reduce_aux(&expr)?;
            if output.tag != Tag::Env {
                bail!("Reduction resulted in {}", repl.fmt(&output));
            }
            repl.env = output;
            println!("{}", repl.fmt(&sym));
            Ok(())
        },
    };

    const UPDATE: Self = Self {
        name: "update",
        summary: "Updates an env variable by applying it to a function.",
        format: "!(update <symbol> <function_expr>)",
        info: &[],
        example: &["!(def a 1)", "!(update a (lambda (x) (+ x 1)))"],
        run: |repl, args, _path| {
            let (&sym, &fun) = repl.peek2(args)?;
            Self::validate_binding_var(repl, &sym)?;
            let expr = repl.zstore.intern_list([fun, sym]);
            let (res, _) = repl.reduce_aux(&expr)?;
            if res.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&res));
            }
            println!("{}", repl.fmt(&sym));
            repl.env = repl.zstore.intern_env(sym, res, repl.env);
            Ok(())
        },
    };

    const CLEAR: Self = Self {
        name: "clear",
        summary: "Resets the current environment to be empty.",
        format: "!(clear)",
        info: &[],
        example: &["!(def a 1)", "(current-env)", "!(clear)", "(current-env)"],
        run: |repl, _args, _path| {
            repl.env = repl.zstore.intern_empty_env();
            Ok(())
        },
    };

    const SET_ENV: Self = Self {
        name: "set-env",
        summary: "Sets the env to the result of evaluating the argument.",
        format: "!(set-env <expr>)",
        info: &[],
        example: &["!(set-env (eval '(let ((a 1)) (current-env))))", "a"],
        run: |repl, args, _path| {
            let env_expr = *repl.peek1(args)?;
            let (env, _) = repl.reduce_aux(&env_expr)?;
            if env.tag != Tag::Env {
                bail!("Value must be an environment");
            }
            repl.env = env;
            Ok(())
        },
    };

    const ERASE_FROM_ENV: Self = Self {
        name: "erase-from-env",
        summary: "Erases all bindings for the provided variables from the environment.",
        format: "!(erase-from-env <var1> <var2> ...)",
        info: &["If a variable is not present in the environment, it's ignored."],
        example: &["!(erase-from-env foo bar)"],
        run: |repl, args, _path| {
            repl.memoize_env_dag();
            let (args_vec, _) = repl.zstore.fetch_list(args);
            let new_env_vec = repl
                .zstore
                .fetch_env(&repl.env)
                .into_iter()
                .filter(|(var, _)| !args_vec.contains(var))
                .map(|(var, val)| (*var, *val))
                .collect::<Vec<_>>();
            let mut env = repl.zstore.intern_empty_env();
            for (var, val) in new_env_vec.into_iter().rev() {
                env = repl.zstore.intern_env(var, val, env);
            }
            repl.env = env;
            Ok(())
        },
    };

    fn persist_comm_data(
        secret: ZPtr<F>,
        payload: ZPtr<F>,
        repl: &mut Repl<F, C1, C2>,
    ) -> Result<()> {
        repl.memoize_dag(secret.tag, &secret.digest);
        repl.memoize_dag(payload.tag, &payload.digest);
        let comm_data = CommData::new(secret, payload, &repl.zstore);
        let comm = comm_data.commit(&mut repl.zstore);
        let hash = format!("{:x}", field_elts_to_biguint(&comm.digest));
        std::fs::write(commits_dir()?.join(&hash), bincode::serialize(&comm_data)?)?;
        println!("Hash: #0x{hash}");
        Ok(())
    }

    fn hide(secret: ZPtr<F>, payload_expr: &ZPtr<F>, repl: &mut Repl<F, C1, C2>) -> Result<()> {
        let (payload, _) = repl.reduce_aux(payload_expr)?;
        if payload.tag == Tag::Err {
            bail!("Payload reduction error: {}", repl.fmt(&payload));
        }
        Self::persist_comm_data(secret, payload, repl)
    }

    const HIDE: Self = Self {
        name: "hide",
        summary: "Persists a hiding commitment.",
        format: "!(hide <secret_expr> <payload_expr>)",
        info: &[
            "The secret is the reduction of <secret_expr>, which must be a",
            "bignum, and the payload is the reduction of <payload_expr>.",
        ],
        example: &["!(hide (bignum (commit 123)) 42)", "!(hide #0x123 42)"],
        run: |repl, args, _path| {
            let (&secret_expr, &payload_expr) = repl.peek2(args)?;
            let (secret, _) = repl.reduce_aux(&secret_expr)?;
            if secret.tag != Tag::BigNum {
                bail!("Secret must reduce to a bignum");
            }
            Self::hide(secret, &payload_expr, repl)
        },
    };

    const COMMIT: Self = Self {
        name: "commit",
        summary: "Persists a commitment.",
        format: "!(commit <payload_expr>)",
        info: &[
            "The secret is an opaque commitment whose digest amounts to zeros",
            "and the payload is the reduction of <payload_expr>. Equivalent to",
            "!(hide #0x0 <payload_expr>).",
        ],
        example: &["!(commit 42)"],
        run: |repl, args, _path| {
            let payload_expr = *repl.peek1(args)?;
            let secret = ZPtr::null(Tag::BigNum);
            Self::hide(secret, &payload_expr, repl)
        },
    };

    fn fetch_comm_data(
        repl: &mut Repl<F, C1, C2>,
        digest: &[F],
        print_payload: Option<bool>,
    ) -> Result<()> {
        let hash = format!("{:x}", field_elts_to_biguint(digest));
        let comm_data_bytes = std::fs::read(commits_dir()?.join(&hash))?;
        let comm_data: CommData<F> = bincode::deserialize(&comm_data_bytes)?;
        let message = print_payload.map(|print_payload| {
            if print_payload {
                repl.fmt(&comm_data.payload)
            } else {
                "Data is now available".to_string()
            }
        });
        comm_data.populate_zstore(&mut repl.zstore);
        if let Some(message) = message {
            println!("{message}");
        }
        Ok(())
    }

    const OPEN: Self = Self {
        name: "open",
        summary: "Fetches a persisted commitment and prints the payload.",
        format: "!(open <comm>)",
        info: &[],
        example: &[
            "!(commit 123)",
            "!(open #c0x944834111822843979ace19833d05ca9daf2f655230faec517433e72fe777b)",
        ],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            match result.tag {
                Tag::BigNum | Tag::Comm => Self::fetch_comm_data(repl, &result.digest, Some(true)),
                _ => bail!("Expected a commitment or a BigNum"),
            }
        },
    };

    const FETCH: Self = Self {
        name: "fetch",
        summary: "Fetches a persisted commitment.",
        format: "!(fetch <comm>)",
        info: &[],
        example: &[
            "!(commit 123)",
            "!(fetch #c0x944834111822843979ace19833d05ca9daf2f655230faec517433e72fe777b)",
        ],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            match result.tag {
                Tag::BigNum | Tag::Comm => Self::fetch_comm_data(repl, &result.digest, Some(false)),
                _ => bail!("Expected a commitment or a BigNum"),
            }
        },
    };

    fn call(
        repl: &mut Repl<F, C1, C2>,
        call_expr: &ZPtr<F>,
        env: Option<ZPtr<F>>,
    ) -> Result<ZPtr<F>> {
        if call_expr == repl.zstore.nil() {
            bail!("Missing callable object");
        }
        let (&callable, _) = repl.zstore.fetch_tuple2(call_expr);
        match callable.tag {
            Tag::BigNum | Tag::Comm => {
                let inv_hashes3 = repl.queries.get_inv_queries("hash3", &repl.toplevel);
                if !inv_hashes3.contains_key(callable.digest.as_slice()) {
                    // try to fetch a persisted commitment
                    Self::fetch_comm_data(repl, &callable.digest, None)?;
                }
            }
            _ => (),
        }
        repl.handle_non_meta(call_expr, env)
    }

    const CALL: Self = Self {
        name: "call",
        summary: "Applies arguments to a callable object",
        format: "!(call <callable> <call_args>)",
        info: &["It's also capable of opening persisted commitments."],
        example: &[
            "(commit (lambda (x) x))",
            "!(call #c0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 0)",
        ],
        run: |repl, args, _path| {
            Self::call(repl, args, None)?;
            Ok(())
        },
    };

    fn persist_chain_comm(repl: &mut Repl<F, C1, C2>, cons: &ZPtr<F>) -> Result<()> {
        if cons.tag != Tag::Cons {
            bail!("Chain result must be a pair");
        }
        let (_, next_callable) = repl.zstore.fetch_tuple2(cons);
        if matches!(next_callable.tag, Tag::Comm | Tag::BigNum) {
            let inv_hashes3 = repl.queries.get_inv_queries("hash3", &repl.toplevel);
            let preimg = inv_hashes3
                .get(next_callable.digest.as_slice())
                .expect("Preimage must be known");
            let (secret, payload) = preimg.split_at(DIGEST_SIZE);
            let secret = ZPtr::from_flat_digest(Tag::BigNum, secret);
            let payload = ZPtr::from_flat_data(payload);
            Self::persist_comm_data(secret, payload, repl)?;
        }
        Ok(())
    }

    const CHAIN: Self = Self {
        name: "chain",
        summary: "Chains a callable object",
        format: "!(chain <callable> <call_args>)",
        info: &[
            "It's also capable of opening persisted commitments.",
            "If the next callable is a commitment, it's persisted.",
        ],
        example: &[
            "(commit (letrec ((add (lambda (counter x)
                       (let ((counter (+ counter x)))
                         (cons counter (commit (add counter)))))))
               (add 0)))",
            "!(chain #c0x8b0d8bd2feef87f7347a8d2dbe7cc74ba045ec0f14c1417266e3f46d0a0ac5 1)",
        ],
        run: |repl, args, _path| {
            let cons = Self::call(repl, args, None)?;
            Self::persist_chain_comm(repl, &cons)
        },
    };

    fn validate_binding_var(repl: &Repl<F, C1, C2>, zptr: &ZPtr<F>) -> Result<()> {
        match zptr.tag {
            Tag::Builtin | Tag::Coroutine => Ok(()),
            Tag::Sym => {
                let zstore = &repl.zstore;
                if zptr.digest != zstore.nil().digest && zptr.digest != zstore.t().digest {
                    Ok(())
                } else {
                    bail!("Illegal binding");
                }
            }
            _ => bail!("Illegal binding"),
        }
    }

    fn transition_call(
        repl: &mut Repl<F, C1, C2>,
        current_state_expr: &ZPtr<F>,
        call_args: ZPtr<F>,
        env: Option<ZPtr<F>>,
    ) -> Result<ZPtr<F>> {
        let (current_state, _) = repl.reduce_aux(current_state_expr)?;
        if current_state.tag != Tag::Cons {
            bail!("Current state must reduce to a pair");
        }
        // reduce `call_args` elements
        let list_sym = repl
            .zstore
            .intern_symbol(&builtin_sym("list"), &repl.lang_symbols);
        let list_expr = repl.zstore.intern_cons(list_sym, call_args);
        let (call_args, _) = repl.reduce_aux(&list_expr)?;
        repl.memoize_dag(current_state.tag, &current_state.digest);
        let (_, &callable) = repl.zstore.fetch_tuple2(&current_state);
        let call_expr = repl.zstore.intern_cons(callable, call_args);
        Self::call(repl, &call_expr, env)
    }

    const TRANSITION: Self = Self {
        name: "transition",
        summary: "Chains a callable object and binds the next state to a variable",
        format: "!(transition <symbol> <state_expr> <call_args>)",
        info: &["It has the same side effects of the `chain` meta command."],
        example: &["!(transition new-state old-state input0)"],
        run: |repl, args, _path| {
            let (&next_state_sym, rest) = repl.car_cdr(args);
            Self::validate_binding_var(repl, &next_state_sym)?;
            let (&current_state_expr, &call_args) = repl.car_cdr(rest);
            let cons = Self::transition_call(repl, &current_state_expr, call_args, None)?;
            Self::persist_chain_comm(repl, &cons)?;
            println!("{}", repl.fmt(&next_state_sym));
            repl.env = repl.zstore.intern_env(next_state_sym, cons, repl.env);
            Ok(())
        },
    };

    const DEFPACKAGE: Self = Self {
        name: "defpackage",
        summary: "Add a package to the state.",
        format: "!(defpackage <string|symbol>)",
        info: &[],
        example: &["!(defpackage abc)"],
        run: |repl, args, _path| {
            // TODO: handle args
            let (name, _args) = repl.car_cdr(args);
            let name = match name.tag {
                Tag::Str => repl
                    .state
                    .borrow_mut()
                    .intern(repl.zstore.fetch_string(name)),
                Tag::Sym => repl.zstore.fetch_symbol(name).into(),
                _ => bail!("Package name must be a string or a symbol"),
            };
            println!("{}", repl.state.borrow().fmt_to_string(&name));
            let package = Package::new(name);
            repl.state.borrow_mut().add_package(package);
            Ok(())
        },
    };

    const IMPORT: Self = Self {
        name: "import",
        summary: "Import a single or several packages.",
        format: "!(import <string|package> ...)",
        info: &[],
        example: &[],
        run: |repl, args, _path| {
            // TODO: handle pkg
            let (mut symbols, _pkg) = repl.car_cdr(args);
            if symbols.tag == Tag::Sym {
                let sym = SymbolRef::new(repl.zstore.fetch_symbol(symbols));
                repl.state.borrow_mut().import(&[sym])?;
            } else {
                let mut symbols_vec = vec![];
                loop {
                    {
                        let (head, tail) = repl.car_cdr(symbols);
                        let sym = repl.zstore.fetch_symbol(head);
                        symbols_vec.push(SymbolRef::new(sym));
                        if tail == repl.zstore.nil() {
                            break;
                        }
                        symbols = tail;
                    }
                }
                repl.state.borrow_mut().import(&symbols_vec)?;
            }
            Ok(())
        },
    };

    const IN_PACKAGE: Self = Self {
        name: "in-package",
        summary: "set the current package.",
        format: "!(in-package <string|symbol>)",
        info: &[],
        example: &[
            "!(defpackage abc)",
            "!(in-package abc)",
            "!(def two (.lurk.builtin.+ 1 1))",
            "!(in-package .lurk-user)",
            ".lurk-user.abc.two",
        ],
        run: |repl, args, _path| {
            let arg = repl.peek1(args)?;
            match arg.tag {
                Tag::Str => {
                    let name = repl.zstore.fetch_string(arg);
                    let package_name = repl.state.borrow_mut().intern(name);
                    repl.state.borrow_mut().set_current_package(package_name)
                }
                Tag::Sym => {
                    let package_name = repl.zstore.fetch_symbol(arg);
                    repl.state
                        .borrow_mut()
                        .set_current_package(package_name.into())
                }
                _ => bail!("Expected string or symbol. Got {}", repl.fmt(arg)),
            }
        },
    };

    const DUMP_EXPR: Self = Self {
        name: "dump-expr",
        summary: "Evaluates an expression and dumps the result to the file system",
        format: "!(dump-expr <expr> <string>)",
        info: &["Commitments are persisted opaquely."],
        example: &["!(dump-expr (+ 1 1) \"my_file\")"],
        run: |repl, args, _path| {
            let (&expr, &path) = repl.peek2(args)?;
            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            let path_str = repl.zstore.fetch_string(&path);
            repl.memoize_dag(result.tag, &result.digest);
            let lurk_data = LurkData::new(result, &repl.zstore);
            let lurk_data_bytes = bincode::serialize(&lurk_data)?;
            std::fs::write(&path_str, lurk_data_bytes)?;
            println!("Data persisted at {path_str}");
            Ok(())
        },
    };

    const LOAD_EXPR: Self = Self {
        name: "load-expr",
        summary: "Loads Lurk data from the file system and binds it to a symbol",
        format: "!(load-expr <symbol> <string>)",
        info: &[],
        example: &[
            "!(dump-expr (+ 1 1) \"my_file\")",
            "!(load-expr x \"my_file\")",
        ],
        run: |repl, args, _path| {
            let (&sym, &path) = repl.peek2(args)?;
            Self::validate_binding_var(repl, &sym)?;
            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let path_str = repl.zstore.fetch_string(&path);
            let lurk_data_bytes = std::fs::read(&path_str)?;
            let lurk_data: LurkData<F> = bincode::deserialize(&lurk_data_bytes)?;
            let payload = lurk_data.populate_zstore(&mut repl.zstore);
            println!("{}", repl.fmt(&sym));
            repl.env = repl.zstore.intern_env(sym, payload, repl.env);
            Ok(())
        },
    };

    const DEFPROTOCOL: Self = Self {
        name: "defprotocol",
        summary: "Defines a protocol",
        format: "!(defprotocol <symbol> <vars> <body> options...)",
        info: &[
            "The protocol body cannot have any free variable besides the ones",
            "declared in the vars list. The body must return a pair such that:",
            "* The first component is of the form ((x . e) . r), where r is the",
            "  result of reducing x with environment e.",
            "  The protocol can reject the proof by returning nil instead.",
            "* The second component is a 0-arg predicate that will run after the",
            "  proof verification to further constrain the proof, if needed.",
            "  If this is not necessary, this component can simply be nil.\n",
            "defprotocol accepts the following options:",
            "  :lang specifies the Lang (ignored, WIP)",
            "  :description is a description of the protocol, defaulting to \"\"",
        ],
        example: &[
            "!(defprotocol my-protocol (hash pair)",
            "  (cons",
            "    (if (= (+ (car pair) (cdr pair)) 30)",
            "      (cons (cons (cons 'open (cons hash nil)) (empty-env)) pair)",
            "      nil)",
            "    (lambda () (> (car pair) 10)))",
            "  :description \"hash opens to a pair (a, b) s.t. a+b=30 and a>10\")",
        ],
        run: |repl, args, _path| {
            let (&name, rest) = repl.car_cdr(args);
            let (&vars, rest) = repl.car_cdr(rest);
            let (&body, &props) = repl.car_cdr(rest);
            Self::validate_binding_var(repl, &name)?;
            if vars.tag != Tag::Cons && &vars != repl.zstore.nil() {
                bail!("Protocol vars must be a list");
            }

            let empty_str = repl.zstore.intern_string("");
            let property_map = repl.zstore.property_map(&props)?;

            let get_prop = |key, accepts: fn(&ZPtr<F>) -> bool, def| -> Result<ZPtr<F>> {
                let Some(val) = property_map.get(key) else {
                    return Ok(def);
                };
                if accepts(val) {
                    Ok(**val)
                } else {
                    bail!("Invalid value for property {key}")
                }
            };

            // TODO: handle lang properly
            let lang = get_prop(
                "lang",
                |_| true, // accept anything for now
                *repl.zstore.nil(),
            )?;

            let description = get_prop("description", |val| val.tag == Tag::Str, empty_str)?;

            let protocol = repl.zstore.intern_list([vars, body, lang, description]);
            println!("{}", repl.fmt(&name));
            repl.env = repl.zstore.intern_env(name, protocol, repl.env);
            Ok(())
        },
    };

    const HELP: Self = Self {
        name: "help",
        summary: "Prints a help message",
        format: "!(help <symbol>)",
        info: &[
            "Without arguments it prints a summary of all available commands.",
            "Otherwise the full help for the command in the first argument is printed.",
        ],
        example: &["!(help)", "!(help prove)"],
        run: |repl, args, _path| {
            if args != repl.zstore.nil() {
                let arg = repl.peek1(args)?;
                if !matches!(arg.tag, Tag::Sym | Tag::Builtin) {
                    bail!("Argument must be a symbol");
                }
                let sym_path = repl.zstore.fetch_symbol_path(arg);
                let Some(name) = sym_path.last() else {
                    bail!("Argument can't be the root symbol");
                };
                let Some(meta_cmd) = repl.meta_cmds.get(name.as_str()) else {
                    bail!("Unknown meta command");
                };
                println!("{} - {}", meta_cmd.name, meta_cmd.summary);
                if !meta_cmd.info.is_empty() {
                    println!("  Info:");
                }
                for e in meta_cmd.info {
                    println!("    {e}");
                }
                println!("  Usage: {}", meta_cmd.format);
                if !meta_cmd.example.is_empty() {
                    println!("  Example:");
                }
                for e in meta_cmd.example {
                    println!("    {e}");
                }
            } else {
                println!("Available commands:");
                for (_, i) in repl.meta_cmds.iter().sorted_by_key(|x| x.0) {
                    println!("  {} - {}", i.name, i.summary);
                }
            }
            Ok(())
        },
    };
}

type F = BabyBear;

impl<C1: Chipset<F>, C2: Chipset<F>> MetaCmd<F, C1, C2> {
    const PROVE: Self = Self {
        name: "prove",
        summary: "Proves a Lurk reduction",
        format: "!(prove <expr>?)",
        info: &["Prove a Lurk reduction, persists the proof and prints its key"],
        example: &["'(1 2 3)", "!(prove)", "!(prove '(1 2 3))"],
        run: |repl, args, _path| {
            if args != repl.zstore.nil() {
                let expr = *repl.peek1(args)?;
                repl.handle_non_meta(&expr, None)?;
            }
            repl.prove_last_reduction()?;
            Ok(())
        },
    };

    fn load_io_proof(proof_key: &str) -> Result<IOProof> {
        let proof_path = proofs_dir()?.join(proof_key);
        if !proof_path.exists() {
            bail!("Proof not found");
        }
        let io_proof_bytes = std::fs::read(proof_path)?;
        let io_proof = bincode::deserialize(&io_proof_bytes)?;
        Ok(io_proof)
    }

    fn load_io_proof_with_repl(
        repl: &Repl<F, C1, C2>,
        args: &ZPtr<F>,
    ) -> Result<(String, IOProof)> {
        let proof_key_zptr = repl.peek1(args)?;
        if proof_key_zptr.tag != Tag::Str {
            bail!("Proof key must be a string");
        }
        let proof_key = repl.zstore.fetch_string(proof_key_zptr);
        let io_proof = Self::load_io_proof(&proof_key)?;
        Ok((proof_key, io_proof))
    }

    const VERIFY: Self = Self {
        name: "verify",
        summary: "Verifies Lurk reduction proof",
        format: "!(verify <string>)",
        info: &["Verifies a Lurk reduction proof by its key"],
        example: &["!(verify \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        run: |repl, args, _path| {
            let (proof_key, io_proof) = Self::load_io_proof_with_repl(repl, args)?;
            let has_same_verifier_version = io_proof.crypto_proof.has_same_verifier_version();
            let machine = repl.stark_machine();
            let machine_proof = io_proof.into_machine_proof();
            let (_, vk) = machine.setup(&LairMachineProgram);
            let challenger = &mut machine.config().challenger();
            if machine.verify(&vk, &machine_proof, challenger).is_ok() {
                println!("✓ Proof \"{proof_key}\" verified");
                Ok(())
            } else {
                let mut msg = format!("✗ Proof \"{proof_key}\" failed on verification");
                if !has_same_verifier_version {
                    msg.push_str("\nWarning: proof was created for a different verifier version");
                }
                bail!(msg);
            }
        },
    };

    const INSPECT: Self = Self {
        name: "inspect",
        summary: "Prints a proof claim",
        format: "!(inspect <string>)",
        info: &[],
        example: &["!(inspect \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        run: |repl, args, _path| {
            let IOProof {
                expr,
                env,
                result,
                zdag,
                ..
            } = Self::load_io_proof_with_repl(repl, args)?.1;
            zdag.populate_zstore(&mut repl.zstore);
            println!(
                "Expr: {}\nEnv: {}\nResult: {}",
                repl.fmt(&expr),
                repl.fmt(&env),
                repl.fmt(&result)
            );
            Ok(())
        },
    };

    fn get_vars_vec_and_body<'a>(
        repl: &'a mut Repl<F, C1, C2>,
        protocol: &'a ZPtr<F>,
    ) -> Result<(Vec<&'a ZPtr<F>>, &'a ZPtr<F>)> {
        let (protocol_elts, None) = repl.zstore.fetch_list(protocol) else {
            bail!("Malformed protocol: must be a list");
        };
        let (Some(vars), Some(body)) = (protocol_elts.first(), protocol_elts.get(1)) else {
            bail!("Malformed protocol: missing first or second element");
        };
        let (vars_vec, None) = repl.zstore.fetch_list(vars) else {
            bail!("Malformed protocol: vars must be a list");
        };
        Ok((vars_vec, body))
    }

    fn get_claim_and_post_verify_predicade<'a>(
        repl: &'a mut Repl<F, C1, C2>,
        vars_vec: Vec<ZPtr<F>>,
        args_vec_reduced: Vec<ZPtr<F>>,
        body: &ZPtr<F>,
    ) -> Result<(&'a ZPtr<F>, &'a ZPtr<F>)> {
        let mut env = repl.zstore.intern_empty_env();
        for (var, arg) in vars_vec.into_iter().zip(args_vec_reduced) {
            env = repl.zstore.intern_env(var, arg, env);
        }
        let (io_data, _) = repl.reduce_aux_with_env(body, &env)?;
        if io_data.tag != Tag::Cons {
            bail!("Protocol body must return a pair");
        }
        repl.memoize_dag(Tag::Cons, &io_data.digest);
        let (claim, post_verify_predicate) = repl.zstore.fetch_tuple2(&io_data);
        if claim == repl.zstore.nil() {
            bail!("Pre-verification predicate rejected the input");
        }
        if claim.tag != Tag::Cons {
            bail!("Malformed protocol claim");
        }
        Ok((claim, post_verify_predicate))
    }

    fn post_verify_check(repl: &mut Repl<F, C1, C2>, post_verify_predicate: ZPtr<F>) -> Result<()> {
        if &post_verify_predicate != repl.zstore.nil() {
            let post_verify_call = repl.zstore.intern_list([post_verify_predicate]);
            let empty_env = repl.zstore.intern_empty_env();
            let (post_verify_result, _) =
                repl.reduce_aux_with_env(&post_verify_call, &empty_env)?;
            if &post_verify_result == repl.zstore.nil() {
                bail!("Post-verification predicate rejected the input");
            }
        }
        Ok(())
    }

    const PROVE_PROTOCOL: Self = Self {
        name: "prove-protocol",
        summary: "Creates a proof for a protocol",
        format: "!(prove-protocol <protocol> <string> args...)",
        info: &[
            "The proof is created only if the protocol can be satisfied by the",
            "provided arguments.",
            "The second (string) argument for this meta command is the path to",
            "the file where the protocol proof will be saved.",
        ],
        example: &[
            "(commit '(13 . 17))",
            "!(prove-protocol my-protocol",
            "  \"protocol-proof\"",
            "  #c0x955f855f302a30ed988cc48685c442ebd98c8711e989fc64df8f27f52e1350",
            "  '(13 . 17))",
        ],
        run: |repl, args, _path| {
            let (&protocol_expr, rest) = repl.car_cdr(args);
            let (path, &args) = repl.car_cdr(rest);

            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let path_str = repl.zstore.fetch_string(path);

            let (protocol, _) = repl.reduce_aux(&protocol_expr)?;
            if protocol.tag == Tag::Err {
                bail!("Error when evaluating the protocol");
            }
            let (vars_vec, &body) = Self::get_vars_vec_and_body(repl, &protocol)?;
            let vars_vec = copy_inner(vars_vec);

            let (args_vec, None) = repl.zstore.fetch_list(&args) else {
                bail!("Arguments must be a list");
            };
            if args_vec.len() != vars_vec.len() {
                bail!(
                    "Mismatching arity. Protocol requires {} arguments but {} were provided",
                    vars_vec.len(),
                    args_vec.len()
                );
            }
            let args_vec = copy_inner(args_vec);
            let mut args_vec_reduced = Vec::with_capacity(args_vec.len());
            for arg in args_vec.iter() {
                let (arg_reduced, _) = repl.reduce_aux(arg)?;
                if arg_reduced.tag == Tag::Err {
                    bail!("Error when evaluating a protocol argument");
                }
                args_vec_reduced.push(arg_reduced);
            }

            let (&claim, &post_verify_predicate) = Self::get_claim_and_post_verify_predicade(
                repl,
                vars_vec,
                args_vec_reduced.clone(),
                &body,
            )?;

            Self::post_verify_check(repl, post_verify_predicate)?;

            let (expr_env, &expected_result) = repl.zstore.fetch_tuple2(&claim);
            if expr_env.tag != Tag::Cons {
                bail!("Malformed protocol claim");
            }
            let (&expr, &env) = repl.zstore.fetch_tuple2(expr_env);
            let result = repl.reduce_with_env(&expr, &env)?;
            if result != expected_result {
                bail!("Mismatch between result and expected result");
            }

            let proof_key = repl.prove_last_reduction()?;
            let io_proof = Self::load_io_proof(&proof_key)?;
            let crypto_proof = io_proof.crypto_proof;
            let args_reduced = repl.zstore.intern_list(args_vec_reduced);
            repl.memoize_dag(args_reduced.tag, &args_reduced.digest);
            let protocol_proof = ProtocolProof::new(crypto_proof, args_reduced, &repl.zstore);
            std::fs::write(&path_str, bincode::serialize(&protocol_proof)?)?;
            println!("Protocol proof saved at {path_str}");
            Ok(())
        },
    };

    const VERIFY_PROTOCOL: Self = Self {
        name: "verify-protocol",
        summary: "Verifies a proof for a protocol",
        format: "!(verify-protocol <protocol> <string>)",
        info: &[
            "Reconstructs the proof input with the args provided by the prover",
            "according to the protocol and then verifies the proof.",
            "If verification succeeds, runs the post-verification predicate,",
            "failing if the predicate returns nil.",
            "The second (string) argument is the path to the file containing the",
            "protocol proof.",
        ],
        example: &["!(verify-protocol my-protocol \"protocol-proof\")"],
        run: |repl, args, _path| {
            let (&protocol_expr, path) = repl.peek2(args)?;
            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let path_str = repl.zstore.fetch_string(path);

            let (protocol, _) = repl.reduce_aux(&protocol_expr)?;
            if protocol.tag == Tag::Err {
                bail!("Error when evaluating the protocol");
            }
            let (vars_vec, &body) = Self::get_vars_vec_and_body(repl, &protocol)?;
            let vars_vec = copy_inner(vars_vec);

            let protocol_proof_bytes = std::fs::read(path_str)?;
            let ProtocolProof { crypto_proof, args } = bincode::deserialize(&protocol_proof_bytes)?;
            if args.has_opaque_data() {
                bail!("Arguments can't have opaque data");
            }
            let args = args.populate_zstore(&mut repl.zstore);
            let (args_vec_reduced, None) = repl.zstore.fetch_list(&args) else {
                bail!("Arguments must be a list");
            };
            if args_vec_reduced.len() != vars_vec.len() {
                bail!(
                    "Mismatching arity. Protocol requires {} arguments but {} were provided",
                    vars_vec.len(),
                    args_vec_reduced.len()
                );
            }
            let args_vec_reduced = copy_inner(args_vec_reduced);

            let (&claim, &post_verify_predicate) =
                Self::get_claim_and_post_verify_predicade(repl, vars_vec, args_vec_reduced, &body)?;

            let (expr_env, result) = repl.zstore.fetch_tuple2(&claim);
            if expr_env.tag != Tag::Cons {
                bail!("Malformed protocol claim");
            }
            let (expr, env) = repl.zstore.fetch_tuple2(expr_env);
            let has_same_verifier_version = crypto_proof.has_same_verifier_version();
            let machine_proof = crypto_proof.into_machine_proof(expr, env, result);
            let machine = repl.stark_machine();
            let (_, vk) = machine.setup(&LairMachineProgram);
            let challenger = &mut machine.config().challenger();
            if machine.verify(&vk, &machine_proof, challenger).is_err() {
                let mut msg = "Proof verification failed".to_string();
                if !has_same_verifier_version {
                    msg.push_str("\nWarning: proof was created for a different verifier version");
                }
                bail!(msg);
            }

            Self::post_verify_check(repl, post_verify_predicate)?;

            println!("Proof accepted by the protocol");
            Ok(())
        },
    };

    fn build_comm_data(repl: &mut Repl<F, C1, C2>, digest: &[F]) -> CommData<F> {
        let inv_hashes3 = repl.queries.get_inv_queries("hash3", &repl.toplevel);
        let callable_preimg = inv_hashes3
            .get(digest)
            .expect("Missing commitment preimage");
        let secret = ZPtr::from_flat_digest(Tag::BigNum, &callable_preimg[..DIGEST_SIZE]);
        let payload = ZPtr::from_flat_data(&callable_preimg[DIGEST_SIZE..]);
        repl.memoize_dag(secret.tag, &secret.digest);
        repl.memoize_dag(payload.tag, &payload.digest);
        CommData::new(secret, payload, &repl.zstore)
    }

    const MICRO_CHAIN_SERVE: Self = Self {
        name: "micro-chain-serve",
        summary:
            "Starts a server to manage state transitions by receiving proofs of chained callables.",
        format: "!(micro-chain-serve <addr_str> <state_expr>)",
        info: &[
            "The initial state must follow the format of a chain output whose next",
            "callable is a commitment.",
        ],
        example: &["!(micro-chain-serve \"127.0.0.1:1234\" (some-callable init-arg0 init-arg1))"],
        run: |repl, args, _path| {
            let (addr, &state_expr) = repl.peek2(args)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let addr_str = repl.zstore.fetch_string(addr);
            let (state, _) = repl.reduce_aux(&state_expr)?;
            if state.tag != Tag::Cons {
                bail!("Initial state must be a pair");
            }
            repl.memoize_dag(Tag::Cons, &state.digest);

            // chain result and callable from the server's state
            let (&(mut state_chain_result), &(mut state_callable)) =
                repl.zstore.fetch_tuple2(&state);

            let listener = TcpListener::bind(&addr_str)?;
            println!("Listening at {addr_str}");
            let empty_env = repl.zstore.intern_empty_env();
            for stream in listener.incoming() {
                match stream {
                    Ok(mut stream) => match read_data::<Request>(&mut stream)? {
                        Request::Get => {
                            // provide the data that fully specifies the current state
                            repl.memoize_dag(state_chain_result.tag, &state_chain_result.digest);
                            let chain_result = LurkData::new(state_chain_result, &repl.zstore);

                            let state_callable_data = if state_callable.tag == Tag::Comm {
                                let comm_data =
                                    Self::build_comm_data(repl, state_callable.digest.as_slice());
                                CallableData::Comm(comm_data)
                            } else {
                                CallableData::Fun(LurkData::new(state_callable, &repl.zstore))
                            };

                            write_data(
                                &mut stream,
                                Response::State(chain_result, state_callable_data),
                            )?;
                        }
                        Request::Transition(chain_proof) => {
                            let ChainProof {
                                crypto_proof,
                                call_args,
                                chain_result,
                                next_callable,
                            } = *chain_proof;
                            if chain_result.has_opaque_data() {
                                write_data(&mut stream, Response::ChainResultIsOpaque)?;
                                continue;
                            }

                            let next_callable_zptr = match &next_callable {
                                CallableData::Comm(comm_data) => {
                                    if comm_data.secret.tag != Tag::BigNum {
                                        write_data(
                                            &mut stream,
                                            Response::NextCallableSecretNotBigNum,
                                        )?;
                                        continue;
                                    }
                                    if comm_data.payload_has_opaque_data() {
                                        write_data(
                                            &mut stream,
                                            Response::NextCallablePayloadIsOpaque,
                                        )?;
                                        continue;
                                    }
                                    comm_data.commit(&mut repl.zstore)
                                }
                                CallableData::Fun(lurk_data) => {
                                    if lurk_data.has_opaque_data() {
                                        write_data(
                                            &mut stream,
                                            Response::NextCallablePayloadIsOpaque,
                                        )?;
                                        continue;
                                    }
                                    lurk_data.zptr
                                }
                            };

                            // the expression is a call whose callable is part of the server state
                            // and the arguments are provided by the client
                            let expr = repl.zstore.intern_cons(state_callable, call_args);

                            // the result is a pair composed by the chain result and next callable
                            // provided by the client
                            let result = repl
                                .zstore
                                .intern_cons(chain_result.zptr, next_callable_zptr);

                            // and now the proof must verify, meaning that the user must have
                            // used the correct callable from the server state
                            let machine_proof =
                                crypto_proof.into_machine_proof(&expr, &empty_env, &result);
                            let machine = repl.stark_machine();
                            let (_, vk) = machine.setup(&LairMachineProgram);
                            let challenger = &mut machine.config().challenger();
                            if machine.verify(&vk, &machine_proof, challenger).is_err() {
                                write_data(
                                    &mut stream,
                                    Response::ProofVerificationFailed(
                                        get_verifier_version().to_string(),
                                    ),
                                )?;
                                continue;
                            }

                            // everything went okay... transition to the next state
                            write_data(&mut stream, Response::ProofAccepted)?;
                            state_chain_result = chain_result.populate_zstore(&mut repl.zstore);
                            match next_callable {
                                CallableData::Comm(comm_data) => {
                                    comm_data.populate_zstore(&mut repl.zstore)
                                }
                                CallableData::Fun(lurk_data) => {
                                    lurk_data.populate_zstore(&mut repl.zstore);
                                }
                            }
                            state_callable = next_callable_zptr;
                        }
                    },
                    Err(e) => {
                        eprintln!("Connection failed: {e}");
                    }
                }
            }
            Ok(())
        },
    };

    const MICRO_CHAIN_GET: Self = Self {
        name: "micro-chain-get",
        summary: "Binds the current state from a micro-chain server to a symbol",
        format: "!(micro-chain-get <addr_str> <symbol>)",
        info: &[],
        example: &["!(micro-chain-get \"127.0.0.1:1234\" state0)"],
        run: |repl, args, _path| {
            let (addr, &state_sym) = repl.peek2(args)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            Self::validate_binding_var(repl, &state_sym)?;
            let addr_str = repl.zstore.fetch_string(addr);
            let stream = &mut TcpStream::connect(addr_str)?;
            write_data(stream, Request::Get)?;
            let Response::State(chain_result, next_callable_data) = read_data(stream)? else {
                bail!("Could not read state from server");
            };
            let state_chain_result = chain_result.populate_zstore(&mut repl.zstore);
            let state_next_callable = match next_callable_data {
                CallableData::Comm(comm_data) => {
                    let zptr = comm_data.commit(&mut repl.zstore);
                    comm_data.populate_zstore(&mut repl.zstore);
                    zptr
                }
                CallableData::Fun(lurk_data) => lurk_data.populate_zstore(&mut repl.zstore),
            };
            let state = repl
                .zstore
                .intern_cons(state_chain_result, state_next_callable);
            println!("{}", repl.fmt(&state_sym));
            repl.env = repl.zstore.intern_env(state_sym, state, repl.env);
            Ok(())
        },
    };

    const MICRO_CHAIN_TRANSITION: Self = Self {
        name: "micro-chain-transition",
        summary:
            "Proves a state transition via chaining and sends the proof to a micro-chain server",
        format: "!(micro-chain-transition <addr_str> <symbol> <state_expr> <call_args>)",
        info: &["The transition is successful iff the proof is accepted by the server"],
        example: &["!(micro-chain-transition \"127.0.0.1:1234\" state1 state0 arg0 arg1)"],
        run: |repl, args, _path| {
            let (&addr, rest) = repl.car_cdr(args);
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (&next_state_sym, rest) = repl.car_cdr(rest);
            Self::validate_binding_var(repl, &next_state_sym)?;
            let (&current_state_expr, &call_args) = repl.car_cdr(rest);
            let empty_env = repl.zstore.intern_empty_env();
            let state =
                Self::transition_call(repl, &current_state_expr, call_args, Some(empty_env))?;
            if state.tag != Tag::Cons {
                bail!("New state is not a pair");
            }
            let (&state_chain_result, &state_callable) = repl.zstore.fetch_tuple2(&state);

            let proof_key = repl.prove_last_reduction()?;
            let io_proof = Self::load_io_proof(&proof_key)?;
            let crypto_proof = io_proof.crypto_proof;

            let chain_result = LurkData::new(state_chain_result, &repl.zstore);
            let next_callable = if state_callable.tag == Tag::Comm {
                let comm_data = Self::build_comm_data(repl, state_callable.digest.as_slice());
                CallableData::Comm(comm_data)
            } else {
                CallableData::Fun(LurkData::new(state_callable, &repl.zstore))
            };

            let chain_proof = ChainProof {
                crypto_proof,
                call_args,
                chain_result,
                next_callable,
            };
            let addr_str = repl.zstore.fetch_string(&addr);
            let stream = &mut TcpStream::connect(addr_str)?;
            write_data(stream, Request::Transition(chain_proof.into()))?;
            match read_data::<Response>(stream)? {
                Response::ProofAccepted => {
                    println!("Proof accepted by the server");
                    println!("{}", repl.fmt(&next_state_sym));
                    repl.env = repl.zstore.intern_env(next_state_sym, state, repl.env);
                }
                Response::ProofVerificationFailed(verifier_version) => {
                    let mut msg = "Proof verification failed".to_string();
                    if verifier_version != get_verifier_version() {
                        msg.push_str(
                            "\nWarning: proof was created for a different verifier version",
                        );
                    }
                    bail!(msg);
                }
                _ => bail!("Bad server response"),
            }
            Ok(())
        },
    };
}

#[derive(Serialize, Deserialize)]
enum Request {
    Get,
    Transition(Box<ChainProof>),
}

#[derive(Serialize, Deserialize)]
enum Response {
    State(LurkData<F>, CallableData),
    ProofAccepted,
    ChainResultIsOpaque,
    NextCallableSecretNotBigNum,
    NextCallablePayloadIsOpaque,
    ProofVerificationFailed(String),
}

fn read_data<T: for<'a> Deserialize<'a>>(stream: &mut TcpStream) -> Result<T> {
    let mut size_bytes = [0; 8];
    stream.read_exact(&mut size_bytes)?;
    let size = usize::from_le_bytes(size_bytes);
    let mut data_buffer = vec![0; size];
    stream.read_exact(&mut data_buffer)?;
    let data = bincode::deserialize(&data_buffer)?;
    Ok(data)
}

fn write_data<T: Serialize>(stream: &mut TcpStream, data: T) -> Result<()> {
    let data_bytes = bincode::serialize(&data)?;
    stream.write_all(&data_bytes.len().to_le_bytes())?;
    stream.write_all(&data_bytes)?;
    stream.flush()?;
    Ok(())
}

fn copy_inner<'a, T: Copy + 'a, I: IntoIterator<Item = &'a T>>(xs: I) -> Vec<T> {
    xs.into_iter().copied().collect()
}

#[inline]
pub(crate) fn meta_cmds<C1: Chipset<F>, C2: Chipset<F>>() -> MetaCmdsMap<F, C1, C2> {
    [
        MetaCmd::ASSERT,
        MetaCmd::ASSERT_EQ,
        MetaCmd::ASSERT_ERROR,
        MetaCmd::ASSERT_EMITTED,
        MetaCmd::DEBUG,
        MetaCmd::LOAD,
        MetaCmd::DEF,
        MetaCmd::DEFREC,
        MetaCmd::UPDATE,
        MetaCmd::CLEAR,
        MetaCmd::SET_ENV,
        MetaCmd::ERASE_FROM_ENV,
        MetaCmd::HIDE,
        MetaCmd::COMMIT,
        MetaCmd::OPEN,
        MetaCmd::FETCH,
        MetaCmd::CALL,
        MetaCmd::CHAIN,
        MetaCmd::TRANSITION,
        MetaCmd::DEFPACKAGE,
        MetaCmd::IMPORT,
        MetaCmd::IN_PACKAGE,
        MetaCmd::DUMP_EXPR,
        MetaCmd::LOAD_EXPR,
        MetaCmd::PROVE,
        MetaCmd::VERIFY,
        MetaCmd::INSPECT,
        MetaCmd::DEFPROTOCOL,
        MetaCmd::PROVE_PROTOCOL,
        MetaCmd::VERIFY_PROTOCOL,
        MetaCmd::MICRO_CHAIN_SERVE,
        MetaCmd::MICRO_CHAIN_GET,
        MetaCmd::MICRO_CHAIN_TRANSITION,
        MetaCmd::HELP,
    ]
    .map(|mc| (mc.name, mc))
    .into_iter()
    .collect()
}
