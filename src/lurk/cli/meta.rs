use anyhow::{bail, Result};
use camino::Utf8Path;
use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
use rustc_hash::FxHashMap;
use sphinx_core::stark::StarkGenericConfig;
use std::net::TcpStream;

use crate::{
    lair::{chipset::Chipset, lair_chip::LairMachineProgram},
    lurk::{
        big_num::field_elts_to_biguint,
        package::{Package, SymbolRef},
        stark_machine::new_machine,
        state::builtin_sym,
        tag::Tag,
        zstore::{ZPtr, DIGEST_SIZE},
    },
};

use super::{
    comm_data::CommData,
    debug::debug_mode,
    lurk_data::LurkData,
    microchain::{read_data, write_data, CallableData, ChainState, Request, Response},
    paths::{commits_dir, proofs_dir},
    proofs::{get_verifier_version, CachedProof, ChainProof, OpaqueChainProof, ProtocolProof},
    repl::Repl,
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
            let [&expr] = repl.take(args)?;
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
            let [&expr1, &expr2] = repl.take(args)?;
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
            let [&expr] = repl.take(args)?;
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
            let [&expected_expr, &expr] = repl.take(args)?;
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
                let [&expr] = repl.take(args)?;
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
            let [file_name_zptr] = repl.take(args)?;
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
        format: "!(def <symbol> <expr>)",
        info: &[
            "Gets macroexpanded to (let ((<symbol> <value>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        example: &["!(def foo (lambda () 123))"],
        run: |repl, args, _path| {
            let [&sym, _] = repl.take(args)?;
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
            let [&sym, _] = repl.take(args)?;
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
            let [&sym, &fun] = repl.take(args)?;
            Self::validate_binding_var(repl, &sym)?;
            let expr = repl.zstore.intern_list([fun, sym]);
            let (res, _) = repl.reduce_aux(&expr)?;
            if res.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&res));
            }
            println!("{}", repl.fmt(&sym));
            repl.bind(sym, res);
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
            let [&env_expr] = repl.take(args)?;
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
            repl.env = repl.zstore.intern_empty_env();
            for (var, val) in new_env_vec.into_iter().rev() {
                repl.bind(var, val);
            }
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
            let [&secret_expr, &payload_expr] = repl.take(args)?;
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
            let [&payload_expr] = repl.take(args)?;
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
            let [&expr] = repl.take(args)?;
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
            let [&expr] = repl.take(args)?;
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
                    bail!("Illegal binding: {}", repl.fmt(zptr));
                }
            }
            _ => bail!("Illegal binding: {}", repl.fmt(zptr)),
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
            repl.bind(next_state_sym, cons);
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
            let [arg] = repl.take(args)?;
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
            let [&expr, &path] = repl.take(args)?;
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
            let [&sym, &path] = repl.take(args)?;
            Self::validate_binding_var(repl, &sym)?;
            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let path_str = repl.zstore.fetch_string(&path);
            let lurk_data_bytes = std::fs::read(&path_str)?;
            let lurk_data: LurkData<F> = bincode::deserialize(&lurk_data_bytes)?;
            let payload = lurk_data.populate_zstore(&mut repl.zstore);
            println!("{}", repl.fmt(&sym));
            repl.bind(sym, payload);
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
            repl.bind(name, protocol);
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
                let [arg] = repl.take(args)?;
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
                let [&expr] = repl.take(args)?;
                repl.handle_non_meta(&expr, None)?;
            }
            repl.prove_last_reduction()?;
            Ok(())
        },
    };

    fn load_cached_proof(proof_key: &str) -> Result<CachedProof> {
        let proof_path = proofs_dir()?.join(proof_key);
        if !proof_path.exists() {
            bail!("Proof not found");
        }
        let cached_proof_bytes = std::fs::read(proof_path)?;
        let cached_proof = bincode::deserialize(&cached_proof_bytes)?;
        Ok(cached_proof)
    }

    fn load_cached_proof_with_repl(
        repl: &Repl<F, C1, C2>,
        args: &ZPtr<F>,
    ) -> Result<(String, CachedProof)> {
        let [proof_key_zptr] = repl.take(args)?;
        if proof_key_zptr.tag != Tag::Str {
            bail!("Proof key must be a string");
        }
        let proof_key = repl.zstore.fetch_string(proof_key_zptr);
        let cached_proof = Self::load_cached_proof(&proof_key)?;
        Ok((proof_key, cached_proof))
    }

    const VERIFY: Self = Self {
        name: "verify",
        summary: "Verifies Lurk reduction proof",
        format: "!(verify <string>)",
        info: &["Verifies a Lurk reduction proof by its key"],
        example: &["!(verify \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        run: |repl, args, _path| {
            let (proof_key, cached_proof) = Self::load_cached_proof_with_repl(repl, args)?;
            let has_same_verifier_version = cached_proof.crypto_proof.has_same_verifier_version();
            let machine = new_machine(&repl.toplevel);
            let machine_proof = cached_proof.into_machine_proof();
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
            let CachedProof {
                expr,
                env,
                result,
                zdag,
                ..
            } = Self::load_cached_proof_with_repl(repl, args)?.1;
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
            let cached_proof = Self::load_cached_proof(&proof_key)?;
            let crypto_proof = cached_proof.crypto_proof;
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
            let [&protocol_expr, path] = repl.take(args)?;
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
            let machine = new_machine(&repl.toplevel);
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

    const MICROCHAIN_START: Self = Self {
        name: "microchain-start",
        summary: "Starts a new microchain and binds the resulting ID to a symbol",
        format: "!(microchain-start <addr_expr> <state_expr> <id_sym>)",
        info: &[
            "A microchain ID is a hiding commitment to the genesis state, using",
            "a timestamp-based secret generated in the server.",
            "Upon success, it becomes possible to open the ID and retrieve genesis",
            "state associated with the microchain.",
        ],
        example: &[
            "!(microchain-start \"127.0.0.1:1234\" state0 id)",
            "!(assert-eq state0 (open id))",
        ],
        run: |repl, args, _path| {
            let [&addr_expr, &state_expr, &id_sym] = repl.take(args)?;
            let (addr, _) = repl.reduce_aux(&addr_expr)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (state, _) = repl.reduce_aux(&state_expr)?;
            if state.tag != Tag::Cons {
                bail!("State must be a pair");
            }
            Self::validate_binding_var(repl, &id_sym)?;

            repl.memoize_dag(state.tag, &state.digest);

            let (&chain_result, &next_callable) = repl.zstore.fetch_tuple2(&state);
            let chain_result = LurkData::new(chain_result, &repl.zstore);
            let callable_data = if next_callable.tag == Tag::Comm {
                let comm_data = Self::build_comm_data(repl, next_callable.digest.as_slice());
                CallableData::Comm(comm_data)
            } else {
                CallableData::Fun(LurkData::new(next_callable, &repl.zstore))
            };

            let genesis = ChainState {
                chain_result,
                callable_data,
            };

            let addr_str = repl.zstore.fetch_string(&addr);
            let stream = &mut TcpStream::connect(addr_str)?;
            write_data(stream, Request::Start(genesis))?;
            let Response::IdSecret(id_secret) = read_data(stream)? else {
                bail!("Could not read ID secret from server");
            };

            let id_digest = CommData::hash(&id_secret, &state, &mut repl.zstore);

            let id = repl.zstore.intern_comm(id_digest);
            println!("{}", repl.fmt(&id_sym));
            repl.bind(id_sym, id);
            Ok(())
        },
    };

    fn send_get_state_request(
        repl: &mut Repl<F, C1, C2>,
        args: &ZPtr<F>,
        mk_request: fn([F; DIGEST_SIZE]) -> Request,
    ) -> Result<(ZPtr<F>, TcpStream)> {
        let [&addr_expr, &id_expr, &state_sym] = repl.take(args)?;
        let (addr, _) = repl.reduce_aux(&addr_expr)?;
        if addr.tag != Tag::Str {
            bail!("Address must be a string");
        }
        let (id, _) = repl.reduce_aux(&id_expr)?;
        Self::validate_binding_var(repl, &state_sym)?;
        let addr_str = repl.zstore.fetch_string(&addr);
        let mut stream = TcpStream::connect(addr_str)?;
        write_data(&mut stream, mk_request(id.digest))?;
        Ok((state_sym, stream))
    }

    const MICROCHAIN_GET_GENESIS: Self = Self {
        name: "microchain-get-genesis",
        summary: "Binds the genesis state of a microchain to a symbol",
        format: "!(microchain-get-genesis <addr_expr> <id_expr> <symbol>)",
        info: &[
            "Similarly to `microchain-start`, the preimage of the ID becomes",
            "available so opening the ID returns the genesis state.",
        ],
        example: &[
            "!(microchain-get-genesis \"127.0.0.1:1234\" #c0x123 state0)",
            "!(assert-eq state0 (open id))",
        ],
        run: |repl, args, _path| {
            let (state_sym, mut stream) =
                Self::send_get_state_request(repl, args, Request::GetGenesis)?;
            let Response::Genesis(id_secret, chain_state) = read_data(&mut stream)? else {
                bail!("Could not read state from server");
            };
            let state = chain_state.into_zptr(&mut repl.zstore);

            // memoize preimg so it's possible to open the ID
            CommData::hash(&id_secret, &state, &mut repl.zstore);

            println!("{}", repl.fmt(&state_sym));
            repl.bind(state_sym, state);
            Ok(())
        },
    };

    const MICROCHAIN_GET_STATE: Self = Self {
        name: "microchain-get-state",
        summary: "Binds the current state of a microchain to a symbol",
        format: "!(microchain-get-state <addr_expr> <id_expr> <symbol>)",
        info: &[],
        example: &["!(microchain-get-state \"127.0.0.1:1234\" #c0x123 state)"],
        run: |repl, args, _path| {
            let (state_sym, mut stream) =
                Self::send_get_state_request(repl, args, Request::GetState)?;
            let Response::State(chain_state) = read_data(&mut stream)? else {
                bail!("Could not read state from server");
            };
            let state = chain_state.into_zptr(&mut repl.zstore);
            println!("{}", repl.fmt(&state_sym));
            repl.bind(state_sym, state);
            Ok(())
        },
    };

    const MICROCHAIN_TRANSITION: Self = Self {
        name: "microchain-transition",
        summary:
            "Proves a state transition via chaining and sends the proof to a microchain server",
        format: "!(microchain-transition <addr_expr> <id_expr> <symbol> <state_expr> <call_args>)",
        info: &[
            "The transition is successful iff the proof is accepted by the server.",
            "Unlike in the `transition` meta command, the call arguments will be",
            "evaluated w.r.t. the empty environment.",
        ],
        example: &["!(microchain-transition \"127.0.0.1:1234\" #c0x123 state2 state1 arg0 arg1)"],
        run: |repl, args, _path| {
            let (&addr_expr, rest) = repl.car_cdr(args);
            let (&id_expr, rest) = repl.car_cdr(rest);
            let (&next_state_sym, &rest) = repl.car_cdr(rest);
            let (addr, _) = repl.reduce_aux(&addr_expr)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (id, _) = repl.reduce_aux(&id_expr)?;
            Self::validate_binding_var(repl, &next_state_sym)?;
            let (&current_state_expr, &call_args) = repl.car_cdr(&rest);
            let empty_env = repl.zstore.intern_empty_env();
            let state =
                Self::transition_call(repl, &current_state_expr, call_args, Some(empty_env))?;
            if state.tag != Tag::Cons {
                bail!("New state is not a pair");
            }
            let (&state_chain_result, &state_callable) = repl.zstore.fetch_tuple2(&state);

            let proof_key = repl.prove_last_reduction()?;
            let cached_proof = Self::load_cached_proof(&proof_key)?;
            let crypto_proof = cached_proof.crypto_proof;

            let next_chain_result = LurkData::new(state_chain_result, &repl.zstore);
            let next_callable = if state_callable.tag == Tag::Comm {
                let comm_data = Self::build_comm_data(repl, state_callable.digest.as_slice());
                CallableData::Comm(comm_data)
            } else {
                CallableData::Fun(LurkData::new(state_callable, &repl.zstore))
            };

            let chain_proof = ChainProof {
                crypto_proof,
                call_args,
                next_chain_result,
                next_callable,
            };
            let addr_str = repl.zstore.fetch_string(&addr);
            let stream = &mut TcpStream::connect(addr_str)?;
            write_data(stream, Request::Transition(id.digest, chain_proof))?;
            match read_data::<Response>(stream)? {
                Response::ProofAccepted => {
                    println!("Proof accepted by the server");
                    println!("{}", repl.fmt(&next_state_sym));
                    repl.bind(next_state_sym, state);
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

    const MICROCHAIN_VERIFY: Self = Self {
        name: "microchain-verify",
        summary: "Checks if a series of microchain transition proofs takes state A to B",
        format: "!(microchain-verify <addr_expr> <id_expr> <state_a_expr> <state_b_expr>)",
        info: &["The state arguments are meant to be the genesis and the current state."],
        example: &["!(microchain-verify \"127.0.0.1:1234\" #c0x123 genesis current)"],
        run: |repl, args, _path| {
            let [&addr_expr, &id_expr, &genesis_state_expr, &current_state_expr] =
                repl.take(args)?;
            let (addr, _) = repl.reduce_aux(&addr_expr)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (id, _) = repl.reduce_aux(&id_expr)?;
            let (genesis_state, _) = repl.reduce_aux(&genesis_state_expr)?;
            if genesis_state.tag != Tag::Cons {
                bail!("Initial state must be a pair");
            }
            let addr_str = repl.zstore.fetch_string(&addr);
            let stream = &mut TcpStream::connect(addr_str)?;
            write_data(stream, Request::GetProofs(id.digest))?;
            let Response::Proofs(proofs) = read_data(stream)? else {
                bail!("Could not read proofs from server");
            };
            repl.memoize_dag(genesis_state.tag, &genesis_state.digest);
            let (_, &(mut callable)) = repl.zstore.fetch_tuple2(&genesis_state);
            let mut state = genesis_state;
            let empty_env = repl.zstore.intern_empty_env();
            for (i, proof) in proofs.into_iter().enumerate() {
                let OpaqueChainProof {
                    crypto_proof,
                    call_args,
                    next_chain_result,
                    next_callable,
                } = proof;
                let expr = repl.zstore.intern_cons(callable, call_args);
                let result = repl.zstore.intern_cons(next_chain_result, next_callable);
                let machine_proof = crypto_proof.into_machine_proof(&expr, &empty_env, &result);
                let machine = new_machine(&repl.toplevel);
                let (_, vk) = machine.setup(&LairMachineProgram);
                let challenger = &mut machine.config().challenger();
                if machine.verify(&vk, &machine_proof, challenger).is_err() {
                    bail!("{}-th transition proof doesn't verify", i + 1);
                }
                callable = next_callable;
                state = result;
            }
            let (current_state, _) = repl.reduce_aux(&current_state_expr)?;
            if state != current_state {
                bail!("Chain final state doesn't match target final state");
            }
            println!("Microchain verification succeeded");
            Ok(())
        },
    };
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
        MetaCmd::MICROCHAIN_START,
        MetaCmd::MICROCHAIN_GET_GENESIS,
        MetaCmd::MICROCHAIN_GET_STATE,
        MetaCmd::MICROCHAIN_TRANSITION,
        MetaCmd::MICROCHAIN_VERIFY,
        MetaCmd::HELP,
    ]
    .map(|mc| (mc.name, mc))
    .into_iter()
    .collect()
}
