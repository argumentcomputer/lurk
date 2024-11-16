use anyhow::{bail, Result};
use camino::Utf8Path;
use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
use rustc_hash::FxHashMap;
use sphinx_core::stark::StarkGenericConfig;
use std::{io::Write, net::TcpStream};

use crate::{
    core::{
        big_num::field_elts_to_biguint,
        package::{Package, SymbolRef},
        stark_machine::new_machine,
        state::{builtin_sym, meta_sym, META_SYMBOLS},
        symbol::Symbol,
        tag::Tag,
        zstore::{ZPtr, DIGEST_SIZE, HASH3_SIZE},
    },
    lair::{chipset::Chipset, lair_chip::LairMachineProgram, List},
    ocaml::compile::compile_and_transform_single_file,
};

use super::{
    comm_data::CommData,
    debug::debug_mode,
    lurk_data::LurkData,
    microchain::{read_data, write_data, CallableData, ChainState, Request, Response},
    paths::{commits_dir, proofs_dir},
    proofs::{get_verifier_version, CachedProof, ChainProof, OpaqueChainProof, ProtocolProof},
    rdg::rand_digest,
    repl::{OuterScope, Repl},
    scope::{
        dump_scope_microchain, load_scope_bindings, load_scope_comms, load_scope_microchain,
        update_scope_bindings, update_scope_comms, ScopeBindings,
    },
};

#[allow(clippy::type_complexity)]
pub(crate) struct MetaCmd<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> {
    name: &'static str,
    summary: &'static str,
    info: &'static [&'static str],
    format: &'static str,
    example: &'static [&'static str],
    returns: &'static str,
    pub(crate) run:
        fn(repl: &mut Repl<F, C1, C2>, args: &ZPtr<F>, file_dir: &Utf8Path) -> Result<ZPtr<F>>,
}

pub(crate) type MetaCmdsMap<F, C1, C2> = FxHashMap<Symbol, MetaCmd<F, C1, C2>>;

impl<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> MetaCmd<F, C1, C2> {
    const ASSERT: Self = Self {
        name: "assert",
        summary: "Asserts that an expression doesn't reduce to nil.",
        info: &["Exits the REPL if the assertion is not satisfied."],
        format: "!(assert <expr>)",
        example: &["!(assert t)", "!(assert (eq 3 (+ 1 2)))"],
        returns: "t",
        run: |repl, args, _dir| {
            let [&expr] = repl.take(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            if &result == repl.zstore.nil() {
                eprintln!("assert failed. {} evaluates to nil", repl.fmt(&expr));
                std::process::exit(1);
            }
            Ok(*repl.zstore.t())
        },
    };

    const ASSERT_EQ: Self = Self {
        name: "assert-eq",
        summary: "Asserts that two expressions evaluate to the same value.",
        info: &["Exits the REPL if the assertion is not satisfied."],
        format: "!(assert-eq <expr1> <expr2>)",
        example: &["!(assert-eq 3 (+ 1 2))"],
        returns: "t",
        run: |repl, args, _dir| {
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
                repl.memoize_dag(&result1);
                repl.memoize_dag(&result2);
                eprintln!(
                    "assert-eq failed. {} ≠ {}",
                    repl.fmt(&result1),
                    repl.fmt(&result2)
                );
                std::process::exit(1);
            }
            Ok(*repl.zstore.t())
        },
    };

    const ASSERT_ERROR: Self = Self {
        name: "assert-error",
        summary: "Asserts that a evaluation of <expr> fails.",
        info: &["Exits the REPL if the assertion is not satisfied."],
        format: "!(assert-error <expr>)",
        example: &["!(assert-error (1 1))"],
        returns: "t",
        run: |repl, args, _dir| {
            let [&expr] = repl.take(args)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag != Tag::Err {
                eprintln!(
                    "assert-error failed. {} doesn't result on evaluation error.",
                    repl.fmt(&expr)
                );
                std::process::exit(1);
            }
            Ok(*repl.zstore.t())
        },
    };

    const ASSERT_EMITTED: Self = Self {
        name: "assert-emitted",
        summary: "Asserts that the evaluation of an expr emits expected values",
        info: &[
            "Asserts that the list of values in the first <expr> are emitted by",
            "the reduction of the second <expr>.",
            "Exits the REPL if the assertion is not satisfied.",
        ],
        format: "!(assert-emitted <expr> <expr>)",
        example: &["!(assert-emitted '(1 2) (begin (emit 1) (emit 2)))"],
        returns: "t",
        run: |repl, args, _dir| {
            let [&expected_expr, &expr] = repl.take(args)?;
            let (expected, _) = repl.reduce_aux(&expected_expr)?;
            let (result, emitted) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            let emitted = repl.zstore.intern_list(emitted);
            if expected != emitted {
                repl.memoize_dag(&expected);
                // DAG for `emitted` has already been memoized
                eprintln!(
                    "assert-emitted failed. Expected {} but got {}",
                    repl.fmt(&expected),
                    repl.fmt(&emitted)
                );
                std::process::exit(1);
            }
            Ok(*repl.zstore.t())
        },
    };

    const DEBUG: Self = Self {
        name: "debug",
        summary: "Enters the debug mode for a reduction",
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
        format: "!(debug <expr>?)",
        example: &["(+ 1 1)", "!(debug)", "!(debug (+ 1 1))"],
        returns: "t",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                let [&expr] = repl.take(args)?;
                let result = repl.handle_non_meta(&expr);
                debug_mode(&repl.format_debug_data())?;
                result.map(|_| ())?;
            } else {
                debug_mode(&repl.format_debug_data())?;
            }
            Ok(*repl.zstore.t())
        },
    };

    fn validate_path_type(path: &ZPtr<F>) -> Result<()> {
        if path.tag != Tag::Str {
            bail!("Path must be a string");
        }
        Ok(())
    }

    const LOAD: Self = Self {
        name: "load",
        summary: "Load Lurk expressions from a file.",
        info: &[],
        format: "!(load <string>)",
        example: &["!(load \"my_file.lurk\")"],
        returns: "t",
        run: |repl, args, path| {
            let [file_name_zptr] = repl.take(args)?;
            Self::validate_path_type(file_name_zptr)?;
            let file_name = repl.zstore.fetch_string(file_name_zptr);
            repl.load_file(&path.join(file_name), false)?;
            Ok(*repl.zstore.t())
        },
    };

    const DEFQ: Self = Self {
        name: "defq",
        summary: "Extends env with a non-evaluated expression.",
        info: &[],
        format: "!(defq <symbol> <value>)",
        example: &["!(defq foo (1 . 2))"],
        returns: "The binding symbol",
        run: |repl, args, _dir| {
            let [&sym, &val] = repl.take(args)?;
            Self::validate_binding_symbol(repl, &sym)?;
            repl.bind(sym, val);
            Ok(sym)
        },
    };

    const DEF: Self = Self {
        name: "def",
        summary: "Extends env with a non-recursive binding.",
        info: &[],
        format: "!(def <symbol> <expr>)",
        example: &["!(def foo (lambda () 123))"],
        returns: "The binding symbol",
        run: |repl, args, _dir| {
            let [&sym, &expr] = repl.take(args)?;
            Self::validate_binding_symbol(repl, &sym)?;
            let (val, _) = repl.reduce_aux(&expr)?;
            if val.tag == Tag::Err {
                bail!(repl.fmt(&val));
            }
            repl.memoize_dag(&val);
            repl.bind(sym, val);
            Ok(sym)
        },
    };

    const DEFREC: Self = Self {
        name: "defrec",
        summary: "Extends env with a recursive binding.",
        info: &[
            "Gets macroexpanded to (letrec ((<symbol> <expr>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        format: "!(defrec <symbol> <expr>)",
        example: &[
            "!(defrec sum (lambda (l) (if (eq l nil) 0 (+ (car l) (sum (cdr l))))))",
            "(sum '(1 2 3))",
        ],
        returns: "The binding symbol",
        run: |repl, args, _dir| {
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
            let (env, _) = repl.reduce_aux(&expr)?;
            if env.tag != Tag::Env {
                bail!("Reduction resulted in {}", repl.fmt(&env));
            }
            repl.env = env;
            Ok(sym)
        },
    };

    fn validate_binding_symbol(repl: &Repl<F, C1, C2>, zptr: &ZPtr<F>) -> Result<()> {
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

    const UPDATE: Self = Self {
        name: "update",
        summary: "Updates an env variable by applying it to a function.",
        info: &[],
        format: "!(update <symbol> <function_expr>)",
        example: &["!(def a 1)", "!(update a (lambda (x) (+ x 1)))"],
        returns: "The symbol whose bound value was updated",
        run: |repl, args, _dir| {
            let [&sym, &fun] = repl.take(args)?;
            Self::validate_binding_symbol(repl, &sym)?;
            let expr = repl.zstore.intern_list([fun, sym]);
            let (res, _) = repl.reduce_aux(&expr)?;
            if res.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&res));
            }
            repl.bind(sym, res);
            Ok(sym)
        },
    };

    const CLEAR: Self = Self {
        name: "clear",
        summary: "Resets the current environment to be empty.",
        info: &[],
        format: "!(clear)",
        example: &["!(def a 1)", "(current-env)", "!(clear)", "(current-env)"],
        returns: "t",
        run: |repl, _args, _dir| {
            repl.env = repl.zstore.intern_empty_env();
            Ok(*repl.zstore.t())
        },
    };

    const SET_ENV: Self = Self {
        name: "set-env",
        summary: "Sets the env to the result of evaluating the argument.",
        info: &[],
        format: "!(set-env <expr>)",
        example: &["!(set-env (eval '(let ((a 1)) (current-env))))", "a"],
        returns: "t",
        run: |repl, args, _dir| {
            let [&env_expr] = repl.take(args)?;
            let (env, _) = repl.reduce_aux(&env_expr)?;
            if env.tag != Tag::Env {
                bail!("Value must be an environment");
            }
            repl.env = env;
            Ok(*repl.zstore.t())
        },
    };

    const ERASE_FROM_ENV: Self = Self {
        name: "erase-from-env",
        summary: "Erases all bindings for the provided variables from the environment.",
        info: &["If a variable is not present in the environment, it's ignored."],
        format: "!(erase-from-env <var1> <var2> ...)",
        example: &["!(erase-from-env foo bar)"],
        returns: "t",
        run: |repl, args, _dir| {
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
            Ok(*repl.zstore.t())
        },
    };

    fn hide(
        secret: [F; DIGEST_SIZE],
        payload_expr: &ZPtr<F>,
        repl: &mut Repl<F, C1, C2>,
    ) -> Result<ZPtr<F>> {
        let (payload, _) = repl.reduce_aux(payload_expr)?;
        if payload.tag == Tag::Err {
            bail!("Payload reduction error: {}", repl.fmt(&payload));
        }
        let comm = repl.persist_comm_data(secret, payload)?;
        if let Some(scope) = repl.current_scope() {
            update_scope_comms(&scope.digest, |mut scope_comms| {
                scope_comms.insert(comm.digest.into());
                Ok(scope_comms)
            })?;
        }
        Ok(comm)
    }

    const HIDE: Self = Self {
        name: "hide",
        summary: "Persists a hiding commitment.",
        info: &[
            "The secret is the reduction of <secret_expr>, which must be a",
            "bignum, and the payload is the reduction of <payload_expr>.",
        ],
        format: "!(hide <secret_expr> <payload_expr>)",
        example: &["!(hide (bignum (commit 123)) 42)", "!(hide #0x123 42)"],
        returns: "The resulting commitment",
        run: |repl, args, _dir| {
            let [&secret_expr, &payload_expr] = repl.take(args)?;
            let (secret, _) = repl.reduce_aux(&secret_expr)?;
            if secret.tag != Tag::BigNum {
                bail!("Secret must reduce to a bignum");
            }
            Self::hide(secret.digest, &payload_expr, repl)
        },
    };

    const RAND: Self = Self {
        name: "rand",
        summary: "Creates a random big num that can be used for secrets",
        info: &["The randomness comes from fresh system entropy everytime."],
        format: "!(rand)",
        example: &["(hide !(rand) 42)"],
        returns: "The random big num",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                bail!("No arguments are accepted");
            }
            Ok(repl.zstore.intern_big_num(rand_digest()))
        },
    };

    const COMMIT: Self = Self {
        name: "commit",
        summary: "Persists a commitment.",
        info: &[
            "The secret is zero big num and the payload is the reduction of",
            "<payload_expr>. Equivalent to !(hide #0x0 <payload_expr>).",
        ],
        format: "!(commit <payload_expr>)",
        example: &["!(commit 42)"],
        returns: "The resulting commitment",
        run: |repl, args, _dir| {
            let [&payload_expr] = repl.take(args)?;
            Self::hide([F::zero(); DIGEST_SIZE], &payload_expr, repl)
        },
    };

    fn fetch_persisted_comm_data(repl: &mut Repl<F, C1, C2>, digest: List<F>) -> Result<ZPtr<F>> {
        let hash = format!("{:x}", field_elts_to_biguint(&digest));
        let comm_data_bytes = std::fs::read(commits_dir()?.join(&hash))?;
        let CommData {
            secret,
            payload,
            zdag,
        } = bincode::deserialize(&comm_data_bytes)?;
        let mut preimg = Vec::with_capacity(HASH3_SIZE);
        preimg.extend(secret);
        preimg.extend(payload.flatten());
        repl.queries
            .inject_inv_queries_owned("commit", &repl.toplevel, [(preimg, digest)]);
        zdag.populate_zstore(&mut repl.zstore);
        Ok(payload)
    }

    /// Tries to fetch persisted commitment data if it's not already available
    /// in the REPL's `QueryRecord`
    fn fetch_comm_data(repl: &mut Repl<F, C1, C2>, digest: List<F>) -> Result<()> {
        let inv_comms = repl.queries.get_inv_queries("commit", &repl.toplevel);
        if !inv_comms.contains_key(&digest) {
            Self::fetch_persisted_comm_data(repl, digest)?;
        }
        Ok(())
    }

    const OPEN: Self = Self {
        name: "open",
        summary: "Fetches a persisted commitment.",
        info: &[],
        format: "!(open <comm>)",
        example: &[
            "!(commit 123)",
            "!(open #c0x944834111822843979ace19833d05ca9daf2f655230faec517433e72fe777b)",
        ],
        returns: "The commitment payload",
        run: |repl, args, _dir| {
            let [&expr] = repl.take(args)?;
            let (ZPtr { tag, digest }, _) = repl.reduce_aux(&expr)?;
            match tag {
                Tag::BigNum | Tag::Comm => Self::fetch_persisted_comm_data(repl, digest.into()),
                _ => bail!("Expected a commitment or a BigNum"),
            }
        },
    };

    fn eval_then_quote(repl: &mut Repl<F, C1, C2>, args: &ZPtr<F>) -> Result<ZPtr<F>> {
        let (args_vec, _) = repl.zstore.fetch_list(args);
        let args_vec = copy_inner(args_vec);
        let mut args_vec_reduced_quoted = Vec::with_capacity(args_vec.len());
        for arg in &args_vec {
            let (arg_reduced, _) = repl.reduce_aux(arg)?;
            if arg_reduced.tag == Tag::Err {
                bail!("Error when evaluating argument {}", repl.fmt(arg));
            }
            repl.memoize_dag(&arg_reduced);
            args_vec_reduced_quoted.push(repl.zstore.intern_quoted(arg_reduced));
        }
        Ok(repl.zstore.intern_list(args_vec_reduced_quoted))
    }

    /// Performs a function call with the arguments evaluated and quoted. Returns
    /// the call result and the final list of arguments.
    ///
    /// The callable and arguments are evaluated with the REPL's env and then the
    /// resulting call expression is evaluated with a custom env.
    fn call(
        repl: &mut Repl<F, C1, C2>,
        call_expr: &ZPtr<F>,
        env: &ZPtr<F>,
    ) -> Result<(ZPtr<F>, ZPtr<F>)> {
        if call_expr == repl.zstore.nil() {
            bail!("Missing callable object");
        }
        let (&callable, &call_args) = repl.zstore.fetch_tuple11(call_expr);
        let (callable, _) = repl.reduce_aux(&callable)?;
        if matches!(callable.tag, Tag::BigNum | Tag::Comm) {
            Self::fetch_comm_data(repl, callable.digest.into())?;
        }
        let call_args = Self::eval_then_quote(repl, &call_args)?;
        let call_expr = repl.zstore.intern_cons(callable, call_args);
        Ok((repl.handle_non_meta_with_env(&call_expr, env)?, call_args))
    }

    const CALL: Self = Self {
        name: "call",
        summary: "Evaluates arguments and applies them, quoted, to a callable object",
        info: &["It's also capable of opening persisted commitments."],
        format: "!(call <callable> <arg1_expr> <arg2_expr> ...)",
        example: &[
            "(commit (lambda (x) x))",
            "!(call #c0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 0)",
        ],
        returns: "The call result",
        run: |repl, args, _dir| {
            let (res, _) = Self::call(repl, args, &repl.env.clone())?;
            Ok(res)
        },
    };

    /// Splits a commitment preimage into the corresponding secret digest and
    /// payload `ZPtr`.
    fn split_comm_data_preimg(preimg: &[F]) -> ([F; DIGEST_SIZE], ZPtr<F>) {
        let mut secret = [F::default(); DIGEST_SIZE];
        secret.copy_from_slice(&preimg[..DIGEST_SIZE]);
        let payload = ZPtr::from_flat_data(&preimg[DIGEST_SIZE..]);
        (secret, payload)
    }

    /// If the callable of a chain result is a commitment, persist its corresponding
    /// `CommData`.
    fn persist_chain_callable_if_comm(repl: &mut Repl<F, C1, C2>, cons: &ZPtr<F>) -> Result<()> {
        if cons.tag != Tag::Cons {
            bail!("Chain result must be a pair");
        }
        if repl.current_scope().is_some() {
            // When in a scope, all commitments are persisted automatically.
            return Ok(());
        }
        let (_, next_callable) = repl.zstore.fetch_tuple11(cons);
        if matches!(next_callable.tag, Tag::Comm | Tag::BigNum) {
            let inv_comms = repl.queries.get_inv_queries("commit", &repl.toplevel);
            let preimg = inv_comms
                .get(next_callable.digest.as_slice())
                .expect("Preimage must be known");
            let (secret, payload) = Self::split_comm_data_preimg(preimg);
            repl.persist_comm_data(secret, payload)?;
        }
        Ok(())
    }

    const CHAIN: Self = Self {
        name: "chain",
        summary: "Evaluates arguments and applies them, quoted, to a chainable callable object",
        info: &[
            "It's also capable of opening persisted commitments.",
            "Persists the next callable if it is a commitment.",
        ],
        format: "!(chain <callable> <arg1_expr> <arg2_expr> ...)",
        example: &[
            "(commit (letrec ((add (lambda (counter x)
                       (let ((counter (+ counter x)))
                         (cons counter (commit (add counter)))))))
               (add 0)))",
            "!(chain #c0x545e921e6ef944cd72811575b1064f8737d520cd04dd75a47ad6c5bf509ea7 1)",
        ],
        returns: "The chained result",
        run: |repl, args, _dir| {
            let env = repl.zstore.intern_empty_env();
            let (cons, _) = Self::call(repl, args, &env)?;
            Self::persist_chain_callable_if_comm(repl, &cons)?;
            Ok(cons)
        },
    };

    /// Performs a chain transition and returns the next chain state and the
    /// list of argument (evaluated+quoted) used to perform the call.
    ///
    /// Note: the call expression is evaluated with the empty env.
    fn transition_call(
        repl: &mut Repl<F, C1, C2>,
        current_state_expr: &ZPtr<F>,
        call_args: ZPtr<F>,
    ) -> Result<(ZPtr<F>, ZPtr<F>)> {
        let (current_state, _) = repl.reduce_aux(current_state_expr)?;
        if current_state.tag != Tag::Cons {
            bail!("Current state must reduce to a pair");
        }
        repl.memoize_dag(&current_state);
        let (_, &callable) = repl.zstore.fetch_tuple11(&current_state);
        let call_expr = repl.zstore.intern_cons(callable, call_args);
        let env = repl.zstore.intern_empty_env();
        Self::call(repl, &call_expr, &env)
    }

    const TRANSITION: Self = Self {
        name: "transition",
        summary: "Chains a callable object and returns the next state",
        info: &["It has the same side effects of the `chain` meta command."],
        format: "!(transition <state_expr> <call_args>)",
        example: &["!(defq new-state !(transition old-state input))"],
        returns: "The chained result",
        run: |repl, args, _dir| {
            let (&current_state_expr, &call_args) = repl.car_cdr(args);
            let (cons, _) = Self::transition_call(repl, &current_state_expr, call_args)?;
            Self::persist_chain_callable_if_comm(repl, &cons)?;
            Ok(cons)
        },
    };

    const DEFPACKAGE: Self = Self {
        name: "defpackage",
        summary: "Adds a package to the state.",
        info: &[],
        format: "!(defpackage <string|symbol>)",
        example: &["!(defpackage abc)"],
        returns: "The symbol naming the new package",
        run: |repl, args, _dir| {
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
            let name_zptr = repl.zstore.intern_symbol(&name, &repl.lang_symbols);
            repl.state.borrow_mut().add_package(Package::new(name));
            Ok(name_zptr)
        },
    };

    const IMPORT: Self = Self {
        name: "import",
        summary: "Import a single or several packages.",
        info: &[],
        format: "!(import <string|package> ...)",
        example: &[],
        returns: "t",
        run: |repl, args, _dir| {
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
            Ok(*repl.zstore.t())
        },
    };

    const IN_PACKAGE: Self = Self {
        name: "in-package",
        summary: "set the current package.",
        info: &[],
        format: "!(in-package <string|symbol>)",
        example: &[
            "!(defpackage abc)",
            "!(in-package abc)",
            "!(def two (.lurk.builtin.+ 1 1))",
            "!(in-package .lurk-user)",
            ".lurk-user.abc.two",
        ],
        returns: "t",
        run: |repl, args, _dir| {
            let [arg] = repl.take(args)?;
            match arg.tag {
                Tag::Str => {
                    let name = repl.zstore.fetch_string(arg);
                    let package_name = repl.state.borrow_mut().intern(name);
                    repl.state.borrow_mut().set_current_package(package_name)?;
                }
                Tag::Sym => {
                    let package_name = repl.zstore.fetch_symbol(arg);
                    repl.state
                        .borrow_mut()
                        .set_current_package(package_name.into())?;
                }
                _ => bail!("Expected string or symbol. Got {}", repl.fmt(arg)),
            }
            Ok(*repl.zstore.t())
        },
    };

    const DUMP_EXPR: Self = Self {
        name: "dump-expr",
        summary: "Evaluates an expression and dumps the result to the file system",
        info: &["Commitments are persisted opaquely."],
        format: "!(dump-expr <expr> <string>)",
        example: &["!(dump-expr (+ 1 1) \"my_file\")"],
        returns: "The persisted data",
        run: |repl, args, _dir| {
            let [&expr, &path] = repl.take(args)?;
            Self::validate_path_type(&path)?;
            let (result, _) = repl.reduce_aux(&expr)?;
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            let path_str = repl.zstore.fetch_string(&path);
            repl.memoize_dag(&result);
            let lurk_data = LurkData::new(result, &repl.zstore);
            let lurk_data_bytes = bincode::serialize(&lurk_data)?;
            std::fs::write(&path_str, lurk_data_bytes)?;
            println!("Data persisted on file `{path_str}`");
            Ok(result)
        },
    };

    const LOAD_EXPR: Self = Self {
        name: "load-expr",
        summary: "Loads Lurk data from the file system",
        info: &[],
        format: "!(load-expr <string>)",
        example: &[
            "!(dump-expr (+ 1 1) \"my_file\")",
            "!(assert-eq 2 !(load-expr \"my_file\"))",
        ],
        returns: "The loaded data",
        run: |repl, args, _dir| {
            let [&path] = repl.take(args)?;
            Self::validate_path_type(&path)?;
            let path_str = repl.zstore.fetch_string(&path);
            let lurk_data_bytes = std::fs::read(&path_str)?;
            let lurk_data: LurkData<F> = bincode::deserialize(&lurk_data_bytes)?;
            let payload = lurk_data.populate_zstore(&mut repl.zstore);
            Ok(payload)
        },
    };

    const DEFPROTOCOL: Self = Self {
        name: "defprotocol",
        summary: "Defines a protocol",
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
        format: "!(defprotocol <symbol> <vars> <body> options...)",
        example: &[
            "!(defprotocol my-protocol (hash pair)",
            "  (cons",
            "    (if (= (+ (car pair) (cdr pair)) 30)",
            "      (cons (cons (cons 'open (cons hash nil)) (empty-env)) pair)",
            "      nil)",
            "    (lambda () (> (car pair) 10)))",
            "  :description \"hash opens to a pair (a, b) s.t. a+b=30 and a>10\")",
        ],
        returns: "The symbol naming the protocol",
        run: |repl, args, _dir| {
            let (&name, rest) = repl.car_cdr(args);
            let (&vars, rest) = repl.car_cdr(rest);
            let (&body, &props) = repl.car_cdr(rest);
            Self::validate_binding_symbol(repl, &name)?;
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
            repl.bind(name, protocol);
            Ok(name)
        },
    };

    const HELP: Self = Self {
        name: "help",
        summary: "Prints a help message",
        info: &[
            "Without arguments it prints a summary of all available commands.",
            "Otherwise the full help for the command in the first argument is printed.",
        ],
        format: "!(help <symbol>)",
        example: &["!(help)", "!(help prove)"],
        returns: "t",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                let [arg] = repl.take(args)?;
                if !matches!(arg.tag, Tag::Sym | Tag::Builtin) {
                    bail!("Argument must be a symbol");
                }
                let sym_path = repl.zstore.fetch_symbol_path(arg);
                let Some(name) = sym_path.last() else {
                    bail!("Argument can't be the root symbol");
                };
                let Some(meta_cmd) = repl.meta_cmds.get(&meta_sym(name)) else {
                    bail!("Unknown meta command");
                };
                println!("{} - {}", meta_cmd.name, meta_cmd.summary);
                if !meta_cmd.info.is_empty() {
                    println!("  Info:");
                }
                for e in meta_cmd.info {
                    println!("    {e}");
                }
                println!("  Format: {}", meta_cmd.format);
                if !meta_cmd.example.is_empty() {
                    println!("  Example:");
                }
                for e in meta_cmd.example {
                    println!("    {e}");
                }
                println!("  Returns: {}", meta_cmd.returns);
            } else {
                println!("Available commands:");
                for (_, i) in repl.meta_cmds.iter().sorted_by_key(|x| x.0) {
                    println!("  {} - {}", i.name, i.summary);
                }
            }
            Ok(*repl.zstore.t())
        },
    };

    fn scope_stack(repl: &mut Repl<F, C1, C2>) -> ZPtr<F> {
        let scope_stack = repl.scopes.iter().rev().map(|(s, _)| *s);
        repl.zstore.intern_list(scope_stack)
    }

    const SCOPE: Self = Self {
        name: "scope",
        summary: "Enters a new or existing scope",
        info: &[
            "Scopes are symbol-named contexts in which:",
            "* Commitments created are persisted and become automatically available",
            "  when entering the same scope again;",
            "* It's possible to store (see `scope-store`) variables, which become",
            "  automatically available when entering the same scope again;",
            "* Setting a microchain (see `microchain-set-info`) persists the microchain",
            "  information within that scope so that it's not necessary to set it",
            "  again.",
            "When entering a scope, commitments and definitions from the outer scope",
            "are available for read purposes. The microchain info, however, is not",
            "inherited as a security measure and must be set again if intended.",
        ],
        format: "!(scope <sym>)",
        example: &["!(scope my-scope)"],
        returns: "The resulting stack of scopes",
        run: |repl, args, _dir| {
            let [&scope] = repl.take(args)?;
            Self::validate_binding_symbol(repl, &scope)?;
            if repl.scopes.contains_key(&scope) {
                bail!("Scope already stacked")
            }

            // Save the data for the current environment.
            let outer_env = repl.env;
            let outer_comms = repl
                .queries
                .get_inv_queries("commit", &repl.toplevel)
                .keys()
                .map(Box::clone)
                .collect();
            // Note: `Option::take` makes new scopes start with no microchain set.
            let outer_microchain = repl.microchain.take();

            // Attempt to load potentially persisted bindings.
            if let Ok(scope_bindings) = load_scope_bindings(&scope.digest) {
                let ScopeBindings { binds, zdag } = scope_bindings;
                zdag.populate_zstore(&mut repl.zstore);
                binds.into_iter().for_each(|(sym, val)| repl.bind(sym, val));
            }

            // Attempt to load potentially persisted commitments.
            if let Ok(comms) = load_scope_comms(&scope.digest) {
                for digest in comms {
                    Self::fetch_comm_data(repl, digest)?;
                }
            }

            // Attempt to load potentially persisted microchain info.
            if let Ok(microchain) = load_scope_microchain(&scope.digest) {
                repl.microchain = microchain;
            }

            let outer_scope = OuterScope {
                env: outer_env,
                comms: outer_comms,
                microchain: outer_microchain,
            };
            repl.scopes.insert(scope, outer_scope);
            Ok(Self::scope_stack(repl))
        },
    };

    const SCOPE_POP: Self = Self {
        name: "scope-pop",
        summary: "Go to the outer scope",
        info: &[
            "When a scope is popped, the context from the outer scope is recovered.",
            "That is, commitments available, definitions and microchain information.",
        ],
        format: "!(scope-pop)",
        example: &["!(scope-pop)"],
        returns: "A pair with the resulting scope stack and the popped scope",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                bail!("Arguments aren't supported")
            }
            let Some((sym, outer_scope)) = repl.scopes.pop() else {
                bail!("Not in a scope")
            };
            let OuterScope {
                env,
                comms,
                microchain,
            } = outer_scope;
            repl.env = env;
            let inv_comms_ref = &mut repl.queries.inv_func_queries[repl.func_indices.commit];
            let inv_comms = std::mem::take(inv_comms_ref).expect("commit coroutine is invertible");
            let filtered = inv_comms
                .into_iter()
                .filter(|(k, _)| comms.contains(k))
                .collect();
            repl.queries.inv_func_queries[repl.func_indices.commit] = Some(filtered);
            repl.microchain = microchain;
            let scope_stack = Self::scope_stack(repl);
            Ok(repl.zstore.intern_cons(scope_stack, sym))
        },
    };

    const SCOPE_STORE: Self = Self {
        name: "scope-store",
        summary: "Stores a symbol binding for availability when re-entering the scope",
        info: &[],
        format: "!(scope-store <sym1> <sym2> ...)",
        example: &["!(scope-store var1 var2 var3)"],
        returns: "t",
        run: |repl, args, _dir| {
            let Some(&scope) = repl.current_scope() else {
                bail!("Not in a scope");
            };
            repl.memoize_env_dag();
            let (syms, _) = repl.zstore.fetch_list(args);
            let env_vec = repl.zstore.fetch_env(&repl.env);
            // `env_vec` needs to be consumed in reverse order so bindings can
            // be shadowed properly.
            let env_map = env_vec.into_iter().rev().collect::<FxHashMap<_, _>>();
            update_scope_bindings(&scope.digest, |mut scope_bindings| {
                for sym in &syms {
                    let Some(val) = env_map.get(sym) else {
                        bail!("Unbound symbol: {}", repl.fmt(sym));
                    };
                    scope_bindings.bind(**sym, **val, &repl.zstore);
                }
                Ok(scope_bindings)
            })?;
            Ok(*repl.zstore.t())
        },
    };
}

type F = BabyBear;

impl<C1: Chipset<F>, C2: Chipset<F>> MetaCmd<F, C1, C2> {
    const PROVE: Self = Self {
        name: "prove",
        summary: "Prove a Lurk reduction, persists the proof and prints its key",
        info: &[],
        format: "!(prove <expr>?)",
        example: &["'(1 2 3)", "!(prove)", "!(prove '(1 2 3))"],
        returns: "The proof key as a string",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                let [&expr] = repl.take(args)?;
                repl.handle_non_meta(&expr)?;
            }
            let proof_key = repl.prove_last_reduction()?;
            Ok(repl.zstore.intern_string(&proof_key))
        },
    };

    fn load_cached_proof(proof_key: &str) -> Result<CachedProof> {
        let proof_dir = proofs_dir()?.join(proof_key);
        if !proof_dir.exists() {
            bail!("Proof not found");
        }
        let cached_proof_bytes = std::fs::read(proof_dir)?;
        let cached_proof = bincode::deserialize(&cached_proof_bytes)?;
        Ok(cached_proof)
    }

    fn load_cached_proof_with_repl(
        repl: &mut Repl<F, C1, C2>,
        args: &ZPtr<F>,
    ) -> Result<(String, CachedProof)> {
        let [&proof_key_expr] = repl.take(args)?;
        let (proof_key_zptr, _) = repl.reduce_aux(&proof_key_expr)?;
        if proof_key_zptr.tag != Tag::Str {
            bail!("Proof key must be a string");
        }
        let proof_key = repl.zstore.fetch_string(&proof_key_zptr);
        let cached_proof = Self::load_cached_proof(&proof_key)?;
        Ok((proof_key, cached_proof))
    }

    const VERIFY: Self = Self {
        name: "verify",
        summary: "Verifies Lurk reduction proof",
        info: &[
            "Verifies a Lurk reduction proof by its key.",
            "Errors if the proof doesn't verify.",
        ],
        format: "!(verify <string>)",
        example: &["!(verify \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        returns: "t",
        run: |repl, args, _dir| {
            let (proof_key, cached_proof) = Self::load_cached_proof_with_repl(repl, args)?;
            let has_same_verifier_version = cached_proof.crypto_proof.has_same_verifier_version();
            let machine = new_machine(&repl.toplevel);
            let machine_proof = cached_proof.into_machine_proof();
            let (_, vk) = machine.setup(&LairMachineProgram);
            let challenger = &mut machine.config().challenger();
            if machine.verify(&vk, &machine_proof, challenger).is_ok() {
                println!("✓ Proof \"{proof_key}\" verified");
                Ok(*repl.zstore.t())
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
        info: &[],
        format: "!(inspect <string>)",
        example: &["!(inspect \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        returns: "The proof claim",
        run: |repl, args, _dir| {
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
            let expr_env = repl.zstore.intern_cons(expr, env);
            Ok(repl.zstore.intern_cons(expr_env, result))
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
        repl.memoize_dag(&io_data);
        let (claim, post_verify_predicate) = repl.zstore.fetch_tuple11(&io_data);
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
        info: &[
            "The proof is created only if the protocol can be satisfied by the",
            "provided arguments.",
            "The second (string) argument for this meta command is the path to",
            "the file where the protocol proof will be saved.",
        ],
        format: "!(prove-protocol <protocol> <string> args...)",
        example: &[
            "(commit '(13 . 17))",
            "!(prove-protocol my-protocol",
            "  \"protocol-proof\"",
            "  #c0x955f855f302a30ed988cc48685c442ebd98c8711e989fc64df8f27f52e1350",
            "  '(13 . 17))",
        ],
        returns: "The proof key",
        run: |repl, args, _dir| {
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

            let (args_vec, _) = repl.zstore.fetch_list(&args);
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
                repl.memoize_dag(&arg_reduced);
                args_vec_reduced.push(arg_reduced);
            }

            let (&claim, &post_verify_predicate) = Self::get_claim_and_post_verify_predicade(
                repl,
                vars_vec,
                args_vec_reduced.clone(),
                &body,
            )?;

            Self::post_verify_check(repl, post_verify_predicate)?;

            let (expr_env, &expected_result) = repl.zstore.fetch_tuple11(&claim);
            if expr_env.tag != Tag::Cons {
                bail!("Malformed protocol claim");
            }
            let (&expr, &env) = repl.zstore.fetch_tuple11(expr_env);
            let result = repl.reduce_with_env(&expr, &env)?;
            if result != expected_result {
                bail!("Mismatch between result and expected result");
            }

            let proof_key = repl.prove_last_reduction()?;
            let cached_proof = Self::load_cached_proof(&proof_key)?;
            let crypto_proof = cached_proof.crypto_proof;
            let args_reduced = repl.zstore.intern_list(args_vec_reduced);
            let protocol_proof = ProtocolProof::new(crypto_proof, args_reduced, &repl.zstore);
            std::fs::write(&path_str, bincode::serialize(&protocol_proof)?)?;
            println!("Protocol proof saved on file `{path_str}`");
            Ok(repl.zstore.intern_string(&proof_key))
        },
    };

    const VERIFY_PROTOCOL: Self = Self {
        name: "verify-protocol",
        summary: "Verifies a proof for a protocol",
        info: &[
            "Reconstructs the proof input with the args provided by the prover",
            "according to the protocol and then verifies the proof.",
            "If verification succeeds, runs the post-verification predicate,",
            "failing if the predicate returns nil.",
            "The second (string) argument is the path to the file containing the",
            "protocol proof.",
            "Errors if the proof doesn't verify.",
        ],
        format: "!(verify-protocol <protocol> <string>)",
        example: &["!(verify-protocol my-protocol \"protocol-proof\")"],
        returns: "t",
        run: |repl, args, _dir| {
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
            if args.is_flawed(&mut repl.zstore) {
                bail!("Arguments contain flawed data");
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

            let (expr_env, result) = repl.zstore.fetch_tuple11(&claim);
            if expr_env.tag != Tag::Cons {
                bail!("Malformed protocol claim");
            }
            let (expr, env) = repl.zstore.fetch_tuple11(expr_env);
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
            Ok(*repl.zstore.t())
        },
    };

    fn set_microchain(
        repl: &mut Repl<F, C1, C2>,
        addr: String,
        id: [F; DIGEST_SIZE],
    ) -> Result<()> {
        if repl.microchain.is_some() {
            print!("A microchain is already set. Overwrite it? (y/*) ");
            std::io::stdout().flush()?;
            let mut input = String::new();
            std::io::stdin().read_line(&mut input)?;
            if input != "y\n" {
                bail!("Microchain set operation was canceled")
            }
        }
        repl.microchain = Some((addr, id));
        if let Some(scope) = repl.current_scope() {
            dump_scope_microchain(&scope.digest, &repl.microchain)?;
        }
        Ok(())
    }

    const MICROCHAIN_SET_INFO: Self = Self {
        name: "microchain-set-info",
        summary: "Sets the REPL to point to a particular microchain address and ID",
        info: &["When in a scope, this information is persisted across REPL instantiations"],
        format: "!(microchain-set-info <addr_expr> <id_expr>)",
        example: &["!(microchain-set-info \"127.0.0.1:1234\" #c0x123)"],
        returns: "t",
        run: |repl, args, _dir| {
            let [&addr_expr, &id_expr] = repl.take(args)?;
            let (addr, _) = repl.reduce_aux(&addr_expr)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (id, _) = repl.reduce_aux(&id_expr)?;
            if !matches!(id.tag, Tag::Comm | Tag::BigNum) {
                bail!("ID must be a commitment or a big num");
            }
            let addr_str = repl.zstore.fetch_string(&addr);
            Self::set_microchain(repl, addr_str, id.digest)?;
            Ok(*repl.zstore.t())
        },
    };

    const MICROCHAIN_GET_INFO: Self = Self {
        name: "microchain-get-info",
        summary: "Retrieves the REPL microchain address and ID",
        info: &[],
        format: "!(microchain-get-info)",
        example: &["!(microchain-get-info)"],
        returns: "The address/ID pair for the REPL microchain",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                bail!("Arguments aren't supported");
            }
            let Some((addr, id)) = &repl.microchain else {
                bail!("No microchain info set");
            };
            let addr = repl.zstore.intern_string(addr);
            let id = repl.zstore.intern_comm(*id);
            Ok(repl.zstore.intern_cons(addr, id))
        },
    };

    fn build_comm_data(repl: &mut Repl<F, C1, C2>, digest: &[F]) -> CommData<F> {
        let inv_comms = repl.queries.get_inv_queries("commit", &repl.toplevel);
        let callable_preimg = inv_comms.get(digest).expect("Missing commitment preimage");
        let (secret, payload) = Self::split_comm_data_preimg(callable_preimg);
        repl.memoize_dag(&payload);
        CommData::new(secret, payload, &repl.zstore)
    }

    /// Computes a microchain ID by delegating the hashing to the REPL's reduction
    /// so the commitment is persisted automatically when in a scope.
    fn compute_microchain_id(
        repl: &mut Repl<F, C1, C2>,
        id_secret: [F; DIGEST_SIZE],
        genesis: ZPtr<F>,
    ) -> Result<ZPtr<F>> {
        let hide = repl
            .zstore
            .intern_symbol(&builtin_sym("hide"), &repl.lang_symbols);
        let secret = repl.zstore.intern_big_num(id_secret);
        let genesis_quoted = repl.zstore.intern_quoted(genesis);
        let expr = repl.zstore.intern_list([hide, secret, genesis_quoted]);
        let (id, _) = repl.reduce_aux(&expr)?;
        Ok(id)
    }

    const MICROCHAIN_START: Self = Self {
        name: "microchain-start",
        summary: "Starts a new microchain and returns the resulting ID",
        info: &[
            "A microchain ID is a hiding commitment to the genesis state, using",
            "a secret generated in the server.",
            "Upon success, it becomes possible to open the ID and retrieve genesis",
            "state associated with the microchain.",
            "Starting a microchain attempts to set the REPL microchain with the",
            "corresponding info.",
        ],
        format: "!(microchain-start <addr_expr> <state_expr>)",
        example: &[
            "!(defq id !(microchain-start \"127.0.0.1:1234\" state0))",
            "!(assert-eq state0 (open id))",
        ],
        returns: "The microchain's ID",
        run: |repl, args, _dir| {
            let [&addr_expr, &state_expr] = repl.take(args)?;
            let (addr, _) = repl.reduce_aux(&addr_expr)?;
            if addr.tag != Tag::Str {
                bail!("Address must be a string");
            }
            let (state, _) = repl.reduce_aux(&state_expr)?;
            if state.tag != Tag::Cons {
                bail!("State must be a pair");
            }

            repl.memoize_dag(&state);

            let (&chain_result, &next_callable) = repl.zstore.fetch_tuple11(&state);
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
            let stream = &mut TcpStream::connect(&addr_str)?;
            write_data(stream, Request::Start(genesis))?;
            let Response::IdSecret(id_secret) = read_data(stream)? else {
                bail!("Could not read ID secret from server");
            };

            let id = Self::compute_microchain_id(repl, id_secret, state)?;

            // Failing to set the microchain should not bail.
            let _ = Self::set_microchain(repl, addr_str, id.digest);

            Ok(id)
        },
    };

    /// Sends a generic "get state" request to the REPL microchain.
    fn send_get_state_request(
        repl: &mut Repl<F, C1, C2>,
        mk_request: fn([F; DIGEST_SIZE]) -> Request,
    ) -> Result<TcpStream> {
        let Some((addr, id)) = &repl.microchain else {
            bail!("No microchain info set");
        };
        let mut stream = TcpStream::connect(addr)?;
        write_data(&mut stream, mk_request(*id))?;
        Ok(stream)
    }

    const MICROCHAIN_GET_GENESIS: Self = Self {
        name: "microchain-get-genesis",
        summary: "Returns the genesis state of the REPL microchain",
        info: &[
            "Similarly to `microchain-start`, the preimage of the ID becomes",
            "available so opening the ID returns the genesis state.",
        ],
        format: "!(microchain-get-genesis)",
        example: &["!(defq state0 !(microchain-get-genesis))"],
        returns: "The microchain's genesis state",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                bail!("Arguments aren't supported");
            }
            let mut stream = Self::send_get_state_request(repl, Request::GetGenesis)?;
            let Response::Genesis(id_secret, chain_state) = read_data(&mut stream)? else {
                bail!("Could not read state from server");
            };
            let state = chain_state.into_zptr(&mut repl.zstore);

            // Memoize preimg so it's possible to open the ID.
            Self::compute_microchain_id(repl, id_secret, state)?;

            Ok(state)
        },
    };

    const MICROCHAIN_GET_STATE: Self = Self {
        name: "microchain-get-state",
        summary: "Returns the current state of the REPL microchain",
        info: &[],
        format: "!(microchain-get-state)",
        example: &["!(microchain-get-state)"],
        returns: "The microchain's latest state",
        run: |repl, args, _dir| {
            if args != repl.zstore.nil() {
                bail!("Arguments aren't supported");
            }
            let mut stream = Self::send_get_state_request(repl, Request::GetState)?;
            let Response::State(chain_state) = read_data(&mut stream)? else {
                bail!("Could not read state from server");
            };
            let state = chain_state.into_zptr(&mut repl.zstore);
            Ok(state)
        },
    };

    const MICROCHAIN_TRANSITION: Self = Self {
        name: "microchain-transition",
        summary:
            "Proves a state transition via chaining and sends the proof to a microchain server",
        info: &["The transition is successful iff the proof is accepted by the server."],
        format: "!(microchain-transition <state_expr> <arg1_expr> ...)",
        example: &["!(microchain-transition state arg0 arg1)"],
        returns: "The new state",
        run: |repl, args, _dir| {
            let Some((addr, id)) = repl.microchain.clone() else {
                bail!("No microchain info set");
            };
            let (&current_state_expr, &call_args) = repl.car_cdr(args);
            let (state, call_args) = Self::transition_call(repl, &current_state_expr, call_args)?;
            if state.tag != Tag::Cons {
                bail!("New state is not a pair");
            }
            let (&state_chain_result, &state_callable) = repl.zstore.fetch_tuple11(&state);

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

            let proof = ChainProof {
                crypto_proof,
                call_args,
                next_chain_result,
                next_callable,
            };
            let stream = &mut TcpStream::connect(addr)?;
            write_data(stream, Request::Transition { id, proof })?;
            match read_data::<Response>(stream)? {
                Response::ProofAccepted => {
                    println!("Proof accepted by the server");
                    Ok(state)
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
        },
    };

    const MICROCHAIN_VERIFY: Self = Self {
        name: "microchain-verify",
        summary: "Checks if a series of microchain transition proofs takes state A to B",
        info: &["The state arguments are meant to be the genesis and the current state."],
        format: "!(microchain-verify <state_a_expr> <state_b_expr>)",
        example: &["!(microchain-verify genesis current)"],
        returns: "t",
        run: |repl, args, _dir| {
            let Some((addr, id)) = repl.microchain.clone() else {
                bail!("No microchain info set");
            };
            let [&initial_state_expr, &final_state_expr] = repl.take(args)?;
            let (initial_state, _) = repl.reduce_aux(&initial_state_expr)?;
            if initial_state.tag != Tag::Cons {
                bail!("Initial state must be a pair");
            }
            let (final_state, _) = repl.reduce_aux(&final_state_expr)?;
            if final_state.tag != Tag::Cons {
                bail!("Final state must be a pair");
            }
            let stream = &mut TcpStream::connect(addr)?;
            write_data(
                stream,
                Request::GetProofs {
                    id,
                    initial_state_digest: initial_state.digest,
                    final_state_digest: final_state.digest,
                },
            )?;
            let Response::Proofs(proofs) = read_data(stream)? else {
                bail!("Could not read proofs from server");
            };
            repl.memoize_dag(&initial_state);
            let (_, &(mut callable)) = repl.zstore.fetch_tuple11(&initial_state);
            let mut state = initial_state;
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
            if state != final_state {
                bail!("Chain final state doesn't match target final state");
            }
            println!("Microchain verification succeeded");
            Ok(*repl.zstore.t())
        },
    };

    const LOAD_OCAML: Self = Self {
        name: "load-ocaml",
        summary: "(Experimental) Load OCaml expressions from a file, and runs the resulting Lurk program, printing the result.",
        info: &[],
        format: "!(load-ocaml <string>)",
        example: &[
            "!(load-ocaml \"my_file.ml\") !(prove)",
        ],
        returns: "t",
        run: |repl, args, path| {
            let [file_name_zptr] = repl.take(args)?;
            if file_name_zptr.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let file_name = repl.zstore.fetch_string(file_name_zptr);

            let zptr = compile_and_transform_single_file(&mut repl.zstore, &repl.state, &path.join(file_name))?;

            let result = repl.handle_non_meta(&zptr)?;
            if result.tag == Tag::Err {
                // error out when loading a file
                bail!("Reduction error: {}", repl.fmt(&result));
            }

            Ok(*repl.zstore.t())
        },
    };

    const LOAD_OCAML_EXPR: Self = Self {
        name: "load-ocaml-expr",
        summary: "(Experimental) Load OCaml expressions from a file.",
        info: &[],
        format: "!(load-ocaml-expr <string>)",
        example: &[
            "!(load-ocaml-expr \"my_file.ml\")",
            "!(defq ocaml-program !(load-ocaml-expr \"my_file.ml\")) (eval ocaml-program)",
            "(eval (quote !(load-ocaml-expr \"my_file.ml\")))",
            "!(prove !(load-ocaml-expr \"my_file.ml\"))",
        ],
        returns: "The Lurk program corresponding to the OCaml expressions in the file",
        run: |repl, args, path| {
            let [file_name_zptr] = repl.take(args)?;
            if file_name_zptr.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let file_name = repl.zstore.fetch_string(file_name_zptr);
            let zptr = compile_and_transform_single_file(
                &mut repl.zstore,
                &repl.state,
                &path.join(file_name),
            )?;
            Ok(zptr)
        },
    };
}

fn copy_inner<'a, T: Copy + 'a, I: IntoIterator<Item = &'a T>>(xs: I) -> Vec<T> {
    xs.into_iter().copied().collect()
}

#[inline]
pub(crate) fn meta_cmds<C1: Chipset<F>, C2: Chipset<F>>() -> MetaCmdsMap<F, C1, C2> {
    let mut meta_cmds = MetaCmdsMap::default();
    for mc in [
        MetaCmd::ASSERT,
        MetaCmd::ASSERT_EQ,
        MetaCmd::ASSERT_ERROR,
        MetaCmd::ASSERT_EMITTED,
        MetaCmd::DEBUG,
        MetaCmd::LOAD,
        MetaCmd::DEFQ,
        MetaCmd::DEF,
        MetaCmd::DEFREC,
        MetaCmd::UPDATE,
        MetaCmd::CLEAR,
        MetaCmd::SET_ENV,
        MetaCmd::ERASE_FROM_ENV,
        MetaCmd::HIDE,
        MetaCmd::RAND,
        MetaCmd::COMMIT,
        MetaCmd::OPEN,
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
        MetaCmd::SCOPE,
        MetaCmd::SCOPE_POP,
        MetaCmd::SCOPE_STORE,
        MetaCmd::MICROCHAIN_SET_INFO,
        MetaCmd::MICROCHAIN_GET_INFO,
        MetaCmd::MICROCHAIN_START,
        MetaCmd::MICROCHAIN_GET_GENESIS,
        MetaCmd::MICROCHAIN_GET_STATE,
        MetaCmd::MICROCHAIN_TRANSITION,
        MetaCmd::MICROCHAIN_VERIFY,
        MetaCmd::LOAD_OCAML,
        MetaCmd::LOAD_OCAML_EXPR,
        MetaCmd::HELP,
    ] {
        assert!(meta_cmds.insert(meta_sym(mc.name), mc).is_none());
    }
    assert_eq!(meta_cmds.len(), META_SYMBOLS.len());
    meta_cmds
}

#[cfg(test)]
mod test {
    use camino::{Utf8Path, Utf8PathBuf};
    use once_cell::sync::OnceCell;

    use crate::core::state::user_sym;

    use super::{MetaCmd, Repl};

    static DUMMY_PATH: OnceCell<Utf8PathBuf> = OnceCell::new();
    fn dummy_path() -> &'static Utf8Path {
        DUMMY_PATH.get_or_init(Utf8PathBuf::default)
    }

    #[test]
    fn test_def() {
        let mut repl = Repl::new_native();
        let foo = repl.zstore.intern_symbol_no_lang(&user_sym("foo"));
        let a = repl.zstore.intern_symbol_no_lang(&user_sym("a"));
        let args = repl.zstore.intern_list([foo, a]);
        assert!((MetaCmd::DEF.run)(&mut repl, &args, dummy_path()).is_err());

        let a = repl.zstore.intern_char('a');
        let args = repl.zstore.intern_list([foo, a]);
        assert_eq!(
            (MetaCmd::DEF.run)(&mut repl, &args, dummy_path()).unwrap(),
            foo
        );
    }
}
