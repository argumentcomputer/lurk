use anyhow::{bail, Result};
use camino::Utf8Path;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
use rustc_hash::FxHashMap;
use sphinx_core::{
    stark::{LocalProver, StarkGenericConfig, StarkMachine},
    utils::{BabyBearPoseidon2, SphinxCoreOpts},
};

use crate::{
    lair::{
        chipset::Chipset,
        execute::Shard,
        func_chip::FuncChip,
        lair_chip::{build_chip_vector, LairChip, LairMachineProgram},
    },
    lurk::{
        cli::{
            io_proof::IOProof,
            paths::{commits_dir, proofs_dir},
            repl::Repl,
        },
        state::lurk_sym,
        syntax::digest_to_biguint,
        tag::Tag,
        zstore::{ZPtr, DIGEST_SIZE},
    },
};

use super::{comm_data::CommData, lurk_data::LurkData};

const INPUT_SIZE: usize = 24;
const OUTPUT_SIZE: usize = 16;
const NUM_PUBLIC_VALUES: usize = INPUT_SIZE + OUTPUT_SIZE;

#[allow(dead_code)]
#[allow(clippy::type_complexity)]
pub(crate) struct MetaCmd<F: PrimeField32, H: Chipset<F>> {
    name: &'static str,
    summary: &'static str,
    format: &'static str,
    description: &'static [&'static str],
    example: &'static [&'static str],
    pub(crate) run: fn(repl: &mut Repl<F, H>, args: &ZPtr<F>, file_path: &Utf8Path) -> Result<()>,
}

pub(crate) type MetaCmdsMap<F, H> = FxHashMap<&'static str, MetaCmd<F, H>>;

impl<F: PrimeField32, H: Chipset<F>> MetaCmd<F, H> {
    const ASSERT: Self = Self {
        name: "assert",
        summary: "Asserts that an expression doesn't reduce to nil.",
        format: "!(assert <expr>)",
        description: &[],
        example: &["!(assert t)", "!(assert (eq 3 (+ 1 2)))"],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let result = repl.reduce_aux(&expr);
            if result.tag == Tag::Err {
                bail!("Reduction error: {}", repl.fmt(&result));
            }
            if result.tag == Tag::Nil {
                eprintln!("`assert` failed. {} evaluates to nil", repl.fmt(&expr));
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const ASSERT_EQ: Self = Self {
        name: "assert-eq",
        summary: "Assert that two expressions evaluate to the same value.",
        format: "!(assert-eq <expr1> <expr2>)",
        description: &[],
        example: &["!(assert-eq 3 (+ 1 2))"],
        run: |repl, args, _path| {
            let (&expr1, &expr2) = repl.peek2(args)?;
            let result1 = repl.reduce_aux(&expr1);
            if result1.tag == Tag::Err {
                bail!("LHS reduction error: {}", repl.fmt(&result1));
            }
            let result2 = repl.reduce_aux(&expr2);
            if result2.tag == Tag::Err {
                bail!("RHS reduction error: {}", repl.fmt(&result2));
            }
            if result1 != result2 {
                eprintln!(
                    "`assert-eq` failed. {} ≠ {}",
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
        description: &[],
        example: &["!(assert-error (1 1))"],
        run: |repl, args, _path| {
            let expr = *repl.peek1(args)?;
            let result = repl.reduce_aux(&expr);
            if result.tag != Tag::Err {
                eprintln!(
                    "`assert-error` failed. {} doesn't result on evaluation error.",
                    repl.fmt(&expr)
                );
                std::process::exit(1);
            }
            Ok(())
        },
    };

    const LOAD: Self = Self {
        name: "load",
        summary: "Load Lurk expressions from a file.",
        format: "!(load <string>)",
        description: &[],
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
        description: &[
            "Gets macroexpanded to (let ((<symbol> <value>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        example: &["!(def foo (lambda () 123))"],
        run: |repl, args, _path| {
            let (&sym, _) = repl.peek2(args)?;
            let let_ = repl.zstore.intern_symbol(&lurk_sym("let"));
            let bindings = repl.zstore.intern_list([*args]);
            let current_env = repl.zstore.intern_symbol(&lurk_sym("current-env"));
            let current_env_call = repl.zstore.intern_list([current_env]);
            let expr = repl.zstore.intern_list([let_, bindings, current_env_call]);
            let output = repl.reduce_aux(&expr);
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
        description: &[
            "Gets macroexpanded to (letrec ((<symbol> <value>)) (current-env)).",
            "The REPL's env is set to the result.",
        ],
        example: &[
            "!(defrec sum (lambda (l) (if (eq l nil) 0 (+ (car l) (sum (cdr l))))))",
            "(sum '(1 2 3))",
        ],
        run: |repl, args, _path| {
            let (&sym, _) = repl.peek2(args)?;
            let letrec = repl.zstore.intern_symbol(&lurk_sym("letrec"));
            let bindings = repl.zstore.intern_list([*args]);
            let current_env = repl.zstore.intern_symbol(&lurk_sym("current-env"));
            let current_env_call = repl.zstore.intern_list([current_env]);
            let expr = repl
                .zstore
                .intern_list([letrec, bindings, current_env_call]);
            let output = repl.reduce_aux(&expr);
            if output.tag != Tag::Env {
                bail!("Reduction resulted in {}", repl.fmt(&output));
            }
            repl.env = output;
            println!("{}", repl.fmt(&sym));
            Ok(())
        },
    };

    const CLEAR: Self = Self {
        name: "clear",
        summary: "Resets the current environment to be empty.",
        format: "!(clear)",
        description: &[],
        example: &["!(def a 1)", "(current-env)", "!(clear)", "(current-env)"],
        run: |repl, _args, _path| {
            repl.env = repl.zstore.intern_empty_env();
            Ok(())
        },
    };

    fn persist_comm_data(secret: ZPtr<F>, payload: ZPtr<F>, repl: &mut Repl<F, H>) -> Result<()> {
        repl.memoize_dag(secret.tag, &secret.digest);
        repl.memoize_dag(payload.tag, &payload.digest);
        let comm_data = CommData::new(secret, payload, &repl.zstore);
        let comm = comm_data.commit(&mut repl.zstore);
        let hash = format!("{:x}", digest_to_biguint(&comm.digest));
        std::fs::write(commits_dir()?.join(&hash), bincode::serialize(&comm_data)?)?;
        println!("Hash: {}", repl.fmt(&comm));
        Ok(())
    }

    fn hide(secret: ZPtr<F>, payload_expr: &ZPtr<F>, repl: &mut Repl<F, H>) -> Result<()> {
        let payload = repl.reduce_aux(payload_expr);
        if payload.tag == Tag::Err {
            bail!("Payload reduction error: {}", repl.fmt(&payload));
        }
        Self::persist_comm_data(secret, payload, repl)
    }

    const HIDE: Self = Self {
        name: "hide",
        summary: "Persists a hiding commitment.",
        format: "!(hide <secret_expr> <payload_expr>)",
        description: &[
            "The secret is the reduction of <secret_expr>, which must be a",
            "commitment, and the payload is the reduction of <payload_expr>.",
        ],
        example: &["!(hide (commit 123) 42)"],
        run: |repl, args, _path| {
            let (&secret_expr, &payload_expr) = repl.peek2(args)?;
            let secret = repl.reduce_aux(&secret_expr);
            if secret.tag != Tag::Comm {
                bail!("Secret must reduce to a commitment");
            }
            Self::hide(secret, &payload_expr, repl)
        },
    };

    const COMMIT: Self = Self {
        name: "commit",
        summary: "Persists a commitment.",
        format: "!(commit <payload_expr>)",
        description: &[
            "The secret is an opaque commitment whose digest amounts to zeros",
            "and the payload is the reduction of <payload_expr>.",
        ],
        example: &["!(commit 42)"],
        run: |repl, args, _path| {
            let payload_expr = *repl.peek1(args)?;
            let secret = ZPtr::null(Tag::Comm);
            Self::hide(secret, &payload_expr, repl)
        },
    };

    fn fetch_comm_data(
        repl: &mut Repl<F, H>,
        comm: &ZPtr<F>,
        print_payload: Option<bool>,
    ) -> Result<()> {
        let hash = format!("{:x}", digest_to_biguint(&comm.digest));
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
        description: &[],
        example: &[
            "!(commit 123)",
            "!(open #0x3719f5d02845123a80da4f5077c803ba0ce1964e08289a9d020603c1f3c450)",
        ],
        run: |repl, args, _path| {
            let comm = *repl.peek1(args)?;
            if comm.tag != Tag::Comm {
                bail!("Expected a commitment");
            }
            Self::fetch_comm_data(repl, &comm, Some(true))
        },
    };

    const FETCH: Self = Self {
        name: "fetch",
        summary: "Fetches a persisted commitment.",
        format: "!(fetch <comm>)",
        description: &[],
        example: &[
            "!(commit 123)",
            "!(fetch #0x3719f5d02845123a80da4f5077c803ba0ce1964e08289a9d020603c1f3c450)",
        ],
        run: |repl, args, _path| {
            let comm = *repl.peek1(args)?;
            if comm.tag != Tag::Comm {
                bail!("Expected a commitment");
            }
            Self::fetch_comm_data(repl, &comm, Some(false))
        },
    };

    fn call(repl: &mut Repl<F, H>, args: &ZPtr<F>) -> Result<()> {
        let (&comm, &arg) = repl.peek2(args)?;
        if comm.tag != Tag::Comm {
            bail!("Expected a commitment");
        }
        let inv_hashes3 = repl.queries.get_inv_queries("hash_24_8", &repl.toplevel);
        if !inv_hashes3.contains_key(comm.digest.as_slice()) {
            // try to fetch a persisted commitment
            Self::fetch_comm_data(repl, &comm, None)?;
        }
        let open = repl.zstore.intern_symbol(&lurk_sym("open"));
        let open_expr = repl.zstore.intern_list([open, comm]);
        let call_expr = repl.zstore.intern_list([open_expr, arg]);
        repl.handle_non_meta(&call_expr);
        Ok(())
    }

    const CALL: Self = Self {
        name: "call",
        summary: "Opens a functional commitment then applies an argument to it.",
        format: "!(call <comm> <arg>)",
        description: &["It's also capable of opening persisted commitments."],
        example: &[
            "(commit (lambda (x) x))",
            "!(call #0x3f2e7102a9f8a303255b90724f24f4eb05b61e99723ca838cf30671676c86a 0)",
        ],
        run: |repl, args, _path| Self::call(repl, args),
    };

    const CHAIN: Self = Self {
        name: "chain",
        summary: "Chains a functional commitment and then persists the resulting commitment",
        format: "!(chain <comm> <arg>)",
        description: &["It's also capable of opening persisted commitments."],
        example: &[
            "(commit (letrec ((add (lambda (counter x)
                       (let ((counter (+ counter x)))
                         (cons counter (commit (add counter)))))))
               (add 0)))",
            "!(chain #0x8ef25bc2228ca9799db65fd2b137a7b0ebccbfc04cf8530133e60087d403db 1)",
        ],
        run: |repl, args, _path| {
            Self::call(repl, args)?;
            let public_values = repl
                .queries
                .public_values
                .as_ref()
                .expect("Computation must have finished");
            let cons = ZPtr::from_flat_data(&public_values[INPUT_SIZE..]);
            if cons.tag != Tag::Cons {
                bail!("Chain result must be a pair");
            }
            let (_, comm) = repl.zstore.fetch_tuple2(&cons);
            if comm.tag != Tag::Comm {
                bail!("Expected a commitment as the second pair component");
            }
            let inv_hashes3 = repl.queries.get_inv_queries("hash_24_8", &repl.toplevel);
            let preimg = inv_hashes3
                .get(comm.digest.as_slice())
                .expect("Preimage must be known");
            let (secret, payload) = preimg.split_at(DIGEST_SIZE);
            let secret = ZPtr::from_flat_digest(Tag::Comm, secret);
            let payload = ZPtr::from_flat_data(payload);
            Self::persist_comm_data(secret, payload, repl)
        },
    };

    const DUMP_EXPR: Self = Self {
        name: "dump-expr",
        summary: "Evaluates an expression and dumps the result to the file system",
        format: "!(dump-expr <expr> <string>)",
        description: &["Commitments are persisted opaquely."],
        example: &["!(dump-expr (+ 1 1) \"my_file\")"],
        run: |repl, args, _path| {
            let (&expr, &path) = repl.peek2(args)?;
            if path.tag != Tag::Str {
                bail!("Path must be a string");
            }
            let result = repl.reduce_aux(&expr);
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
        description: &[],
        example: &[
            "!(dump-expr (+ 1 1) \"my_file\")",
            "!(load-expr x \"my_file\")",
        ],
        run: |repl, args, _path| {
            let (&sym, &path) = repl.peek2(args)?;
            if sym.tag != Tag::Sym {
                bail!("Binding variable must be a symbol");
            }
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
}

type F = BabyBear;

impl<H: Chipset<F>> MetaCmd<F, H> {
    fn stark_machine(repl: &Repl<F, H>) -> StarkMachine<BabyBearPoseidon2, LairChip<'_, F, H>> {
        let lurk_main_chip = FuncChip::from_index(repl.lurk_main_idx, &repl.toplevel);
        StarkMachine::new(
            BabyBearPoseidon2::new(),
            build_chip_vector(&lurk_main_chip),
            NUM_PUBLIC_VALUES,
        )
    }

    const PROVE: Self = Self {
        name: "prove",
        summary: "Proves a Lurk reduction",
        format: "!(prove <expr>?)",
        description: &["Prove a Lurk reduction, persists the proof and prints its key"],
        example: &["'(1 2 3)", "!(prove)", "!(prove '(1 2 3))"],
        run: |repl, args, _path| {
            if args.tag != Tag::Nil {
                let expr = *repl.peek1(args)?;
                repl.handle_non_meta(&expr);
            }
            // make env DAG available so `IOProof` can carry it
            repl.memoize_env_dag();
            let Some(public_values) = repl.queries.public_values.as_ref() else {
                bail!("No data found for latest computation");
            };
            let proof_key_img: &[F; DIGEST_SIZE] = &repl
                .zstore
                .hasher()
                .hash(&public_values[..INPUT_SIZE])
                .try_into()
                .unwrap();
            let proof_key = format!("{:x}", digest_to_biguint(proof_key_img));
            let proof_path = proofs_dir()?.join(&proof_key);
            let must_prove = if !proof_path.exists() {
                true
            } else {
                let io_proof_bytes = std::fs::read(&proof_path)?;
                // force an overwrite if deserialization goes wrong
                bincode::deserialize::<IOProof>(&io_proof_bytes).is_err()
            };
            if must_prove {
                let machine = Self::stark_machine(repl);
                let (pk, _) = machine.setup(&LairMachineProgram);
                let challenger = &mut machine.config().challenger();
                let shard = Shard::new(&repl.queries);
                let opts = SphinxCoreOpts::default();
                let sphinx_proof = machine.prove::<LocalProver<_, _>>(&pk, shard, challenger, opts);
                let io_proof = IOProof::new(sphinx_proof, public_values, &repl.zstore);
                let io_proof_bytes = bincode::serialize(&io_proof)?;
                std::fs::write(proof_path, io_proof_bytes)?;
            }
            println!("Proof key: \"{proof_key}\"");
            Ok(())
        },
    };

    fn load_io_proof(repl: &Repl<F, H>, args: &ZPtr<F>) -> Result<(String, IOProof)> {
        let proof_key_zptr = repl.peek1(args)?;
        if proof_key_zptr.tag != Tag::Str {
            bail!("Proof key must be a string");
        }
        let proof_key = repl.zstore.fetch_string(proof_key_zptr);
        let proof_path = proofs_dir()?.join(&proof_key);
        if !proof_path.exists() {
            bail!("Proof not found");
        }
        let io_proof_bytes = std::fs::read(proof_path)?;
        let io_proof: IOProof = bincode::deserialize(&io_proof_bytes)?;
        Ok((proof_key, io_proof))
    }

    const VERIFY: Self = Self {
        name: "verify",
        summary: "Verifies Lurk reduction proof",
        format: "!(verify <string>)",
        description: &["Verifies a Lurk reduction proof by its key"],
        example: &["!(verify \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        run: |repl, args, _path| {
            let (proof_key, io_proof) = Self::load_io_proof(repl, args)?;
            let machine = Self::stark_machine(repl);
            if io_proof.verify(&machine) {
                println!("✓ Proof \"{proof_key}\" verified");
            } else {
                println!("✗ Proof \"{proof_key}\" failed on verification");
            }
            Ok(())
        },
    };

    const INSPECT: Self = Self {
        name: "inspect",
        summary: "Prints a proof claim",
        format: "!(inspect <string>)",
        description: &[],
        example: &["!(inspect \"2ae20412c6f4740f409196522c15b0e42aae2338c2b5b9c524f675cba0a93e\")"],
        run: |repl, args, _path| {
            let IOProof {
                expr,
                env,
                result,
                zdag,
                ..
            } = Self::load_io_proof(repl, args)?.1;
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
}

#[inline]
pub(crate) fn meta_cmds<H: Chipset<F>>() -> MetaCmdsMap<F, H> {
    [
        MetaCmd::ASSERT,
        MetaCmd::ASSERT_EQ,
        MetaCmd::ASSERT_ERROR,
        MetaCmd::LOAD,
        MetaCmd::DEF,
        MetaCmd::DEFREC,
        MetaCmd::CLEAR,
        MetaCmd::HIDE,
        MetaCmd::COMMIT,
        MetaCmd::OPEN,
        MetaCmd::FETCH,
        MetaCmd::CALL,
        MetaCmd::CHAIN,
        MetaCmd::DUMP_EXPR,
        MetaCmd::LOAD_EXPR,
        MetaCmd::PROVE,
        MetaCmd::VERIFY,
        MetaCmd::INSPECT,
    ]
    .map(|mc| (mc.name, mc))
    .into_iter()
    .collect()
}
