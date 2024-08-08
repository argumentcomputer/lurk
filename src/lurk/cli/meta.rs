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

use super::comm_data::CommData;

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

    fn hide(secret: ZPtr<F>, payload_expr: &ZPtr<F>, repl: &mut Repl<F, H>) -> Result<()> {
        let payload = repl.reduce_aux(payload_expr);
        if payload.tag == Tag::Err {
            bail!("Payload reduction error: {}", repl.fmt(&payload));
        }
        repl.memoize_dag(secret.tag, &secret.digest);
        repl.memoize_dag(payload.tag, &payload.digest);
        let comm_data = CommData::new(secret, payload, &repl.zstore);
        let comm = comm_data.commit(&mut repl.zstore);
        let hash = format!("{:x}", digest_to_biguint(&comm.digest));
        std::fs::write(commits_dir()?.join(&hash), bincode::serialize(&comm_data)?)?;
        println!("Hash: {}", repl.fmt(&comm));
        Ok(())
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

    fn open(repl: &mut Repl<F, H>, args: &ZPtr<F>, print_payload: bool) -> Result<()> {
        let comm = *repl.peek1(args)?;
        if comm.tag != Tag::Comm {
            bail!("Expected a commitment");
        }
        let hash = format!("{:x}", digest_to_biguint(&comm.digest));
        let comm_data_bytes = std::fs::read(commits_dir()?.join(&hash))?;
        let comm_data: CommData<F> = bincode::deserialize(&comm_data_bytes)?;
        let message = if print_payload {
            repl.fmt(&comm_data.payload)
        } else {
            "Data is now available".to_string()
        };
        comm_data.fetch(&mut repl.zstore);
        println!("{message}");
        Ok(())
    }

    const OPEN: Self = Self {
        name: "open",
        summary: "Fetches a persisted commitment and prints the payload.",
        format: "!(open <comm>)",
        description: &[],
        example: &["!(open #0x3719f5d02845123a80da4f5077c803ba0ce1964e08289a9d020603c1f3c450)"],
        run: |repl, args, _path| Self::open(repl, args, true),
    };

    const FETCH: Self = Self {
        name: "fetch",
        summary: "Fetches a persisted commitment.",
        format: "!(fetch <comm>)",
        description: &[],
        example: &["!(fetch #0x3719f5d02845123a80da4f5077c803ba0ce1964e08289a9d020603c1f3c450)"],
        run: |repl, args, _path| Self::open(repl, args, false),
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
        MetaCmd::LOAD,
        MetaCmd::DEF,
        MetaCmd::DEFREC,
        MetaCmd::CLEAR,
        MetaCmd::HIDE,
        MetaCmd::COMMIT,
        MetaCmd::OPEN,
        MetaCmd::FETCH,
        MetaCmd::PROVE,
        MetaCmd::VERIFY,
        MetaCmd::INSPECT,
    ]
    .map(|mc| (mc.name, mc))
    .into_iter()
    .collect()
}
