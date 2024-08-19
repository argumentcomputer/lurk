use anyhow::{bail, Result};
use camino::{Utf8Path, Utf8PathBuf};
use nom::sequence::delimited;
use nom::Parser;
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeField32};
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{ValidationContext, ValidationResult, Validator},
    Completer, Editor, Helper, Highlighter, Hinter,
};
use sphinx_core::{
    stark::{LocalProver, StarkGenericConfig, StarkMachine},
    utils::{BabyBearPoseidon2, SphinxCoreOpts},
};
use std::io::Write;
use std::{fmt::Debug, marker::PhantomData};

use crate::{
    lair::{
        chipset::Chipset,
        execute::{QueryRecord, Shard},
        func_chip::FuncChip,
        lair_chip::{build_chip_vector, LairChip, LairMachineProgram},
        toplevel::Toplevel,
    },
    lurk::{
        chipset::LurkChip,
        cli::{
            meta::{meta_cmds, MetaCmdsMap},
            paths::{current_dir, repl_history},
        },
        eval::build_lurk_toplevel,
        parser::{
            syntax::{parse_maybe_meta, parse_space},
            Error, Span,
        },
        state::{State, StateRcCell},
        syntax::digest_to_biguint,
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE},
    },
};

use super::{
    paths::proofs_dir,
    proofs::{CryptoProof, IOProof},
};

const INPUT_SIZE: usize = 24;
const OUTPUT_SIZE: usize = 16;
const NUM_PUBLIC_VALUES: usize = INPUT_SIZE + OUTPUT_SIZE;

#[derive(Helper, Highlighter, Hinter, Completer)]
struct InputValidator<F: Field + Debug> {
    state: StateRcCell,
    _marker: PhantomData<F>,
}

impl<F: Field + Debug> InputValidator<F> {
    fn try_parse(&self, input: &str) -> Result<(), Error> {
        match delimited(
            parse_space::<F>,
            parse_maybe_meta(self.state.clone(), false),
            parse_space,
        )
        .parse(Span::new(input))
        {
            Err(e) => Err(Error::Syntax(format!("{}", e))),
            Ok((_, None)) => Ok(()),
            Ok((rest, Some(_))) => {
                if rest.is_empty() {
                    Ok(())
                } else {
                    Err(Error::Syntax(format!("Leftover input: {}", rest)))
                }
            }
        }
    }
}

impl<F: Field + Debug> Validator for InputValidator<F> {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        let parse_result = self.try_parse(input);
        let result = match parse_result {
            Ok(_) => ValidationResult::Valid(None),
            Err(_) => ValidationResult::Invalid(None),
        };
        if input.ends_with("\n\n") {
            // user has pressed enter a lot of times, there is probably a syntax error and we should just send it to the repl
            Ok(ValidationResult::Valid(None))
        } else {
            Ok(result)
        }
    }
}

pub(crate) struct Repl<F: PrimeField32, H: Chipset<F>> {
    pub(crate) zstore: ZStore<F, H>,
    pub(crate) queries: QueryRecord<F>,
    pub(crate) toplevel: Toplevel<F, H>,
    pub(crate) lurk_main_idx: usize,
    eval_idx: usize,
    egress_idx: usize,
    pub(crate) env: ZPtr<F>,
    pub(crate) state: StateRcCell,
    pwd_path: Utf8PathBuf,
    pub(crate) meta_cmds: MetaCmdsMap<F, H>,
    pub(crate) nil: ZPtr<F>,
}

impl Repl<BabyBear, LurkChip> {
    pub(crate) fn new() -> Self {
        let (toplevel, mut zstore) = build_lurk_toplevel();
        let queries = QueryRecord::new(&toplevel);
        let lurk_main_idx = toplevel.get_by_name("lurk_main").index;
        let eval_idx = toplevel.get_by_name("eval").index;
        let egress_idx = toplevel.get_by_name("egress").index;
        let env = zstore.intern_empty_env();
        let nil = zstore.intern_nil();
        Self {
            zstore,
            queries,
            toplevel,
            lurk_main_idx,
            eval_idx,
            egress_idx,
            env,
            state: State::init_lurk_state().rccell(),
            pwd_path: current_dir().expect("Couldn't get current directory"),
            meta_cmds: meta_cmds(),
            nil,
        }
    }
}

impl<H: Chipset<BabyBear>> Repl<BabyBear, H> {
    pub(crate) fn stark_machine(
        &self,
    ) -> StarkMachine<BabyBearPoseidon2, LairChip<'_, BabyBear, H>> {
        let lurk_main_chip = FuncChip::from_index(self.lurk_main_idx, &self.toplevel);
        StarkMachine::new(
            BabyBearPoseidon2::new(),
            build_chip_vector(&lurk_main_chip),
            NUM_PUBLIC_VALUES,
        )
    }

    pub(crate) fn prove_last_reduction(&mut self) -> Result<String> {
        // make env DAG available so `IOProof` can carry it
        self.memoize_env_dag();
        let Some(public_values) = self.queries.public_values.as_ref() else {
            bail!("No data found for latest computation");
        };
        let proof_key_img: &[BabyBear; DIGEST_SIZE] = &self
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
            let machine = self.stark_machine();
            let (pk, vk) = machine.setup(&LairMachineProgram);
            let challenger_p = &mut machine.config().challenger();
            let challenger_v = &mut challenger_p.clone();
            let shard = Shard::new(&self.queries);
            let opts = SphinxCoreOpts::default();
            let machine_proof = machine.prove::<LocalProver<_, _>>(&pk, shard, challenger_p, opts);
            machine
                .verify(&vk, &machine_proof, challenger_v)
                .expect("Proof verification failed");
            let crypto_proof: CryptoProof = machine_proof.into();
            let io_proof = IOProof::new(crypto_proof, public_values, &self.zstore);
            let io_proof_bytes = bincode::serialize(&io_proof)?;
            std::fs::write(proof_path, io_proof_bytes)?;
        }
        Ok(proof_key)
    }
}

fn pretty_iterations_display(iterations: usize) -> String {
    if iterations != 1 {
        format!("{iterations} iterations")
    } else {
        "1 iteration".into()
    }
}

impl<F: PrimeField32, H: Chipset<F>> Repl<F, H> {
    pub(crate) fn peek1(&self, args: &ZPtr<F>) -> Result<&ZPtr<F>> {
        if args.tag != Tag::Cons {
            bail!("Missing first argument")
        }
        let (arg, rst) = self.zstore.fetch_tuple2(args);
        if rst.tag != Tag::Nil {
            bail!("Only one argument is supported")
        }
        Ok(arg)
    }

    pub(crate) fn peek2(&self, args: &ZPtr<F>) -> Result<(&ZPtr<F>, &ZPtr<F>)> {
        if args.tag != Tag::Cons {
            bail!("Missing first argument")
        }
        let (arg1, rst) = self.zstore.fetch_tuple2(args);
        if rst.tag != Tag::Cons {
            bail!("Missing second argument")
        }
        let (arg2, rst) = self.zstore.fetch_tuple2(rst);
        if rst.tag != Tag::Nil {
            bail!("Only two arguments are supported")
        }
        Ok((arg1, arg2))
    }

    pub(crate) fn car_cdr(&self, zptr: &ZPtr<F>) -> (&ZPtr<F>, &ZPtr<F>) {
        match zptr.tag {
            Tag::Cons => self.zstore.fetch_tuple2(zptr),
            Tag::Nil => (&self.nil, &self.nil),
            _ => panic!("Invalid ZPtr"),
        }
    }

    fn input_marker(&self) -> String {
        let state = self.state.borrow();
        format!(
            "{}> ",
            state.fmt_to_string(state.get_current_package_name())
        )
    }

    #[inline]
    pub(crate) fn fmt(&self, zptr: &ZPtr<F>) -> String {
        self.zstore.fmt_with_state(&self.state, zptr)
    }

    fn prepare_queries(&mut self) {
        self.queries.clean();
        self.queries
            .inject_inv_queries("hash_24_8", &self.toplevel, &self.zstore.hashes3);
        self.queries
            .inject_inv_queries("hash_32_8", &self.toplevel, &self.zstore.hashes4);
        self.queries
            .inject_inv_queries("hash_48_8", &self.toplevel, &self.zstore.hashes6);
    }

    fn build_input(&self, expr: &ZPtr<F>, env: &ZPtr<F>) -> [F; INPUT_SIZE] {
        let mut input = [F::zero(); INPUT_SIZE];
        input[..16].copy_from_slice(&expr.flatten());
        input[16..].copy_from_slice(&env.digest);
        input
    }

    pub(crate) fn memoize_dag(&mut self, tag: Tag, digest: &[F]) {
        self.zstore.memoize_dag(
            tag,
            digest,
            self.queries.get_inv_queries("hash_24_8", &self.toplevel),
            self.queries.get_inv_queries("hash_32_8", &self.toplevel),
            self.queries.get_inv_queries("hash_48_8", &self.toplevel),
        )
    }

    #[inline]
    pub(crate) fn memoize_env_dag(&mut self) {
        self.memoize_dag(Tag::Env, &self.env.digest.clone())
    }

    fn retrieve_emitted(&self, queries_tmp: &mut QueryRecord<F>) -> Vec<ZPtr<F>> {
        let mut emitted = Vec::with_capacity(queries_tmp.emitted.len());
        for emitted_raw in queries_tmp.emitted.clone() {
            let digest = self
                .toplevel
                .execute_by_index(self.egress_idx, &emitted_raw, queries_tmp);
            emitted.push(ZPtr::from_flat_digest(
                Tag::from_field(&emitted_raw[0]),
                &digest,
            ));
        }
        emitted
    }

    /// Reduces a Lurk expression with a clone of the REPL's queries so the latest
    /// provable computation isn't affected. After the reduction is over, retrieve
    /// the (potentially enriched) inverse query maps so commitments aren't lost.
    pub(crate) fn reduce_aux_with_env(
        &mut self,
        expr: &ZPtr<F>,
        env: &ZPtr<F>,
    ) -> (ZPtr<F>, Vec<ZPtr<F>>) {
        self.prepare_queries();
        let mut queries_tmp = self.queries.clone();
        let result = ZPtr::from_flat_data(&self.toplevel.execute_by_index(
            self.lurk_main_idx,
            &self.build_input(expr, env),
            &mut queries_tmp,
        ));
        let emitted = self.retrieve_emitted(&mut queries_tmp);
        self.queries.inv_func_queries = queries_tmp.inv_func_queries;
        for zptr in &emitted {
            self.memoize_dag(zptr.tag, &zptr.digest);
            println!("{}", self.fmt(zptr));
        }
        (result, emitted)
    }

    #[inline]
    pub(crate) fn reduce_aux(&mut self, expr: &ZPtr<F>) -> (ZPtr<F>, Vec<ZPtr<F>>) {
        let env = self.env;
        self.reduce_aux_with_env(expr, &env)
    }

    /// Produces a minimal `QueryRecord` with just enough data to manually execute
    /// the `egress` chip and to register inverse queries that might be needed for
    /// later DAG memoization
    fn tmp_queries_for_emitted_retrieval(&self) -> QueryRecord<F> {
        let mut inv_func_queries = Vec::with_capacity(self.queries.inv_func_queries.len());
        for inv_query_map in &self.queries.inv_func_queries {
            if inv_query_map.is_some() {
                inv_func_queries.push(Some(Default::default()));
            } else {
                inv_func_queries.push(None);
            }
        }
        QueryRecord {
            public_values: None,
            func_queries: vec![Default::default(); self.queries.func_queries.len()],
            inv_func_queries,
            mem_queries: self.queries.mem_queries.clone(),
            bytes: Default::default(),
            emitted: self.queries.emitted.clone(),
        }
    }

    /// Extends the inverse query maps with data from a `QueryRecord`
    fn retrieve_inv_query_data_from_tmp_queries(&mut self, queries_tmp: QueryRecord<F>) {
        for (func_idx, inv_queries_tmp) in queries_tmp.inv_func_queries.into_iter().enumerate() {
            if let Some(inv_queries) = &mut self.queries.inv_func_queries[func_idx] {
                inv_queries.extend(
                    inv_queries_tmp
                        .expect("Inv map corresponds to an invertible func and shouldn't be None"),
                );
            }
        }
    }

    pub(crate) fn reduce_with_env(&mut self, expr: &ZPtr<F>, env: &ZPtr<F>) -> ZPtr<F> {
        self.prepare_queries();
        let result = ZPtr::from_flat_data(&self.toplevel.execute_by_index(
            self.lurk_main_idx,
            &self.build_input(expr, env),
            &mut self.queries,
        ));
        if !self.queries.emitted.is_empty() {
            let mut queries_tmp = self.tmp_queries_for_emitted_retrieval();
            let emitted = self.retrieve_emitted(&mut queries_tmp);
            self.retrieve_inv_query_data_from_tmp_queries(queries_tmp);
            for zptr in &emitted {
                self.memoize_dag(zptr.tag, &zptr.digest);
                println!("{}", self.fmt(zptr));
            }
        }
        result
    }

    #[inline]
    pub(crate) fn reduce(&mut self, expr: &ZPtr<F>) -> ZPtr<F> {
        let env = self.env;
        self.reduce_with_env(expr, &env)
    }

    pub(crate) fn handle_non_meta(&mut self, expr: &ZPtr<F>) -> ZPtr<F> {
        let result = self.reduce(expr);
        self.memoize_dag(result.tag, &result.digest);
        let iterations = self.queries.func_queries[self.eval_idx].len();
        println!(
            "[{}] => {}",
            pretty_iterations_display(iterations),
            self.fmt(&result)
        );
        result
    }

    fn handle_meta(&mut self, expr: &ZPtr<F>, file_dir: &Utf8Path) -> Result<()> {
        if expr.tag != Tag::Cons {
            bail!("Meta command calls must be written as cons lists");
        }
        let (cmd_sym, &args) = self.zstore.fetch_tuple2(expr);
        if cmd_sym.tag != Tag::Sym {
            bail!("The meta command must be a symbol");
        }
        let (cmd_sym_head, _) = self.zstore.fetch_tuple2(cmd_sym);
        let cmd = self.zstore.fetch_string(cmd_sym_head);
        if let Some(meta_cmd) = self.meta_cmds.get(cmd.as_str()) {
            (meta_cmd.run)(self, &args, file_dir)
        } else {
            bail!("Invalid meta command: {cmd}")
        }
    }

    fn handle_form<'a>(
        &mut self,
        input: Span<'a>,
        file_dir: &Utf8Path,
        demo: bool,
    ) -> Result<Span<'a>> {
        let (syntax_start, mut new_input, is_meta, zptr) = self
            .zstore
            .read_maybe_meta_with_state(self.state.clone(), &input)?;
        if demo {
            // adjustment to print the exclamation mark in the right place
            let syntax_start = syntax_start - usize::from(is_meta);
            let potential_commentaries = &input[..syntax_start];
            let actual_syntax = &input[syntax_start..new_input.location_offset()];
            let input_marker = &self.input_marker();
            if actual_syntax.contains('\n') {
                // print the expression on a new line to avoid messing with the user's formatting
                print!("{potential_commentaries}{input_marker}\n{actual_syntax}");
            } else {
                print!("{potential_commentaries}{input_marker}{actual_syntax}");
            }
            std::io::stdout().flush()?;
            // wait for ENTER to be pressed
            std::io::stdin().read_line(&mut String::new())?;
            // ENTER already prints a new line so we can remove it from the start of incoming input
            new_input = new_input.trim_start_matches('\n').into();
        }
        if is_meta {
            self.handle_meta(&zptr, file_dir)?;
        } else {
            let result = self.handle_non_meta(&zptr);
            if result.tag == Tag::Err {
                // error out when loading a file
                bail!("Reduction error");
            }
        }
        Ok(new_input)
    }

    pub(crate) fn load_file(&mut self, file_path: &Utf8Path, demo: bool) -> Result<()> {
        let input = std::fs::read_to_string(file_path)?;
        let Some(file_dir) = file_path.parent() else {
            bail!("Can't get the parent of {file_path}");
        };
        if demo {
            println!("Loading {file_path} in demo mode");
        } else {
            println!("Loading {file_path}");
        }
        let mut input = Span::new(&input);
        loop {
            match self.handle_form(input, file_dir, demo) {
                Ok(new_input) => input = new_input,
                Err(e) => {
                    if let Some(Error::NoInput) = e.downcast_ref::<Error>() {
                        // It's ok, it just means we've hit the EOF
                        return Ok(());
                    }
                    return Err(e);
                }
            }
        }
    }

    pub(crate) fn run(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let mut editor: Editor<InputValidator<F>, DefaultHistory> = Editor::new()?;

        editor.set_helper(Some(InputValidator::<F> {
            state: self.state.clone(),
            _marker: Default::default(),
        }));

        let repl_history = &repl_history()?;
        if repl_history.exists() {
            editor.load_history(repl_history)?;
        }

        loop {
            match editor.readline(&self.input_marker()) {
                Ok(line) => {
                    if line.trim_end().is_empty() {
                        continue;
                    }
                    editor.add_history_entry(&line)?;
                    match self
                        .zstore
                        .read_maybe_meta_with_state(self.state.clone(), &line)
                    {
                        Ok((.., is_meta, zptr)) => {
                            if is_meta {
                                if let Err(e) = self.handle_meta(&zptr, &self.pwd_path.clone()) {
                                    eprintln!("!Error: {e}");
                                }
                            } else {
                                self.handle_non_meta(&zptr);
                            }
                        }
                        Err(Error::NoInput) => {
                            // It's ok, the line is only a single comment
                        }
                        Err(e) => {
                            eprintln!("Read error: {e}");
                        }
                    }
                }
                Err(ReadlineError::Interrupted | ReadlineError::Eof) => {
                    println!("Exiting...");
                    break;
                }
                Err(e) => {
                    eprintln!("Read line error: {e}");
                    break;
                }
            }
        }
        editor.save_history(repl_history)?;

        Ok(())
    }
}
