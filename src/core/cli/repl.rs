use anyhow::{bail, Result};
use camino::Utf8Path;
use nom::sequence::delimited;
use nom::Parser;
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeField32};
use rustc_hash::{FxHashMap, FxHashSet};
use rustyline::{
    config::{Config, EditMode},
    error::ReadlineError,
    history::DefaultHistory,
    validate::{ValidationContext, ValidationResult, Validator},
    Completer, Editor, Helper, Highlighter, Hinter,
};
use sphinx_core::{
    stark::{LocalProver, StarkGenericConfig},
    utils::SphinxCoreOpts,
};
use std::{fmt::Debug, io::Write, marker::PhantomData};

use crate::{
    core::{
        big_num::field_elts_to_biguint,
        chipset::LurkChip,
        cli::{
            debug::{FormattedDebugData, FormattedDebugEntry},
            meta::{meta_cmds, MetaCmdsMap},
            paths::{current_dir, proofs_dir, repl_history},
            proofs::{CachedProof, CryptoProof},
        },
        eval_direct::build_lurk_toplevel,
        lang::Lang,
        parser::{
            syntax::{parse, parse_space, parse_syntax_eof},
            Error, Span,
        },
        stark_machine::{new_machine, INPUT_SIZE},
        state::{State, StateRcCell},
        symbol::Symbol,
        syntax::Syntax,
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE},
    },
    lair::{
        chipset::{Chipset, NoChip},
        execute::{DebugEntry, DebugEntryKind, QueryRecord, QueryResult, Shard},
        lair_chip::LairMachineProgram,
        toplevel::Toplevel,
    },
};

#[derive(Helper, Highlighter, Hinter, Completer)]
struct InputValidator<F: Field> {
    state: StateRcCell,
    _marker: PhantomData<F>,
}

impl<F: Field> InputValidator<F> {
    fn try_parse(&self, input: &str) -> Result<(), Error> {
        let mut input = Span::new(input);
        loop {
            match delimited(
                parse_space,
                parse_syntax_eof::<F>(self.state.clone(), false),
                parse_space,
            )
            .parse(input)
            {
                Err(e) => return Err(Error::Syntax(format!("{}", e))),
                Ok((_, None)) => return Ok(()),
                Ok((rest, Some(_))) => {
                    if rest.is_empty() {
                        return Ok(());
                    } else {
                        input = rest;
                    }
                }
            }
        }
    }
}

impl<F: Field + Debug> Validator for InputValidator<F> {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        if input.ends_with("\n\n") || self.try_parse(input).is_ok() {
            // user has pressed enter a lot of times so there is probably a syntax
            // error and we should just send it to the repl
            Ok(ValidationResult::Valid(None))
        } else {
            Ok(ValidationResult::Invalid(None))
        }
    }
}

enum ProcessedDebugEntryKind<F> {
    Push(ZPtr<F>),
    Pop(ZPtr<F>, ZPtr<F>),
    Memoized(ZPtr<F>, ZPtr<F>),
}

struct ProcessedDebugEntry<F> {
    dbg_depth: usize,
    kind: ProcessedDebugEntryKind<F>,
}

/// Holds the indices of some functions in the Lurk toplevel
struct FuncIndices {
    lurk_main: usize,
    eval: usize,
    egress: usize,
}

impl FuncIndices {
    fn new<F, C1: Chipset<F>, C2: Chipset<F>>(toplevel: &Toplevel<F, C1, C2>) -> Self {
        Self {
            lurk_main: toplevel.func_by_name("lurk_main").index,
            eval: toplevel.func_by_name("eval").index,
            egress: toplevel.func_by_name("egress").index,
        }
    }
}

pub(crate) struct Repl<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> {
    pub(crate) zstore: ZStore<F, C1>,
    pub(crate) queries: QueryRecord<F>,
    pub(crate) toplevel: Toplevel<F, C1, C2>,
    func_indices: FuncIndices,
    pub(crate) env: ZPtr<F>,
    pub(crate) state: StateRcCell,
    pub(crate) meta_cmds: MetaCmdsMap<F, C1, C2>,
    pub(crate) lang_symbols: FxHashSet<Symbol>,
}

impl<C2: Chipset<BabyBear>> Repl<BabyBear, LurkChip, C2> {
    pub(crate) fn new(lang: Lang<BabyBear, C2>) -> Self {
        let (toplevel, mut zstore, lang_symbols) = build_lurk_toplevel(lang);
        let func_indices = FuncIndices::new(&toplevel);
        let env = zstore.intern_empty_env();
        Self {
            zstore,
            queries: QueryRecord::new(&toplevel),
            toplevel,
            func_indices,
            env,
            state: State::init_lurk_state().rccell(),
            meta_cmds: meta_cmds(),
            lang_symbols,
        }
    }
}

impl Repl<BabyBear, LurkChip, NoChip> {
    /// Creates a REPL instance for the empty Lang with `C2 = NoChip`
    #[inline]
    pub(crate) fn new_native() -> Self {
        Self::new(Lang::empty())
    }
}

impl<C1: Chipset<BabyBear>, C2: Chipset<BabyBear>> Repl<BabyBear, C1, C2> {
    /// Generates a STARK proof for the latest Lurk reduction, persists it and
    /// returns the corresponding proof key
    pub(crate) fn prove_last_reduction(&mut self) -> Result<String> {
        // make env DAG available so `IOProof` can carry it
        self.memoize_env_dag();
        let Some(public_values) = self.queries.public_values.as_ref() else {
            bail!("No data found for latest computation");
        };
        let proof_key_img: &[BabyBear; DIGEST_SIZE] = &self
            .zstore
            .hash3(public_values[..INPUT_SIZE].try_into().unwrap());
        let proof_key = format!("{:x}", field_elts_to_biguint(proof_key_img));
        let proof_path = proofs_dir()?.join(&proof_key);
        let machine = new_machine(&self.toplevel);
        let (pk, vk) = machine.setup(&LairMachineProgram);
        let challenger_p = &mut machine.config().challenger();
        let must_prove = if !proof_path.exists() {
            true
        } else {
            let cached_proof_bytes = std::fs::read(&proof_path)?;
            if let Ok(cached_proof) = bincode::deserialize::<CachedProof>(&cached_proof_bytes) {
                let machine_proof = cached_proof.into_machine_proof();
                let challenger_v = &mut challenger_p.clone();
                // force an overwrite if verification goes wrong
                machine.verify(&vk, &machine_proof, challenger_v).is_err()
            } else {
                // force an overwrite if deserialization goes wrong
                true
            }
        };
        if must_prove {
            let challenger_v = &mut challenger_p.clone();
            let shard = Shard::new(&self.queries);
            let opts = SphinxCoreOpts::default();
            let machine_proof = machine.prove::<LocalProver<_, _>>(&pk, shard, challenger_p, opts);
            machine
                .verify(&vk, &machine_proof, challenger_v)
                .expect("Proof verification failed");
            let crypto_proof: CryptoProof = machine_proof.into();
            let cached_proof = CachedProof::new(crypto_proof, public_values, &self.zstore);
            let cached_proof_bytes = bincode::serialize(&cached_proof)?;
            std::fs::write(proof_path, cached_proof_bytes)?;
        }
        println!("Proof key: \"{proof_key}\"");
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

const VI_EDITORS: [&str; 3] = ["vi", "vim", "nvim"];

impl<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> Repl<F, C1, C2> {
    /// Deconstructs the arguments of a cons list expected to have a known number
    /// of elements. Errors if the list has a different length.
    pub(crate) fn take<'a, const N: usize>(
        &'a self,
        mut args: &'a ZPtr<F>,
    ) -> Result<[&'a ZPtr<F>; N]> {
        let mut res = Vec::with_capacity(N);
        for i in 0..N {
            if args.tag != Tag::Cons {
                bail!("Missing argument {}", i + 1);
            }
            let (arg, rst) = self.zstore.fetch_tuple11(args);
            res.push(arg);
            args = rst;
        }
        if args != self.zstore.nil() {
            bail!("Only {N} arguments are supported");
        }
        Ok(res.try_into().unwrap())
    }

    pub(crate) fn car_cdr(&self, zptr: &ZPtr<F>) -> (&ZPtr<F>, &ZPtr<F>) {
        if zptr.tag == Tag::Cons {
            self.zstore.fetch_tuple11(zptr)
        } else if zptr == self.zstore.nil() {
            (self.zstore.nil(), self.zstore.nil())
        } else {
            panic!("Invalid ZPtr")
        }
    }

    fn prompt_marker(&self) -> String {
        let state = self.state.borrow();
        let root_package = state
            .get_package(&Symbol::root_sym())
            .expect("Root package is missing");
        let package_name_formatted = root_package.fmt_to_string(state.get_current_package_name());
        format!("{package_name_formatted}> ")
    }

    #[inline]
    pub(crate) fn fmt(&self, zptr: &ZPtr<F>) -> String {
        self.zstore.fmt_with_state(&self.state, zptr)
    }

    fn prepare_queries(&mut self) {
        self.queries.clean();
        let hashes3 = std::mem::take(&mut self.zstore.hashes3_diff);
        let hashes4 = std::mem::take(&mut self.zstore.hashes4_diff);
        let hashes5 = std::mem::take(&mut self.zstore.hashes5_diff);
        self.queries
            .inject_inv_queries_owned("hash3", &self.toplevel, hashes3);
        self.queries
            .inject_inv_queries_owned("hash4", &self.toplevel, hashes4);
        self.queries
            .inject_inv_queries_owned("hash5", &self.toplevel, hashes5);
    }

    fn build_input(&self, expr: &ZPtr<F>, env: &ZPtr<F>) -> [F; INPUT_SIZE] {
        let mut input = [F::zero(); INPUT_SIZE];
        input[..16].copy_from_slice(&expr.flatten());
        input[16..].copy_from_slice(&env.digest);
        input
    }

    #[inline]
    pub(crate) fn memoize_dag(&mut self, zptr: &ZPtr<F>) {
        self.zstore.memoize_dag(
            zptr.tag,
            &zptr.digest,
            self.queries.get_inv_queries("hash4", &self.toplevel),
            self.queries.get_inv_queries("hash5", &self.toplevel),
        )
    }

    #[inline]
    pub(crate) fn memoize_env_dag(&mut self) {
        self.memoize_dag(&self.env.clone())
    }

    #[inline]
    pub(crate) fn bind(&mut self, sym: ZPtr<F>, val: ZPtr<F>) {
        self.memoize_env_dag();
        self.env = self.zstore.intern_env(sym, val, self.env);
    }

    /// Produces a minimal `QueryRecord` with just enough data to manually execute
    /// the `egress` chip and to register inverse queries that might be needed for
    /// later DAG memoization
    fn tmp_queries_for_egression(&self) -> QueryRecord<F> {
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
            emitted: Default::default(),
            debug_data: Default::default(),
            provable: false,
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

    fn manual_egression(&self, egress_input: &[F], queries_tmp: &mut QueryRecord<F>) -> ZPtr<F> {
        let egress_output = self
            .toplevel
            .execute_by_index(self.func_indices.egress, egress_input, queries_tmp, None)
            .expect("Egression failed");
        ZPtr::from_flat_digest(Tag::from_field(&egress_output[0]), &egress_output[1..])
    }

    pub(crate) fn format_debug_data(&mut self) -> FormattedDebugData<'_> {
        let mut dbg_depth_map: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        let mut processed_debug_entries = Vec::with_capacity(self.queries.debug_data.entries.len());
        let mut queries_tmp = self.tmp_queries_for_egression();
        for debug_data_entry in &self.queries.debug_data.entries {
            let DebugEntry {
                dbg_depth,
                query_idx,
                kind,
            } = debug_data_entry;
            if let Some(depth_indices) = dbg_depth_map.get_mut(dbg_depth) {
                depth_indices.push(processed_debug_entries.len());
            } else {
                dbg_depth_map.insert(*dbg_depth, vec![processed_debug_entries.len()]);
            }
            let (input, QueryResult { output, .. }) = &self.queries.func_queries
                [self.func_indices.eval]
                .get_index(*query_idx)
                .expect("Missing query");
            let input_zptr = self.manual_egression(&input[..2], &mut queries_tmp);
            match kind {
                DebugEntryKind::Push => {
                    processed_debug_entries.push(ProcessedDebugEntry {
                        dbg_depth: *dbg_depth,
                        kind: ProcessedDebugEntryKind::Push(input_zptr),
                    });
                }
                DebugEntryKind::Pop => {
                    let output = output.as_ref().expect("Missing query result");
                    let output_zptr = self.manual_egression(output, &mut queries_tmp);
                    processed_debug_entries.push(ProcessedDebugEntry {
                        dbg_depth: *dbg_depth,
                        kind: ProcessedDebugEntryKind::Pop(input_zptr, output_zptr),
                    });
                }
                DebugEntryKind::Memoized => {
                    let output = output.as_ref().expect("Missing query result");
                    let output_zptr = self.manual_egression(output, &mut queries_tmp);
                    processed_debug_entries.push(ProcessedDebugEntry {
                        dbg_depth: *dbg_depth,
                        kind: ProcessedDebugEntryKind::Memoized(input_zptr, output_zptr),
                    });
                }
            }
        }
        self.retrieve_inv_query_data_from_tmp_queries(queries_tmp);
        let mut formatted_debug_entries = Vec::with_capacity(processed_debug_entries.len());
        for processed_debug_entry in processed_debug_entries {
            let ProcessedDebugEntry { dbg_depth, kind } = processed_debug_entry;
            match &kind {
                ProcessedDebugEntryKind::Push(inp) => {
                    self.memoize_dag(inp);
                    formatted_debug_entries.push(FormattedDebugEntry {
                        dbg_depth,
                        formatted: format!("?{dbg_depth}: {}", self.fmt(inp)),
                    });
                }
                ProcessedDebugEntryKind::Pop(inp, out) => {
                    self.memoize_dag(inp);
                    self.memoize_dag(out);
                    formatted_debug_entries.push(FormattedDebugEntry {
                        dbg_depth,
                        formatted: format!(" {dbg_depth}: {} ↦ {}", self.fmt(inp), self.fmt(out)),
                    });
                }
                ProcessedDebugEntryKind::Memoized(inp, out) => {
                    self.memoize_dag(inp);
                    self.memoize_dag(out);
                    formatted_debug_entries.push(FormattedDebugEntry {
                        dbg_depth,
                        formatted: format!("!{dbg_depth}: {} ↦ {}", self.fmt(inp), self.fmt(out)),
                    });
                }
            }
        }
        FormattedDebugData {
            entries: formatted_debug_entries,
            dbg_depth_map,
            breakpoints: &self.queries.debug_data.breakpoints,
        }
    }

    /// Reduces a Lurk expression with a clone of the REPL's queries so the latest
    /// provable computation isn't affected. After the reduction is over, retrieve
    /// the (potentially enriched) inverse query maps so commitments aren't lost.
    pub(crate) fn reduce_aux_with_env(
        &mut self,
        expr: &ZPtr<F>,
        env: &ZPtr<F>,
    ) -> Result<(ZPtr<F>, Vec<ZPtr<F>>)> {
        self.prepare_queries();
        let mut queries_tmp = self.queries.clone();
        let result_data = self.toplevel.execute_by_index(
            self.func_indices.lurk_main,
            &self.build_input(expr, env),
            &mut queries_tmp,
            None,
        );
        let emitted_raw_vec = std::mem::take(&mut queries_tmp.emitted);
        let mut emitted = Vec::with_capacity(emitted_raw_vec.len());
        for emitted_raw in &emitted_raw_vec {
            emitted.push(self.manual_egression(emitted_raw, &mut queries_tmp));
        }
        self.queries.inv_func_queries = queries_tmp.inv_func_queries;
        for zptr in &emitted {
            self.memoize_dag(zptr);
            println!("{}", self.fmt(zptr));
        }
        result_data.map(|data| (ZPtr::from_flat_data(&data), emitted))
    }

    #[inline]
    pub(crate) fn reduce_aux(&mut self, expr: &ZPtr<F>) -> Result<(ZPtr<F>, Vec<ZPtr<F>>)> {
        let env = self.env;
        self.reduce_aux_with_env(expr, &env)
    }

    pub(crate) fn reduce_with_env(&mut self, expr: &ZPtr<F>, env: &ZPtr<F>) -> Result<ZPtr<F>> {
        self.prepare_queries();
        let result_data = self.toplevel.execute_by_index(
            self.func_indices.lurk_main,
            &self.build_input(expr, env),
            &mut self.queries,
            Some(self.func_indices.eval),
        );
        if !self.queries.emitted.is_empty() {
            let mut queries_tmp = self.tmp_queries_for_egression();
            let mut emitted = Vec::with_capacity(self.queries.emitted.len());
            for emitted_raw in &self.queries.emitted {
                emitted.push(self.manual_egression(emitted_raw, &mut queries_tmp));
            }
            self.retrieve_inv_query_data_from_tmp_queries(queries_tmp);
            for zptr in &emitted {
                self.memoize_dag(zptr);
                println!("{}", self.fmt(zptr));
            }
        }
        result_data.map(|data| ZPtr::from_flat_data(&data))
    }

    /// Evaluates an expression with a custom env and prints the number of
    /// iterations and the result. The computation is cached for proving.
    pub(crate) fn handle_non_meta_with_env(
        &mut self,
        expr: &ZPtr<F>,
        env: &ZPtr<F>,
    ) -> Result<ZPtr<F>> {
        let result = self.reduce_with_env(expr, env)?;
        self.memoize_dag(&result);
        let iterations = self.queries.func_queries[self.func_indices.eval].len();
        println!(
            "[{}] => {}",
            pretty_iterations_display(iterations),
            self.fmt(&result)
        );
        Ok(result)
    }

    pub(crate) fn handle_non_meta(&mut self, expr: &ZPtr<F>) -> Result<ZPtr<F>> {
        let env = self.env;
        self.handle_non_meta_with_env(expr, &env)
    }

    fn intern_syntax_slice(
        &mut self,
        slice: &[Syntax<F>],
        file_dir: &Utf8Path,
    ) -> Result<Vec<ZPtr<F>>> {
        slice
            .iter()
            .map(|x| self.intern_syntax(x, file_dir))
            .collect()
    }

    fn intern_syntax(&mut self, syn: &Syntax<F>, file_dir: &Utf8Path) -> Result<ZPtr<F>> {
        let zptr = match syn {
            Syntax::Meta(_, sym, args) => {
                let zptrs = self.intern_syntax_slice(args, file_dir)?;
                let args = self.zstore.intern_list(zptrs);
                if let Some(meta_cmd) = self.meta_cmds.get(sym) {
                    (meta_cmd.run)(self, &args, file_dir)?
                } else {
                    bail!("Invalid meta command: {sym}")
                }
            },
            Syntax::Num(_, f) => self.zstore.intern_num(*f),
            Syntax::Char(_, c) => self.zstore.intern_char(*c),
            Syntax::U64(_, u) => self.zstore.intern_u64(*u),
            Syntax::I64(..) => bail!("Transient error: Signed integers are not yet supported. Using `(- 0 x)` instead of `-x` might work as a temporary workaround."),
            Syntax::BigNum(_, c) => self.zstore.intern_big_num(*c),
            Syntax::Comm(_, c) => self.zstore.intern_comm(*c),
            Syntax::String(_, s) => self.zstore.intern_string(s),
            Syntax::Symbol(_, s) => self.zstore.intern_symbol(s, &self.lang_symbols),
            Syntax::List(_, xs) => {
                let zptrs = self.intern_syntax_slice(xs, file_dir)?;
                self.zstore.intern_list(zptrs)
            }
            Syntax::Improper(_, xs, y) => {
                let zptrs = self.intern_syntax_slice(xs, file_dir)?;
                let y = self.intern_syntax(y, file_dir)?;
                self.zstore.intern_list_full(zptrs, y)
            }
            Syntax::Quote(_, x) => {
                let x = self.intern_syntax(x, file_dir)?;
                self.zstore.intern_list([*self.zstore.quote(), x])
            }
        };
        Ok(zptr)
    }

    /// Parses textual input, resolves meta commands and returns:
    /// * `None` if there was no `Syntax` to parse
    /// * `Some(offset, rest, zptr, non_meta)` if a `Syntax` node was parsed, where
    ///     * `offset: usize` is the number of characters before the `Syntax`
    ///     * `rest: Span<'_>` is the textual input to be parsed next
    ///     * `zptr: ZPtr<F>` is the pointer to the interned Lurk expression
    ///     * `meta: bool` tells whether the parsed code was a meta command or not
    #[allow(clippy::type_complexity)]
    fn process<'a>(
        &mut self,
        input: Span<'a>,
        file_dir: &Utf8Path,
    ) -> Result<Option<(usize, Span<'a>, ZPtr<F>, bool)>> {
        let Some((rest, syn)) = parse(input, self.state.clone(), false)? else {
            return Ok(None);
        };
        let offset = syn
            .get_pos()
            .get_from_offset()
            .expect("Parsed syntax should have its Pos set");
        let meta = matches!(syn, Syntax::Meta(..));
        let zptr = self.intern_syntax(&syn, file_dir)?;
        Ok(Some((offset, rest, zptr, meta)))
    }

    fn handle_form<'a>(
        &mut self,
        input: Span<'a>,
        file_dir: &Utf8Path,
        demo: bool,
    ) -> Result<Option<Span<'a>>> {
        let Some((syntax_start, mut new_input, zptr, meta)) = self.process(input, file_dir)? else {
            return Ok(None);
        };
        if demo {
            let potential_commentaries = &input[..syntax_start];
            let actual_syntax = &input[syntax_start..new_input.location_offset()];
            let prompt_marker = &self.prompt_marker();
            if actual_syntax.contains('\n') {
                // print the expression on a new line to avoid messing with the user's formatting
                print!("{potential_commentaries}{prompt_marker}\n{actual_syntax}");
            } else {
                print!("{potential_commentaries}{prompt_marker}{actual_syntax}");
            }
            std::io::stdout().flush()?;
            // wait for ENTER to be pressed
            std::io::stdin().read_line(&mut String::new())?;
            // ENTER already prints a new line so we can remove it from the start of incoming input
            new_input = new_input.trim_start_matches('\n').into();
        }
        if meta {
            println!("{}", self.fmt(&zptr));
        } else {
            let result = self.handle_non_meta(&zptr)?;
            if result.tag == Tag::Err {
                // error out when loading a file
                bail!("Reduction error: {}", self.fmt(&result));
            }
        }
        Ok(Some(new_input))
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
                Ok(None) => return Ok(()),
                Ok(Some(new_input)) => input = new_input,
                Err(e) => return Err(e),
            }
        }
    }

    pub(crate) fn init_config() -> Config {
        let var = std::env::var("EDITOR");
        let is_vi = |var: String| VI_EDITORS.iter().any(|&x| x == var.as_str());
        if let Ok(true) = var.map(is_vi) {
            Config::builder().edit_mode(EditMode::Vi).build()
        } else {
            Config::default()
        }
    }

    pub(crate) fn run(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let config = Self::init_config();
        let mut editor: Editor<InputValidator<F>, DefaultHistory> = Editor::with_config(config)?;

        editor.set_helper(Some(InputValidator::<F> {
            state: self.state.clone(),
            _marker: Default::default(),
        }));

        let repl_history = &repl_history()?;
        if repl_history.exists() {
            editor.load_history(repl_history)?;
        }

        let pwd_path = current_dir().expect("Couldn't get current directory");

        loop {
            match editor.readline(&self.prompt_marker()) {
                Ok(mut line) => {
                    editor.add_history_entry(&line)?;

                    while !line.trim_end().is_empty() {
                        match self.process(Span::new(&line), &pwd_path) {
                            Ok(Some((_, rest, zptr, meta))) => {
                                if meta {
                                    println!("{}", self.fmt(&zptr));
                                } else if let Err(e) = self.handle_non_meta(&zptr) {
                                    eprintln!("Error: {e}");
                                }
                                line = rest.to_string();
                            }
                            Ok(None) => break,
                            Err(e) => {
                                eprintln!("Error: {e}");
                                break;
                            }
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
