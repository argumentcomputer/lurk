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
use std::fmt::Debug;
use std::io::Write;

use crate::{
    lair::{chipset::Chipset, execute::QueryRecord, toplevel::Toplevel},
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
        tag::Tag,
        zstore::{ZPtr, ZStore},
    },
};

#[derive(Helper, Highlighter, Hinter, Completer)]
struct InputValidator {
    state: StateRcCell,
}

impl InputValidator {
    fn try_parse<F: Field + Debug>(&self, input: &str) -> Result<(), Error> {
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

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        let parse_result = self.try_parse::<BabyBear>(input);
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
    pub(crate) env: ZPtr<F>,
    state: StateRcCell,
    pwd_path: Utf8PathBuf,
    meta_cmds: MetaCmdsMap<F, H>,
}

impl Repl<BabyBear, LurkChip> {
    pub(crate) fn new() -> Self {
        let (toplevel, mut zstore) = build_lurk_toplevel();
        let queries = QueryRecord::new(&toplevel);
        let lurk_main_idx = toplevel.get_by_name("lurk_main").index;
        let eval_idx = toplevel.get_by_name("eval").index;
        let env = zstore.intern_empty_env();
        Self {
            zstore,
            queries,
            toplevel,
            lurk_main_idx,
            eval_idx,
            env,
            state: State::init_lurk_state().rccell(),
            pwd_path: current_dir().expect("Couldn't get current directory"),
            meta_cmds: meta_cmds(),
        }
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

    fn build_input(&self, expr: &ZPtr<F>) -> [F; 24] {
        let mut input = [F::zero(); 24];
        input[..16].copy_from_slice(&expr.flatten());
        input[16..].copy_from_slice(&self.env.digest);
        input
    }

    /// Reduces a Lurk expression with a clone of the REPL's queries so the latest
    /// provable computation isn't affected. After the reduction is over, retrieve
    /// the (potentially enriched) inverse query maps so commitments aren't lost.
    pub(crate) fn reduce_aux(&mut self, expr: &ZPtr<F>) -> ZPtr<F> {
        self.prepare_queries();
        let mut queries = self.queries.clone();
        let output = ZPtr::from_flat_data(&self.toplevel.execute_by_index(
            self.lurk_main_idx,
            &self.build_input(expr),
            &mut queries,
        ));
        self.queries.inv_func_queries = queries.inv_func_queries;
        output
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

    pub(crate) fn handle_non_meta(&mut self, expr: &ZPtr<F>) {
        self.prepare_queries();
        let output = ZPtr::from_flat_data(&self.toplevel.execute_by_index(
            self.lurk_main_idx,
            &self.build_input(expr),
            &mut self.queries,
        ));
        self.memoize_dag(output.tag, &output.digest);
        let iterations = self.queries.func_queries[self.eval_idx].len();
        println!(
            "[{}] => {}",
            pretty_iterations_display(iterations),
            self.fmt(&output)
        );
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
            bail!("Invalid meta command")
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
            self.handle_non_meta(&zptr);
        }
        Ok(new_input)
    }

    pub(crate) fn load_file(&mut self, file_path: &Utf8Path, demo: bool) -> Result<()> {
        let input = std::fs::read_to_string(file_path)?;
        if demo {
            println!("Loading {file_path} in demo mode");
        } else {
            println!("Loading {file_path}");
        }
        let mut input = Span::new(&input);
        loop {
            let Some(file_dir) = file_path.parent() else {
                bail!("Can't load parent of {}", file_path);
            };

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

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::new()?;

        editor.set_helper(Some(InputValidator {
            state: self.state.clone(),
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
                                self.handle_non_meta(&zptr)
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
