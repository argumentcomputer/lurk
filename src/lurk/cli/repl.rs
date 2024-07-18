use anyhow::Result;
use p3_baby_bear::BabyBear;
use p3_field::PrimeField32;
use rustyline::{
    error::ReadlineError,
    history::DefaultHistory,
    validate::{MatchingBracketValidator, ValidationContext, ValidationResult, Validator},
    Completer, Editor, Helper, Highlighter, Hinter,
};

use crate::{
    lair::{chipset::Chipset, execute::QueryRecord, toplevel::Toplevel},
    lurk::{
        chipset::LurkChip,
        cli::paths::repl_history,
        eval::build_lurk_toplevel,
        state::{State, StateRcCell},
        zstore::{ZPtr, ZStore},
    },
};

#[derive(Helper, Highlighter, Hinter, Completer, Default)]
struct InputValidator {
    brackets: MatchingBracketValidator,
}

impl Validator for InputValidator {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        self.brackets.validate(ctx)
    }
}

pub(crate) struct Repl<F: PrimeField32, H: Chipset<F>> {
    zstore: ZStore<F, H>,
    record: QueryRecord<F>,
    toplevel: Toplevel<F, H>,
    lurk_main_idx: usize,
    eval_idx: usize,
    state: StateRcCell,
}

impl Repl<BabyBear, LurkChip> {
    pub(crate) fn new() -> Self {
        let (toplevel, zstore) = build_lurk_toplevel();
        let record = QueryRecord::new(&toplevel);
        let lurk_main_idx = toplevel.get_by_name("lurk_main").index;
        let eval_idx = toplevel.get_by_name("eval").index;
        let state = State::init_lurk_state().rccell();
        Self {
            zstore,
            record,
            toplevel,
            lurk_main_idx,
            eval_idx,
            state,
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
    fn input_marker(&self) -> String {
        format!(
            "{}> ",
            self.state
                .borrow()
                .fmt_to_string(self.state.borrow().get_current_package_name())
        )
    }

    fn handle_non_meta(&mut self, zptr: ZPtr<F>) {
        self.record.clean();
        self.record
            .inject_inv_queries("hash_32_8", &self.toplevel, self.zstore.tuple2_hashes());
        self.record
            .inject_inv_queries("hash_48_8", &self.toplevel, self.zstore.tuple3_hashes());
        let mut input = [F::zero(); 24];
        input[..16].copy_from_slice(&zptr.flatten());
        let output = self
            .toplevel
            .execute_by_index(self.lurk_main_idx, &input, &mut self.record);
        let output_zptr = ZPtr::from_flat_data(&output);
        self.zstore.memoize_dag(
            output_zptr.tag,
            &output_zptr.digest,
            self.record.get_inv_queries("hash_32_8", &self.toplevel),
            self.record.get_inv_queries("hash_48_8", &self.toplevel),
        );
        let iterations = self.record.func_queries[self.eval_idx].len();
        println!(
            "[{}] => {}",
            pretty_iterations_display(iterations),
            self.zstore.fmt_with_state(&self.state, &output_zptr)
        );
    }

    fn handle_meta(&mut self, _zptr: ZPtr<F>) {
        todo!()
    }

    pub(crate) fn run(&mut self) -> Result<()> {
        println!("Lurk REPL welcomes you.");

        let mut editor: Editor<InputValidator, DefaultHistory> = Editor::new()?;

        editor.set_helper(Some(InputValidator::default()));

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
                        Ok((is_meta, zptr)) => {
                            if is_meta {
                                self.handle_meta(zptr)
                            } else {
                                self.handle_non_meta(zptr)
                            }
                        }
                        Err(e) => eprintln!("Read error: {e}"),
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
