use anyhow::{bail, Result};
use camino::Utf8Path;
use p3_field::PrimeField32;
use rustc_hash::FxHashMap;

use crate::{
    lair::chipset::Chipset,
    lurk::{cli::repl::Repl, state::lurk_sym, tag::Tag, zstore::ZPtr},
};

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
        format: "!(defrec <binding> <body>)",
        description: &[
            "Gets macroexpanded to (letrec ((foo (lambda () 123))) (current-env))",
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
}

#[inline]
pub(crate) fn meta_cmds<F: PrimeField32, H: Chipset<F>>() -> MetaCmdsMap<F, H> {
    [MetaCmd::DEF, MetaCmd::DEFREC]
        .map(|mc| (mc.name, mc))
        .into_iter()
        .collect()
}
