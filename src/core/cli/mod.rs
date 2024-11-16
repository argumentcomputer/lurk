mod comm_data;
mod config;
mod debug;
mod lurk_data;
mod meta;
mod microchain;
mod paths;
mod proofs;
mod rdg;
pub mod repl;
mod scope;
#[cfg(test)]
mod tests;
mod zdag;

use anyhow::{bail, Result};
use camino::Utf8PathBuf;
use clap::{Args, Parser, Subcommand};
use config::{set_config, Config};
use microchain::MicrochainArgs;
use repl::Repl;

#[derive(Parser, Debug)]
#[clap(version)]
struct Cli {
    #[clap(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Enters Lurk's REPL environment ("repl" can be elided)
    Repl(ReplArgs),
    /// Loads a file, processing forms sequentially ("load" can be elided)
    Load(LoadArgs),
    /// Starts the microchain server
    Microchain(MicrochainArgs),
}

#[derive(Args, Debug)]
struct ReplArgs {
    /// Optional file to be loaded before entering the REPL
    #[clap(long, value_parser)]
    preload: Option<Utf8PathBuf>,
}

#[derive(Parser, Debug)]
struct ReplCli {
    #[clap(long, value_parser)]
    preload: Option<Utf8PathBuf>,
}

#[derive(Args, Debug)]
struct LoadArgs {
    /// The file to be loaded
    #[clap(value_parser)]
    lurk_file: Utf8PathBuf,

    /// Flag to prove the last reduction
    #[arg(long)]
    prove: bool,

    /// Flag to load the file in demo mode
    #[arg(long)]
    demo: bool,
}

#[derive(Parser, Debug)]
struct LoadCli {
    #[clap(value_parser = parse_filename)]
    lurk_file: Utf8PathBuf,

    #[arg(long)]
    prove: bool,

    #[arg(long)]
    demo: bool,
}

fn parse_filename(file: &str) -> Result<Utf8PathBuf> {
    if ["help", "microchain"].contains(&file) {
        bail!("Invalid file name");
    }
    Ok(file.into())
}

impl ReplArgs {
    fn into_cli(self) -> ReplCli {
        let Self { preload } = self;
        ReplCli { preload }
    }
}

impl LoadArgs {
    fn into_cli(self) -> LoadCli {
        let Self {
            lurk_file,
            prove,
            demo,
        } = self;
        LoadCli {
            lurk_file,
            prove,
            demo,
        }
    }
}

impl Cli {
    fn run(self) -> Result<()> {
        match self.command {
            Command::Repl(repl_args) => repl_args.into_cli().run(),
            Command::Load(load_args) => load_args.into_cli().run(),
            Command::Microchain(microchain_args) => microchain_args.run(),
        }
    }
}

impl ReplCli {
    fn run(&self) -> Result<()> {
        let mut repl = Repl::new_native();
        if let Some(lurk_file) = &self.preload {
            repl.load_file(lurk_file, false)?;
        }
        repl.run()
    }
}

impl LoadCli {
    fn run(&self) -> Result<()> {
        let mut repl = Repl::new_native();
        repl.load_file(&self.lurk_file, self.demo)?;
        if self.prove {
            repl.prove_last_reduction()?;
        }
        Ok(())
    }
}

pub fn run() -> Result<()> {
    set_config(Config::default());
    if let Ok(cli) = Cli::try_parse() {
        cli.run()
    } else if let Ok(repl_cli) = ReplCli::try_parse() {
        repl_cli.run()
    } else if let Ok(load_cli) = LoadCli::try_parse() {
        load_cli.run()
    } else {
        // force printing help
        Cli::parse();
        Ok(())
    }
}
