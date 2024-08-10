mod comm_data;
mod config;
mod io_proof;
mod lurk_data;
mod meta;
mod paths;
pub mod repl;
mod zdag;

use anyhow::Result;
use config::{set_config, Config};
use repl::Repl;

pub fn run() -> Result<()> {
    set_config(Config::default());
    Repl::new().run()
}
