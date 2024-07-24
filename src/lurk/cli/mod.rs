mod config;
mod meta;
mod paths;
pub mod repl;

use anyhow::Result;
use config::{set_config, Config};
use repl::Repl;

pub fn run() -> Result<()> {
    set_config(Config::default());
    Repl::new().run()
}
