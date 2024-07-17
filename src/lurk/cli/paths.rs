use anyhow::Result;
use camino::Utf8PathBuf;
use std::path::Path;

use super::config::get_config;

fn create_dir_all_and_return<P: AsRef<Path>>(path: P) -> Result<P> {
    std::fs::create_dir_all(path.as_ref())?;
    Ok(path)
}

#[inline]
pub(crate) fn lurk_dir() -> Result<&'static Utf8PathBuf> {
    create_dir_all_and_return(&get_config().lurk_dir)
}

#[inline]
pub(crate) fn repl_history() -> Result<Utf8PathBuf> {
    Ok(lurk_dir()?.join("repl-history"))
}
