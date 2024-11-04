use anyhow::Result;
use camino::Utf8PathBuf;
use std::path::Path;

use super::config::get_config;

#[inline]
pub(crate) fn current_dir() -> Result<Utf8PathBuf> {
    let path = Utf8PathBuf::try_from(std::env::current_dir()?)?;
    Ok(path)
}

#[inline]
fn create_dir_all_and_return<P: AsRef<Path>>(path: P) -> Result<P> {
    std::fs::create_dir_all(path.as_ref())?;
    Ok(path)
}

#[inline]
pub(crate) fn lurk_dir() -> Result<&'static Utf8PathBuf> {
    create_dir_all_and_return(&get_config().lurk_dir)
}

#[inline]
pub(crate) fn proofs_dir() -> Result<Utf8PathBuf> {
    create_dir_all_and_return(get_config().lurk_dir.join("proofs"))
}

#[inline]
pub(crate) fn commits_dir() -> Result<Utf8PathBuf> {
    create_dir_all_and_return(get_config().lurk_dir.join("commits"))
}

#[inline]
pub(crate) fn microchains_dir() -> Result<Utf8PathBuf> {
    create_dir_all_and_return(get_config().lurk_dir.join("microchains"))
}

#[inline]
pub(crate) fn repl_history() -> Result<Utf8PathBuf> {
    Ok(lurk_dir()?.join("repl-history"))
}
