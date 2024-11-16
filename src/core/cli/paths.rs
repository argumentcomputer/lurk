use anyhow::Result;
use camino::{Utf8Path, Utf8PathBuf};
use p3_field::PrimeField;
use serde::{Deserialize, Serialize};
use std::path::Path;

use crate::core::big_num::field_elts_to_biguint;

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
pub(crate) fn repl_history() -> Result<Utf8PathBuf> {
    Ok(lurk_dir()?.join("repl-history"))
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
pub(crate) fn microchains_dir() -> Utf8PathBuf {
    get_config().lurk_dir.join("microchains")
}

#[inline]
pub(crate) fn scopes_dir() -> Utf8PathBuf {
    get_config().lurk_dir.join("scopes")
}

pub(crate) fn dump_to_hash_dir<F: PrimeField, T: Serialize + ?Sized>(
    outer_dir: &Utf8PathBuf,
    hash: &[F],
    name: impl AsRef<Utf8Path>,
    data: &T,
) -> Result<()> {
    let hash = format!("{:x}", field_elts_to_biguint(hash));
    let dir = outer_dir.join(hash);
    std::fs::create_dir_all(&dir)?;
    std::fs::write(dir.join(name), bincode::serialize(data)?)?;
    Ok(())
}

pub(crate) fn load_from_hash_dir<F: PrimeField, T: for<'a> Deserialize<'a>>(
    outer_dir: &Utf8PathBuf,
    hash: &[F],
    name: impl AsRef<Utf8Path>,
) -> Result<T> {
    let hash = format!("{:x}", field_elts_to_biguint(hash));
    let bytes = std::fs::read(outer_dir.join(hash).join(name))?;
    let data = bincode::deserialize(&bytes)?;
    Ok(data)
}

pub(crate) fn remove_from_hash_dir<F: PrimeField>(
    outer_dir: &Utf8PathBuf,
    hash: &[F],
    name: impl AsRef<Utf8Path>,
) -> Result<()> {
    let hash = format!("{:x}", field_elts_to_biguint(hash));
    let path = outer_dir.join(hash).join(name);
    if path.exists() {
        std::fs::remove_file(path)?;
    }
    Ok(())
}
