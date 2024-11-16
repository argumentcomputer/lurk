//! This module implements the persistency layer to support scope-related meta commands.
//!
//! One remarkable note is that, even though scopes are named after symbols, their
//! data have to be persisted on directories named after symbol digests because
//! symbols paths may contain characters that aren't allowed for folder names.

use anyhow::Result;
use p3_field::PrimeField;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::hash::Hash;

use crate::{
    core::{
        cli::{repl::MicrochainInfo, zdag::ZDag},
        zstore::{ZPtr, ZStore},
    },
    lair::{chipset::Chipset, List},
};

use super::paths::{dump_to_hash_dir, load_from_hash_dir, remove_from_hash_dir, scopes_dir};

#[derive(Serialize, Deserialize, Default)]
pub(crate) struct ScopeBindings<F: Eq + Hash> {
    pub(crate) binds: FxHashMap<ZPtr<F>, ZPtr<F>>,
    pub(crate) zdag: ZDag<F>,
}

impl<F: Eq + Hash + Copy> ScopeBindings<F> {
    // FIXME: `zdag` may contain dead unreachable data if a binding is shadowed.
    pub(crate) fn bind<C: Chipset<F>>(
        &mut self,
        sym: ZPtr<F>,
        val: ZPtr<F>,
        zstore: &ZStore<F, C>,
    ) {
        self.zdag.populate_with_many([&sym, &val], zstore);
        self.binds.insert(sym, val);
    }
}

const BINDINGS_FILE: &str = "bindings";
const COMMS_FILE: &str = "comms";
const MICROCHAIN_FILE: &str = "microchain";

// Scope commitments

pub(crate) fn update_scope_comms<F: PrimeField, T>(scope_digest: &[F], mut f: T) -> Result<()>
where
    T: FnMut(FxHashSet<List<F>>) -> Result<FxHashSet<List<F>>>,
{
    let comms = load_scope_comms(scope_digest).unwrap_or_default();
    let comms = f(comms)?;
    if comms.is_empty() {
        remove_scope_comms(scope_digest)
    } else {
        dump_scope_comms(scope_digest, &comms)
    }
}

#[inline]
pub(crate) fn load_scope_comms<F: PrimeField>(scope_digest: &[F]) -> Result<FxHashSet<List<F>>> {
    load_from_hash_dir(&scopes_dir(), scope_digest, COMMS_FILE)
}

fn dump_scope_comms<F: PrimeField>(scope_digest: &[F], comms: &FxHashSet<List<F>>) -> Result<()> {
    dump_to_hash_dir(&scopes_dir(), scope_digest, COMMS_FILE, comms)
}

fn remove_scope_comms<F: PrimeField>(scope_digest: &[F]) -> Result<()> {
    remove_from_hash_dir(&scopes_dir(), scope_digest, COMMS_FILE)
}

// Scope bindings

pub(crate) fn update_scope_bindings<F: PrimeField, T>(scope_digest: &[F], mut f: T) -> Result<()>
where
    T: FnMut(ScopeBindings<F>) -> Result<ScopeBindings<F>>,
{
    let bindings = load_scope_bindings(scope_digest).unwrap_or_default();
    let bindings = f(bindings)?;
    if bindings.binds.is_empty() {
        remove_scope_bindings(scope_digest)
    } else {
        dump_scope_bindings(scope_digest, &bindings)
    }
}

#[inline]
pub(crate) fn load_scope_bindings<F: PrimeField>(scope_digest: &[F]) -> Result<ScopeBindings<F>> {
    load_from_hash_dir(&scopes_dir(), scope_digest, BINDINGS_FILE)
}

fn dump_scope_bindings<F: Eq + Hash + PrimeField>(
    scope_digest: &[F],
    scope_bindings: &ScopeBindings<F>,
) -> Result<()> {
    dump_to_hash_dir(&scopes_dir(), scope_digest, BINDINGS_FILE, scope_bindings)
}

fn remove_scope_bindings<F: PrimeField>(scope_digest: &[F]) -> Result<()> {
    remove_from_hash_dir(&scopes_dir(), scope_digest, BINDINGS_FILE)
}

// Scope microchain

#[inline]
pub(crate) fn load_scope_microchain<F: PrimeField>(
    scope_digest: &[F],
) -> Result<Option<MicrochainInfo<F>>> {
    load_from_hash_dir(&scopes_dir(), scope_digest, MICROCHAIN_FILE)
}

#[inline]
pub(crate) fn dump_scope_microchain<F: PrimeField>(
    scope_digest: &[F],
    microchain: &Option<MicrochainInfo<F>>,
) -> Result<()> {
    dump_to_hash_dir(&scopes_dir(), scope_digest, MICROCHAIN_FILE, microchain)
}
