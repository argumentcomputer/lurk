use p3_field::AbstractField;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::{
    lair::chipset::Chipset,
    core::zstore::{ZPtr, ZPtrType, ZStore},
};

/// Holds Lurk data meant to be persisted and/or shared
#[derive(Default, Serialize, Deserialize)]
pub(crate) struct ZDag<F: std::hash::Hash + Eq>(FxHashMap<ZPtr<F>, ZPtrType<F>>);

impl<F: std::hash::Hash + Eq + Copy> ZDag<F> {
    /// Traverses a ZStore DAG, starting from a given `ZPtr`, while populating
    /// itself.
    pub(crate) fn populate_with<'a, C: Chipset<F>>(
        &mut self,
        zptr: &'a ZPtr<F>,
        zstore: &'a ZStore<F, C>,
        cache: &mut FxHashSet<&'a ZPtr<F>>,
    ) {
        if cache.contains(zptr) {
            return;
        }
        let zptr_type = zstore
            .dag
            .get(zptr)
            .expect("Data missing from ZStore's DAG");
        match zptr_type {
            ZPtrType::Atom => (),
            ZPtrType::Tuple11(a, b) => {
                self.populate_with(a, zstore, cache);
                self.populate_with(b, zstore, cache);
            }
            ZPtrType::Tuple110(a, b, c) => {
                self.populate_with(a, zstore, cache);
                self.populate_with(b, zstore, cache);
                self.populate_with(c, zstore, cache);
            }
        }
        cache.insert(zptr);
        self.0.insert(*zptr, *zptr_type);
    }

    /// Calls `populate_with` for a sequence of `ZPtr`s
    pub(crate) fn populate_with_many<'a, C: Chipset<F>>(
        &mut self,
        zptrs: impl IntoIterator<Item = &'a ZPtr<F>>,
        zstore: &ZStore<F, C>,
    ) where
        F: 'a,
    {
        let cache = &mut FxHashSet::default();
        for zptr in zptrs {
            self.populate_with(zptr, zstore, cache);
        }
    }

    /// Moves its data to a target ZStore
    pub(crate) fn populate_zstore<C: Chipset<F>>(self, zstore: &mut ZStore<F, C>)
    where
        F: AbstractField + Copy,
    {
        for (zptr, zptr_type) in self.0 {
            match &zptr_type {
                ZPtrType::Atom => (),
                ZPtrType::Tuple11(a, b) => {
                    let preimg = ZPtr::flatten_as_tuple11(a, b);
                    zstore.hashes4.insert(preimg, zptr.digest);
                    zstore.hashes4_diff.insert(preimg, zptr.digest);
                }
                ZPtrType::Tuple110(a, b, c) => {
                    let preimg = ZPtr::flatten_as_tuple110(a, b, c);
                    zstore.hashes5.insert(preimg, zptr.digest);
                    zstore.hashes5_diff.insert(preimg, zptr.digest);
                }
            }
            zstore.dag.insert(zptr, zptr_type);
        }
    }

    /// Whether there's data missing in the ZDag or not
    pub(crate) fn has_opaque_data(&self, zptr: &ZPtr<F>) -> bool {
        match self.0.get(zptr) {
            None => true,
            Some(ZPtrType::Atom) => false,
            Some(ZPtrType::Tuple11(a, b)) => self.has_opaque_data(a) || self.has_opaque_data(b),
            Some(ZPtrType::Tuple110(a, b, c)) => {
                self.has_opaque_data(a) || self.has_opaque_data(b) || self.has_opaque_data(c)
            }
        }
    }
}
