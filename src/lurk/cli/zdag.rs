use p3_field::AbstractField;
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::{
    lair::chipset::Chipset,
    lurk::zstore::{ZPtr, ZPtrType, ZStore},
};

/// Holds Lurk data meant to be persisted and/or shared
#[derive(Default, Serialize, Deserialize)]
pub(crate) struct ZDag<F: std::hash::Hash + Eq>(FxHashMap<ZPtr<F>, ZPtrType<F>>);

impl<F: std::hash::Hash + Eq + Copy> ZDag<F> {
    /// Traverses a ZStore DAG, starting from a given `ZPtr`, while populating
    /// itself.
    pub(crate) fn populate_with<'a, H: Chipset<F>>(
        &mut self,
        zptr: &'a ZPtr<F>,
        zstore: &'a ZStore<F, H>,
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
            ZPtrType::Tuple2(a, b) | ZPtrType::Compact10(a, b) => {
                self.populate_with(a, zstore, cache);
                self.populate_with(b, zstore, cache);
            }
            ZPtrType::Compact110(a, b, c) => {
                self.populate_with(a, zstore, cache);
                self.populate_with(b, zstore, cache);
                self.populate_with(c, zstore, cache);
            }
        }
        cache.insert(zptr);
        self.0.insert(*zptr, *zptr_type);
    }

    /// Calls `populate_with` for a sequence of `ZPtr`s
    pub(crate) fn populate_with_many<'a, H: Chipset<F>>(
        &mut self,
        zptrs: impl IntoIterator<Item = &'a ZPtr<F>>,
        zstore: &ZStore<F, H>,
    ) where
        F: 'a,
    {
        let cache = &mut FxHashSet::default();
        for zptr in zptrs {
            self.populate_with(zptr, zstore, cache);
        }
    }

    /// Moves its data to a target ZStore
    pub(crate) fn populate_zstore<H: Chipset<F>>(self, zstore: &mut ZStore<F, H>)
    where
        F: AbstractField + Copy,
    {
        for (zptr, zptr_type) in self.0 {
            match &zptr_type {
                ZPtrType::Atom => (),
                ZPtrType::Tuple2(a, b) => {
                    let preimg = ZPtr::flatten2(a, b);
                    zstore.hashes32.insert(preimg, zptr.digest);
                    zstore.hashes32_diff.insert(preimg, zptr.digest);
                }
                ZPtrType::Compact10(a, b) => {
                    let preimg = ZPtr::flatten_compact10(a, b);
                    zstore.hashes24.insert(preimg, zptr.digest);
                    zstore.hashes24_diff.insert(preimg, zptr.digest);
                }
                ZPtrType::Compact110(a, b, c) => {
                    let preimg = ZPtr::flatten_compact110(a, b, c);
                    zstore.hashes40.insert(preimg, zptr.digest);
                    zstore.hashes40_diff.insert(preimg, zptr.digest);
                }
            }
            zstore.dag.insert(zptr, zptr_type);
        }
    }
}
