use p3_field::{AbstractField, Field};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};

use crate::{
    core::zstore::{ZPtr, ZPtrType, ZStore},
    lair::chipset::Chipset,
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
}

impl<F: Field> ZDag<F> {
    /// Returns `true` if one of the following flaws is encountered when traversing
    /// from `zptr`:
    /// * A digest mismatch is found (which is enough to also spot cycles)
    /// * There's data missing
    pub(crate) fn is_flawed<'a, C: Chipset<F>>(
        &'a self,
        zptr: &'a ZPtr<F>,
        zstore: &mut ZStore<F, C>,
    ) -> bool {
        let checked = &mut FxHashSet::default();
        self.is_flawed_aux(zptr, zstore, checked)
    }

    fn is_flawed_aux<'a, C: Chipset<F>>(
        &'a self,
        zptr: &'a ZPtr<F>,
        zstore: &mut ZStore<F, C>,
        checked: &mut FxHashSet<&'a ZPtr<F>>,
    ) -> bool {
        if checked.contains(zptr) {
            // already checked on a different DAG branch
            return false;
        }
        macro_rules! return_if_true {
            ($cond:expr) => {
                if $cond {
                    return true;
                }
            };
        }
        match self.0.get(zptr) {
            None => return true, // missing data
            Some(ZPtrType::Atom) => (),
            Some(ZPtrType::Tuple11(a, b)) => {
                return_if_true!(zptr.digest != zstore.hash4(ZPtr::flatten_as_tuple11(a, b)));
                return_if_true!(self.is_flawed_aux(a, zstore, checked));
                return_if_true!(self.is_flawed_aux(b, zstore, checked));
            }
            Some(ZPtrType::Tuple110(a, b, c)) => {
                return_if_true!(zptr.digest != zstore.hash5(ZPtr::flatten_as_tuple110(a, b, c)));
                return_if_true!(self.is_flawed_aux(a, zstore, checked));
                return_if_true!(self.is_flawed_aux(b, zstore, checked));
                return_if_true!(self.is_flawed_aux(c, zstore, checked));
            }
        }
        assert!(checked.insert(zptr));
        false
    }
}

#[cfg(test)]
mod test {
    use crate::core::{
        tag::Tag,
        zstore::{lurk_zstore, ZPtr, ZPtrType},
    };

    use super::ZDag;

    #[test]
    fn test_is_flawed() {
        let zstore = &mut lurk_zstore();
        let mut zdag = ZDag::default();

        // digest mismatch because [0; 8] is not the digest of two null nums
        let num_zero = ZPtr::null(Tag::Num);
        zdag.0.insert(num_zero, ZPtrType::Atom);
        let cons_zero = ZPtr::null(Tag::Cons);
        zdag.0
            .insert(cons_zero, ZPtrType::Tuple11(num_zero, num_zero));
        assert!(zdag.is_flawed(&cons_zero, zstore));

        // missing data because `char_a` is not in `zdag`
        let char_a = zstore.intern_char('a');
        let cons_a_a = zstore.intern_cons(char_a, char_a);
        zdag.0.insert(cons_a_a, ZPtrType::Tuple11(char_a, char_a));
        assert!(zdag.is_flawed(&cons_a_a, zstore));

        // no false alarm here
        zdag.populate_with(&cons_a_a, zstore, &mut Default::default());
        assert!(!zdag.is_flawed(&cons_a_a, zstore));
    }
}
