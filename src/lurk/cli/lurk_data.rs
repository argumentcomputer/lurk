use p3_field::AbstractField;
use serde::{Deserialize, Serialize};

use crate::{
    lair::chipset::Chipset,
    lurk::zstore::{ZPtr, ZStore},
};

use super::zdag::ZDag;

#[derive(Serialize, Deserialize, Clone)]
pub(crate) struct LurkData<F: std::hash::Hash + Eq> {
    pub(crate) zptr: ZPtr<F>,
    zdag: ZDag<F>,
}

impl<F: std::hash::Hash + Eq + Default + Copy> LurkData<F> {
    #[inline]
    pub(crate) fn new<C: Chipset<F>>(zptr: ZPtr<F>, zstore: &ZStore<F, C>) -> Self {
        let mut zdag = ZDag::default();
        zdag.populate_with(&zptr, zstore, &mut Default::default());
        Self { zptr, zdag }
    }

    #[inline]
    pub(crate) fn populate_zstore<C: Chipset<F>>(self, zstore: &mut ZStore<F, C>) -> ZPtr<F>
    where
        F: AbstractField,
    {
        let Self { zptr, zdag } = self;
        zdag.populate_zstore(zstore);
        zptr
    }

    #[inline]
    pub(crate) fn has_opaque_data(&self) -> bool {
        self.zdag.has_opaque_data(&self.zptr)
    }
}
