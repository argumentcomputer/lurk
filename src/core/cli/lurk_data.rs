use p3_field::{AbstractField, Field};
use serde::{Deserialize, Serialize};

use crate::{
    core::zstore::{ZPtr, ZStore},
    lair::chipset::Chipset,
};

use super::zdag::ZDag;

#[derive(Serialize, Deserialize)]
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
}

impl<F: Field> LurkData<F> {
    #[inline]
    pub(crate) fn is_flawed<C: Chipset<F>>(&self, zstore: &mut ZStore<F, C>) -> bool {
        self.zdag.is_flawed(&self.zptr, zstore)
    }
}
