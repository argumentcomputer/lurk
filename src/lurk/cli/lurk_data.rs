use p3_field::AbstractField;
use serde::{Deserialize, Serialize};

use crate::{
    lair::chipset::Chipset,
    lurk::zstore::{ZPtr, ZStore},
};

use super::zdag::ZDag;

#[derive(Serialize, Deserialize)]
pub(crate) struct LurkData<F: std::hash::Hash + Eq> {
    zptr: ZPtr<F>,
    zdag: ZDag<F>,
}

impl<F: std::hash::Hash + Eq + Default + Copy> LurkData<F> {
    #[inline]
    pub(crate) fn new<H: Chipset<F>>(zptr: ZPtr<F>, zstore: &ZStore<F, H>) -> Self {
        let mut zdag = ZDag::default();
        zdag.populate_with(&zptr, zstore, &mut Default::default());
        Self { zptr, zdag }
    }

    #[inline]
    pub(crate) fn populate_zstore<H: Chipset<F>>(self, zstore: &mut ZStore<F, H>) -> ZPtr<F>
    where
        F: AbstractField,
    {
        let Self { zptr, zdag } = self;
        zdag.populate_zstore(zstore);
        zptr
    }
}
