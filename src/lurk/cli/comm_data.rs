use p3_field::{AbstractField, Field};
use serde::{Deserialize, Serialize};

use crate::{
    lair::chipset::Chipset,
    lurk::{
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE, HASH3_SIZE},
    },
};

use super::zdag::ZDag;

#[derive(Serialize, Deserialize)]
pub(crate) struct CommData<F: std::hash::Hash + Eq> {
    pub(crate) secret: ZPtr<F>,
    pub(crate) payload: ZPtr<F>,
    pub(crate) zdag: ZDag<F>,
}

impl<F: std::hash::Hash + Eq + Default + Copy> CommData<F> {
    pub(crate) fn new<H: Chipset<F>>(
        secret: ZPtr<F>,
        payload: ZPtr<F>,
        zstore: &ZStore<F, H>,
    ) -> Self {
        assert_eq!(secret.tag, Tag::Comm);
        let mut zdag = ZDag::default();
        zdag.populate_with_many([&secret, &payload], zstore);
        Self {
            secret,
            payload,
            zdag,
        }
    }

    fn build_preimg(&self) -> [F; HASH3_SIZE]
    where
        F: AbstractField,
    {
        let mut preimg = [F::zero(); HASH3_SIZE];
        preimg[..DIGEST_SIZE].copy_from_slice(&self.secret.digest);
        preimg[DIGEST_SIZE..].copy_from_slice(&self.payload.flatten());
        preimg
    }

    #[inline]
    pub(crate) fn commit<H: Chipset<F>>(&self, zstore: &mut ZStore<F, H>) -> ZPtr<F>
    where
        F: Field,
    {
        ZPtr::comm(zstore.hash3(self.build_preimg()))
    }

    pub(crate) fn fetch<H: Chipset<F>>(self, zstore: &mut ZStore<F, H>)
    where
        F: Field,
    {
        let preimg = self.build_preimg();
        zstore.hash3(preimg);
        let Self { zdag, .. } = self;
        zdag.populate_zstore(zstore);
    }
}
