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
    #[inline]
    pub(crate) fn new<H: Chipset<F>>(
        secret: ZPtr<F>,
        payload: ZPtr<F>,
        zstore: &ZStore<F, H>,
    ) -> Self {
        assert_eq!(secret.tag, Tag::BigNum);
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

    fn compute_hash<H: Chipset<F>>(&self, zstore: &mut ZStore<F, H>) -> [F; DIGEST_SIZE]
    where
        F: Field,
    {
        zstore.hash3(self.build_preimg())
    }

    #[inline]
    pub(crate) fn commit<H: Chipset<F>>(&self, zstore: &mut ZStore<F, H>) -> ZPtr<F>
    where
        F: Field,
    {
        ZPtr::comm(self.compute_hash(zstore))
    }

    #[inline]
    pub(crate) fn populate_zstore<H: Chipset<F>>(self, zstore: &mut ZStore<F, H>)
    where
        F: Field,
    {
        let digest = self.compute_hash(zstore);
        zstore.intern_comm(digest);
        self.zdag.populate_zstore(zstore);
    }

    #[inline]
    pub(crate) fn payload_has_opaque_data(&self) -> bool {
        self.zdag.has_opaque_data(&self.payload)
    }
}
