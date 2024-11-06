use p3_field::Field;
use serde::{Deserialize, Serialize};
use std::hash::Hash;

use crate::{
    core::{
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE, HASH3_SIZE},
    },
    lair::chipset::Chipset,
};

use super::zdag::ZDag;

#[derive(Serialize, Deserialize)]
pub(crate) struct CommData<F: Hash + Eq> {
    pub(crate) secret: [F; DIGEST_SIZE],
    pub(crate) payload: ZPtr<F>,
    pub(crate) zdag: ZDag<F>,
}

impl<F: Field> CommData<F> {
    pub(crate) fn hash<C: Chipset<F>>(
        secret: &[F; DIGEST_SIZE],
        payload: &ZPtr<F>,
        zstore: &mut ZStore<F, C>,
    ) -> [F; DIGEST_SIZE] {
        let mut preimg = [F::default(); HASH3_SIZE];
        preimg[..DIGEST_SIZE].copy_from_slice(secret);
        preimg[DIGEST_SIZE..].copy_from_slice(&payload.flatten());
        zstore.hash3(preimg)
    }
}

impl<F: Hash + Eq + Default + Copy> CommData<F> {
    #[inline]
    pub(crate) fn new<C: Chipset<F>>(
        secret: ZPtr<F>,
        payload: ZPtr<F>,
        zstore: &ZStore<F, C>,
    ) -> Self {
        assert_eq!(secret.tag, Tag::BigNum);
        let mut zdag = ZDag::default();
        zdag.populate_with_many([&secret, &payload], zstore);
        Self {
            secret: secret.digest,
            payload,
            zdag,
        }
    }

    fn compute_digest<H: Chipset<F>>(&self, zstore: &mut ZStore<F, H>) -> [F; DIGEST_SIZE]
    where
        F: Field,
    {
        Self::hash(&self.secret, &self.payload, zstore)
    }

    #[inline]
    pub(crate) fn commit<C: Chipset<F>>(&self, zstore: &mut ZStore<F, C>) -> ZPtr<F>
    where
        F: Field,
    {
        ZPtr::comm(self.compute_digest(zstore))
    }

    #[inline]
    pub(crate) fn populate_zstore<C: Chipset<F>>(self, zstore: &mut ZStore<F, C>)
    where
        F: Field,
    {
        let digest = self.compute_digest(zstore);
        zstore.intern_comm(digest);
        self.zdag.populate_zstore(zstore);
    }

    #[inline]
    pub(crate) fn payload_has_opaque_data(&self) -> bool {
        self.zdag.has_opaque_data(&self.payload)
    }
}
