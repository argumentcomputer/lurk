use anyhow::Result;
use p3_field::{Field, PrimeField32};
use serde::{Deserialize, Serialize};
use std::hash::Hash;

use crate::{
    core::{
        big_num::field_elts_to_biguint,
        zstore::{ZPtr, ZStore, DIGEST_SIZE, HASH3_SIZE},
    },
    lair::chipset::Chipset,
};

use super::{paths::commits_dir, zdag::ZDag};

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
        zstore.commit(preimg)
    }
}

impl<F: Hash + Eq + Default + Copy> CommData<F> {
    #[inline]
    pub(crate) fn new<C: Chipset<F>>(
        secret: [F; DIGEST_SIZE],
        payload: ZPtr<F>,
        zstore: &ZStore<F, C>,
    ) -> Self {
        let mut zdag = ZDag::default();
        zdag.populate_with(&payload, zstore, &mut Default::default());
        Self {
            secret,
            payload,
            zdag,
        }
    }

    fn compute_digest<C: Chipset<F>>(&self, zstore: &mut ZStore<F, C>) -> [F; DIGEST_SIZE]
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
}

impl<F: Field> CommData<F> {
    #[inline]
    pub(crate) fn payload_is_flawed<C: Chipset<F>>(&self, zstore: &mut ZStore<F, C>) -> bool {
        self.zdag.is_flawed(&self.payload, zstore)
    }
}

impl<F: PrimeField32> CommData<F> {
    #[inline]
    pub(crate) fn dump<C: Chipset<F>>(&self, zstore: &mut ZStore<F, C>) -> Result<ZPtr<F>> {
        let comm = self.commit(zstore);
        let hash = format!("{:x}", field_elts_to_biguint(&comm.digest));
        std::fs::write(commits_dir()?.join(hash), bincode::serialize(self)?)?;
        Ok(comm)
    }
}
