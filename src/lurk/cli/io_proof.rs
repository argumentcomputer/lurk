use p3_baby_bear::BabyBear;
use serde::{Deserialize, Serialize};
use sphinx_core::{
    stark::{MachineProof, StarkGenericConfig, StarkMachine},
    utils::BabyBearPoseidon2,
};

use crate::{
    lair::{
        chipset::Chipset,
        lair_chip::{LairChip, LairMachineProgram},
    },
    lurk::{
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE, ZPTR_SIZE},
    },
};

use super::zdag::ZDag;

type F = BabyBear;

/// Carries a cryptographic proof and the Lurk data needed to make sense of its
/// public values
#[derive(Serialize, Deserialize)]
pub(crate) struct IOProof {
    sphinx_proof: MachineProof<BabyBearPoseidon2>,
    pub(crate) expr: ZPtr<F>,
    pub(crate) env: ZPtr<F>,
    pub(crate) result: ZPtr<F>,
    pub(crate) zdag: ZDag<F>,
}

impl IOProof {
    pub(crate) fn new<H: Chipset<F>>(
        sphinx_proof: MachineProof<BabyBearPoseidon2>,
        public_values: &[F],
        zstore: &ZStore<F, H>,
    ) -> Self {
        let mut zdag = ZDag::default();
        let expr = ZPtr::from_flat_data(&public_values[..ZPTR_SIZE]);
        let env =
            ZPtr::from_flat_digest(Tag::Env, &public_values[ZPTR_SIZE..ZPTR_SIZE + DIGEST_SIZE]);
        let result = ZPtr::from_flat_data(&public_values[ZPTR_SIZE + DIGEST_SIZE..]);
        zdag.populate_with_many([&expr, &env, &result], zstore);
        Self {
            sphinx_proof,
            expr,
            env,
            result,
            zdag,
        }
    }

    /// Returns `true` if public values are consistent and the proof verifies for
    /// them. Returns `false` otherwise.
    pub(crate) fn verify<H: Chipset<F>>(
        &self,
        machine: &StarkMachine<BabyBearPoseidon2, LairChip<'_, F, H>>,
    ) -> bool {
        let mut public_values = Vec::with_capacity(40);
        public_values.extend(self.expr.flatten());
        public_values.extend(self.env.digest);
        public_values.extend(self.result.flatten());
        for shard_proof in &self.sphinx_proof.shard_proofs {
            if shard_proof.public_values != public_values {
                return false;
            }
        }
        let (_, vk) = machine.setup(&LairMachineProgram);
        let challenger = &mut machine.config().challenger();
        machine.verify(&vk, &self.sphinx_proof, challenger).is_ok()
    }
}
