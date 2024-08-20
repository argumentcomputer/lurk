use hashbrown::HashMap;
use p3_baby_bear::BabyBear;
use serde::{Deserialize, Serialize};
use sphinx_core::{
    stark::{
        Challenge, Com, MachineProof, OpeningProof, ShardCommitment, ShardOpenedValues, ShardProof,
    },
    utils::BabyBearPoseidon2,
};

use crate::{
    lair::chipset::Chipset,
    lurk::{
        tag::Tag,
        zstore::{ZPtr, ZStore, DIGEST_SIZE, ZPTR_SIZE},
    },
};

use super::{lurk_data::LurkData, zdag::ZDag};

#[derive(Serialize, Deserialize)]
struct CryptoShardProof {
    commitment: ShardCommitment<Com<BabyBearPoseidon2>>,
    opened_values: ShardOpenedValues<Challenge<BabyBearPoseidon2>>,
    opening_proof: OpeningProof<BabyBearPoseidon2>,
    chip_ordering: HashMap<String, usize>,
}

#[derive(Serialize, Deserialize)]
pub(crate) struct CryptoProof {
    shard_proofs: Vec<CryptoShardProof>,
    verifier_version: String,
}

type F = BabyBear;

impl CryptoProof {
    #[inline]
    pub(crate) fn into_machine_proof(
        self,
        expr: &ZPtr<F>,
        env: &ZPtr<F>,
        result: &ZPtr<F>,
    ) -> MachineProof<BabyBearPoseidon2> {
        let mut public_values = Vec::with_capacity(40);
        public_values.extend(expr.flatten());
        public_values.extend(env.digest);
        public_values.extend(result.flatten());
        let shard_proofs = self
            .shard_proofs
            .into_iter()
            .map(|csp| {
                let CryptoShardProof {
                    commitment,
                    opened_values,
                    opening_proof,
                    chip_ordering,
                } = csp;
                ShardProof {
                    commitment,
                    opened_values,
                    opening_proof,
                    chip_ordering,
                    public_values: public_values.clone(),
                }
            })
            .collect();
        MachineProof { shard_proofs }
    }

    #[inline]
    pub(crate) fn has_same_verifier_version(&self) -> bool {
        self.verifier_version == env!("VERGEN_GIT_SHA")
    }
}

impl From<MachineProof<BabyBearPoseidon2>> for CryptoProof {
    #[inline]
    fn from(value: MachineProof<BabyBearPoseidon2>) -> Self {
        let shard_proofs = value
            .shard_proofs
            .into_iter()
            .map(|sp| {
                let ShardProof {
                    commitment,
                    opened_values,
                    opening_proof,
                    chip_ordering,
                    ..
                } = sp;
                CryptoShardProof {
                    commitment,
                    opened_values,
                    opening_proof,
                    chip_ordering,
                }
            })
            .collect();
        Self {
            shard_proofs,
            verifier_version: env!("VERGEN_GIT_SHA").to_string(),
        }
    }
}

/// Carries a cryptographic proof and the Lurk data for its public values
#[derive(Serialize, Deserialize)]
pub(crate) struct IOProof {
    pub(crate) crypto_proof: CryptoProof,
    pub(crate) expr: ZPtr<F>,
    pub(crate) env: ZPtr<F>,
    pub(crate) result: ZPtr<F>,
    pub(crate) zdag: ZDag<F>,
}

impl IOProof {
    pub(crate) fn new<H: Chipset<F>>(
        crypto_proof: CryptoProof,
        public_values: &[F],
        zstore: &ZStore<F, H>,
    ) -> Self {
        let mut zdag = ZDag::default();
        let (expr_data, rest) = public_values.split_at(ZPTR_SIZE);
        let (env_digest, result_data) = rest.split_at(DIGEST_SIZE);
        let expr = ZPtr::from_flat_data(expr_data);
        let env = ZPtr::from_flat_digest(Tag::Env, env_digest);
        let result = ZPtr::from_flat_data(result_data);
        zdag.populate_with_many([&expr, &env, &result], zstore);
        Self {
            crypto_proof,
            expr,
            env,
            result,
            zdag,
        }
    }

    #[inline]
    pub(crate) fn into_machine_proof(self) -> MachineProof<BabyBearPoseidon2> {
        let Self {
            crypto_proof,
            expr,
            env,
            result,
            ..
        } = self;
        crypto_proof.into_machine_proof(&expr, &env, &result)
    }
}

#[derive(Serialize, Deserialize)]
pub(crate) struct ProtocolProof {
    pub(crate) crypto_proof: CryptoProof,
    pub(crate) args: LurkData<F>,
}

impl ProtocolProof {
    #[inline]
    pub(crate) fn new<H: Chipset<F>>(
        crypto_proof: CryptoProof,
        args: ZPtr<F>,
        zstore: &ZStore<F, H>,
    ) -> Self {
        Self {
            crypto_proof,
            args: LurkData::new(args, zstore),
        }
    }
}
