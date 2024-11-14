use anyhow::Result;
use clap::Args;
use p3_baby_bear::BabyBear;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sphinx_core::stark::StarkGenericConfig;
use std::{
    hash::Hash,
    io::{Read, Write},
    net::{TcpListener, TcpStream},
};

use crate::{
    core::{
        big_num::field_elts_to_biguint,
        chipset::LurkChip,
        cli::{paths::microchains_dir, rdg::rand_digest},
        eval_direct::build_lurk_toplevel,
        lang::Lang,
        stark_machine::new_machine,
        zstore::{ZPtr, ZStore, DIGEST_SIZE},
    },
    lair::{chipset::Chipset, lair_chip::LairMachineProgram},
};

use super::{
    comm_data::CommData,
    lurk_data::LurkData,
    proofs::get_verifier_version,
    proofs::{ChainProof, OpaqueChainProof},
};

#[derive(Args, Debug)]
pub(crate) struct MicrochainArgs {
    // The IP address with the port. E.g. "127.0.0.1:1234"
    #[clap(value_parser)]
    addr: String,
}

type F = BabyBear;

#[derive(Serialize, Deserialize)]
pub(crate) enum CallableData {
    Comm(CommData<F>),
    Fun(LurkData<F>),
}

impl CallableData {
    fn is_flawed(&self, zstore: &mut ZStore<F, LurkChip>) -> bool {
        match self {
            Self::Comm(comm_data) => comm_data.payload_is_flawed(zstore),
            Self::Fun(lurk_data) => lurk_data.is_flawed(zstore),
        }
    }

    fn zptr(&self, zstore: &mut ZStore<F, LurkChip>) -> ZPtr<F> {
        match self {
            Self::Comm(comm_data) => comm_data.commit(zstore),
            Self::Fun(lurk_data) => lurk_data.zptr,
        }
    }
}

/// Encodes a `(chain-result . callable)` pair, the result of chaining a callable.
/// The pair components carry the corresponding `ZDag`s in order to be fully
/// transferable between clients (through the server)
#[derive(Serialize, Deserialize)]
pub(crate) struct ChainState {
    pub(crate) chain_result: LurkData<F>,
    pub(crate) callable_data: CallableData,
}

impl ChainState {
    pub(crate) fn into_zptr<C1: Chipset<F>>(self, zstore: &mut ZStore<F, C1>) -> ZPtr<F> {
        let Self {
            chain_result,
            callable_data,
        } = self;
        let chain_result_zptr = chain_result.populate_zstore(zstore);
        let callable_zptr = match callable_data {
            CallableData::Comm(comm_data) => {
                let zptr = comm_data.commit(zstore);
                comm_data.populate_zstore(zstore);
                zptr
            }
            CallableData::Fun(lurk_data) => lurk_data.populate_zstore(zstore),
        };
        zstore.intern_cons(chain_result_zptr, callable_zptr)
    }
}

#[derive(Serialize, Deserialize)]
pub(crate) enum Request {
    Start(ChainState),
    GetGenesis([F; DIGEST_SIZE]),
    GetState([F; DIGEST_SIZE]),
    Transition([F; DIGEST_SIZE], ChainProof),
    GetProofs([F; DIGEST_SIZE], [F; DIGEST_SIZE], [F; DIGEST_SIZE]),
}

#[derive(Serialize, Deserialize)]
pub(crate) enum Response {
    BadRequest,
    IdSecret([F; DIGEST_SIZE]),
    NoDataForId,
    Genesis([F; DIGEST_SIZE], ChainState),
    State(ChainState),
    ChainResultIsFlawed,
    NextCallableIsFlawed,
    ProofVerificationFailed(String),
    ProofAccepted,
    NoProofForInitialState,
    NoProofForFinalState,
    Proofs(Vec<OpaqueChainProof>),
}

/// The data for the genesis state also contains the secret used to generate
/// the microchain ID
type Genesis = ([F; DIGEST_SIZE], ChainState);

impl MicrochainArgs {
    pub(crate) fn run(self) -> Result<()> {
        let MicrochainArgs { addr } = self;
        let listener = TcpListener::bind(&addr)?;
        println!("Listening at {addr}");

        let (toplevel, mut zstore, _) = build_lurk_toplevel(Lang::empty());
        let empty_env = zstore.intern_empty_env();

        for stream in listener.incoming() {
            match stream {
                Ok(mut stream) => {
                    macro_rules! return_msg {
                        ($data:expr) => {{
                            write_data(&mut stream, $data)?;
                            continue;
                        }};
                    }
                    let Ok(request) = read_data::<Request>(&mut stream) else {
                        return_msg!(Response::BadRequest);
                    };
                    match request {
                        Request::Start(chain_state) => {
                            if chain_state.chain_result.is_flawed(&mut zstore) {
                                return_msg!(Response::ChainResultIsFlawed);
                            }
                            if chain_state.callable_data.is_flawed(&mut zstore) {
                                return_msg!(Response::NextCallableIsFlawed);
                            }

                            let id_secret = rand_digest();
                            let callable_zptr = chain_state.callable_data.zptr(&mut zstore);
                            let state_cons =
                                zstore.intern_cons(chain_state.chain_result.zptr, callable_zptr);
                            let id = CommData::hash(&id_secret, &state_cons, &mut zstore);

                            dump_state(&id, &chain_state)?;
                            dump_genesis(&id, &(id_secret, chain_state))?;
                            dump_proofs(&id, &[])?;
                            return_msg!(Response::IdSecret(id_secret));
                        }
                        Request::GetGenesis(id) => {
                            let Ok((id_secret, genesis)) = load_genesis(&id) else {
                                return_msg!(Response::NoDataForId);
                            };
                            return_msg!(Response::Genesis(id_secret, genesis))
                        }
                        Request::GetState(id) => {
                            let Ok(state) = load_state(&id) else {
                                return_msg!(Response::NoDataForId);
                            };
                            return_msg!(Response::State(state));
                        }
                        Request::Transition(id, chain_proof) => {
                            let (Ok(mut proofs), Ok(state)) = (load_proofs(&id), load_state(&id))
                            else {
                                return_msg!(Response::NoDataForId);
                            };

                            let ChainProof {
                                crypto_proof,
                                call_args,
                                next_chain_result,
                                next_callable,
                            } = chain_proof;

                            let next_chain_result_zptr = {
                                if next_chain_result.is_flawed(&mut zstore) {
                                    return_msg!(Response::ChainResultIsFlawed);
                                }
                                next_chain_result.zptr
                            };

                            let next_callable_zptr = match &next_callable {
                                CallableData::Comm(comm_data) => {
                                    if comm_data.payload_is_flawed(&mut zstore) {
                                        return_msg!(Response::NextCallableIsFlawed);
                                    }
                                    comm_data.commit(&mut zstore)
                                }
                                CallableData::Fun(lurk_data) => {
                                    if lurk_data.is_flawed(&mut zstore) {
                                        return_msg!(Response::NextCallableIsFlawed);
                                    }
                                    lurk_data.zptr
                                }
                            };

                            // the expression is a call whose callable is part of the server state
                            // and the arguments are provided by the client
                            let callable_zptr = state.callable_data.zptr(&mut zstore);
                            let expr = zstore.intern_cons(callable_zptr, call_args);

                            // the next state is a pair composed by the chain result and next callable
                            // provided by the client
                            let next_state =
                                zstore.intern_cons(next_chain_result_zptr, next_callable_zptr);

                            // and now the proof must verify, meaning that the user must have
                            // used the correct callable from the server state
                            let machine_proof =
                                crypto_proof.into_machine_proof(&expr, &empty_env, &next_state);
                            let machine = new_machine(&toplevel);
                            let (_, vk) = machine.setup(&LairMachineProgram);
                            let challenger = &mut machine.config().challenger();
                            if machine.verify(&vk, &machine_proof, challenger).is_err() {
                                let verifier_version = get_verifier_version().to_string();
                                return_msg!(Response::ProofVerificationFailed(verifier_version));
                            }

                            // everything went okay... transition to the next state

                            // store new proof
                            proofs.push(OpaqueChainProof {
                                crypto_proof: machine_proof.into(),
                                call_args,
                                next_chain_result: next_chain_result_zptr,
                                next_callable: next_callable_zptr,
                            });
                            dump_proofs(&id, &proofs)?;

                            // update the state
                            dump_state(
                                &id,
                                &ChainState {
                                    chain_result: next_chain_result,
                                    callable_data: next_callable,
                                },
                            )?;

                            // update the proof index
                            let mut proof_index = load_proof_index(&id).unwrap_or_default();
                            let prev_chain_result_zptr = state.chain_result.zptr;
                            let prev_state =
                                zstore.intern_cons(prev_chain_result_zptr, callable_zptr);
                            proof_index.insert(
                                prev_state.digest,
                                next_state.digest,
                                proofs.len() - 1,
                            );
                            dump_proof_index(&id, &proof_index)?;

                            return_msg!(Response::ProofAccepted);
                        }
                        Request::GetProofs(id, initial_digest, final_digest) => {
                            let Ok(mut proofs) = load_proofs(&id) else {
                                return_msg!(Response::NoDataForId);
                            };
                            // let proof_index = load_proof_index(&id)?;
                            // let Some(initial_index) = proof_index.index_by_prev(&initial_digest) else {
                            //     return_msg!(Response::NoProofForInitialState);
                            // };
                            // let Some(final_index) = proof_index.index_by_next(&final_digest) else {
                            //     return_msg!(Response::NoProofForFinalState);
                            // };

                            // the following code snippet is only meant to support version transitioning
                            // and should be eliminated (in favor of the code above) once legacy microchains
                            // are dropped
                            let proof_index = load_proof_index(&id).unwrap_or_default();
                            let initial_index =
                                if let Some(index) = proof_index.index_by_prev(&initial_digest) {
                                    index
                                } else {
                                    let (_, genesis_state) = load_genesis(&id)?;
                                    let genesis_result_zptr = genesis_state.chain_result.zptr;
                                    let genesis_callable_zptr =
                                        genesis_state.callable_data.zptr(&mut zstore);
                                    let genesis_zptr = zstore
                                        .intern_cons(genesis_result_zptr, genesis_callable_zptr);
                                    if genesis_zptr.digest == initial_digest {
                                        0
                                    } else {
                                        let mut index = None;
                                        for (i, proof) in proofs.iter().enumerate() {
                                            let OpaqueChainProof {
                                                next_chain_result,
                                                next_callable,
                                                ..
                                            } = proof;
                                            let next_state = zstore
                                                .intern_cons(*next_chain_result, *next_callable);
                                            if next_state.digest == initial_digest {
                                                index = Some(i + 1);
                                                break;
                                            }
                                        }
                                        let Some(index) = index else {
                                            return_msg!(Response::NoProofForInitialState);
                                        };
                                        index
                                    }
                                };
                            let final_index =
                                if let Some(index) = proof_index.index_by_next(&final_digest) {
                                    index
                                } else {
                                    let mut index = None;
                                    for (i, proof) in proofs.iter().enumerate() {
                                        let OpaqueChainProof {
                                            next_chain_result,
                                            next_callable,
                                            ..
                                        } = proof;
                                        let next_state =
                                            zstore.intern_cons(*next_chain_result, *next_callable);
                                        if next_state.digest == final_digest {
                                            index = Some(i);
                                            break;
                                        }
                                    }
                                    let Some(index) = index else {
                                        return_msg!(Response::NoProofForFinalState);
                                    };
                                    index
                                };

                            proofs.truncate(final_index + 1);
                            proofs.drain(..initial_index);
                            return_msg!(Response::Proofs(proofs));
                        }
                    }
                }
                Err(e) => eprintln!("Connection failed: {e}"),
            }
        }

        Ok(())
    }
}

/// Holds indices of proofs in a sequence of state transitions. The index of a
/// proof can be looked up by the digest of the previous state or by the digest
/// of the next state.
#[derive(Serialize, Deserialize, Default)]
struct ProofIndex<F: Hash + Eq> {
    prev_map: FxHashMap<[F; DIGEST_SIZE], usize>,
    next_map: FxHashMap<[F; DIGEST_SIZE], usize>,
}

impl<F: Hash + Eq> ProofIndex<F> {
    fn insert(
        &mut self,
        prev_digest: [F; DIGEST_SIZE],
        next_digest: [F; DIGEST_SIZE],
        index: usize,
    ) {
        self.prev_map.insert(prev_digest, index);
        self.next_map.insert(next_digest, index);
    }

    fn index_by_prev(&self, digest: &[F]) -> Option<usize> {
        self.prev_map.get(digest).copied()
    }

    fn index_by_next(&self, digest: &[F]) -> Option<usize> {
        self.next_map.get(digest).copied()
    }
}

fn dump_microchain_data<T: Serialize + ?Sized>(id: &[F], name: &str, data: &T) -> Result<()> {
    let hash = format!("{:x}", field_elts_to_biguint(id));
    let dir = microchains_dir()?.join(hash);
    std::fs::create_dir_all(&dir)?;
    std::fs::write(dir.join(name), bincode::serialize(data)?)?;
    Ok(())
}

fn dump_genesis(id: &[F], genesis: &Genesis) -> Result<()> {
    dump_microchain_data(id, "genesis", genesis)
}

fn dump_proofs(id: &[F], proofs: &[OpaqueChainProof]) -> Result<()> {
    dump_microchain_data(id, "proofs", proofs)
}

fn dump_state(id: &[F], state: &ChainState) -> Result<()> {
    dump_microchain_data(id, "state", state)
}

fn dump_proof_index(id: &[F], proof_index: &ProofIndex<F>) -> Result<()> {
    dump_microchain_data(id, "proof_index", proof_index)
}

fn load_microchain_data<T: for<'a> Deserialize<'a>>(id: &[F], name: &str) -> Result<T> {
    let hash = format!("{:x}", field_elts_to_biguint(id));
    let bytes = std::fs::read(microchains_dir()?.join(hash).join(name))?;
    let data = bincode::deserialize(&bytes)?;
    Ok(data)
}

fn load_genesis(id: &[F]) -> Result<Genesis> {
    load_microchain_data(id, "genesis")
}

fn load_proofs(id: &[F]) -> Result<Vec<OpaqueChainProof>> {
    load_microchain_data(id, "proofs")
}

fn load_state(id: &[F]) -> Result<ChainState> {
    load_microchain_data(id, "state")
}

fn load_proof_index(id: &[F]) -> Result<ProofIndex<F>> {
    load_microchain_data(id, "proof_index")
}

pub(crate) fn read_data<T: for<'a> Deserialize<'a>>(stream: &mut TcpStream) -> Result<T> {
    let mut size_bytes = [0; 8];
    stream.read_exact(&mut size_bytes)?;
    let size = usize::from_le_bytes(size_bytes);
    let mut data_buffer = vec![0; size];
    stream.read_exact(&mut data_buffer)?;
    let data = bincode::deserialize(&data_buffer)?;
    Ok(data)
}

pub(crate) fn write_data<T: Serialize>(stream: &mut TcpStream, data: T) -> Result<()> {
    let data_bytes = bincode::serialize(&data)?;
    stream.write_all(&data_bytes.len().to_le_bytes())?;
    stream.write_all(&data_bytes)?;
    stream.flush()?;
    Ok(())
}
