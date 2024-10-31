use anyhow::Result;
use clap::Args;
use p3_baby_bear::BabyBear;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use sphinx_core::stark::StarkGenericConfig;
use std::{
    io::{Read, Write},
    net::{TcpListener, TcpStream},
};

use crate::{
    lair::{chipset::Chipset, lair_chip::LairMachineProgram},
    lurk::{
        chipset::LurkChip,
        cli::rdg::rand_digest,
        eval_direct::build_lurk_toplevel,
        lang::Lang,
        stark_machine::new_machine,
        zstore::{ZPtr, ZStore, DIGEST_SIZE},
    },
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

#[derive(Serialize, Deserialize, Clone)]
pub(crate) enum CallableData {
    Comm(CommData<F>),
    Fun(LurkData<F>),
}

impl CallableData {
    fn has_opaque_data(&self) -> bool {
        match self {
            Self::Comm(comm_data) => comm_data.payload_has_opaque_data(),
            Self::Fun(lurk_data) => lurk_data.has_opaque_data(),
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
#[derive(Serialize, Deserialize, Clone)]
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
    GetProofs([F; DIGEST_SIZE]),
}

#[derive(Serialize, Deserialize)]
pub(crate) enum Response {
    BadRequest,
    IdSecret([F; DIGEST_SIZE]),
    NoDataForId,
    Genesis([F; DIGEST_SIZE], ChainState),
    State(ChainState),
    ChainResultIsOpaque,
    NextCallableIsOpaque,
    ProofVerificationFailed(String),
    ProofAccepted,
    Proofs(Vec<OpaqueChainProof>),
}

/// Holds the data for a microchain, mapped from an ID
struct ChainData {
    /// The data for the genesis state also contains the secret used to generate
    /// the microchain ID
    genesis: ([F; DIGEST_SIZE], ChainState),
    /// Sequence of chain proofs, from the first transition to the latest
    proofs: Vec<OpaqueChainProof>,
    /// Current state of a microchain
    state: ChainState,
}

impl MicrochainArgs {
    pub(crate) fn run(self) -> Result<()> {
        let MicrochainArgs { addr } = self;
        let listener = TcpListener::bind(&addr)?;
        println!("Listening at {addr}");

        let (toplevel, mut zstore, _) = build_lurk_toplevel(Lang::empty());
        let empty_env = zstore.intern_empty_env();

        // chain id -> chain data
        let mut chains = FxHashMap::default();

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
                            if chain_state.chain_result.has_opaque_data() {
                                return_msg!(Response::ChainResultIsOpaque);
                            }
                            if chain_state.callable_data.has_opaque_data() {
                                return_msg!(Response::NextCallableIsOpaque);
                            }

                            let id_secret = rand_digest();
                            let callable_zptr = chain_state.callable_data.zptr(&mut zstore);
                            let state_cons =
                                zstore.intern_cons(chain_state.chain_result.zptr, callable_zptr);
                            let id = CommData::hash(&id_secret, &state_cons, &mut zstore);

                            let chain_data = ChainData {
                                genesis: (id_secret, chain_state.clone()),
                                proofs: vec![],
                                state: chain_state,
                            };
                            assert!(chains.insert(id, chain_data).is_none());
                            return_msg!(Response::IdSecret(id_secret));
                        }
                        Request::GetGenesis(id) => {
                            let Some(ChainData {
                                genesis: (id_secret, state),
                                ..
                            }) = chains.get(&id)
                            else {
                                return_msg!(Response::NoDataForId);
                            };
                            return_msg!(Response::Genesis(*id_secret, state.clone()))
                        }
                        Request::GetState(id) => {
                            let Some(ChainData { state, .. }) = chains.get(&id) else {
                                return_msg!(Response::NoDataForId);
                            };
                            return_msg!(Response::State(state.clone()));
                        }
                        Request::Transition(id, chain_proof) => {
                            let Some(ChainData { proofs, state, .. }) = chains.get_mut(&id) else {
                                return_msg!(Response::NoDataForId);
                            };

                            let ChainProof {
                                crypto_proof,
                                call_args,
                                next_chain_result,
                                next_callable,
                            } = chain_proof;

                            let next_chain_result_zptr = {
                                if next_chain_result.has_opaque_data() {
                                    return_msg!(Response::ChainResultIsOpaque);
                                }
                                next_chain_result.zptr
                            };

                            let next_callable_zptr = match &next_callable {
                                CallableData::Comm(comm_data) => {
                                    if comm_data.payload_has_opaque_data() {
                                        return_msg!(Response::NextCallableIsOpaque);
                                    }
                                    comm_data.commit(&mut zstore)
                                }
                                CallableData::Fun(lurk_data) => {
                                    if lurk_data.has_opaque_data() {
                                        return_msg!(Response::NextCallableIsOpaque);
                                    }
                                    lurk_data.zptr
                                }
                            };

                            // the expression is a call whose callable is part of the server state
                            // and the arguments are provided by the client
                            let callable_zptr = state.callable_data.zptr(&mut zstore);
                            let expr = zstore.intern_cons(callable_zptr, call_args);

                            // the result is a pair composed by the chain result and next callable
                            // provided by the client
                            let result =
                                zstore.intern_cons(next_chain_result_zptr, next_callable_zptr);

                            // and now the proof must verify, meaning that the user must have
                            // used the correct callable from the server state
                            let machine_proof =
                                crypto_proof.into_machine_proof(&expr, &empty_env, &result);
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

                            // update the state
                            *state = ChainState {
                                chain_result: next_chain_result,
                                callable_data: next_callable,
                            };

                            return_msg!(Response::ProofAccepted);
                        }
                        Request::GetProofs(id) => {
                            let Some(ChainData { proofs, .. }) = chains.get(&id) else {
                                return_msg!(Response::NoDataForId);
                            };
                            return_msg!(Response::Proofs(proofs.clone()));
                        }
                    }
                }
                Err(e) => eprintln!("Connection failed: {e}"),
            }
        }

        Ok(())
    }
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
