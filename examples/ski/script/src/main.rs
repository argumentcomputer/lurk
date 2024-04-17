//! A simple script to generate and verify the proof of a given program.
use std::str::FromStr;

const ELF: &[u8] = include_bytes!("../../program/elf/riscv32im-succinct-zkvm-elf");

use wp1_sdk::{utils, ProverClient, SP1Stdin};

use ski::SKI;

fn main() {
    // Setup a tracer for logging.
    utils::setup_logger();

    // Generate proof.
    let mut stdin = SP1Stdin::new();
    let ski = SKI::from_str(&"(S(K(SI))K)KI").unwrap();
    stdin.write(&ski);

    let client = ProverClient::new();
    let mut proof = client.prove(ELF, stdin).expect("proving failed");

    // Read output.
    let evaled = proof.public_values.read::<SKI>();
    assert_eq!("K", evaled.to_string());
    println!("{ski} evaled to {evaled}");

    // Verify proof.
    client.verify(ELF, &proof).expect("verification failed");

    // Save proof.
    proof
        .save("proof-with-io.json")
        .expect("saving proof failed");

    println!("successfully generated and verified proof for the program!")
}
