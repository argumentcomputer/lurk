//! A simple program to be proven inside the zkVM.

#![no_main]
wp1_zkvm::entrypoint!(main);

use ski::{Term, Mem, SKI};

//  INFO summary: cycles=254197, e2e=4552, khz=55.84, proofSize=1.24 MiB
// (S(K(SI))K)KI evaled to K
#[allow(dead_code)]
pub fn main() {
    let ski = wp1_zkvm::io::read::<SKI>();
    let mem = &mut Mem::new();
    let term = Term::try_from_ski(mem, &ski).unwrap();
    let evaled = term.eval(mem, 0).to_ski(mem);

    wp1_zkvm::io::commit(&evaled);
}
