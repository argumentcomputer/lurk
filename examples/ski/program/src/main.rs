//! A simple program to be proven inside the zkVM.

#![no_main]
wp1_zkvm::entrypoint!(main);

use ski::{Mem, Term, SKI};

// INFO summary: cycles=204758, e2e=3709, khz=55.21, proofSize=1.16 MiB
// (S(K(SI))K)KI evaled to K
#[allow(dead_code)]
pub fn main() {
    let ski = wp1_zkvm::io::read::<SKI>();
    let mem = &mut Mem::new();
    let term = Term::try_from_ski(mem, &ski).unwrap();
    let evaled = term.eval(mem, 0).to_ski(mem);

    wp1_zkvm::io::commit(&evaled);
}
