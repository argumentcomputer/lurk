use p3_field::PrimeField32;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha20Rng;

/// A random digest generator whose randomness is initiated from system entropy
/// everytime it's called.
pub(crate) fn rand_digest<F: PrimeField32, const SIZE: usize>() -> [F; SIZE] {
    let mut rng = ChaCha20Rng::from_entropy();
    let mut res = [F::zero(); SIZE];
    for limb in res.iter_mut().take(SIZE) {
        *limb = F::from_canonical_u32(rng.gen_range(0..F::ORDER_U32));
    }
    res
}
