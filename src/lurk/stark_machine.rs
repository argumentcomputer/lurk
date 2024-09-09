use p3_baby_bear::BabyBear;
use sphinx_core::{
    stark::StarkMachine,
    utils::{BabyBearPoseidon2, DIGEST_SIZE},
};

use crate::lair::{
    chipset::Chipset,
    func_chip::FuncChip,
    lair_chip::{build_chip_vector, LairChip},
    toplevel::Toplevel,
};

use super::zstore::ZPTR_SIZE;

pub(crate) const INPUT_SIZE: usize = ZPTR_SIZE + DIGEST_SIZE;
pub(crate) const NUM_PUBLIC_VALUES: usize = INPUT_SIZE + ZPTR_SIZE;

/// Returns a `StarkMachine` for the Lurk toplevel, with `lurk_main` as entrypoint
pub(crate) fn new_machine<C1: Chipset<BabyBear>, C2: Chipset<BabyBear>>(
    lurk_toplevel: &Toplevel<BabyBear, C1, C2>,
) -> StarkMachine<BabyBearPoseidon2, LairChip<BabyBear, C1, C2>> {
    let lurk_main_idx = lurk_toplevel.func_by_name("lurk_main").index;
    let lurk_main_chip = FuncChip::from_index(lurk_main_idx, lurk_toplevel);
    StarkMachine::new(
        BabyBearPoseidon2::new(),
        build_chip_vector(&lurk_main_chip),
        NUM_PUBLIC_VALUES,
    )
}
