mod eval_compiled;
mod eval_direct;
mod eval_ocaml;
mod lang_compiled;
mod lang_direct;

use p3_baby_bear::BabyBear as F;
use p3_field::AbstractField;
use sphinx_core::{stark::StarkMachine, utils::BabyBearPoseidon2};

use crate::{
    air::debug::debug_chip_constraints_and_queries_with_sharding,
    lair::{
        chipset::Chipset,
        execute::{QueryRecord, Shard, ShardingConfig},
        func_chip::FuncChip,
        lair_chip::{
            build_chip_vector_from_lair_chips, build_lair_chip_vector, LairMachineProgram,
        },
        toplevel::Toplevel,
    },
    lurk::{
        chipset::LurkChip,
        zstore::{ZPtr, ZStore},
    },
};

use super::state::user_sym;

fn run_tests<C2: Chipset<F>>(
    zptr: &ZPtr<F>,
    env: &ZPtr<F>,
    toplevel: &Toplevel<F, LurkChip, C2>,
    zstore: &mut ZStore<F, LurkChip>,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
    config: BabyBearPoseidon2,
) {
    let mut record = QueryRecord::new(toplevel);
    let hashes3 = std::mem::take(&mut zstore.hashes3_diff);
    let hashes4 = std::mem::take(&mut zstore.hashes4_diff);
    let hashes5 = std::mem::take(&mut zstore.hashes5_diff);
    record.inject_inv_queries_owned("hash3", toplevel, hashes3);
    record.inject_inv_queries_owned("hash4", toplevel, hashes4);
    record.inject_inv_queries_owned("hash5", toplevel, hashes5);

    let mut input = [F::zero(); 24];
    input[..16].copy_from_slice(&zptr.flatten());
    input[16..].copy_from_slice(&env.digest);

    let lurk_main = FuncChip::from_name("lurk_main", toplevel);
    let result = toplevel
        .execute(lurk_main.func, &input, &mut record, None)
        .unwrap();

    assert_eq!(result.as_ref(), &expected_cloj(zstore).flatten());

    let lair_chips = build_lair_chip_vector(&lurk_main);

    // debug constraints and verify lookup queries with and without sharding
    debug_chip_constraints_and_queries_with_sharding(&record, &lair_chips, None);
    debug_chip_constraints_and_queries_with_sharding(
        &record,
        &lair_chips,
        Some(ShardingConfig { max_shard_size: 4 }),
    );

    // debug constraints with Sphinx
    let full_shard = Shard::new(&record);
    let machine = StarkMachine::new(
        config,
        build_chip_vector_from_lair_chips(lair_chips),
        record.expect_public_values().len(),
    );
    let (pk, _) = machine.setup(&LairMachineProgram);
    machine.debug_constraints(&pk, full_shard);
}

fn trivial_id_fun(zstore: &mut ZStore<F, LurkChip>) -> ZPtr<F> {
    let x = zstore.intern_symbol_no_lang(&user_sym("x"));
    let list_x = zstore.intern_list([x]);
    let env = zstore.intern_empty_env();
    zstore.intern_fun(list_x, list_x, env)
}

fn trivial_a_1_env(zstore: &mut ZStore<F, LurkChip>) -> ZPtr<F> {
    let empty_env = zstore.intern_empty_env();
    let a = zstore.intern_symbol_no_lang(&user_sym("a"));
    let one = uint(1);
    zstore.intern_env(a, one, empty_env)
}

fn uint(u: u64) -> ZPtr<F> {
    ZPtr::u64(u)
}

fn int64(i: i64) -> ZPtr<F> {
    ZPtr::i64(i)
}

fn int63(i: i64) -> ZPtr<F> {
    ZPtr::i63(i.into())
}
