// Usage: `LOAM_FIB_ARG=<ARG> cargo nextest run -E 'test(<test-name>)' --nocapture --run-ignored all`
// where <ARG> is the fibonacci input
// If `LOAM_FIB_ARG` is unset, the tests will run with `DEFAULT_FIB_ARG=500`
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use sphinx_core::{
    air::MachineAir,
    stark::{LocalProver, StarkGenericConfig, StarkMachine},
    utils::{BabyBearPoseidon2, SphinxCoreOpts},
};
use std::time::Instant;

use loam::{
    lair::{
        execute::{QueryRecord, Shard},
        func_chip::FuncChip,
        hasher::{Hasher, LurkHasher},
        lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
        toplevel::Toplevel,
        List,
    },
    lurk::{
        eval::build_lurk_toplevel,
        zstore::{ZPtr, ZStore},
    },
};

const DEFAULT_FIB_ARG: usize = 500;

fn get_fib_arg() -> usize {
    std::env::var("LOAM_FIB_ARG")
        .unwrap_or(DEFAULT_FIB_ARG.to_string())
        .parse::<usize>()
        .expect("Expected a number")
}

fn build_lurk_expr(arg: usize) -> String {
    format!(
        "(letrec ((fib
                (lambda (n)
                (if (= n 0) 0
                    (if (= n 1) 1
                    (+ (fib (- n 1)) (fib (- n 2))))))))
            (fib {arg}))"
    )
}

fn setup<H: Hasher<BabyBear>>(
    arg: usize,
    toplevel: &Toplevel<BabyBear, H>,
) -> (
    List<BabyBear>,
    FuncChip<'_, BabyBear, H>,
    QueryRecord<BabyBear>,
) {
    let code = build_lurk_expr(arg);
    let zstore = &mut ZStore::<_, LurkHasher>::default();
    let ZPtr { tag, digest } = zstore.read(&code).unwrap();

    let mut record = QueryRecord::new(toplevel);
    record.inject_inv_queries("hash_32_8", toplevel, zstore.tuple2_hashes());

    let mut full_input = [BabyBear::zero(); 24];
    full_input[0] = tag.to_field();
    full_input[8..16].copy_from_slice(&digest);

    let args: List<_> = full_input.into();
    let lurk_main = FuncChip::from_name("lurk_main", toplevel);

    (args, lurk_main, record)
}

#[ignore]
#[test]
fn fib_evaluation() {
    let arg = get_fib_arg();
    let (toplevel, _) = build_lurk_toplevel();
    let (args, lurk_main, mut record) = setup(arg, &toplevel);
    let start_time = Instant::now();

    toplevel.execute(lurk_main.func(), &args, &mut record);

    let elapsed_time = start_time.elapsed().as_millis();
    println!("Total time for evaluation-{arg} = {:.2} ms", elapsed_time);
}

#[ignore]
#[test]
fn fib_trace_generation() {
    let arg = get_fib_arg();
    let (toplevel, _) = build_lurk_toplevel();
    let (args, lurk_main, mut record) = setup(arg, &toplevel);
    let start_time = Instant::now();

    toplevel.execute(lurk_main.func(), &args, &mut record);
    let lair_chips = build_lair_chip_vector(&lurk_main);
    lair_chips.par_iter().for_each(|func_chip| {
        let shard = Shard::new(&record);
        func_chip.generate_trace(&shard, &mut Default::default());
    });

    let elapsed_time = start_time.elapsed().as_millis();
    println!(
        "Total time for trace-generation-{arg} = {:.2} ms",
        elapsed_time
    );
}

#[ignore]
#[test]
fn fib_e2e() {
    let arg = get_fib_arg();
    let (toplevel, _) = build_lurk_toplevel();
    let (args, lurk_main, mut record) = setup(arg, &toplevel);
    let start_time = Instant::now();

    toplevel.execute(lurk_main.func(), &args, &mut record);
    let config = BabyBearPoseidon2::new();
    let machine = StarkMachine::new(
        config,
        build_chip_vector(&lurk_main),
        record.expect_public_values().len(),
    );
    let (pk, _) = machine.setup(&LairMachineProgram);
    let mut challenger_p = machine.config().challenger();
    let opts = SphinxCoreOpts::default();
    let shard = Shard::new(&record);
    machine.prove::<LocalProver<_, _>>(&pk, shard, &mut challenger_p, opts);

    let elapsed_time = start_time.elapsed().as_secs_f32();
    println!("Total time for e2e-{arg} = {:.2} s", elapsed_time);
}
