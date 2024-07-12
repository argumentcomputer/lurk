use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use sphinx_core::{
    air::MachineAir,
    stark::{LocalProver, StarkGenericConfig, StarkMachine},
    utils::{BabyBearPoseidon2, SphinxCoreOpts},
};
use std::time::Duration;

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
    std::env::args()
        .collect::<Vec<_>>()
        .get(2)
        .map_or(DEFAULT_FIB_ARG, |a| a.parse().expect("failed to parse arg"))
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

fn evaluation(c: &mut Criterion) {
    let arg = get_fib_arg();
    c.bench_function(&format!("evaluation-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(arg, &toplevel);
        b.iter_batched(
            || (args.clone(), record.clone()),
            |(args, mut queries)| {
                toplevel.execute(lurk_main.func(), &args, &mut queries);
            },
            BatchSize::SmallInput,
        )
    });
}

fn trace_generation(c: &mut Criterion) {
    let arg = get_fib_arg();
    c.bench_function(&format!("trace-generation-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, mut record) = setup(arg, &toplevel);
        toplevel.execute(lurk_main.func(), &args, &mut record);
        let lair_chips = build_lair_chip_vector(&lurk_main);
        b.iter(|| {
            lair_chips.par_iter().for_each(|func_chip| {
                let shard = Shard::new(&record);
                func_chip.generate_trace(&shard, &mut Default::default());
            })
        })
    });
}

fn e2e(c: &mut Criterion) {
    let arg = get_fib_arg();
    c.bench_function(&format!("e2e-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(arg, &toplevel);

        b.iter_batched(
            || (record.clone(), args.clone()),
            |(mut record, args)| {
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
            },
            BatchSize::SmallInput,
        )
    });
}

criterion_group! {
    name = fib_benches;
    config = Criterion::default()
                .measurement_time(Duration::from_secs(15))
                .sample_size(10);
    targets =
        evaluation,
        trace_generation,
        e2e,
}

// `cargo criterion --bench fib -- <ARG>` to benchmark fib of <ARG>
// `cargo criterion --bench fib` to benchmark fib of `DEFAULT_FIB_ARG`
criterion_main!(fib_benches);
