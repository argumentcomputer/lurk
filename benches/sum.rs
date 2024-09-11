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
        chipset::Chipset,
        execute::{QueryRecord, Shard},
        func_chip::FuncChip,
        lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
        toplevel::Toplevel,
        List,
    },
    lurk::{
        eval::build_lurk_toplevel,
        zstore::{lurk_zstore, ZPtr},
    },
};

const DEFAULT_SUM_ARG: usize = 100000;

fn get_sum_arg() -> usize {
    std::env::var("LOAM_SUM_ARG")
        .unwrap_or(DEFAULT_SUM_ARG.to_string())
        .parse::<usize>()
        .expect("Expected a number")
}

fn u64s_below(n: usize) -> String {
    (0..n).map(|i| format!("{i}")).collect::<Vec<_>>().join(" ")
}

fn build_lurk_expr(n: usize) -> String {
    let input = u64s_below(n);
    format!(
        "
(letrec ((sum (lambda (l) (if l (+ (car l) (sum (cdr l))) 0))))
  (sum '({input})))
"
    )
}

fn setup<H: Chipset<BabyBear>>(
    n: usize,
    toplevel: &Toplevel<BabyBear, H>,
) -> (
    List<BabyBear>,
    FuncChip<'_, BabyBear, H>,
    QueryRecord<BabyBear>,
) {
    let code = build_lurk_expr(n);

    let zstore = &mut lurk_zstore();
    let ZPtr { tag, digest } = zstore.read(&code).unwrap();

    let mut record = QueryRecord::new(toplevel);
    record.inject_inv_queries("hash_32_8", toplevel, &zstore.hashes4);

    let mut full_input = [BabyBear::zero(); 24];
    full_input[0] = tag.to_field();
    full_input[8..16].copy_from_slice(&digest);

    let args: List<_> = full_input.into();
    let lurk_main = FuncChip::from_name("lurk_main", toplevel);

    (args, lurk_main, record)
}

fn evaluation(c: &mut Criterion) {
    let arg = get_sum_arg();
    c.bench_function(&format!("sum-evaluation-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(arg, &toplevel);
        b.iter_batched(
            || (args.clone(), record.clone()),
            |(args, mut queries)| {
                toplevel
                    .execute(lurk_main.func(), &args, &mut queries, None)
                    .unwrap();
            },
            BatchSize::SmallInput,
        )
    });
}

fn trace_generation(c: &mut Criterion) {
    let arg = get_sum_arg();
    c.bench_function(&format!("sum-trace-generation-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, mut record) = setup(arg, &toplevel);
        toplevel
            .execute(lurk_main.func(), &args, &mut record, None)
            .unwrap();
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
    let arg = get_sum_arg();
    c.bench_function(&format!("sum-e2e-{arg}"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(arg, &toplevel);

        b.iter_batched(
            || (record.clone(), args.clone()),
            |(mut record, args)| {
                toplevel
                    .execute(lurk_main.func(), &args, &mut record, None)
                    .unwrap();
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
    name = sum_benches;
    config = Criterion::default()
                .measurement_time(Duration::from_secs(15))
                .sample_size(10);
    targets =
        evaluation,
        trace_generation,
        e2e,
}

// FIXME: bench fails to run when ARG is supplied, for some reason.
// `cargo criterion --bench sum -- <ARG>` to benchmark sum of <ARG>
// `cargo criterion --bench sum` to benchmark sum of `DEFAULT_SUM_ARG`
criterion_main!(sum_benches);
