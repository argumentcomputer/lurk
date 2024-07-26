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

fn get_lcs_args() -> (&'static str, &'static str) {
    (
        "when in the course of human events",
        "he only ever cares about saving himself",
    )
}

fn build_lurk_expr(a: &str, b: &str) -> String {
    format!(
        r#"
(letrec ((longer (lambda (a b)
                   (letrec ((aux (lambda (a b orig-a orig-b)
                                   (if (eq a "")
                                       orig-b
                                       (if (eq b "")
                                           orig-a
                                           (aux (cdr a) (cdr b) orig-a orig-b))))))
                     (aux a b a b))))
         (lcs (lambda (a b)
                (if (eq a "") ""
                    (if (eq b "") ""
                        (if (eq (car a) (car b))
                            (strcons (car a) (lcs (cdr a) (cdr b)))
                            (longer (lcs a (cdr b)) (lcs (cdr a) b))))))))
  (lcs "{a}" "{b}"))"#
    )
}

fn setup<'a, H: Chipset<BabyBear>>(
    a: &'a str,
    b: &'a str,
    toplevel: &'a Toplevel<BabyBear, H>,
) -> (
    List<BabyBear>,
    FuncChip<'a, BabyBear, H>,
    QueryRecord<BabyBear>,
) {
    let code = build_lurk_expr(a, b);
    let zstore = &mut lurk_zstore();
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
    let args = get_lcs_args();
    c.bench_function(&format!("evaluation"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(args.0, args.1, &toplevel);
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
    let args = get_lcs_args();
    c.bench_function(&format!("trace-generation"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, mut record) = setup(args.0, args.1, &toplevel);
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
    let args = get_lcs_args();
    c.bench_function(&format!("e2e"), |b| {
        let (toplevel, _) = build_lurk_toplevel();
        let (args, lurk_main, record) = setup(args.0, args.1, &toplevel);

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
    name = lcs_benches;
    config = Criterion::default()
                .measurement_time(Duration::from_secs(15))
                .sample_size(10);
    targets =
        evaluation,
        trace_generation,
        e2e,
}

// `cargo criterion --bench lcs
criterion_main!(lcs_benches);
