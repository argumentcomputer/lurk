use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::{mem::take, time::Duration};

use loam::{
    lair::{
        chip::FuncChip,
        execute::QueryRecord,
        hasher::{Hasher, LurkHasher},
        toplevel::Toplevel,
        List,
    },
    lurk::{
        eval::build_lurk_toplevel,
        memory::Memory,
        zstore::{PoseidonBabyBearHasher, ZStore},
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
                (if (= n 0) 1
                    (if (= n 1) 1
                    (+ (fib (- n 1)) (fib (- n 2))))))))
            (fib {arg}))"
    )
}

fn setup<'a, H: Hasher<BabyBear>>(
    arg: usize,
    mem: &mut Memory<BabyBear, PoseidonBabyBearHasher>,
    store: &ZStore<BabyBear, PoseidonBabyBearHasher>,
    toplevel: &'a Toplevel<BabyBear, H>,
) -> (
    List<BabyBear>,
    FuncChip<'a, BabyBear, H>,
    QueryRecord<BabyBear>,
) {
    let mut queries = QueryRecord::new_with_init_mem(toplevel, take(&mut mem.map));

    mem.map = take(&mut queries.mem_queries);
    let expr = mem.read_and_ingress(&build_lurk_expr(arg), store).unwrap();
    queries.mem_queries = take(&mut mem.map);

    let env = BabyBear::zero();

    let args: List<_> = [expr.tag, expr.raw, env].into();

    let eval = FuncChip::from_name("eval", toplevel);

    (args, eval, queries)
}

fn evaluation(c: &mut Criterion) {
    let arg = get_fib_arg();
    c.bench_function(&format!("evaluation-{arg}"), |b| {
        let mem = &mut Memory::init();
        let store = ZStore::<BabyBear, PoseidonBabyBearHasher>::new();
        let toplevel = build_lurk_toplevel::<_, _, LurkHasher>(mem, &store);
        let (args, eval, queries) = setup(arg, mem, &store, &toplevel);

        b.iter_batched(
            || (args.clone(), queries.clone()),
            |(args, mut queries)| {
                eval.execute_iter(args, &mut queries);
            },
            BatchSize::SmallInput,
        )
    });
}

fn trace_generation(c: &mut Criterion) {
    let arg = get_fib_arg();
    c.bench_function(&format!("trace-generation-{arg}"), |b| {
        let mem = &mut Memory::init();
        let store = ZStore::<BabyBear, PoseidonBabyBearHasher>::new();
        let toplevel = build_lurk_toplevel::<_, _, LurkHasher>(mem, &store);
        let (args, eval, mut queries) = setup(arg, mem, &store, &toplevel);

        eval.execute_iter(args, &mut queries);

        let func_chips = FuncChip::from_toplevel(&toplevel);

        b.iter(|| {
            func_chips.par_iter().for_each(|func_chip| {
                func_chip.generate_trace_parallel(&queries);
            })
        })
    });
}

criterion_group! {
    name = fib_benches;
    config = Criterion::default().measurement_time(Duration::from_secs(9));
    targets =
        evaluation,
        trace_generation,
}

// `cargo criterion --bench fib -- <ARG>` to benchmark fib of <ARG>
// `cargo criterion --bench fib` to benchmark fib of `DEFAULT_FIB_ARG`
criterion_main!(fib_benches);
