use criterion::{criterion_group, criterion_main, Criterion};
use std::time::Duration;

use loam::lurk::eval_direct::build_lurk_toplevel_native;

fn toplevel(c: &mut Criterion) {
    c.bench_function("toplevel", |b| {
        b.iter(|| {
            build_lurk_toplevel_native();
        })
    });
}

criterion_group! {
    name = lurk;
    config = Criterion::default().measurement_time(Duration::from_secs(9));
    targets =
        toplevel,
}

criterion_main!(lurk);
