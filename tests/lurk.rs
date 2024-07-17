// Usage: `cargo nextest run -E 'test(lurk_toplevel)' --nocapture --run-ignored all`
use std::time::Instant;

use loam::lurk::eval::build_lurk_toplevel;

#[ignore]
#[test]
fn lurk_toplevel() {
    let start_time = Instant::now();

    build_lurk_toplevel();

    let elapsed_time = start_time.elapsed().as_millis();
    println!("Total time for toplevel = {:.2} ms", elapsed_time);
}
