//! Conditional `if` clause
// Ignore xclippy for now -- it really doesn't like the macro :(
#![allow(clippy::all)]

use ascent::ascent;
use loam_macros::loam;

ascent! {
    // Facts:
    relation number(isize);

    // Rules:
    relation fib(isize, isize);
    relation fib_table(isize, isize, isize);

    fib(0, 1) <-- number(0);
    fib(1, 1) <-- number(1);
    fib_table(x, y, z), fib(x, y + z) <-- number(x), if *x >= 2, fib(x - 1, y), fib(x - 2, z);
    // basically collect the queries on the RHS into a tuple, so
    // - number(x) -> x
    // - fib(x - 1, y) -> y
    // - fib(x - 2, z) ->  z
    // and in total we get x, x-1, y, x-2, z
    // fib_table(x, y, z) <-- number(x), if *x >= 2, fib(x - 1, y), fib(x - 2, z);
}

loam! {
    struct FibProgram;

    // Facts:
    // #[distill(preserve)]
    relation number(isize);

    // Rules:
    relation fib(isize, isize);

    #[with_bindings(this_does_nothing)]
    fib(0, 1) <-- number(0);
    fib(1, 1) <-- number(1);

    #[with_bindings(fib_table_2)]
    fib(x, y + z) <-- number(x), if *x >= 2, fib(x - 1, y), fib(x - 2, z);
}

fn main() {
    let mut ascent_prog = AscentProgram::default();
    ascent_prog.number = (0..6).map(|n| (n,)).collect();
    ascent_prog.run();

    let AscentProgram { mut fib_table, .. } = ascent_prog;

    let mut loam_prog = FibProgram::default();
    loam_prog.number = (0..6).map(|n| (n,)).collect();
    loam_prog.run();

    let FibProgram {
        mut fib_table_2, ..
    } = loam_prog;

    fib_table.sort_by_key(|(key, _, _)| *key);
    println!("{:?}", fib_table);

    fib_table_2.sort_by_key(|(key, _, _)| *key);
    println!("{:?}", fib_table_2);

    assert_eq!(fib_table, fib_table_2);
    println!("success!");

    let mut distilled_program = DistilledFibProgram::default();
    distilled_program.number = (0..6).map(|n| (n,)).collect();
    distilled_program.fib = vec![(0, 1), (1, 1)];
    distilled_program.run();

    let DistilledFibProgram { fib, .. } = distilled_program;

    println!("fib: {:?}", fib);
}
