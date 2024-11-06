use nom::Parser;
use once_cell::sync::OnceCell;
use sphinx_core::utils::BabyBearPoseidon2;

use crate::{
    core::{
        chipset::LurkChip,
        eval_direct::build_lurk_toplevel_native,
        parser::Span,
        state::State,
        tag::Tag,
        zstore::{ZPtr, ZStore},
    },
    lair::{chipset::NoChip, toplevel::Toplevel},
    ocaml::{
        compile::{compile_single_file_contents, transform_lambda_program},
        parser::syntax::parse_syntax,
    },
};

use p3_baby_bear::BabyBear as F;

use super::run_tests;

#[allow(clippy::type_complexity)]
static TEST_SETUP_DATA: OnceCell<(
    Toplevel<F, LurkChip, NoChip>,
    ZStore<F, LurkChip>,
    BabyBearPoseidon2,
)> = OnceCell::new();

fn test_setup_data() -> &'static (
    Toplevel<F, LurkChip, NoChip>,
    ZStore<F, LurkChip>,
    BabyBearPoseidon2,
) {
    TEST_SETUP_DATA.get_or_init(|| {
        let (toplevel, zstore, _) = build_lurk_toplevel_native();
        let config = BabyBearPoseidon2::new();
        (toplevel, zstore, config)
    })
}

fn test_case(
    test_name: &str,
    ocaml_source: &str,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
) {
    let (toplevel, zstore, config) = test_setup_data();
    let state = State::init_lurk_state().rccell();
    let mut zstore = zstore.clone();

    let lambda_ir = compile_single_file_contents(ocaml_source, &format!("{test_name}.ml"))
        .expect("Could not compile test file");
    let (rest, lambda) = parse_syntax
        .parse(Span::new(&lambda_ir))
        .expect("Lambda IR failed to parse");
    assert!(rest.is_empty(), "Lambda parsing failure");
    let zptr = transform_lambda_program(&mut zstore, &state, &lambda)
        .expect("Could not transform lambda IR into lurk data");

    run_tests(
        &zptr,
        &ZPtr::null(Tag::Env),
        toplevel,
        &mut zstore,
        expected_cloj,
        config.clone(),
    );
}

macro_rules! test {
    ($test_func:ident, $input_str:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case(stringify!($test_func), $input_str, $expected_cloj)
        }
    };
}

macro_rules! test_file {
    ($test_func:ident, $input_file:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case(
                stringify!($test_func),
                include_str!($input_file),
                $expected_cloj,
            )
        }
    };
}

fn record(zstore: &mut ZStore<F, LurkChip>, tag: u64, xs: &[ZPtr<F>]) -> ZPtr<F> {
    let mut vals = vec![ZPtr::u64(tag)];
    vals.extend(xs);
    zstore.intern_list(vals)
}

// Default record with tag 0 generated at the end of the .ml file from `(makeblock 0 ...)`
fn block(zstore: &mut ZStore<F, LurkChip>, xs: &[ZPtr<F>]) -> ZPtr<F> {
    record(zstore, 0, xs)
}

// Currently, when compiling an individual file, the `setglobal` is ignored, and the entire file
// returns the record of bindings in the file.
// Individual expressions like "123" get evaluated inside a `seq` but do not add bindings to the
// bindings record.
// This means most of these tests have an outer `let` binding to make sure this bindings record
// is not empty. This is susceptible to change.
test!(test_int, "let x = 123", |z| block(z, &[ZPtr::u64(123)]));
test!(test_int2, "let x = 123;; let x = 456", |z| block(
    z,
    &[ZPtr::u64(456)]
));
test!(test_int3, "let x = 123;; let y = 456", |z| block(
    z,
    &[ZPtr::u64(123), ZPtr::u64(456)]
));
test!(test_op, "let x = 123;; let y = 456;; let sum = x + y;; let sub = y - x;; let mul = x * y;; let div = y / x;; let rem = y mod x", |z| block(
    z,
    &[ZPtr::u64(123), ZPtr::u64(456), ZPtr::u64(123 + 456), ZPtr::u64(456 - 123), ZPtr::u64(123 * 456), ZPtr::u64(456 / 123), ZPtr::u64(456 % 123)]
));
test!(test_cmp, "let x = 123;; let y = 456;; let lt = x < y;; let lteq = x <= y;; let gt = x > y;; let gteq = x >= y;; let eq = x == y;; let noteq = x != y", |z| block(
    z,
    &[ZPtr::u64(123), ZPtr::u64(456), *z.t(), *z.t(), *z.nil(), *z.nil(), *z.nil(), *z.t()]
));
// TODO: ocaml uses all the same comparison builtins for non-integer data types as well (strings, chars, possibly others)
// test!(test_cmp_char, "let x = 'a';; let y = 'z';; let lt = x < y;; let lteq = x <= y;; let gt = x > y;; let gteq = x >= y;; let eq = x == y;; let noteq = x != y", |z| block(
//     z,
//     &[ZPtr::char('a'), ZPtr::char('z'), *z.t(), *z.t(), *z.nil(), *z.nil(), *z.nil(), *z.t()]
// ));
test!(test_char, "let x = 'a';; let y = 'b'", |z| block(
    z,
    &[ZPtr::char('a'), ZPtr::char('b')]
));
test!(test_string, r#"let x = "abc";; let y = "def""#, |z| {
    let abc = z.intern_string("abc");
    let def = z.intern_string("def");
    block(z, &[abc, def])
});
test!(
    test_fib,
    "let x = let rec fib n = if n <= 1 then n else fib(n - 1) + fib(n - 2) in fib 15",
    |z| block(z, &[ZPtr::u64(610)])
);
test!(
    test_letrec,
    "let x = let rec odd x = if (x = 0) then false else even (x - 1) and even x = if (x = 0) then true else odd (x - 1) in odd 17",
    |z| {
        block(z, &[ZPtr::u64(1)])
    }
);

test_file!(test_fib2, "ocaml/fib.ml", |z| block(
    z,
    &[ZPtr::u64(3736710778780434371)]
));
