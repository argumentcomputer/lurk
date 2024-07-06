use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear as F;
use p3_field::AbstractField;
use sphinx_core::{
    air::MachineAir,
    stark::{MachineRecord, StarkMachine},
    utils::BabyBearPoseidon2,
};

use crate::{
    air::debug::{debug_constraints_collecting_queries, TraceQueries},
    lair::{
        execute::{QueryRecord, Shard, ShardingConfig},
        func_chip::FuncChip,
        hasher::{Chipset, LurkChip, LurkHasher},
        lair_chip::{
            build_chip_vector_from_lair_chips, build_lair_chip_vector, LairMachineProgram,
        },
        toplevel::Toplevel,
    },
};

use super::{
    eval::{build_lurk_toplevel, EvalErr},
    state::{lurk_sym, user_sym},
    symbol::Symbol,
    tag::Tag,
    zstore::{ZPtr, ZStore},
};

#[allow(clippy::type_complexity)]
static TEST_SETUP_DATA: OnceCell<(
    Toplevel<F, LurkChip>,
    ZStore<F, LurkHasher>,
    BabyBearPoseidon2,
)> = OnceCell::new();

fn test_setup_data() -> &'static (
    Toplevel<F, LurkChip>,
    ZStore<F, LurkHasher>,
    BabyBearPoseidon2,
) {
    TEST_SETUP_DATA.get_or_init(|| {
        let (toplevel, zstore) = build_lurk_toplevel();
        let config = BabyBearPoseidon2::new();
        (toplevel, zstore, config)
    })
}

fn run_test(
    zptr: &ZPtr<F>,
    toplevel: &Toplevel<F, LurkChip>,
    zstore: &mut ZStore<F, LurkHasher>,
    expected_cloj: fn(&mut ZStore<F, LurkHasher>) -> ZPtr<F>,
    config: BabyBearPoseidon2,
) {
    let mut record = QueryRecord::new(toplevel);
    record.inject_inv_queries("hash_32_8", toplevel, zstore.tuple2_hashes());
    record.inject_inv_queries("hash_48_8", toplevel, zstore.tuple3_hashes());

    let mut input = [F::zero(); 24];
    input[..16].copy_from_slice(&zptr.flatten());

    let lurk_main = FuncChip::from_name("lurk_main", toplevel);
    let result = toplevel.execute(lurk_main.func, &input, &mut record);

    assert_eq!(result.as_ref(), &expected_cloj(zstore).flatten());

    let lair_chips = build_lair_chip_vector(&lurk_main);

    // debug constraints and verify lookup queries without sharding
    let full_shard = Shard::new(&record);
    let lookup_queries: Vec<_> = lair_chips
        .iter()
        .map(|chip| {
            let trace = chip.generate_trace(&full_shard, &mut Default::default());
            debug_constraints_collecting_queries(chip, &[], None, &trace)
        })
        .collect();
    let num_lookups = lookup_queries.len();
    TraceQueries::verify_many(lookup_queries);

    // debug constraints and verify lookup queries with aggressive sharding
    let shards = full_shard
        .clone()
        .shard(&ShardingConfig { max_shard_size: 4 });
    let mut lookup_queries = Vec::with_capacity(num_lookups);
    for shard in shards.iter() {
        let queries: Vec<_> = lair_chips
            .iter()
            .map(|chip| {
                if chip.included(shard) {
                    let trace = chip.generate_trace(shard, &mut Shard::default());
                    debug_constraints_collecting_queries(chip, &[], None, &trace)
                } else {
                    Default::default()
                }
            })
            .collect();
        lookup_queries.extend(queries.into_iter());
    }
    TraceQueries::verify_many(lookup_queries);

    // debug constraints with Sphinx
    let machine = StarkMachine::new(
        config,
        build_chip_vector_from_lair_chips(lair_chips),
        record.expect_public_values().len(),
    );
    let (pk, _) = machine.setup(&LairMachineProgram);
    machine.debug_constraints(&pk, full_shard);
}

#[allow(clippy::type_complexity)]
fn test_case_raw(
    input_cloj: fn(&mut ZStore<F, LurkHasher>) -> ZPtr<F>,
    expected_cloj: fn(&mut ZStore<F, LurkHasher>) -> ZPtr<F>,
) {
    let (toplevel, zstore, config) = test_setup_data();
    let zstore = &mut zstore.clone();
    let zptr = input_cloj(zstore);
    run_test(&zptr, toplevel, zstore, expected_cloj, config.clone());
}

fn test_case(input_code: &'static str, expected_cloj: fn(&mut ZStore<F, LurkHasher>) -> ZPtr<F>) {
    let (toplevel, zstore, config) = test_setup_data();
    let mut zstore = zstore.clone();
    let zptr = zstore.read(input_code).expect("Read failure");
    run_test(&zptr, toplevel, &mut zstore, expected_cloj, config.clone());
}

macro_rules! test_raw {
    ($test_func:ident, $input_cloj:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case_raw($input_cloj, $expected_cloj)
        }
    };
}

macro_rules! test {
    ($test_func:ident, $input_code:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case($input_code, $expected_cloj)
        }
    };
}

fn trivial_id_fun(zstore: &mut ZStore<F, LurkHasher>) -> ZPtr<F> {
    let x = zstore.intern_symbol(&user_sym("x"));
    let args = zstore.intern_list([x]);
    let env = zstore.intern_empty_env();
    zstore.intern_fun(args, x, env)
}

fn num(u: u32) -> ZPtr<F> {
    ZPtr::num(F::from_canonical_u32(u))
}

// self-evaluating
test!(test_num, "1", |_| ZPtr::num(F::one()));
test!(test_char, "'a'", |_| ZPtr::char('a'));
test!(test_str, "\"abc\"", |z| z.intern_string("abc"));
test!(test_key, ":hi", |z| z.intern_symbol(&Symbol::key(&["hi"])));
test!(test_u64, "1u64", |_| ZPtr::u64(1));
test!(test_t, "t", |z| z.intern_symbol(&lurk_sym("t")));
test!(test_nil, "nil", |z| z.intern_nil());
test_raw!(test_fun, trivial_id_fun, trivial_id_fun);
test_raw!(test_comm, |_| ZPtr::null(Tag::Comm), |_| ZPtr::null(
    Tag::Comm
));

// functions & applications
test!(test_lambda, "(lambda (x) x)", trivial_id_fun);
test!(test_app1, "((lambda (x) x) 1)", |_| ZPtr::num(F::one()));
test!(test_app2, "((lambda (x y z) y) 1 2 3)", |_| num(2));
test!(test_app3, "((lambda (x) (lambda (y) x)) 1 2)", |_| {
    ZPtr::num(F::one())
});

// builtins
test!(test_if, "(if 1 1 0)", |_| ZPtr::num(F::one()));
test!(test_if2, "(if nil 1 0)", |_| ZPtr::num(F::zero()));
test!(test_let, "(let ((x 0) (y 1)) x)", |_| ZPtr::num(F::zero()));
test!(test_let2, "(let ((x 0) (y 1)) y)", |_| ZPtr::num(F::one()));
test!(test_add, "(+ 1 2)", |_| num(3));
test!(test_sub, "(- 5 2)", |_| num(3));
test!(test_mul, "(* 2 3)", |_| num(6));
test!(test_div, "(/ 6 3)", |_| num(2));
test!(test_arith, "(+ (* 2 2) (* 2 3))", |_| num(10));
test!(test_num_eq, "(= 0 1)", |z| z.intern_nil());
test!(test_num_eq2, "(= 1 1)", |z| z.intern_symbol(&lurk_sym("t")));
test!(test_begin, "(begin 1 2 3)", |_| num(3));
test!(test_quote, "'(x 1 :foo)", |z| {
    let x = z.intern_symbol(&user_sym("x"));
    let one = ZPtr::num(F::one());
    let foo = z.intern_symbol(&Symbol::key(&["foo"]));
    z.intern_list([x, one, foo])
});
test!(test_eval, "(eval '(+ 1 2) (empty-env))", |_| num(3));
test!(test_eval2, "(eval 'x (let ((x 1)) (current-env)))", |_| {
    ZPtr::num(F::one())
});
test!(test_cons, "(cons 0 1)", |z| {
    z.intern_cons(ZPtr::num(F::zero()), ZPtr::num(F::one()))
});
test!(test_car, "(car (cons 0 1))", |_| ZPtr::num(F::zero()));
test!(test_cdr, "(cdr (cons 0 1))", |_| ZPtr::num(F::one()));
test!(test_strcons, "(strcons 'a' \"bc\")", |z| z
    .intern_string("abc"));
test!(test_eq1, "(eq (cons 1 2) '(1 . 2))", |z| z
    .intern_symbol(&lurk_sym("t")));
test!(test_eq2, "(eq (cons 1 3) '(1 . 2))", |z| z.intern_nil());
test!(
    test_misc1,
    "(letrec ((ones (cons 1 (lambda () ones))))
       (car ((cdr ones))))",
    |_| ZPtr::num(F::one())
);

// heavier computations
test!(
    test_fact,
    "(letrec ((factorial
        (lambda (n)
        (if (= n 0) 1
          (* n (factorial (- n 1)))))))
      (factorial 5))",
    |_| num(120)
);
test!(
    test_fib,
    "(letrec ((fib
          (lambda (n)
            (if (= n 0) 0
              (if (= n 1) 1
                (+ (fib (- n 1)) (fib (- n 2))))))))
        (fib 10))",
    |_| num(55)
);

// commitments
test!(test_commit, "(commit 123)", |_| {
    let mut preimg = Vec::with_capacity(24);
    preimg.extend([F::zero(); 8]);
    preimg.extend(num(123).flatten());
    ZPtr::comm(LurkHasher::default().execute(&preimg).try_into().unwrap())
});
test!(
    test_raw_commit,
    "#0x4b51f7ca76e9700190d753b328b34f3f59e0ad3c70c486645b5890068862f3",
    |_| {
        let mut preimg = Vec::with_capacity(24);
        preimg.extend([F::zero(); 8]);
        preimg.extend(num(123).flatten());
        ZPtr::comm(LurkHasher::default().execute(&preimg).try_into().unwrap())
    }
);
test!(test_hide, "(hide (commit 321) 123)", |_| {
    let mut secret_preimg = Vec::with_capacity(24);
    secret_preimg.extend([F::zero(); 8]);
    secret_preimg.extend(num(321).flatten());
    let hasher = LurkHasher::default();
    let mut preimg = Vec::with_capacity(24);
    preimg.extend(hasher.execute(&secret_preimg));
    preimg.extend(num(123).flatten());
    ZPtr::comm(hasher.execute(&preimg).try_into().unwrap())
});
test!(test_open_roundtrip, "(open (commit 123))", |_| num(123));
test!(
    test_open_raw_roundtrip,
    "(begin (commit 123) (open #0x4b51f7ca76e9700190d753b328b34f3f59e0ad3c70c486645b5890068862f3))",
    |_| num(123)
);
test!(test_secret, "(secret (commit 123))", |_| ZPtr::comm(
    [F::zero(); 8]
));

// errors
test!(test_unbound_var, "a", |_| ZPtr::err(EvalErr::UnboundVar));
test!(test_div_by_zero, "(/ 1 0)", |_| ZPtr::err(
    EvalErr::DivByZero
));
