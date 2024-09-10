use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear as F;
use p3_field::AbstractField;
use sphinx_core::{stark::StarkMachine, utils::BabyBearPoseidon2};

use crate::{
    air::debug::debug_chip_constraints_and_queries_with_sharding,
    lair::{
        execute::{QueryRecord, Shard, ShardingConfig},
        func_chip::FuncChip,
        lair_chip::{
            build_chip_vector_from_lair_chips, build_lair_chip_vector, LairMachineProgram,
        },
        toplevel::Toplevel,
    },
};

use super::{
    chipset::{lurk_hasher, LurkChip},
    eval::{build_lurk_toplevel, EvalErr},
    state::{builtin_sym, user_sym},
    symbol::Symbol,
    tag::Tag,
    zstore::{ZPtr, ZStore},
};

#[allow(clippy::type_complexity)]
static TEST_SETUP_DATA: OnceCell<(
    Toplevel<F, LurkChip>,
    ZStore<F, LurkChip>,
    BabyBearPoseidon2,
)> = OnceCell::new();

fn test_setup_data() -> &'static (
    Toplevel<F, LurkChip>,
    ZStore<F, LurkChip>,
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
    env: &ZPtr<F>,
    toplevel: &Toplevel<F, LurkChip>,
    zstore: &mut ZStore<F, LurkChip>,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
    config: BabyBearPoseidon2,
) {
    let mut record = QueryRecord::new(toplevel);
    record.inject_inv_queries("hash_24_8", toplevel, &zstore.hashes24);
    record.inject_inv_queries("hash_32_8", toplevel, &zstore.hashes32);
    record.inject_inv_queries("hash_40_8", toplevel, &zstore.hashes40);

    let mut input = [F::zero(); 24];
    input[..16].copy_from_slice(&zptr.flatten());
    input[16..].copy_from_slice(&env.digest);

    let lurk_main = FuncChip::from_name("lurk_main", toplevel);
    let result = toplevel
        .execute(lurk_main.func, &input, &mut record, None)
        .unwrap();

    assert_eq!(result.as_ref(), &expected_cloj(zstore).flatten());

    let lair_chips = build_lair_chip_vector(&lurk_main);

    // debug constraints and verify lookup queries with and without sharding
    debug_chip_constraints_and_queries_with_sharding(&record, &lair_chips, None);
    debug_chip_constraints_and_queries_with_sharding(
        &record,
        &lair_chips,
        Some(ShardingConfig { max_shard_size: 4 }),
    );

    // debug constraints with Sphinx
    let full_shard = Shard::new(&record);
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
    input_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
) {
    let (toplevel, zstore, config) = test_setup_data();
    let zstore = &mut zstore.clone();
    let zptr = input_cloj(zstore);
    run_test(
        &zptr,
        &ZPtr::null(Tag::Env),
        toplevel,
        zstore,
        expected_cloj,
        config.clone(),
    );
}

fn test_case(input_code: &'static str, expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>) {
    let (toplevel, zstore, config) = test_setup_data();
    let mut zstore = zstore.clone();
    let zptr = zstore.read(input_code).expect("Read failure");
    run_test(
        &zptr,
        &ZPtr::null(Tag::Env),
        toplevel,
        &mut zstore,
        expected_cloj,
        config.clone(),
    );
}

fn test_case_env(
    input_code: &'static str,
    env_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
) {
    let (toplevel, zstore, config) = test_setup_data();
    let mut zstore = zstore.clone();
    let zptr = zstore.read(input_code).expect("Read failure");
    let env = env_cloj(&mut zstore);
    run_test(
        &zptr,
        &env,
        toplevel,
        &mut zstore,
        expected_cloj,
        config.clone(),
    );
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

macro_rules! test_env {
    ($test_func:ident, $input_code:expr, $env_cloj:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case_env($input_code, $env_cloj, $expected_cloj)
        }
    };
}

fn trivial_id_fun(zstore: &mut ZStore<F, LurkChip>) -> ZPtr<F> {
    let x = zstore.intern_symbol(&user_sym("x"));
    let args = zstore.intern_list([x]);
    let env = zstore.intern_empty_env();
    zstore.intern_fun(args, x, env)
}

fn trivial_a_1_env(zstore: &mut ZStore<F, LurkChip>) -> ZPtr<F> {
    let empty_env = zstore.intern_empty_env();
    let a = zstore.intern_symbol(&user_sym("a"));
    let one = uint(1);
    zstore.intern_env(a, one, empty_env)
}

fn uint(u: u64) -> ZPtr<F> {
    ZPtr::u64(u)
}

// self-evaluating
test!(test_num, "1", |_| uint(1));
test!(test_char, "'a'", |_| ZPtr::char('a'));
test!(test_str, "\"abc\"", |z| z.intern_string("abc"));
test!(test_key, ":hi", |z| z.intern_symbol(&Symbol::key(&["hi"])));
test!(test_u64, "1u64", |_| ZPtr::u64(1));
test!(test_field_elem, "1n", |_| ZPtr::num(F::one()));
test!(test_t, "t", |z| *z.t());
test!(test_nil, "nil", |z| *z.nil());
test_raw!(test_fun, trivial_id_fun, trivial_id_fun);
test_raw!(test_comm, |_| ZPtr::null(Tag::Comm), |_| ZPtr::null(
    Tag::Comm
));

// functions & applications
test!(test_lambda, "(lambda (x) x)", trivial_id_fun);
test!(test_app1, "((lambda (x) x) 1)", |_| uint(1));
test!(test_app2, "((lambda (x y z) y) 1 2 3)", |_| uint(2));
test!(test_app3, "((lambda (x) (lambda (y) x)) 1 2)", |_| {
    uint(1)
});
test!(test_app_err, "(a)", |_| ZPtr::err(EvalErr::UnboundVar));
test!(test_app_err2, "((lambda () a) 2)", |_| ZPtr::err(
    EvalErr::UnboundVar
));

// builtins
test!(test_if, "(if 1 1 0)", |_| uint(1));
test!(test_if2, "(if nil 1 0)", |_| uint(0));
test!(test_if3, "(if 1 1)", |_| uint(1));
test!(test_if4, "(if nil 1)", |z| *z.nil());
test!(test_let, "(let ((x 0) (y 1)) x)", |_| uint(0));
test!(test_let2, "(let ((x 0) (y 1)) y)", |_| uint(1));
test!(test_add, "(+ 1 2)", |_| uint(3));
test!(test_sub, "(- 5 2)", |_| uint(3));
test!(test_mul, "(* 2 3)", |_| uint(6));
test!(test_div, "(/ 6 3)", |_| uint(2));
test!(test_arith, "(+ (* 2 2) (* 2 3))", |_| uint(10));
test!(test_num_eq, "(= 0 1)", |z| *z.nil());
test!(test_num_eq2, "(= 1 1)", |z| *z.t());
test!(
    test_num_eq3,
    "(= 3844955657946763191 18057789389824918841)",
    |z| *z.nil()
);
test!(
    test_num_eq4,
    "(= 3844955657946763191 3844955657946763191)",
    |z| *z.t()
);
test!(test_num_eq5, "(= 0n 1n)", |z| *z.nil());
test!(test_num_eq6, "(= 1n 1n)", |z| *z.t());
test!(test_u64_order1, "(>= 0 1)", |z| *z.nil());
test!(test_u64_order2, "(>= 1 1)", |z| *z.t());
test!(test_u64_order3, "(>= 2 1)", |z| *z.t());
test!(test_u64_order4, "(<= 0 1)", |z| *z.t());
test!(test_u64_order5, "(<= 1 1)", |z| *z.t());
test!(test_u64_order6, "(<= 2 1)", |z| *z.nil());
test!(test_u64_order7, "(> 0 1)", |z| *z.nil());
test!(test_u64_order8, "(> 1 1)", |z| *z.nil());
test!(test_u64_order9, "(> 2 1)", |z| *z.t());
test!(test_u64_order10, "(< 0 1)", |z| *z.t());
test!(test_u64_order11, "(< 1 1)", |z| *z.nil());
test!(test_u64_order12, "(< 2 1)", |z| *z.nil());
test!(
    test_u64_order13,
    "(< 3844955657946763191 18057789389824918841)",
    |z| *z.t()
);
test!(
    test_u64_order14,
    "(<= 3844955657946763191 3844955657946763191)",
    |z| *z.t()
);
test!(test_begin_empty, "(begin)", |z| *z.nil());
test!(test_begin, "(begin 1 2 3)", |_| uint(3));
test!(test_list, "(list)", |z| *z.nil());
test!(test_list2, "(list (+ 1 1) \"hi\")", |z| {
    let hi = z.intern_string("hi");
    let two = uint(2);
    z.intern_list([two, hi])
});
test!(test_quote, "'(x 1 :foo)", |z| {
    let x = z.intern_symbol(&user_sym("x"));
    let one = uint(1);
    let foo = z.intern_symbol(&Symbol::key(&["foo"]));
    z.intern_list([x, one, foo])
});
test!(test_eval, "(eval '(+ 1 2) (empty-env))", |_| uint(3));
test!(test_eval2, "(eval 'x (let ((x 1)) (current-env)))", |_| {
    uint(1)
});
test!(test_eval3, "(let ((a '(+ 1 1))) (eval a))", |_| uint(2));
test!(test_cons, "(cons 0n 1n)", |z| {
    z.intern_cons(ZPtr::num(F::zero()), ZPtr::num(F::one()))
});
test!(test_car, "(car (cons 0 1))", |_| uint(0));
test!(test_cdr, "(cdr (cons 0 1))", |_| uint(1));
test!(test_strcons, "(strcons 'a' \"bc\")", |z| z
    .intern_string("abc"));
test!(test_eq1, "(eq (cons 1 2) '(1 . 2))", |z| *z.t());
test!(test_eq2, "(eq (cons 1 3) '(1 . 2))", |z| *z.nil());
test!(test_eq3, "(eq :a :a)", |z| *z.t());
test!(test_eq4, "(eq :a :b)", |z| *z.nil());
test!(test_eq5, "(eq 'a 'a)", |z| *z.t());
test!(test_eq6, "(eq 'a 'b)", |z| *z.nil());
test!(test_eq7, "(eq nil nil)", |z| *z.t());
test!(test_eq8, "(eq t t)", |z| *z.t());
test!(test_eq9, "(eq t nil)", |z| *z.nil());
test!(test_eq10, "(eq 'a' 'b')", |z| *z.nil());
test!(test_eq11, "(eq 'a' 'a')", |z| *z.t());
test!(test_eq12, "(eq \"abc\" \"abd\")", |z| *z.nil());
test!(test_eq13, "(eq \"abc\" \"abc\")", |z| *z.t());
test!(test_eq14, "(eq (cons 'a 1) (cons 'a 2))", |z| *z.nil());
test!(test_eq15, "(eq (cons :a 1) (cons :a 1))", |z| *z.t());
test!(test_eq16, "(eq (lambda (x) x) (lambda (x) x))", |z| *z.t());
test!(test_eq17, "(eq (lambda (x) x) (lambda (y) y))", |z| *z
    .nil());
test!(
    test_eq18,
    "(eq (let ((x 1)) (current-env)) (let ((x 1)) (current-env)))",
    |z| *z.t()
);
test!(
    test_eq19,
    "(eq (let ((x 1)) (current-env)) (current-env))",
    |z| *z.nil()
);
test_raw!(
    test_eq20,
    |z| {
        let eq = z.intern_symbol(&builtin_sym("eq"));
        let env = z.intern_empty_env();
        let arg1 = z.intern_thunk(*z.t(), env);
        let arg2 = z.intern_thunk(*z.t(), env);
        z.intern_list([eq, arg1, arg2])
    },
    |z| *z.t()
);
test_raw!(
    test_eq21,
    |z| {
        let eq = z.intern_symbol(&builtin_sym("eq"));
        let env = z.intern_empty_env();
        let arg1 = z.intern_thunk(*z.nil(), env);
        let arg2 = z.intern_thunk(*z.t(), env);
        z.intern_list([eq, arg1, arg2])
    },
    |z| *z.nil()
);
test!(test_eq22, "(eq 1n 0n)", |z| *z.nil());
test!(test_eq23, "(eq 1n 1n)", |z| *z.t());

test!(
    test_misc1,
    "(letrec ((ones (cons 1 (lambda () ones))))
       (car ((cdr ones))))",
    |_| uint(1)
);
test!(test_type_eq1, "(type-eq 1 (+ 1 2))", |z| *z.t());
test!(test_type_eq2, "(type-eq (+ 1 1) 'a')", |z| *z.nil());
test!(test_type_eq3, "(type-eq nil t)", |z| *z.t());
test!(test_type_eq4, "(type-eq 'a t)", |z| *z.t());
test!(test_type_eq5, "(type-eq 'cons t)", |z| *z.nil());
test!(test_type_eq6, "(type-eq 'cons 'let)", |z| *z.t());
test!(test_type_eqq1, "(type-eqq (nil) (cons 1 2))", |z| *z.t());
test!(test_type_eqq2, "(type-eqq 2 'a')", |z| *z.nil());
test!(test_breakpoint, "(breakpoint)", |z| *z.nil());
test!(test_breakpoint2, "(breakpoint (+ 1 1))", |_| uint(2));

// coercions
test!(test_char1, "(char 'a')", |z| z.intern_char('a'));
test!(test_char2, "(char 97)", |z| z.intern_char('a'));
test!(test_u64_1, "(u64 97)", |_| uint(97));
test!(test_u64_2, "(u64 'a')", |_| uint(97));

// environment
test!(
    test_current_env,
    "(let ((a 1)) (current-env))",
    trivial_a_1_env
);
test_env!(test_manual_env, "a", trivial_a_1_env, |_| uint(1));

// heavier computations
test!(
    test_fact,
    "(letrec ((factorial
        (lambda (n)
        (if (= n 0) 1
          (* n (factorial (- n 1)))))))
      (factorial 5))",
    |_| uint(120)
);
test!(
    test_fib,
    "(letrec ((fib
          (lambda (n)
            (if (= n 0) 0
              (if (= n 1) 1
                (+ (fib (- n 1)) (fib (- n 2))))))))
        (fib 10))",
    |_| uint(55)
);

// commitments
test!(test_commit, "(commit 123)", |_| {
    let mut preimg = Vec::with_capacity(24);
    preimg.extend([F::zero(); 8]);
    preimg.extend(uint(123).flatten());
    ZPtr::comm(lurk_hasher().hash(&preimg).try_into().unwrap())
});
test!(test_hide, "(hide (bignum (commit 321)) 123)", |_| {
    let mut secret_preimg = Vec::with_capacity(24);
    secret_preimg.extend([F::zero(); 8]);
    secret_preimg.extend(uint(321).flatten());
    let hasher = lurk_hasher();
    let mut preimg = Vec::with_capacity(24);
    preimg.extend(hasher.hash(&secret_preimg));
    preimg.extend(uint(123).flatten());
    ZPtr::comm(hasher.hash(&preimg).try_into().unwrap())
});
test!(test_hide2, "(hide (commit 321) 123)", |_| ZPtr::err(
    EvalErr::NotBigNum
));
test!(test_open_roundtrip, "(open (commit 123))", |_| uint(123));
test!(
    test_open_raw_roundtrip,
    "(begin (commit 123n) (open #0x20a6e497cdc1145d6684f0d31474f160ddf2832673d1d57885a5f28a732882))",
    |_| ZPtr::num(F::from_canonical_u32(123))
);
test!(test_secret, "(secret (commit 123))", |_| ZPtr::big_num(
    [F::zero(); 8]
));
test!(
    test_func_big_num_app,
    "(begin (commit (lambda (x) x)) (#0x83420bafb3cb56870b10b498607c0a6314b0ea331328bbb232c74078abb5dc 42))",
    |_| uint(42)
);
test!(
    test_func_comm_app,
    "(begin (commit (lambda (x) x)) ((comm #0x83420bafb3cb56870b10b498607c0a6314b0ea331328bbb232c74078abb5dc) 42))",
    |_| uint(42)
);

// big num
test!(test_raw_big_num, "#0x0", |_| ZPtr::big_num([F::zero(); 8]));
test!(test_raw_comm, "#c0x0", |_| ZPtr::comm([F::zero(); 8]));
test!(
    test_raw_big_num2,
    "#0x20a6e497cdc1145d6684f0d31474f160ddf2832673d1d57885a5f28a732882",
    |_| {
        let mut preimg = Vec::with_capacity(24);
        preimg.extend([F::zero(); 8]);
        preimg.extend(ZPtr::num(F::from_canonical_u32(123)).flatten());
        ZPtr::big_num(lurk_hasher().hash(&preimg).try_into().unwrap())
    }
);
test!(
    test_raw_comm2,
    "#c0x20a6e497cdc1145d6684f0d31474f160ddf2832673d1d57885a5f28a732882",
    |_| {
        let mut preimg = Vec::with_capacity(24);
        preimg.extend([F::zero(); 8]);
        preimg.extend(ZPtr::num(F::from_canonical_u32(123)).flatten());
        ZPtr::comm(lurk_hasher().hash(&preimg).try_into().unwrap())
    }
);
test!(test_big_num_to_comm, "(comm #0x0)", |_| ZPtr::comm(
    [F::zero(); 8]
));
test!(test_comm_to_big_num, "(bignum #c0x0)", |_| ZPtr::big_num(
    [F::zero(); 8]
));
test!(
    test_big_num_to_comm_to_big_num,
    "(bignum (comm #0x0))",
    |_| ZPtr::big_num([F::zero(); 8])
);
test!(
    test_comm_to_big_num_to_comm,
    "(comm (bignum #c0x0))",
    |_| ZPtr::comm([F::zero(); 8])
);
test!(test_big_num_equal1, "(= #0x0 #0x1)", |z| *z.nil());
test!(test_big_num_equal2, "(= #0x0 #0x0)", |z| *z.t());
test!(test_big_num_order1, "(>= #0x0 #0x1)", |z| *z.nil());
test!(test_big_num_order2, "(>= #0x1 #0x1)", |z| *z.t());
test!(test_big_num_order3, "(>= #0x2 #0x1)", |z| *z.t());
test!(test_big_num_order4, "(<= #0x0 #0x1)", |z| *z.t());
test!(test_big_num_order5, "(<= #0x1 #0x1)", |z| *z.t());
test!(test_big_num_order6, "(<= #0x2 #0x1)", |z| *z.nil());
test!(test_big_num_order7, "(> #0x0 #0x1)", |z| *z.nil());
test!(test_big_num_order8, "(> #0x1 #0x1)", |z| *z.nil());
test!(test_big_num_order9, "(> #0x2 #0x1)", |z| *z.t());
test!(test_big_num_order10, "(< #0x0 #0x1)", |z| *z.t());
test!(test_big_num_order11, "(< #0x1 #0x1)", |z| *z.nil());
test!(test_big_num_order12, "(< #0x2 #0x1)", |z| *z.nil());
test!(test_big_num_order13, "(< #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7 #0x7b4dd31c2678ef3c257cda6a06f0c830aaeab011c2c4e7fa9a27c699550539)", |z| *z.t());
test!(test_big_num_order14, "(<= #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7 #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7)", |z| *z.t());
test!(test_big_num_order15, "(eq #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7 #0x7b4dd31c2678ef3c257cda6a06f0c830aaeab011c2c4e7fa9a27c699550539)", |z| *z.nil());
test!(test_big_num_order16, "(eq #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7 #0x17084a3b94580234614c1ebde7dbb24bc3cb26ba2a84d1355c06cca90b8fb7)", |z| *z.t());

// shadowing built-ins
test!(test_shadow1, "(let ((cons 1)) (+ cons 1))", |_| uint(2));
test!(test_shadow2, "(letrec ((cons 1)) (+ cons 1))", |_| uint(2));
test!(test_shadow3, "((lambda (cons) (+ cons 1)) 1)", |_| uint(2));
test!(test_shadow4, "(let ((cons 1)) (cons cons cons))", |z| {
    z.intern_cons(uint(1), uint(1))
});

// errors
test!(test_unbound_var, "a", |_| ZPtr::err(EvalErr::UnboundVar));
test!(test_div_by_zero_fel, "(/ 1n 0n)", |_| ZPtr::err(
    EvalErr::DivByZero
));
test!(test_div_by_zero, "(/ 1 0)", |_| ZPtr::err(
    EvalErr::DivByZero
));
test!(test_equal_non_num, "(= 'a 'a)", |_| ZPtr::err(
    EvalErr::ArgNotNumber
));
test!(test_equal_non_num2, "(= (comm #0x0) (comm #0x0))", |_| {
    ZPtr::err(EvalErr::ArgNotNumber)
});
test!(
    test_shadow_err1,
    "(let ((nil 1)) (+ nil 1))",
    |_| ZPtr::err(EvalErr::IllegalBindingVar)
);
test!(test_shadow_err2, "(letrec ((nil 1)) (+ nil 1))", |_| {
    ZPtr::err(EvalErr::IllegalBindingVar)
});
test!(test_shadow_err3, "((lambda (nil) (+ nil 1)) 1)", |_| {
    ZPtr::err(EvalErr::IllegalBindingVar)
});
test!(test_shadow_err4, "(let ((t 1)) (+ t 1))", |_| ZPtr::err(
    EvalErr::IllegalBindingVar
));
test!(test_shadow_err5, "(letrec ((t 1)) (+ t 1))", |_| ZPtr::err(
    EvalErr::IllegalBindingVar
));
test!(test_shadow_err6, "((lambda (t) (+ t 1)) 1)", |_| ZPtr::err(
    EvalErr::IllegalBindingVar
));
