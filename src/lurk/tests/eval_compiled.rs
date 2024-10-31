//! Correctness tests for the Lurk evaluation model

use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear as F;
use p3_field::AbstractField;
use sphinx_core::utils::BabyBearPoseidon2;

use crate::{
    lair::{chipset::NoChip, toplevel::Toplevel},
    lurk::{
        chipset::{lurk_hasher, LurkChip},
        error::EvalErr,
        eval_compiled::build_lurk_toplevel_native,
        state::{builtin_sym, user_sym},
        symbol::Symbol,
        tag::Tag,
        zstore::{ZPtr, ZStore},
    },
};

use super::{int63, int64, run_tests, trivial_a_1_env, trivial_id_fun, uint};

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

#[allow(clippy::type_complexity)]
fn test_case_raw(
    input_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
    expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
) {
    let (toplevel, zstore, config) = test_setup_data();
    let zstore = &mut zstore.clone();
    let zptr = input_cloj(zstore);
    run_tests(
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
    let zptr = zstore.read(input_code, &Default::default());
    run_tests(
        &zptr,
        &ZPtr::null(Tag::Env),
        toplevel,
        &mut zstore,
        expected_cloj,
        config.clone(),
    );
}

// TODO
// fn test_case_env(
//     input_code: &'static str,
//     env_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
//     expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>,
// ) {
//     let (toplevel, zstore, config) = test_setup_data();
//     let mut zstore = zstore.clone();
//     let zptr = zstore.read(input_code, &Default::default());
//     let env = env_cloj(&mut zstore);
//     run_tests(
//         &zptr,
//         &env,
//         toplevel,
//         &mut zstore,
//         expected_cloj,
//         config.clone(),
//     );
// }

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

// TODO
// macro_rules! test_env {
//     ($test_func:ident, $input_code:expr, $env_cloj:expr, $expected_cloj:expr) => {
//         #[test]
//         fn $test_func() {
//             test_case_env($input_code, $env_cloj, $expected_cloj)
//         }
//     };
// }

// self-evaluating
test!(test_num, "1", |_| uint(1));
test!(test_char, "'a'", |_| ZPtr::char('a'));
test!(test_str, "\"abc\"", |z| z.intern_string("abc"));
test!(test_key, ":hi", |z| z
    .intern_symbol_no_lang(&Symbol::key(&["hi"])));
test!(test_u64, "1u64", |_| ZPtr::u64(1));
test!(test_field_elem, "1n", |_| ZPtr::num(F::one()));
test!(test_t, "t", |z| *z.t());
test!(test_nil, "nil", |z| *z.nil());
test_raw!(test_fun, trivial_id_fun, trivial_id_fun);
test_raw!(test_comm, |_| ZPtr::null(Tag::Comm), |_| ZPtr::null(
    Tag::Comm
));

// functions & applications
// TODO FIXME
// test!(test_lambda, "(lambda (x) x)", trivial_id_fun);
test!(test_app1, "((lambda (x) x) 1)", |_| uint(1));
test!(test_app2, "((lambda (x y z) y) 1 2 3)", |_| uint(2));
test!(test_app3, "((lambda (x) (lambda (y) x)) 1 2)", |_| {
    uint(1)
});
// TODO FIXME
// test!(test_app4, "(apply (lambda (x) x) '(1))", |_| uint(1));
// test!(test_app5, "(apply (lambda (x y z) y) (list 1 2 3))", |_| {
//     uint(2)
// });
// test!(
//     test_app6,
//     "(apply (lambda (x) (lambda (y) x)) '(1 2))",
//     |_| { uint(1) }
// );
// test!(test_app7, "((lambda (x &rest y) (car (cdr y))) 1)", |z| *z
//     .nil());
test!(test_app8, "((lambda (x &rest y) (car (cdr y))) 1 2)", |z| {
    *z.nil()
});
test!(
    test_app9,
    "((lambda (x &rest y) (car (cdr y))) 1 2 3)",
    |_| uint(3)
);
test!(
    test_app10,
    "((lambda (x &rest y) (car (cdr y))) 1 2 3 4)",
    |_| uint(3)
);
test!(test_app_err, "(a)", |_| ZPtr::err(EvalErr::UnboundVar));
test!(test_app_err2, "((lambda () a) 2)", |_| ZPtr::err(
    EvalErr::UnboundVar
));
// TODO FIXME
// test!(test_app_err3, "(apply (lambda (x) x) 1)", |_| ZPtr::err(
//     EvalErr::ArgsNotList
// ));

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

// i64
test!(test_i64_add_simple, "(+ 2i64 1i64)", |_| int64(3));
test!(test_i64_add_simple2, "(+ 2i64 -1i64)", |_| int64(1));
test!(
    test_i64_add_wrap,
    "(+ -9223372036854775808i64 -9223372036854775808i64)",
    |_| int64(0)
);
test!(
    test_i64_add_wrap2,
    "(+ 9223372036854775807i64 9223372036854775807i64)",
    |_| int64(2)
);
test!(
    test_i64_add_wrap3,
    "(+ -9223372036854775808i64 9223372036854775807i64)",
    |_| int64(-1)
);
test!(
    test_i64_add_wrap4,
    "(+ 9223372036854775807i64 -9223372036854775808i64)",
    |_| int64(-1)
);
test!(test_i64_mul_simple, "(* 2i64 3i64)", |_| int64(6));
test!(test_i64_mul_simple2, "(* 2i64 -31i64)", |_| int64(-6));
test!(test_i64_mul_simple3, "(* -2i64 31i64)", |_| int64(-6));
test!(test_i64_mul_simple4, "(* -2i64 -31i64)", |_| int64(6));
test!(
    test_i64_mul_wrap,
    "(* -9223372036854775808i64 -9223372036854775808i64)",
    |_| int64(0)
);
test!(
    test_i64_mul_wrap2,
    "(* 9223372036854775807i64 9223372036854775807i64)",
    |_| int64(1)
);
test!(
    test_i64_mul_wrap3,
    "(* -9223372036854775808i64 9223372036854775807i64)",
    |_| int64(-9223372036854775808)
);
test!(
    test_i64_mul_wrap4,
    "(* 9223372036854775807i64 -9223372036854775808i64)",
    |_| int64(-9223372036854775808)
);
test!(test_i64_sub, "(- 2i64 1i64)", |_| int64(1));
test!(test_i64_sub2, "(- 2i64 -1i64)", |_| int64(3));
test!(test_i64_div, "(/ 5i64 2i64)", |_| int64(2));
test!(test_i64_div2, "(/ 5i64 -2i64)", |_| int64(-2));
test!(test_i64_div3, "(/ -5i64 2i64)", |_| int64(-2));
test!(test_i64_div4, "(/ -5i64 -2i64)", |_| int64(2));
test!(test_i64_mod, "(% 5i64 2i64)", |_| int64(1));
test!(test_i64_mod2, "(% 5i64 -2i64)", |_| int64(1));
test!(test_i64_mod3, "(% -5i64 2i64)", |_| int64(-1));
test!(test_i64_mod4, "(% -5i64 -2i64)", |_| int64(-1));
// <
test!(test_i64_cmp, "(< 0i64 1i64)", |z| *z.t());
test!(test_i64_cmp2, "(< -1i64 0i64)", |z| *z.t());
test!(test_i64_cmp3, "(< 1i64 0i64)", |z| *z.nil());
test!(test_i64_cmp4, "(< 0i64 -1i64)", |z| *z.nil());
test!(test_i64_cmp5, "(< 0i64 0i64)", |z| *z.nil());
// >
test!(test_i64_cmp6, "(> 1i64 0i64)", |z| *z.t());
test!(test_i64_cmp7, "(> 0i64 -1i64)", |z| *z.t());
test!(test_i64_cmp8, "(> 0i64 1i64)", |z| *z.nil());
test!(test_i64_cmp9, "(> -1i64 0i64)", |z| *z.nil());
test!(test_i64_cmp10, "(> 0i64 0i64)", |z| *z.nil());
// <=
test!(test_i64_cmp11, "(<= 0i64 1i64)", |z| *z.t());
test!(test_i64_cmp12, "(<= -1i64 0i64)", |z| *z.t());
test!(test_i64_cmp13, "(<= 1i64 0i64)", |z| *z.nil());
test!(test_i64_cmp14, "(<= 0i64 -1i64)", |z| *z.nil());
test!(test_i64_cmp15, "(<= 0i64 0i64)", |z| *z.t());
// >=
test!(test_i64_cmp16, "(>= 1i64 0i64)", |z| *z.t());
test!(test_i64_cmp17, "(>= 0i64 -1i64)", |z| *z.t());
test!(test_i64_cmp18, "(>= 0i64 1i64)", |z| *z.nil());
test!(test_i64_cmp19, "(>= -1i64 0i64)", |z| *z.nil());
test!(test_i64_cmp20, "(>= 0i64 0i64)", |z| *z.t());

// i63
test!(test_i63_add_simple, "(+ 2i63 1i63)", |_| int63(3));
test!(
    test_i63_add_wrap,
    "(+ -4611686018427387904i63 -4611686018427387904i63)",
    |_| int63(0)
);
test!(
    test_i63_add_wrap2,
    "(+ 4611686018427387903i63 4611686018427387903i63)",
    |_| int63(2)
);
test!(
    test_i63_add_wrap3,
    "(+ -4611686018427387904i63 4611686018427387903i63)",
    |_| int63(-1)
);
test!(
    test_i63_add_wrap4,
    "(+ 4611686018427387903i63 -4611686018427387904i63)",
    |_| int63(-1)
);
test!(test_i63_mul_simple, "(* 2i63 3i63)", |_| int63(6));
test!(test_i63_mul_simple2, "(* 2i63 -31i63)", |_| int63(-6));
test!(test_i63_mul_simple3, "(* -2i63 31i63)", |_| int63(-6));
test!(test_i63_mul_simple4, "(* -2i63 -31i63)", |_| int63(6));
test!(
    test_i63_mul_wrap,
    "(+ -4611686018427387904i63 -4611686018427387904i63)",
    |_| int63(0)
);
test!(
    test_i63_mul_wrap2,
    "(+ 4611686018427387903i63 4611686018427387903i63)",
    |_| int63(-1)
);
test!(
    test_i63_mul_wrap3,
    "(+ -4611686018427387904i63 4611686018427387903i63)",
    |_| int63(-4611686018427387904)
);
test!(
    test_i63_mul_wrap4,
    "(+ 4611686018427387903i63 -4611686018427387904i63)",
    |_| int63(-4611686018427387904)
);
test!(test_i63_sub, "(- 2i63 1i63)", |_| int63(1));
test!(test_i63_sub2, "(- 2i63 -1i63)", |_| int63(3));
test!(test_i63_div, "(/ 5i63 2i63)", |_| int63(2));
test!(test_i63_div2, "(/ 5i63 -2i63)", |_| int63(-2));
test!(test_i63_div3, "(/ -5i63 2i63)", |_| int63(-2));
test!(test_i63_div4, "(/ -5i63 -2i63)", |_| int63(2));
test!(test_i63_mod, "(% 5i63 2i63)", |_| int63(1));
test!(test_i63_mod2, "(% 5i63 -2i63)", |_| int63(1));
test!(test_i63_mod3, "(% -5i63 2i63)", |_| int63(-1));
test!(test_i63_mod4, "(% -5i63 -2i63)", |_| int63(-1));
// <
test!(test_i63_cmp, "(< 0i63 1i63)", |z| *z.t());
test!(test_i63_cmp2, "(< -1i63 0i63)", |z| *z.t());
test!(test_i63_cmp3, "(< 1i63 0i63)", |z| *z.nil());
test!(test_i63_cmp4, "(< 0i63 -1i63)", |z| *z.nil());
test!(test_i63_cmp5, "(< 0i63 0i63)", |z| *z.nil());
// >
test!(test_i63_cmp6, "(> 1i63 0i63)", |z| *z.t());
test!(test_i63_cmp7, "(> 0i63 -1i63)", |z| *z.t());
test!(test_i63_cmp8, "(> 0i63 1i63)", |z| *z.nil());
test!(test_i63_cmp9, "(> -1i63 0i63)", |z| *z.nil());
test!(test_i63_cmp10, "(> 0i63 0i63)", |z| *z.nil());
// <=
test!(test_i63_cmp11, "(<= 0i63 1i63)", |z| *z.t());
test!(test_i63_cmp12, "(<= -1i63 0i63)", |z| *z.t());
test!(test_i63_cmp13, "(<= 1i63 0i63)", |z| *z.nil());
test!(test_i63_cmp14, "(<= 0i63 -1i63)", |z| *z.nil());
test!(test_i63_cmp15, "(<= 0i63 0i63)", |z| *z.t());
// >=
test!(test_i63_cmp16, "(>= 1i63 0i63)", |z| *z.t());
test!(test_i63_cmp17, "(>= 0i63 -1i63)", |z| *z.t());
test!(test_i63_cmp18, "(>= 0i63 1i63)", |z| *z.nil());
test!(test_i63_cmp19, "(>= -1i63 0i63)", |z| *z.nil());
test!(test_i63_cmp20, "(>= 0i63 0i63)", |z| *z.t());

test!(test_begin_empty, "(begin)", |z| *z.nil());
test!(test_begin, "(begin 1 2 3)", |_| uint(3));
test!(test_list, "(list)", |z| *z.nil());
test!(test_list2, "(list (+ 1 1) \"hi\")", |z| {
    let hi = z.intern_string("hi");
    let two = uint(2);
    z.intern_list([two, hi])
});
test!(test_quote, "'(x 1 :foo)", |z| {
    let x = z.intern_symbol_no_lang(&user_sym("x"));
    let one = uint(1);
    let foo = z.intern_symbol_no_lang(&Symbol::key(&["foo"]));
    z.intern_list([x, one, foo])
});
// TODO FIXME
// test!(test_eval, "(eval '(+ 1 2) (empty-env))", |_| uint(3));
// test!(test_eval2, "(eval 'x (let ((x 1)) (current-env)))", |_| {
//     uint(1)
// });
// test!(test_eval3, "(let ((a '(+ 1 1))) (eval a))", |_| uint(2));
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
// test_raw!(
//     test_eq20,
//     |z| {
//         let eq = z.intern_symbol_no_lang(&builtin_sym("eq"));
//         let env = z.intern_empty_env();
//         let arg1 = z.intern_fix(*z.t(), *z.nil(), env);
//         let arg2 = z.intern_fix(*z.t(), *z.nil(), env);
//         z.intern_list([eq, arg1, arg2])
//     },
//     |z| *z.t()
// );
// test_raw!(
//     test_eq21,
//     |z| {
//         let eq = z.intern_symbol_no_lang(&builtin_sym("eq"));
//         let env = z.intern_empty_env();
//         let arg1 = z.intern_fix(*z.nil(), env, env);
//         let arg2 = z.intern_fix(*z.t(), env, env);
//         z.intern_list([eq, arg1, arg2])
//     },
//     |z| *z.nil()
// );
test!(test_eq22, "(eq 1n 0n)", |z| *z.nil());
test!(test_eq23, "(eq 1n 1n)", |z| *z.t());

// TODO FIXME
// test!(test_eqq, "(eqq (1 . 2) (cons 1 2))", |z| *z.t());
// test!(test_eqq2, "(eqq (cons 1 2) (cons 1 2))", |z| *z.nil());

test!(
    test_misc1,
    "(letrec ((ones (cons 1 (lambda () ones))))
       (car ((cdr ones))))",
    |_| uint(1)
);
// TODO FIXME
// test!(test_type_eq1, "(type-eq 1 (+ 1 2))", |z| *z.t());
// test!(test_type_eq2, "(type-eq (+ 1 1) 'a')", |z| *z.nil());
test!(test_type_eq3, "(type-eq nil t)", |z| *z.t());
test!(test_type_eq4, "(type-eq 'a t)", |z| *z.t());
// TODO FIXME
// test!(test_type_eq5, "(type-eq 'cons t)", |z| *z.nil());
// test!(test_type_eq6, "(type-eq 'cons 'let)", |z| *z.t());
// test!(test_type_eqq1, "(type-eqq (nil) (cons 1 2))", |z| *z.t());
// test!(test_type_eqq2, "(type-eqq 2 'a')", |z| *z.nil());
// test!(test_breakpoint, "(breakpoint)", |z| *z.nil());
// test!(test_breakpoint2, "(breakpoint (+ 1 1))", |_| uint(2));

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
// TODO FIXME
// test_env!(test_manual_env, "a", trivial_a_1_env, |_| uint(1));

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
    test_letrec,
    "(letrec ((odd? (lambda (n) (if (= n 0) nil (even? (- n 1)))))
         (x (even? 3))
         (even? (lambda (n) (if (= n 0) t (odd? (- n 1))))))
       (cons x (odd? 5)))",
    |z| z.intern_cons(*z.nil(), *z.t())
);
test!(
    test_letrec2,
    "(letrec ((odd? (lambda (n) (if (= n 0) nil (even? (- n 1)))))
              (even? (lambda (n) (if (= n 0) t (odd? (- n 1))))))
        (let ((even? (lambda (n) 1000)))
          (odd? 5)))",
    |z| *z.t()
);
test!(
    test_letrec3,
    "(let ((true t))
       (letrec ((odd? (lambda (n) (if (= n 0) nil (even? (- n 1)))))
                (even? (lambda (n) (if (= n 0) true (odd? (- n 1))))))
         (let ((true nil)) (odd? 5))))",
    |z| *z.t()
);
test!(
    test_letrec_error,
    "(letrec ((odd? (lambda (n) (if (= n 0) nil (even? (- n 1)))))
              (x a)
              (even? (lambda (n) (if (= n 0) t (odd? (- n 1))))))
       (odd? 1))",
    |_| ZPtr::err(EvalErr::UnboundVar)
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
// TODO FIXME
// test!(
//     test_sum,
//     "(letrec ((sum
//           (lambda (x &rest y)
//             (if y (+ x (apply sum y)) x))))
//        (sum 1 2 3 4 5 6 7 8 9 10))",
//     |_| uint(55)
// );

// commitments
test!(test_commit, "(commit 123)", |_| {
    let mut preimg = Vec::with_capacity(24);
    preimg.extend([F::zero(); 8]);
    preimg.extend(uint(123).flatten());
    ZPtr::comm(lurk_hasher().hash(&preimg).try_into().unwrap())
});
// TODO FIXME
// test!(test_hide, "(hide (bignum (commit 321)) 123)", |_| {
//     let mut secret_preimg = Vec::with_capacity(24);
//     secret_preimg.extend([F::zero(); 8]);
//     secret_preimg.extend(uint(321).flatten());
//     let hasher = lurk_hasher();
//     let mut preimg = Vec::with_capacity(24);
//     preimg.extend(hasher.hash(&secret_preimg));
//     preimg.extend(uint(123).flatten());
//     ZPtr::comm(hasher.hash(&preimg).try_into().unwrap())
// });
test!(test_hide2, "(hide (commit 321) 123)", |_| ZPtr::err(
    EvalErr::NotBigNum
));
test!(test_open_roundtrip, "(open (commit 123))", |_| uint(123));
test!(
    test_open_raw_roundtrip,
    "(begin (commit 123n) (open #c0xaa8db8504fa55b480f3da7a75f3480174f28d683f4c3ac451b7cee488d2fe))",
    |_| ZPtr::num(F::from_canonical_u32(123))
);
// TODO FIXME
// test!(test_secret, "(secret (commit 123))", |_| ZPtr::big_num(
//     [F::zero(); 8]
// ));
// TODO FIXME
// test!(
//     test_func_big_num_app,
//     "(begin (commit (lambda (x) x)) (#0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 42))",
//     |_| uint(42)
// );
// test!(
//     test_func_comm_app,
//     "(begin (commit (lambda (x) x)) ((comm #0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808) 42))",
//     |_| uint(42)
// );

// test!(
//     test_implicit_begin_let,
//     "(let () (commit (lambda (x) x)) (#0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 42))",
//     |_| uint(42)
// );
// test!(
//     test_implicit_begin_letrec,
//     "(letrec () (commit (lambda (x) x)) (#0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 42))",
//     |_| uint(42)
// );
// test!(
//     test_implicit_begin_lambda,
//     "((lambda () (commit (lambda (x) x)) (#0x275439f3606672312cd1fd9caf95cfd5bc05c6b8d224819e2e8ea1a6c5808 42)))",
//     |_| uint(42)
// );

// big num
// TODO FIXME
// test!(test_raw_big_num, "#0x0", |_| ZPtr::big_num([F::zero(); 8]));
test!(test_raw_comm, "#c0x0", |_| ZPtr::comm([F::zero(); 8]));
// TODO FIXME
// test!(
//     test_raw_big_num2,
//     "#0xaa8db8504fa55b480f3da7a75f3480174f28d683f4c3ac451b7cee488d2fe",
//     |_| {
//         let mut preimg = Vec::with_capacity(24);
//         preimg.extend([F::zero(); 8]);
//         preimg.extend(ZPtr::num(F::from_canonical_u32(123)).flatten());
//         ZPtr::big_num(lurk_hasher().hash(&preimg).try_into().unwrap())
//     }
// );
test!(
    test_raw_comm2,
    "#c0xaa8db8504fa55b480f3da7a75f3480174f28d683f4c3ac451b7cee488d2fe",
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
// TODO FIXME
// test!(test_comm_to_big_num, "(bignum #c0x0)", |_| ZPtr::big_num(
//     [F::zero(); 8]
// ));
// test!(
//     test_big_num_to_comm_to_big_num,
//     "(bignum (comm #0x0))",
//     |_| ZPtr::big_num([F::zero(); 8])
// );
// test!(
//     test_comm_to_big_num_to_comm,
//     "(comm (bignum #c0x0))",
//     |_| ZPtr::comm([F::zero(); 8])
// );
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
test!(
    test_shadow5,
    "((lambda (cons &rest car) (+ cons (car car))) 1 2 5)",
    |_| uint(3)
);
test!(
    test_shadow6,
    "((lambda (&rest &rest) (car &rest)) 1 2 5)",
    |_| uint(1)
);
test!(test_shadow7, "(let ((&rest 1)) &rest)", |_| uint(1));
test!(
    test_shadow8,
    "(let ((&rest (lambda (x) x))) (&rest 1))",
    |_| uint(1)
);

// errors
test!(test_unbound_var, "a", |_| ZPtr::err(EvalErr::UnboundVar));
test_raw!(
    test_unbound_var2,
    |z| {
        // binding the built-in `cons` but evaluating a `Tag::Sym`-tagged `cons`
        // should resuld in an unbound var error
        let let_ = z.intern_symbol_no_lang(&builtin_sym("let"));
        let cons = z.intern_symbol_no_lang(&builtin_sym("cons"));
        let one = uint(1);
        assert_eq!(cons.tag, Tag::Builtin);
        let mut cons_sym = cons;
        cons_sym.tag = Tag::Sym;
        let binding = z.intern_list([cons, one]);
        let bindings = z.intern_list([binding]);
        z.intern_list([let_, bindings, cons_sym])
    },
    |_| ZPtr::err(EvalErr::UnboundVar)
);

test!(invalid_form_let, "(let ((a 1)))", |_| ZPtr::err(
    EvalErr::InvalidForm
));
test!(invalid_form_letrec, "(letrec ((a 1)))", |_| ZPtr::err(
    EvalErr::InvalidForm
));
test!(invalid_form_lambda, "(lambda (x))", |_| ZPtr::err(
    EvalErr::InvalidForm
));

test!(test_div_by_zero_fel, "(/ 1n 0n)", |_| ZPtr::err(
    EvalErr::DivByZero
));
test!(test_div_by_zero, "(/ 1 0)", |_| ZPtr::err(
    EvalErr::DivByZero
));
test!(test_equal_non_num, "(= 'a 'a)", |_| ZPtr::err(
    EvalErr::InvalidArg
));
test!(test_equal_non_num2, "(= (comm #0x0) (comm #0x0))", |_| {
    ZPtr::err(EvalErr::InvalidArg)
});
// TODO FIXME
// test!(
//     test_shadow_err1,
//     "(let ((nil 1)) (+ nil 1))",
//     |_| ZPtr::err(EvalErr::IllegalBindingVar)
// );
// test!(test_shadow_err2, "(letrec ((nil 1)) (+ nil 1))", |_| {
//     ZPtr::err(EvalErr::IllegalBindingVar)
// });
// test!(test_shadow_err3, "((lambda (nil) (+ nil 1)) 1)", |_| {
//     ZPtr::err(EvalErr::IllegalBindingVar)
// });
// test!(test_shadow_err4, "(let ((t 1)) (+ t 1))", |_| ZPtr::err(
//     EvalErr::IllegalBindingVar
// ));
// test!(test_shadow_err5, "(letrec ((t 1)) (+ t 1))", |_| ZPtr::err(
//     EvalErr::IllegalBindingVar
// ));
// test!(test_shadow_err6, "((lambda (t) (+ t 1)) 1)", |_| ZPtr::err(
//     EvalErr::IllegalBindingVar
// ));
// test!(test_shadow_err7, "((lambda (x &rest t) (+ x 1)) 1)", |_| {
//     ZPtr::err(EvalErr::IllegalBindingVar)
// });
// test!(
//     test_shadow_err8,
//     "((lambda (x &rest nil) (+ x 1)) 1)",
//     |_| ZPtr::err(EvalErr::IllegalBindingVar)
// );
// test!(test_rest_err1, "((lambda (x &rest) x) 1)", |_| ZPtr::err(
//     EvalErr::ParamInvalidRest
// ));
// test!(test_rest_err2, "((lambda (x &rest y z) x) 1)", |_| {
//     ZPtr::err(EvalErr::ParamInvalidRest)
// });
// test!(test_rest_err3, "((lambda (&rest y z) z) 1)", |_| ZPtr::err(
//     EvalErr::ParamInvalidRest
// ));
// test!(test_rest_err4, "((lambda (&rest) &rest) 1)", |_| {
//     ZPtr::err(EvalErr::ParamInvalidRest)
// });
