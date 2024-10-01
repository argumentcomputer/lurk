//! Tests for the correct coupling of custom coroutines and gadgets

use once_cell::sync::OnceCell;
use p3_air::AirBuilder;
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rustc_hash::FxHashSet;
use sphinx_core::utils::BabyBearPoseidon2;

use crate::{
    func,
    lair::{chipset::Chipset, toplevel::Toplevel, Name},
    lurk::{
        chipset::LurkChip,
        eval::{build_lurk_toplevel, EvalErr},
        lang::{Coroutine, Lang},
        state::user_sym,
        symbol::Symbol,
        tag::Tag,
        zstore::{ZPtr, ZStore},
    },
};

use super::run_tests;

struct SquareGadget;

impl<F: AbstractField> Chipset<F> for SquareGadget {
    fn input_size(&self) -> usize {
        1
    }

    fn output_size(&self) -> usize {
        1
    }

    fn execute_simple(&self, input: &[F]) -> Vec<F> {
        vec![input[0].clone() * input[0].clone()]
    }

    fn witness_size(&self) -> usize {
        1
    }

    fn require_size(&self) -> usize {
        0
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        witness[0] = input[0].clone() * input[0].clone();
        witness[..1].to_vec()
    }

    fn eval<AB: crate::air::builder::LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        input: Vec<AB::Expr>,
        witness: &[AB::Var],
        _nonce: AB::Expr,
        _requires: &[crate::air::builder::RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        builder
            .when(is_real)
            .assert_eq(input[0].clone() * input[0].clone(), witness[0]);
        vec![witness[0].into()]
    }
}

fn extern_square<F: AbstractField>() -> Coroutine<F> {
    let func_expr = func!(
        fn extern_square(num_tag, num): [2] {
            match num_tag {
                Tag::Num => {
                    let squared = extern_call(square_gadget, num);
                    return (num_tag, squared)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::InvalidArg;
            return (err_tag, err)
        }
    );
    Coroutine {
        lurk_arity: 1,
        func_expr,
        uses_env: false,
    }
}

fn mul_square<F: AbstractField>() -> Coroutine<F> {
    let func_expr = func!(
        fn mul_square(num_tag, num): [2] {
            match num_tag {
                Tag::Num => {
                    let squared = mul(num, num);
                    return (num_tag, squared)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::InvalidArg;
            return (err_tag, err)
        }
    );
    Coroutine {
        lurk_arity: 1,
        func_expr,
        uses_env: false,
    }
}

fn square_lang<F: AbstractField>() -> Lang<F, SquareGadget> {
    Lang::new(
        [
            (user_sym("extern-square"), extern_square()),
            (user_sym("mul-square"), mul_square()),
        ],
        [(Name("square_gadget"), SquareGadget)],
    )
}

type F = BabyBear;

#[allow(clippy::type_complexity)]
static TEST_SETUP_DATA: OnceCell<(
    FxHashSet<Symbol>,
    Toplevel<F, LurkChip, SquareGadget>,
    ZStore<F, LurkChip>,
    BabyBearPoseidon2,
)> = OnceCell::new();

#[allow(clippy::type_complexity)]
fn test_setup_data() -> &'static (
    FxHashSet<Symbol>,
    Toplevel<F, LurkChip, SquareGadget>,
    ZStore<F, LurkChip>,
    BabyBearPoseidon2,
) {
    TEST_SETUP_DATA.get_or_init(|| {
        let lang = square_lang();
        let (toplevel, zstore, lang_symbols) = build_lurk_toplevel(lang);
        let config = BabyBearPoseidon2::new();
        (lang_symbols, toplevel, zstore, config)
    })
}

fn test_case(input_code: &'static str, expected_cloj: fn(&mut ZStore<F, LurkChip>) -> ZPtr<F>) {
    let (lang_symbols, toplevel, zstore, config) = test_setup_data();
    let mut zstore = zstore.clone();
    let zptr = zstore.read(input_code, lang_symbols).expect("Read failure");
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
    ($test_func:ident, $input_code:expr, $expected_cloj:expr) => {
        #[test]
        fn $test_func() {
            test_case($input_code, $expected_cloj)
        }
    };
}

fn num(n: u32) -> ZPtr<F> {
    ZPtr::num(F::from_canonical_u32(n))
}

test!(test_mul, "(mul-square (+ 1n 2n))", |_| num(9));
test!(test_extern, "(extern-square (+ 1n 2n))", |_| num(9));

test!(test_mul_undersaturated, "(mul-square)", |_| ZPtr::err(
    EvalErr::InvalidForm
));
test!(
    test_extern_undersaturated,
    "(extern-square)",
    |_| ZPtr::err(EvalErr::InvalidForm)
);

test!(test_mul_oversaturated, "(mul-square 3n 2n)", |_| ZPtr::err(
    EvalErr::InvalidForm
));
test!(test_extern_oversaturated, "(extern-square 3n 2n)", |_| {
    ZPtr::err(EvalErr::InvalidForm)
});

test!(test_mul_mistype, "(mul-square 3)", |_| ZPtr::err(
    EvalErr::InvalidArg
));
test!(test_extern_mistype, "(extern-square 3)", |_| ZPtr::err(
    EvalErr::InvalidArg
));

test!(test_mul_arg_err, "(mul-square a)", |_| ZPtr::err(
    EvalErr::UnboundVar
));
test!(test_extern_arg_err, "(extern-square a)", |_| ZPtr::err(
    EvalErr::UnboundVar
));

test!(
    test_mul_shadow1,
    "(let ((mul-square 1n)) mul-square)",
    |_| num(1)
);
test!(
    test_extern_shadow1,
    "(let ((extern-square 1n)) extern-square)",
    |_| num(1)
);

test!(
    test_mul_shadow2,
    "(letrec ((mul-square 1n)) mul-square)",
    |_| num(1)
);
test!(
    test_extern_shadow2,
    "(letrec ((extern-square 1n)) extern-square)",
    |_| num(1)
);

test!(
    test_mul_shadow3,
    "((lambda (mul-square) (+ mul-square 1n)) 2n)",
    |_| num(3)
);
test!(
    test_extern_shadow3,
    "((lambda (extern-square) (+ extern-square 1n)) 2n)",
    |_| num(3)
);
