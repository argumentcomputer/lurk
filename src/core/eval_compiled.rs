use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField32};
use rustc_hash::FxHashSet;

use crate::{
    core::{
        big_num::field_elts_to_biguint,
        compile::{Op, Val},
        error::EvalErr,
        ingress::InternalTag,
    },
    func,
    lair::{
        chipset::{Chipset, NoChip},
        expr::FuncE,
        toplevel::Toplevel,
        FxIndexMap,
    },
};

use super::{
    chipset::{lurk_chip_map, LurkChip},
    compile::{
        compile, compile_fold_left, compile_fold_rel, compile_fold_right, compile_lambda,
        compile_let, compile_mutual_binds, convert_data, deconvert_data, symbol_to_op,
    },
    ingress::{egress, ingress, preallocate_symbols, SymbolsDigests},
    lang::{Coroutine, Lang},
    misc::{
        big_num_lessthan, commit, digest_equal, hash4, hash5, u64_add, u64_divrem, u64_iszero,
        u64_lessthan, u64_mul, u64_sub,
    },
    symbol::Symbol,
    tag::Tag,
    zstore::{lurk_zstore, ZStore},
};

fn native_lurk_funcs<F: PrimeField32>(
    digests: &SymbolsDigests<F>,
    _coroutines: &FxIndexMap<Symbol, Coroutine<F>>,
) -> [FuncE<F>; 35] {
    [
        // Entrypoint
        lurk_main(),
        // Builtins
        preallocate_symbols(digests),
        // External chip wrappers
        commit(),
        hash4(),
        hash5(),
        u64_add(),
        u64_sub(),
        u64_mul(),
        u64_divrem(),
        u64_lessthan(),
        u64_iszero(),
        digest_equal(),
        big_num_lessthan(),
        // Ingress/Egress
        ingress(digests),
        egress(digests),
        // Compiler
        compile(digests),
        symbol_to_op(digests),
        compile_lambda(digests),
        compile_let(),
        compile_mutual_binds(),
        compile_fold_right(),
        compile_fold_left(),
        compile_fold_rel(digests),
        convert_data(digests),
        deconvert_data(digests),
        // Evaluator
        eval(),
        apply(),
        eval_unop(digests),
        eval_binop(digests),
        eval_binop_num(digests),
        eval_op_misc(),
        extend_env_with_mutuals(),
        eval_mutual_bindings(),
        env_lookup(),
        equal_inner(),
    ]
}

/// Creates a `Toplevel` with the functions used for Lurk evaluation, also returning
/// a `ZStore` with the Lurk builtins already interned.
#[inline]
pub fn build_lurk_toplevel<C2: Chipset<BabyBear>>(
    lang: Lang<BabyBear, C2>,
) -> (
    Toplevel<BabyBear, LurkChip, C2>,
    ZStore<BabyBear, LurkChip>,
    FxHashSet<Symbol>,
) {
    let mut zstore = lurk_zstore();
    let lang_symbols = lang.coroutines().keys().cloned().collect();
    let digests = SymbolsDigests::new(&lang_symbols, &mut zstore);
    let (coroutines, gadgets) = lang.into_parts();
    let mut func_expr_map: FxIndexMap<_, _> = native_lurk_funcs(&digests, &coroutines)
        .into_iter()
        .map(|func_expr| (func_expr.name, func_expr))
        .collect();
    for coroutine in coroutines.into_values() {
        let Coroutine { func_expr, .. } = coroutine;
        let name = func_expr.name;
        assert!(
            !func_expr_map.contains_key(&name),
            "Name conflict with native function {name}"
        );
        func_expr_map.insert(name, func_expr);
    }
    let funcs_exprs: Vec<_> = func_expr_map.into_values().collect();
    let lurk_chip_map = lurk_chip_map(gadgets);
    let toplevel = Toplevel::new(&funcs_exprs, lurk_chip_map);
    (toplevel, zstore, lang_symbols)
}

#[inline]
pub fn build_lurk_toplevel_native() -> (
    Toplevel<BabyBear, LurkChip, NoChip>,
    ZStore<BabyBear, LurkChip>,
    FxHashSet<Symbol>,
) {
    build_lurk_toplevel(Lang::empty())
}

pub fn lurk_main<F: AbstractField>() -> FuncE<F> {
    func!(
        partial fn lurk_main(full_expr_tag: [8], expr_digest: [8], env_digest: [8]): [16] {
            let _foo: [0] = call(preallocate_symbols,); // TODO: replace by `exec` - needs to be constrained to run though
            // Ingress
            let (expr_tag, expr) = call(ingress, full_expr_tag, expr_digest);
            let env_tag = Tag::Env;
            let padding = [0; 7];
            let (_env_tag, env) = call(ingress, env_tag, padding, env_digest);
            // Compile
            let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
            let (cenv_tag, cenv) = call(convert_data, env_tag, env);
            // If the environment is incorrect, return immediately the error
            match cenv_tag {
                Tag::Err => {
                    let (res_tag, res_digest: [8]) = call(egress, cenv_tag, cenv);
                    return (res_tag, padding, res_digest)
                }
            };
            // Eval
            let (cval_tag, cval) = call(eval, cexpr_tag, cexpr, cenv);
            // Decompile
            let (val_tag, val) = call(deconvert_data, cval_tag, cval);
            // Egress
            let (val_tag, val_digest: [8]) = call(egress, val_tag, val);
            return (val_tag, padding, val_digest)
        }
    )
}

pub fn eval<F: AbstractField>() -> FuncE<F> {
    func!(
        partial fn eval(expr_tag, expr, env): [2] {
            match expr_tag {
                Val::Fun, Val::Thunk, Val::RestFun, Tag::U64, Tag::Num, Tag::BigNum, Tag::Comm, Tag::Char, Tag::Str,
                Tag::Key, Tag::Fun, Tag::Cons, Tag::Env, Tag::Err, InternalTag::T, InternalTag::Nil => {
                    return (expr_tag, expr)
                }
                Tag::Builtin, Tag::Sym, Tag::Coroutine => {
                    let expr_digest: [8] = load(expr);
                    let (res_tag, res) = call(env_lookup, expr_tag, expr_digest, env);
                    match res_tag {
                        Val::Fix => {
                            // Fixed points are closed expressions, so we can choose an empty environment
                            let null_env = 0;
                            let (res_tag, res) = call(eval, res_tag, res, null_env);
                            return (res_tag, res)
                        }
                    };
                    return (res_tag, res)
                }
                Val::Fix => {
                    let (body_tag, body, binds, mutual_env) = load(expr);
                    // extend `mutual_env` with the fixed points from the `letrec` bindings
                    let ext_env = call(extend_env_with_mutuals, binds, binds, mutual_env);
                    let (res_tag, res) = call(eval, body_tag, body, ext_env);
                    return (res_tag, res)
                }
                // immediate operations
                Op::MkThunk => {
                    let (cbody_tag, cbody) = load(expr);
                    let tag = Val::Thunk;
                    let ptr = store(cbody_tag, cbody, env);
                    return (tag, ptr)
                }
                Op::MkFun => {
                    let (var_tag, var, cbody_tag, cbody) = load(expr);
                    let tag = Val::Fun;
                    let ptr = store(var_tag, var, cbody_tag, cbody, env);
                    return (tag, ptr)
                }
                Op::MkRestFun => {
                    let (var_tag, var, cbody_tag, cbody) = load(expr);
                    let tag = Val::RestFun;
                    let ptr = store(var_tag, var, cbody_tag, cbody, env);
                    return (tag, ptr)
                }
                Op::App => {
                    let (head_tag, head, args_tag, args) = load(expr);
                    let (fun_tag, fun) = call(eval, head_tag, head, env);
                    let (val_tag, val) = call(apply, fun_tag, fun, args_tag, args, env);
                    return (val_tag, val)
                }
                Op::Car, Op::Cdr, Op::Atom, Op::Open, Op::Secret, Op::U64, Op::Char, Op::Comm, Op::Bignum, Op::Emit => {
                    // The reason this is unconstrained is because `eval_unop` fully constrains the tag
                    #[unconstrained]
                    let (val_tag, val) = call(eval_unop, expr_tag, expr, env);
                    return (val_tag, val)
                }
                Op::MkCons, Op::MkStrcons, Op::Eq, Op::TypeEq, Op::Begin, Op::Hide => {
                    // The reason this is unconstrained is because `eval_binop` fully constrains the tag
                    #[unconstrained]
                    let (val_tag, val) = call(eval_binop, expr_tag, expr, env);
                    return (val_tag, val)
                }
                Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Mod, Op::Less, Op::LessEq, Op::Great, Op::GreatEq, Op::NumEq => {
                    // The reason this is unconstrained is because `eval_binop` fully constrains the tag
                    #[unconstrained]
                    let (val_tag, val) = call(eval_binop_num, expr_tag, expr, env);
                    return (val_tag, val)
                }
            };
            // The reason this is unconstrained is because `eval_op_misc` fully constrains the tag
            #[unconstrained]
            let (val_tag, val) = call(eval_op_misc, expr_tag, expr, env);
            return (val_tag, val)
        }
    )
}

pub fn apply<F: AbstractField>() -> FuncE<F> {
    func!(
        partial fn apply(fun_tag, fun, args_tag, args, env): [2] {
            match fun_tag {
                Val::Fun => {
                    let (param_tag, param, body_tag, body, fun_env) = load(fun);
                    // `args` can only be a nil or a make-cons
                    match args_tag {
                        InternalTag::Nil => {
                            return (fun_tag, fun)
                        }
                        Op::MkCons => {
                            let (arg_tag, arg, rest_args_tag, rest_args) = load(args);
                            let (arg_tag, arg) = call(eval, arg_tag, arg, env);
                            match arg_tag {
                                Tag::Err => {
                                    return (arg_tag, arg)
                                }
                            };
                            let ext_env = store(param_tag, param, arg_tag, arg, fun_env);
                            let (head_tag, head) = call(eval, body_tag, body, ext_env);
                            match rest_args_tag {
                                InternalTag::Nil => {
                                    return (head_tag, head)
                                }
                            };
                            let (res_tag, res) = call(apply, head_tag, head, rest_args_tag, rest_args, env);
                            return (res_tag, res)
                        }
                    }
                }
                Val::RestFun => {
                    let (param_tag, param, body_tag, body, fun_env) = load(fun);
                    let (args_list_tag, args_list) = call(eval, args_tag, args, env);
                    match args_list_tag {
                        Tag::Err => {
                            return (args_list_tag, args_list)
                        }
                    };
                    let ext_env = store(param_tag, param, args_list_tag, args_list, fun_env);
                    let (res_tag, res) = call(eval, body_tag, body, ext_env);
                    return (res_tag, res)
                }
                Val::Thunk => {
                    let (body_tag, body, thunk_env) = load(fun);
                    let (val_tag, val) = call(eval, body_tag, body, thunk_env);
                    match args_tag {
                        InternalTag::Nil => {
                            return (val_tag, val)
                        }
                    };
                    let (res_tag, res) = call(apply, val_tag, val, args_tag, args, env);
                    return (res_tag, res)
                }
                Tag::Err => {
                    return (fun_tag, fun)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::ApplyNonFunc;
            return (err_tag, err)
        }
    )
}

pub fn eval_unop<F: PrimeField32>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        partial fn eval_unop(expr_tag, expr, env): [2] {
            match expr_tag {
                Op::Car, Op::Cdr, Op::Atom, Op::Open, Op::Secret, Op::U64, Op::Char, Op::Comm, Op::Bignum, Op::Emit => {
                    let (arg_tag, arg) = load(expr);
                    let (arg_tag, arg) = call(eval, arg_tag, arg, env);
                    match arg_tag {
                        Tag::Err => {
                            return (arg_tag, arg)
                        }
                    };
                    let err_tag = Tag::Err;
                    let nil_tag = InternalTag::Nil;
                    let nil = digests.lurk_symbol_ptr("nil");
                    match expr_tag {
                        Op::Car => {
                            match arg_tag {
                                Tag::Cons => {
                                    let (car_tag, car, _cdr_tag, _cdr) = load(arg);
                                    return (car_tag, car)
                                }
                                InternalTag::Nil => {
                                    return (nil_tag, nil)
                                }
                                Tag::Str => {
                                    let empty = 0;
                                    let not_empty = sub(arg, empty);
                                    if not_empty {
                                        let (car_tag, car, _cdr_tag, _cdr) = load(arg);
                                        return (car_tag, car)
                                    }
                                    return (nil_tag, nil)
                                }
                            };
                            let not_cons = EvalErr::NotCons;
                            return (err_tag, not_cons)
                        }
                        Op::Cdr => {
                            match arg_tag {
                                Tag::Cons => {
                                    let (_car_tag, _car, cdr_tag, cdr) = load(arg);
                                    return (cdr_tag, cdr)
                                }
                                InternalTag::Nil => {
                                    return (nil_tag, nil)
                                }
                                Tag::Str => {
                                    let empty = 0;
                                    let not_empty = sub(arg, empty);
                                    if not_empty {
                                        let (_car_tag, _car, cdr_tag, cdr) = load(arg);
                                        return (cdr_tag, cdr)
                                    }
                                    return (nil_tag, nil)
                                }
                            };
                            let not_cons = EvalErr::NotCons;
                            return (err_tag, not_cons)
                        }
                        Op::Atom => {
                            match arg_tag {
                                Tag::Cons => {
                                    let t_tag = InternalTag::T;
                                    let t = digests.lurk_symbol_ptr("t");
                                    return (t_tag, t)
                                }
                            };
                            return (nil_tag, nil)
                        }
                        Op::Open, Op::Secret => {
                            match arg_tag {
                                Tag::Comm, Tag::BigNum => {
                                    let comm_hash: [8] = load(arg);
                                    let (secret: [8], tag, padding: [7], arg_digest: [8]) = preimg(
                                        commit,
                                        comm_hash,
                                        |fs| format!("Preimage not found for #{:#x}", field_elts_to_biguint(fs))
                                    );
                                    match expr_tag {
                                        Op::Open => {
                                            let (tag, ptr) = call(ingress, tag, padding, arg_digest);
                                            return (tag, ptr)
                                        }
                                        Op::Secret => {
                                            let ptr = store(secret);
                                            let big_num_tag = Tag::BigNum;
                                            return (big_num_tag, ptr)
                                        }
                                    }
                                }
                            };
                            let cant_open = EvalErr::CantOpen;
                            return (err_tag, cant_open)
                        }
                        Op::U64 => {
                            match arg_tag {
                                Tag::U64 => {
                                    return (arg_tag, arg)
                                }
                                Tag::Char => {
                                    let bytes: [4] = load(arg);
                                    let padding = [0; 4];
                                    let val = store(bytes, padding);
                                    let val_tag = Tag::U64;
                                    return (val_tag, val)
                                }
                            };
                            let err = EvalErr::CantCastToU64;
                            return(err_tag, err)
                        }
                        Op::Emit => {
                            emit(arg_tag, arg);
                            return (arg_tag, arg)
                        }
                        Op::Comm => {
                            match arg_tag {
                                Tag::BigNum => {
                                    let comm_tag = Tag::Comm;
                                    return (comm_tag, arg)
                                }
                                Tag::Comm => {
                                    return (arg_tag, arg)
                                }
                            };
                            let err = EvalErr::CantCastToComm;
                            return(err_tag, err)
                        }
                        Op::Char => {
                            match arg_tag {
                                Tag::Char => {
                                    return (arg_tag, arg)
                                }
                                Tag::U64 => {
                                    let (bytes: [4], _ignored: [4]) = load(arg);
                                    let arg = store(bytes);
                                    let arg_tag = Tag::Char;
                                    return (arg_tag, arg)
                                }
                            };
                            let err = EvalErr::CantCastToChar;
                            return(err_tag, err)
                        }
                    }
                }
            }
        }
    )
}

pub fn eval_binop<F: PrimeField32>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        partial fn eval_binop(expr_tag, expr, env): [2] {
            match expr_tag {
                Op::MkCons, Op::MkStrcons, Op::Eq, Op::TypeEq, Op::Begin, Op::Hide => {
                    let (exp1_tag, exp1, exp2_tag, exp2) = load(expr);
                    let (val1_tag, val1) = call(eval, exp1_tag, exp1, env);
                    match val1_tag {
                        Tag::Err => {
                            return (val1_tag, val1)
                        }
                    };
                    let (val2_tag, val2) = call(eval, exp2_tag, exp2, env);
                    match val2_tag {
                        Tag::Err => {
                            return (val2_tag, val2)
                        }
                    };
                    match expr_tag {
                        Op::MkCons => {
                            let cons_tag = Tag::Cons;
                            let cons = store(val1_tag, val1, val2_tag, val2);
                            return (cons_tag, cons)
                        }
                        Op::MkStrcons => {
                            let err_tag = Tag::Err;
                            let char_tag = Tag::Char;
                            let str_tag = Tag::Str;
                            let strcons = store(val1_tag, val1, val2_tag, val2);
                            let not_char = sub(val1_tag, char_tag);
                            let not_str = sub(val2_tag, str_tag);
                            if not_char {
                                let err = EvalErr::NotChar;
                                return (err_tag, err)
                            }
                            if not_str {
                                let err = EvalErr::NotString;
                                return (err_tag, err)
                            }
                            return (str_tag, strcons)
                        }
                        Op::Begin => {
                            return (val2_tag, val2)
                        }
                        Op::Hide => {
                            let err_tag = Tag::Err;
                            match val1_tag {
                                Tag::BigNum => {
                                    let secret: [8] = load(val1);
                                    let (val2_tag, val2_digest: [8]) = call(egress, val2_tag, val2);
                                    let padding = [0; 7];
                                    let comm_hash: [8] = call(commit, secret, val2_tag, padding, val2_digest);
                                    let comm_ptr = store(comm_hash);
                                    let comm_tag = Tag::Comm;
                                    return (comm_tag, comm_ptr)
                                }
                            };
                            let not_comm = EvalErr::NotBigNum;
                            return (err_tag, not_comm)
                        }
                        Op::Eq => {
                            let eq = call(equal_inner, val1_tag, val1, val2_tag, val2);
                            if eq {
                                let t_tag = InternalTag::T;
                                let t = digests.lurk_symbol_ptr("t");
                                return (t_tag, t)
                            }
                            let nil_tag = InternalTag::Nil;
                            let nil = digests.lurk_symbol_ptr("nil");
                            return (nil_tag, nil)
                        }
                        Op::TypeEq => {
                            let type_not_eq = sub(val1_tag, val2_tag);
                            if type_not_eq {
                                let t_tag = InternalTag::T;
                                let t = digests.lurk_symbol_ptr("t");
                                return (t_tag, t)
                            }
                            let nil = digests.lurk_symbol_ptr("nil");
                            let nil_tag = InternalTag::Nil;
                            return (nil_tag, nil)
                        }
                    }
                }
            }
        }
    )
}

pub fn eval_binop_num<F: PrimeField32>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        partial fn eval_binop_num(expr_tag, expr, env): [2] {
            match expr_tag {
                Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Mod, Op::Less, Op::LessEq, Op::Great, Op::GreatEq, Op::NumEq => {
                    let err_tag = Tag::Err;
                    let num_tag = Tag::Num;
                    let u64_tag = Tag::U64;
                    let err_div_zero = EvalErr::DivByZero;
                    let nil = digests.lurk_symbol_ptr("nil");
                    let nil_tag = InternalTag::Nil;
                    let t = digests.lurk_symbol_ptr("t");
                    let t_tag = InternalTag::T;

                    let (exp1_tag, exp1, exp2_tag, exp2) = load(expr);
                    let (val1_tag, val1) = call(eval, exp1_tag, exp1, env);
                    match val1_tag {
                        Tag::Err => {
                            return (val1_tag, val1)
                        }
                    };
                    let (val2_tag, val2) = call(eval, exp2_tag, exp2, env);
                    match val2_tag {
                        Tag::Err => {
                            return (val2_tag, val2)
                        }
                    };

                    let tags: [2] = (val1_tag, val2_tag);
                    match tags {
                        [Tag::U64, Tag::U64] => {
                            match expr_tag {
                                Op::Add => {
                                    let res = call(u64_add, val1, val2);
                                    return (u64_tag, res)
                                }
                                Op::Sub => {
                                    let res = call(u64_sub, val1, val2);
                                    return (u64_tag, res)
                                }
                                Op::Mul => {
                                    let res = call(u64_mul, val1, val2);
                                    return (u64_tag, res)
                                }
                                Op::Div, Op::Mod => {
                                    let is_zero = call(u64_iszero, val2);
                                    if is_zero {
                                        return (err_tag, err_div_zero)
                                    }
                                    let (quot, rem) = call(u64_divrem, val1, val2);
                                    match expr_tag {
                                        Op::Div => {
                                            return (u64_tag, quot)
                                        }
                                        Op::Mod => {
                                            return (u64_tag, rem)
                                        }
                                    }
                                }
                                Op::Less => {
                                    let res = call(u64_lessthan, val1, val2);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                                Op::GreatEq => {
                                    let res = call(u64_lessthan, val1, val2);
                                    if res {
                                        return (nil_tag, nil)
                                    }
                                    return (t_tag, t)

                                }
                                Op::Great => {
                                    let res = call(u64_lessthan, val2, val1);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                                Op::LessEq => {
                                    let res = call(u64_lessthan, val2, val1);
                                    if res {
                                        return (nil_tag, nil)
                                    }
                                    return (t_tag, t)
                                }
                                Op::NumEq => {
                                    let res = call(digest_equal, val1, val2);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                            }
                        }
                        [Tag::Num, Tag::Num] => {
                            match expr_tag {
                                Op::Add => {
                                    let res = add(val1, val2);
                                    return (num_tag, res)
                                }
                                Op::Sub => {
                                    let res = sub(val1, val2);
                                    return (num_tag, res)
                                }
                                Op::Mul => {
                                    let res = mul(val1, val2);
                                    return (num_tag, res)
                                }
                                Op::Div => {
                                    if !val2 {
                                        return (err_tag, err_div_zero)
                                    }
                                    let res = div(val1, val2);
                                    return (num_tag, res)
                                }
                                Op::NumEq => {
                                    let diff = sub(val1, val2);
                                    if diff {
                                        return (nil_tag, nil)
                                    }
                                    return (t_tag, t)
                                }
                                Op::Mod, Op::Less, Op::Great, Op::LessEq, Op::GreatEq => {
                                    let err = EvalErr::NotU64;
                                    return (err_tag, err)
                                }
                            }
                        }
                        [Tag::BigNum, Tag::BigNum] => {
                            match expr_tag {
                                Op::Less => {
                                    let res = call(big_num_lessthan, val1, val2);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                                Op::GreatEq => {
                                    let res = call(big_num_lessthan, val1, val2);
                                    if res {
                                        return (nil_tag, nil)
                                    }
                                    return (t_tag, t)

                                }
                                Op::Great => {
                                    let res = call(big_num_lessthan, val2, val1);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                                Op::LessEq => {
                                    let res = call(big_num_lessthan, val2, val1);
                                    if res {
                                        return (nil_tag, nil)
                                    }
                                    return (t_tag, t)
                                }
                                Op::NumEq => {
                                    let res = call(digest_equal, val2, val1);
                                    if res {
                                        return (t_tag, t)
                                    }
                                    return (nil_tag, nil)
                                }
                                Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Mod => {
                                    let err = EvalErr::InvalidArg;
                                    return (err_tag, err)
                                }
                            }
                        }
                    };
                    let err = EvalErr::InvalidArg;
                    return (err_tag, err)
                }
            }
        }
    )
}

pub fn eval_op_misc<F: PrimeField32>() -> FuncE<F> {
    func!(
        partial fn eval_op_misc(expr_tag, expr, env): [2] {
            match expr_tag {
                // immediate operations
                Op::EmptyEnv => {
                    let env_tag = Tag::Env;
                    let env = 0;
                    return (env_tag, env)
                }
                Op::CurrentEnv => {
                    let env_tag = Tag::Env;
                    return (env_tag, env)
                }
                Op::Quote => {
                    let (res_tag, res) = load(expr);
                    return (res_tag, res)
                }
                Op::Fail => {
                    let zero = 0;
                    let one = 1;
                    assert_eq!(zero, one, |_, _| "Explicit fail encountered".to_string());
                    return (zero, zero)
                }
                // other operations
                Op::Let => {
                    let (param_tag, param, val_tag, val, body_tag, body) = load(expr);
                    let (val_tag, val) = call(eval, val_tag, val, env);
                    match val_tag {
                        Tag::Err => {
                            return (val_tag, val)
                        }
                    };
                    let env = store(param_tag, param, val_tag, val, env);
                    let (res_tag, res) = call(eval, body_tag, body, env);
                    return (res_tag, res)
                }
                Op::Letrec => {
                    // extend `env` with the bindings from the mutual env
                    let (binds, body_tag, body) = load(expr);
                    let ext_env = call(extend_env_with_mutuals, binds, binds, env);
                    // preemptively evaluate each binding value for side-effects, error detection and memoization
                    let (res_tag, res) = call(eval_mutual_bindings, env, ext_env);
                    match res_tag {
                        Tag::Err => {
                            return (res_tag, res)
                        }
                    };
                    let (res_tag, res) = call(eval, body_tag, body, ext_env);
                    return (res_tag, res)
                }
                Op::If => {
                    let (b_tag, b, t_tag, t, f_tag, f) = load(expr);
                    let (b_tag, b) = call(eval, b_tag, b, env);
                    match b_tag {
                        InternalTag::Nil => {
                            let (res_tag, res) = call(eval, f_tag, f, env);
                            return (res_tag, res)
                        }
                        Tag::Err => {
                            return (b_tag, b)
                        }
                    };
                    let (res_tag, res) = call(eval, t_tag, t, env);
                    return (res_tag, res)
                }
                Op::App, Op::Apply,
                Op::And, Op::Or, Op::Not, Op::Eval, Op::Breakpoint => {
                    let err_tag = Tag::Err;
                    let err = EvalErr::Todo;
                    return (err_tag, err)
                }
                Op::Eqq, Op::TypeEqq => {
                    // (might be compiled away)
                    let err_tag = Tag::Err;
                    let err = EvalErr::Todo;
                    return (err_tag, err)
                }
            }
        }
    )
}

pub fn equal_inner<F: AbstractField>() -> FuncE<F> {
    func!(
        fn equal_inner(a_tag, a, b_tag, b): [1] {
            let not_eq_tag = sub(a_tag, b_tag);
            let zero = 0;
            let one = 1;
            if not_eq_tag {
                return zero
            }
            let not_eq = sub(a, b);
            if !not_eq {
                return one
            }
            match a_tag {
                // The Nil and Err cases are impossible
                Tag::Num => {
                    return zero
                }
                Tag::Char => {
                    let a_bytes: [4] = load(a);
                    let b_bytes: [4] = load(b);
                    let diff = sub(a_bytes, b_bytes);
                    if diff {
                        return zero
                    }
                    return one
                }
                Tag::Key, Tag::Sym, Tag::Builtin, Tag::Coroutine, Tag::U64, Tag::BigNum, Tag::Comm => {
                    let a_digest: [8] = load(a);
                    let b_digest: [8] = load(b);
                    let diff = sub(a_digest, b_digest);
                    if diff {
                        return zero
                    }
                    return one
                }
                Tag::Str => {
                    let a_and_b = mul(a, b);
                    if !a_and_b {
                        return zero
                    }
                    let (a_fst: [2], a_snd: [2]) = load(a);
                    let (b_fst: [2], b_snd: [2]) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, a_snd, b_snd);
                    let eq = mul(fst_eq, snd_eq);
                    return eq
                }
                Tag::Cons => {
                    let (a_fst: [2], a_snd: [2]) = load(a);
                    let (b_fst: [2], b_snd: [2]) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, a_snd, b_snd);
                    let eq = mul(fst_eq, snd_eq);
                    return eq
                }
                Tag::Env => {
                    let a_and_b = mul(a, b);
                    if !a_and_b {
                        return zero
                    }
                    let (a_fst: [2], a_snd: [2], a_trd) = load(a);
                    let (b_fst: [2], b_snd: [2], b_trd) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, a_snd, b_snd);
                    let trd_eq = call(equal_inner, a_tag, a_trd, a_tag, b_trd); // `a_tag` is `Tag::Env`
                    let eq = mul(fst_eq, snd_eq);
                    let eq = mul(eq, trd_eq);
                    return eq
                }
                Val::RestFun, Val::Fun, Val::Fix, Val::Thunk => {
                    // TODO
                    let zero = 0;
                    return zero
                }
            }
        }
    )
}

pub fn env_lookup<F: AbstractField>() -> FuncE<F> {
    func!(
        fn env_lookup(x_tag_digest: [9], env): [2] {
            if !env {
                let err_tag = Tag::Err;
                let err = EvalErr::UnboundVar;
                return (err_tag, err)
            }
            let (y_tag, y, val_tag, val, tail_env) = load(env);
            let y_digest: [8] = load(y);
            let y_tag_digest: [9] = (y_tag, y_digest);
            let not_eq = sub(x_tag_digest, y_tag_digest);
            if !not_eq {
                return (val_tag, val)
            }
            let (res_tag, res) = call(env_lookup, x_tag_digest, tail_env);
            return (res_tag, res)
        }
    )
}

pub fn extend_env_with_mutuals<F: AbstractField>() -> FuncE<F> {
    func!(
        fn extend_env_with_mutuals(binds, mutual_binds, mutual_env): [1] {
            if !binds {
                return mutual_env
            }
            let (var_tag, var, expr_tag, expr, binds) = load(binds);
            let ext_env = call(extend_env_with_mutuals, binds, mutual_binds, mutual_env);
            let fix_tag = Val::Fix;
            let fix = store(expr_tag, expr, mutual_binds, mutual_env);
            let res_env = store(var_tag, var, fix_tag, fix, ext_env);
            return res_env
        }
    )
}

pub fn eval_mutual_bindings<F: AbstractField>() -> FuncE<F> {
    func!(
        partial fn eval_mutual_bindings(init_env, ext_env): [2] {
            let not_eq = sub(ext_env, init_env);
            if !not_eq {
                let env_tag = Tag::Env;
                return (env_tag, init_env)
            }
            let (_var_tag, _var, val_tag, val, ext_env) = load(ext_env);
            let fix_tag = Val::Fix;
            // Safety check: letrec bindings must be fixed points
            assert_eq!(fix_tag, val_tag);
            let null_env = 0;
            // Fixed points are closed expressions, so we can choose an empty environment
            let (res_tag, res) = call(eval, val_tag, val, null_env);
            match res_tag {
                Tag::Err => {
                    return (res_tag, res)
                }
            };
            let (res_tag, res) = call(eval_mutual_bindings, init_env, ext_env);
            return (res_tag, res)
        }
    )
}

#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};

    use crate::lair::func_chip::FuncChip;

    use super::build_lurk_toplevel_native;

    #[test]
    fn test_eval_widths() {
        let (toplevel, ..) = &build_lurk_toplevel_native();

        let lurk_main = FuncChip::from_name("lurk_main", toplevel);
        let eval = FuncChip::from_name("eval", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let eval_unop = FuncChip::from_name("eval_unop", toplevel);
        let eval_binop = FuncChip::from_name("eval_binop", toplevel);
        let eval_binop_num = FuncChip::from_name("eval_binop_num", toplevel);
        let eval_op_misc = FuncChip::from_name("eval_op_misc", toplevel);
        let extend_env_with_mutuals = FuncChip::from_name("extend_env_with_mutuals", toplevel);
        let eval_mutual_bindings = FuncChip::from_name("eval_mutual_bindings", toplevel);
        let equal_inner = FuncChip::from_name("equal_inner", toplevel);

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(lurk_main.width(), expect!["114"]);
        expect_eq(eval.width(), expect!["73"]);
        expect_eq(apply.width(), expect!["105"]);
        expect_eq(eval_op_misc.width(), expect!["81"]);
        expect_eq(eval_unop.width(), expect!["122"]);
        expect_eq(eval_binop.width(), expect!["119"]);
        expect_eq(eval_binop_num.width(), expect!["120"]);
        expect_eq(extend_env_with_mutuals.width(), expect!["30"]);
        expect_eq(eval_mutual_bindings.width(), expect!["66"]);
        expect_eq(equal_inner.width(), expect!["58"]);
    }
}
