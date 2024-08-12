use p3_baby_bear::BabyBear;
use p3_field::AbstractField;

use crate::{
    func,
    lair::{expr::FuncE, toplevel::Toplevel},
};

use super::{
    chipset::{lurk_chip_map, LurkChip},
    compile::{
        compile, compile_apply, compile_begin, compile_lambda, compile_let, convert_data,
        deconvert_data, CTag,
    },
    eval_direct::{env_lookup, EvalErr},
    ingress::{
        egress, egress_builtin, hash_24_8, hash_32_8, hash_48_8, ingress, ingress_builtin,
        BuiltinMemo,
    },
    state::State,
    tag::Tag,
    zstore::{lurk_zstore, ZStore},
};

/// Creates a `Toplevel` with the functions used for Lurk evaluation, also returning
/// a `ZStore` with the Lurk builtins already interned.
#[inline]
pub fn build_lurk_toplevel() -> (Toplevel<BabyBear, LurkChip>, ZStore<BabyBear, LurkChip>) {
    let state = State::init_lurk_state().rccell();
    let mut zstore = lurk_zstore();
    let builtins = BuiltinMemo::new(&state, &mut zstore);
    let nil = zstore.read_with_state(state, "nil").unwrap().digest.into();
    let funcs = &[
        lurk_main2(),
        ingress(),
        ingress_builtin(&builtins),
        compile(&builtins),
        compile_apply(),
        compile_lambda(),
        compile_let(),
        compile_begin(),
        convert_data(&builtins),
        deconvert_data(&builtins),
        egress(nil),
        egress_builtin(&builtins),
        hash_24_8(),
        hash_32_8(),
        hash_48_8(),
        eval(),
        apply(),
        force(),
        env_lookup(),
        equal(),
    ];
    let lurk_chip_map = lurk_chip_map();
    let toplevel = Toplevel::new(funcs, lurk_chip_map);
    (toplevel, zstore)
}

pub fn lurk_main2<F: AbstractField>() -> FuncE<F> {
    func!(
        fn lurk_main(expr_tag, expr_tag_rest: [7], expr_digest: [8], env_digest: [8]): [16] {
            let padding = [0; 7];
            // Ingress
            let expr = call(ingress, expr_tag, expr_tag_rest, expr_digest);
            let env_tag = Tag::Env;
            let env = call(ingress, env_tag, padding, env_digest);
            // Compile
            let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
            let (cenv_tag, cenv) = call(convert_data, env_tag, env);
            // If the environment is incorrect, return immediately the error
            match cenv_tag {
                Tag::Err => {
                    let val_digest: [8] = call(egress, cenv_tag, cenv);
                    return (cenv_tag, padding, val_digest)
                }
            };
            // Eval
            let (cval_tag, cval) = call(eval, cexpr_tag, cexpr, cenv);
            // Decompile
            let (val_tag, val) = call(deconvert_data, cval_tag, cval);
            // Egress
            let val_digest: [8] = call(egress, val_tag, val);
            return (val_tag, padding, val_digest)
        }
    )
}

pub fn eval<F: AbstractField>() -> FuncE<F> {
    func!(
        fn eval(cexpr_tag, cexpr, cenv): [2] {
            match cexpr_tag {
                Tag::Builtin => {
                    let err_tag = Tag::Err;
                    let non_constant_builtin = EvalErr::NonConstantBuiltin;
                    return (err_tag, non_constant_builtin)
                }
                Tag::Nil, Tag::Cons, Tag::Fun, Tag::Num, Tag::Str, Tag::Char, Tag::Comm,
                Tag::U64, Tag::Key, Tag::Env, Tag::Err, CTag::True, CTag::CFun, CTag::CThunk => {
                    return (cexpr_tag, cexpr)
                }
                Tag::Sym => {
                    let expr_digest: [8] = load(cexpr);
                    let (res_tag, res) = call(env_lookup, expr_digest, cenv);
                    // This match is expensive, maybe move to a different function
                    match res_tag {
                        CTag::CFix => {
                            // In the case the result is a fixed point we extend
                            // its environment with itself and reduce its body in
                            // the extended environment
                            let (cbody_tag, cbody, cbody_env) = load(res);
                            // `expr` is the symbol
                            let fix_env = store(cexpr, res_tag, res, cbody_env);
                            let (res_tag, res) = call(eval, cbody_tag, cbody, fix_env);
                            return (res_tag, res)
                        }
                    };
                    return (res_tag, res)
                }
                CTag::EmptyEnv => {
                    let env_tag = Tag::Env;
                    let env = 0;
                    return (env_tag, env)
                }
                CTag::CurrentEnv => {
                    let env_tag = Tag::Env;
                    return (env_tag, cenv)
                }
                CTag::Quote => {
                    let (res_tag, res) = load(cexpr);
                    return (res_tag, res)
                }
                CTag::Eval => {
                    let (expr_tag, expr, expr_env_tag, expr_env) = load(cexpr);
                    // Eval the expression, which will return an s-expr
                    let (sexpr_tag, sexpr) = call(eval, expr_tag, expr, cenv);
                    match sexpr_tag {
                        Tag::Err => {
                            return (sexpr_tag, sexpr)
                        }
                    };
                    // Compile the s-expression
                    let (code_tag, code) = call(compile, sexpr_tag, sexpr);
                    match code_tag {
                        Tag::Err => {
                            return (code_tag, code)
                        }
                    };
                    let (env_tag, env) = call(eval, expr_env_tag, expr_env, cenv);
                    match env_tag {
                        Tag::Err => {
                            return (env_tag, env)
                        }
                        Tag::Env => {
                            let (res_tag, res) = call(eval, code_tag, code, env);
                            return (res_tag, res)
                        }
                    };
                    let err_tag = Tag::Err;
                    let err = EvalErr::NotEnv;
                    return (err_tag, err)
                }
                CTag::If => {
                    let (b_tag, b, t_tag, t, f_tag, f) = load(cexpr);
                    let (b_tag, b) = call(eval, b_tag, b, cenv);
                    match b_tag {
                        Tag::Nil => {
                            let (res_tag, res) = call(eval, f_tag, f, cenv);
                            return (res_tag, res)
                        }
                        Tag::Err => {
                            return (b_tag, b)
                        }
                    };
                    let (res_tag, res) = call(eval, t_tag, t, cenv);
                    return (res_tag, res)
                }
                CTag::Let => {
                    let (param, val_tag, val, body_tag, body) = load(cexpr);
                    let (val_tag, val) = call(eval, val_tag, val, cenv);
                    match val_tag {
                        Tag::Err => {
                            return (val_tag, val)
                        }
                    };
                    let cenv = store(param, val_tag, val, cenv);
                    let (res_tag, res) = call(eval, body_tag, body, cenv);
                    return (res_tag, res)
                }
                CTag::Letrec => {
                    let (param, val_tag, val, body_tag, body) = load(cexpr);
                    let fix_tag = CTag::CFix;
                    let fix = store(val_tag, val, cenv);
                    let ext_env = store(param, fix_tag, fix, cenv);
                    // this will preemptively evaluate the fixed point, so that we do not skip evaluation
                    // in case the variable is not used inside the letrec body, and furthermore it follows
                    // a strict evaluation order
                    let (val_tag, val) = call(eval, val_tag, val, ext_env);
                    match val_tag {
                        Tag::Err => {
                            return (val_tag, val)
                        }
                    };
                    let cenv = store(param, val_tag, val, cenv);
                    let (res_tag, res) = call(eval, body_tag, body, cenv);
                    return (res_tag, res)
                }
                CTag::MkThunk => {
                    let (cbody_tag, cbody) = load(cexpr);
                    let tag = CTag::CThunk;
                    let ptr = store(cbody_tag, cbody, cenv);
                    return (tag, ptr)
                }
                CTag::MkFun => {
                    let (var, cbody_tag, cbody) = load(cexpr);
                    let tag = CTag::CFun;
                    let ptr = store(var, cbody_tag, cbody, cenv);
                    return (tag, ptr)
                }
                CTag::App => {
                    let (head_tag, head, arg_tag, arg) = load(cexpr);
                    let (head_tag, head) = call(eval, head_tag, head, cenv);
                    let (res_tag, res) = call(apply, head_tag, head, arg_tag, arg, cenv);
                    return (res_tag, res)
                }
                CTag::Force => {
                    let (head_tag, head) = load(cexpr);
                    let (head_tag, head) = call(eval, head_tag, head, cenv);
                    let (res_tag, res) = call(force, head_tag, head);
                    return (res_tag, res)
                }
                CTag::Add, CTag::Sub, CTag::Mul, CTag::Div, CTag::Mod,
                CTag::Less, CTag::LessEq, CTag::Great, CTag::GreatEq => {
                    let (arg1_tag, arg1, arg2_tag, arg2) = load(cexpr);
                    let (arg1_tag, arg1) = call(eval, arg1_tag, arg1, cenv);
                    match arg1_tag {
                        Tag::Err => {
                            return (arg1_tag, arg1)
                        }
                    };
                    let (arg2_tag, arg2) = call(eval, arg2_tag, arg2, cenv);
                    match arg2_tag {
                        Tag::Err => {
                            return (arg2_tag, arg2)
                        }
                    };
                    let tags: [2] = (arg1_tag, arg2_tag);
                    let zero = 0;
                    let t_tag = CTag::True;
                    let nil_tag = Tag::Nil;
                    let err_tag = Tag::Err;
                    let num_tag = Tag::Num;
                    let u64_tag = Tag::U64;
                    match tags {
                        [Tag::U64, Tag::U64] => {
                            match cexpr_tag {
                                CTag::Add => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res: [8] = extern_call(u64_add, arg1, arg2);
                                    let res = store(res);
                                    return (u64_tag, res)
                                }
                                CTag::Sub => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res: [8] = extern_call(u64_sub, arg1, arg2);
                                    let res = store(res);
                                    return (u64_tag, res)
                                }
                                CTag::Mul => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res: [8] = extern_call(u64_mul, arg1, arg2);
                                    let res = store(res);
                                    return (u64_tag, res)
                                }
                                CTag::Div => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let is_zero = extern_call(u64_iszero, arg2);
                                    if is_zero {
                                        let err = EvalErr::DivByZero;
                                        return (err_tag, err)
                                    }
                                    let (q: [8], _r: [8]) = extern_call(u64_divrem, arg1, arg2);
                                    let q = store(q);
                                    return (u64_tag, q)
                                }
                                CTag::Mod => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let is_zero = extern_call(u64_iszero, arg2);
                                    if is_zero {
                                        let err = EvalErr::DivByZero;
                                        return (err_tag, err)
                                    }
                                    let (_q: [8], r: [8]) = extern_call(u64_divrem, arg1, arg2);
                                    let r = store(r);
                                    return (u64_tag, r)
                                }
                                CTag::Less => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res = extern_call(u64_lessthan, arg1, arg2);
                                    if res {
                                        return (t_tag, zero)
                                    }
                                    return (nil_tag, zero)
                                }
                                CTag::LessEq => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res = extern_call(u64_lessthan, arg2, arg1);
                                    if res {
                                        return (nil_tag, zero)
                                    }
                                    return (t_tag, zero)
                                }
                                CTag::Great => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res = extern_call(u64_lessthan, arg2, arg1);
                                    if res {
                                        return (t_tag, zero)
                                    }
                                    return (nil_tag, zero)
                                }
                                CTag::GreatEq => {
                                    let arg1: [8] = load(arg1);
                                    let arg2: [8] = load(arg2);
                                    let res = extern_call(u64_lessthan, arg1, arg2);
                                    if res {
                                        return (nil_tag, zero)
                                    }
                                    return (t_tag, zero)
                                }
                            }
                        }
                        [Tag::Num, Tag::Num] => {
                            match cexpr_tag {
                                CTag::Add => {
                                    let res = add(arg1, arg2);
                                    return (num_tag, res)
                                }
                                CTag::Sub => {
                                    let res = sub(arg1, arg2);
                                    return (num_tag, res)
                                }
                                CTag::Mul => {
                                    let res = mul(arg1, arg2);
                                    return (num_tag, res)
                                }
                                CTag::Div => {
                                    if !arg2 {
                                        let err = EvalErr::DivByZero;
                                        return (err_tag, err)
                                    }
                                    let res = div(arg1, arg2);
                                    return (num_tag, res)
                                }
                                CTag::Mod,
                                CTag::Less,
                                CTag::LessEq,
                                CTag::Great,
                                CTag::GreatEq => {
                                    let err = EvalErr::NotU64;
                                    return (err_tag, err)
                                }
                            }
                        }
                    };
                    let err = EvalErr::ArgNotNumber;
                    return (err_tag, err)
                }
                CTag::Eq, CTag::Hide, CTag::MkCons, CTag::MkStrcons, CTag::Begin => {
                    let (arg1_tag, arg1, arg2_tag, arg2) = load(cexpr);
                    let (arg1_tag, arg1) = call(eval, arg1_tag, arg1, cenv);
                    match arg1_tag {
                        Tag::Err => {
                            return (arg1_tag, arg1)
                        }
                    };
                    let (arg2_tag, arg2) = call(eval, arg2_tag, arg2, cenv);
                    match arg2_tag {
                        Tag::Err => {
                            return (arg2_tag, arg2)
                        }
                    };
                    match cexpr_tag {
                        CTag::Eq => {
                            let res = call(equal, arg1_tag, arg1, arg2_tag, arg2);
                            let zero = 0;
                            if res {
                                let t_tag = CTag::True;
                                return (t_tag, zero)
                            }
                            let nil_tag = Tag::Nil;
                            return (nil_tag, zero)
                        }
                        CTag::Hide => {
                            match arg1_tag {
                                Tag::Comm => {
                                    let secret: [8] = load(arg1);
                                    let arg2_digest: [8] = call(egress, arg2_tag, arg2);
                                    let padding = [0; 7];
                                    let comm_hash: [8] = call(hash_24_8, secret, arg2_tag, padding, arg2_digest);
                                    let comm_ptr = store(comm_hash);
                                    return (arg1_tag, comm_ptr) // `arg1_tag` is `Tag::Comm`
                                }
                            };
                            let not_comm = EvalErr::NotComm;
                            let err_tag = Tag::Err;
                            return (err_tag, not_comm)
                        }
                        CTag::MkCons => {
                            let tag = Tag::Cons;
                            let ptr = store(arg1_tag, arg1, arg2_tag, arg2);
                            return (tag, ptr)
                        }
                        CTag::MkStrcons => {
                            let char_tag = Tag::Char;
                            let str_tag = Tag::Str;
                            let err_tag = Tag::Err;
                            let strcons = store(arg1_tag, arg1, arg2_tag, arg2);
                            let not_char = sub(arg1_tag, char_tag);
                            let not_str = sub(arg2_tag, str_tag);
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
                        CTag::Begin => {
                            return (arg2_tag, arg2)
                        }
                    }
                }
                CTag::Car, CTag::Cdr, CTag::Atom, CTag::Commit, CTag::Open, CTag::Secret,
                CTag::Num, CTag::U64, CTag::Char, CTag::Comm, CTag::Emit => {
                    let (arg_tag, arg) = load(cexpr);
                    let (arg_tag, arg) = call(eval, arg_tag, arg, cenv);
                    match arg_tag {
                        Tag::Err => {
                            return (arg_tag, arg)
                        }
                    };
                    let err_tag = Tag::Err;
                    let nil_tag = Tag::Nil;
                    let zero = 0;
                    match cexpr_tag {
                        CTag::Car => {
                            match arg_tag {
                                Tag::Cons => {
                                    let (car_tag, car, _cdr_tag, _cdr) = load(arg);
                                    return (car_tag, car)
                                }
                                Tag::Nil => {
                                    return (nil_tag, zero)
                                }
                                Tag::Str => {
                                    let empty = 0;
                                    let not_empty = sub(arg, empty);
                                    if not_empty {
                                        let (car_tag, car, _cdr_tag, _cdr) = load(arg);
                                        return (car_tag, car)
                                    }
                                    return (nil_tag, zero)
                                }
                            };
                            let not_cons = EvalErr::NotCons;
                            return (err_tag, not_cons)
                        }
                        CTag::Cdr => {
                            match arg_tag {
                                Tag::Cons => {
                                    let (_car_tag, _car, cdr_tag, cdr) = load(arg);
                                    return (cdr_tag, cdr)
                                }
                                Tag::Nil => {
                                    return (nil_tag, zero)
                                }
                                Tag::Str => {
                                    let empty = 0;
                                    let not_empty = sub(arg, empty);
                                    if not_empty {
                                        let (_car_tag, _car, cdr_tag, cdr) = load(arg);
                                        return (cdr_tag, cdr)
                                    }
                                    return (nil_tag, zero)
                                }
                            };
                            let not_cons = EvalErr::NotCons;
                            return (err_tag, not_cons)
                        }
                        CTag::Atom => {
                            let zero = 0;
                            match arg_tag {
                                Tag::Cons => {
                                    let tag = CTag::True;
                                    return (tag, zero)
                                }
                            };
                            return (nil_tag, zero)
                        }
                        CTag::Commit => {
                            let arg_digest: [8] = call(egress, arg_tag, arg);
                            let padding = [0; 7];
                            let zero = 0;
                            let comm_hash: [8] = call(hash_24_8, zero, padding, arg_tag, padding, arg_digest);
                            let comm_ptr = store(comm_hash);
                            let comm_tag = Tag::Comm;
                            return (comm_tag, comm_ptr)
                        }
                        CTag::Open => {
                            let comm_tag = Tag::Comm;
                            let arg_not_comm = sub(arg_tag, comm_tag);
                            if arg_not_comm {
                                let not_comm = EvalErr::NotComm;
                                return (err_tag, not_comm)
                            }
                            let comm_hash: [8] = load(arg);
                            let (_secret: [8], tag, padding: [7], arg_digest: [8]) = preimg(hash_24_8, comm_hash);
                            let ptr = call(ingress, tag, padding, arg_digest);
                            return (tag, ptr)
                        }
                        CTag::Secret => {
                            let comm_tag = Tag::Comm;
                            let arg_not_comm = sub(arg_tag, comm_tag);
                            if arg_not_comm {
                                let not_comm = EvalErr::NotComm;
                                return (err_tag, not_comm)
                            }
                            let comm_hash: [8] = load(arg);
                            let (secret: [8], _payload: [16]) = preimg(hash_24_8, comm_hash);
                            let ptr = store(secret);
                            return (comm_tag, ptr)
                        }
                        CTag::Num => {
                            let char_tag = Tag::Char;
                            let u64_tag = Tag::U64;
                            let num_tag = Tag::Num;
                            let arg_not_char = sub(arg_tag, char_tag);
                            let arg_not_u64 = sub(arg_tag, u64_tag);
                            let arg_not_num = sub(arg_tag, num_tag);

                            // Commitments cannot be cast to numbers anymore
                            let acc = mul(arg_not_char, arg_not_num);
                            let cannot_cast = mul(acc, arg_not_u64);
                            if cannot_cast {
                                let err = EvalErr::CannotCastToNum;
                                return(err_tag, err)
                            }
                            return(num_tag, arg)
                        }
                        CTag::Emit => {
                            // TODO emit
                            return (arg_tag, arg)
                        }
                        CTag::Comm => {
                            // Can you really cast field elements to commitments?
                            let err_tag = Tag::Err;
                            let todo = EvalErr::Todo;
                            return (err_tag, todo)
                        }
                        CTag::U64 => {
                            let err_tag = Tag::Err;
                            let todo = EvalErr::Todo;
                            return (err_tag, todo)
                        }
                        CTag::Char => {
                            let err_tag = Tag::Err;
                            let todo = EvalErr::Todo;
                            return (err_tag, todo)
                        }
                    }
                }
            }
        }
    )
}

pub fn apply<F: AbstractField>() -> FuncE<F> {
    func!(
        fn apply(head_tag, head, arg_tag, arg, env): [2] {
            match head_tag {
                CTag::CFun => {
                    let (param, body_tag, body, body_env) = load(head);
                    let (arg_tag, arg) = call(eval, arg_tag, arg, env);
                    match arg_tag {
                        Tag::Err => {
                            return (arg_tag, arg)
                        }
                    };
                    let ext_env = store(param, arg_tag, arg, body_env);
                    let (res_tag, res) = call(eval, body_tag, body, ext_env);
                    return (res_tag, res)
                }
                CTag::CThunk => {
                    let (body_tag, body, body_env) = load(head);
                    let (res_tag, res) = call(eval, body_tag, body, body_env);
                    let (res_tag, res) = call(apply, res_tag, res, arg_tag, arg, env);
                    return (res_tag, res)
                }
                Tag::Err => {
                    return (head_tag, head)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::ApplyNonFunc;
            return (err_tag, err)
        }
    )
}

pub fn force<F: AbstractField>() -> FuncE<F> {
    func!(
        fn force(head_tag, head): [2] {
            match head_tag {
                CTag::CFun => {
                    return (head_tag, head)
                }
                CTag::CThunk => {
                    let (body_tag, body, body_env) = load(head);
                    let (res_tag, res) = call(eval, body_tag, body, body_env);
                    return (res_tag, res)
                }
                Tag::Err => {
                    return (head_tag, head)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::ApplyNonFunc;
            return (err_tag, err)
        }
    )
}

pub fn equal<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn equal(a_tag, a, b_tag, b): [1] {
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
                // The Nil case is impossible
                CTag::True, Tag::Num, Tag::Char, Tag::Err => {
                    return zero
                }
                Tag::Sym, Tag::U64, Tag::Comm => {
                    let a_digest: [8] = load(a);
                    let b_digest: [8] = load(b);
                    let diff = sub(a_digest, b_digest);
                    if diff {
                        return zero
                    }
                    return one
                }
                Tag::Str, Tag::Key => {
                    let a_and_b = mul(a, b);
                    if !a_and_b {
                        return zero
                    }
                    let (a_fst: [2], a_snd: [2]) = load(a);
                    let (b_fst: [2], b_snd: [2]) = load(b);
                    let fst_eq = call(equal, a_fst, b_fst);
                    let snd_eq = call(equal, a_snd, b_snd);
                    let eq = mul(fst_eq, snd_eq);
                    return eq
                }
                Tag::Cons => {
                    let (a_fst: [2], a_snd: [2]) = load(a);
                    let (b_fst: [2], b_snd: [2]) = load(b);
                    let fst_eq = call(equal, a_fst, b_fst);
                    let snd_eq = call(equal, a_snd, b_snd);
                    let eq = mul(fst_eq, snd_eq);
                    return eq
                }
                CTag::CFix, CTag::CThunk => {
                    let (a_body: [2], a_env) = load(a);
                    let (b_body: [2], b_env) = load(b);
                    let env_tag = Tag::Env;
                    let body_eq = call(equal, a_body, b_body);
                    let env_eq = call(equal, env_tag, a_env, env_tag, b_env);
                    let eq = mul(body_eq, env_eq);
                    return eq
                }
                CTag::CFun => {
                    let (a_var, a_body: [2], a_env) = load(a);
                    let (b_var, b_body: [2], b_env) = load(b);
                    let var_tag = Tag::Sym;
                    let env_tag = Tag::Env;
                    let var_eq = call(equal, var_tag, a_var, var_tag, b_var);
                    let body_eq = call(equal, a_body, b_body);
                    let env_eq = call(equal, env_tag, a_env, env_tag, b_env);
                    let eq = mul(var_eq, body_eq);
                    let eq = mul(eq, env_eq);
                    return eq
                }
                Tag::Env => {
                    let a_and_b = mul(a, b);
                    if !a_and_b {
                        return zero
                    }
                    let (a_var, a_val: [2], a_env) = load(a);
                    let (b_var, b_val: [2], b_env) = load(b);
                    let var_tag = Tag::Sym;
                    let env_tag = Tag::Env;
                    let var_eq = call(equal, var_tag, a_var, var_tag, b_var);
                    let val_eq = call(equal, a_val, b_val);
                    let env_eq = call(equal, env_tag, a_env, env_tag, b_env);
                    let eq = mul(var_eq, val_eq);
                    let eq = mul(eq, env_eq);
                    return eq
                }
            }
        }
    )
}
#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};

    use crate::lair::func_chip::FuncChip;

    use super::build_lurk_toplevel;

    #[test]
    fn test_eval_widths() {
        let (toplevel, _) = &build_lurk_toplevel();

        let lurk_main = FuncChip::from_name("lurk_main", toplevel);
        let compile = FuncChip::from_name("compile", toplevel);
        let compile_apply = FuncChip::from_name("compile_apply", toplevel);
        let compile_lambda = FuncChip::from_name("compile_lambda", toplevel);
        let compile_let = FuncChip::from_name("compile_let", toplevel);
        let compile_begin = FuncChip::from_name("compile_begin", toplevel);
        let convert_data = FuncChip::from_name("convert_data", toplevel);
        let deconvert_data = FuncChip::from_name("deconvert_data", toplevel);
        let eval = FuncChip::from_name("eval", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let force = FuncChip::from_name("force", toplevel);
        let env_lookup = FuncChip::from_name("env_lookup", toplevel);
        let equal = FuncChip::from_name("equal", toplevel);

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(lurk_main.width(), expect!["69"]);
        expect_eq(compile.width(), expect!["125"]);
        expect_eq(compile_apply.width(), expect!["33"]);
        expect_eq(compile_lambda.width(), expect!["29"]);
        expect_eq(compile_let.width(), expect!["55"]);
        expect_eq(compile_begin.width(), expect!["35"]);
        expect_eq(convert_data.width(), expect!["62"]);
        expect_eq(deconvert_data.width(), expect!["59"]);
        expect_eq(eval.width(), expect!["279"]);
        expect_eq(apply.width(), expect!["35"]);
        expect_eq(force.width(), expect!["20"]);
        expect_eq(env_lookup.width(), expect!["47"]);
        expect_eq(equal.width(), expect!["52"]);
    }
}
