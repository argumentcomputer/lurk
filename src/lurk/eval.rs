use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeField};

use crate::{
    func,
    lair::{
        expr::{BlockE, CasesE, CtrlE, FuncE, OpE, Var},
        hasher::Hasher,
        map::Map,
        toplevel::Toplevel,
        Name,
    },
};

use super::{
    memory::Memory,
    reader::read,
    state::{State, LURK_PACKAGE_NONNIL_SYMBOLS_NAMES},
    zstore::{HasherTemp, Tag, ZStore},
};

static BUILTIN_BABYBEAR_DIGESTS: OnceCell<Vec<Vec<BabyBear>>> = OnceCell::new();
fn builtin_digests() -> &'static Vec<Vec<BabyBear>> {
    BUILTIN_BABYBEAR_DIGESTS.get_or_init(|| {
        LURK_PACKAGE_NONNIL_SYMBOLS_NAMES
            .map(|sym| {
                read(State::init_lurk_state().rccell(), sym)
                    .unwrap()
                    .digest
                    .to_vec()
            })
            .into_iter()
            .collect()
    })
}

// let builtins: Vec<Vec<F>> = ;
/// Creates a `Toplevel` with the functions used for Lurk evaluation
#[inline]
pub fn build_lurk_toplevel<HT: HasherTemp<F = BabyBear>, H: Hasher<BabyBear>>(
    mem: &mut Memory<BabyBear, HT>,
    store: &ZStore<BabyBear, HT>,
) -> Toplevel<BabyBear, H> {
    let builtins = builtin_digests();
    Toplevel::new(&[
        eval(mem, store),
        eval_unop(mem, store),
        eval_binop_num(mem, store),
        eval_binop_misc(mem, store),
        car_cdr(mem, store),
        eval_let(),
        eval_letrec(),
        apply(),
        env_lookup(),
        ingress(),
        ingress_builtin(builtins),
        egress(),
        egress_builtin(builtins),
        hash_32_8(),
        hash_48_8(),
    ])
}

#[derive(Clone, Copy)]
#[repr(u8)]
enum EvalErr {
    UnboundVar,
    InvalidForm,
    ApplyNonFunc,
    ParamsNotList,
    ParamNotSymbol,
    ArgsNotList,
    ArgNotNumber,
    DivByZero,
    GenericError,
    NotEnv,
    NotChar,
    NotCons,
    NotComm,
    NotString,
    CannotCastToNum,
    Todo,
}

impl EvalErr {
    fn to_field<F: Field>(self) -> F {
        F::from_canonical_u8(self as u8)
    }
}

pub fn ingress<F: PrimeField>() -> FuncE<F> {
    func!(
        fn ingress(tag_full: [8], digest: [8]): [1] {
            let (tag, _rest: [7]) = tag_full;
            match tag {
                Tag::Num | Tag::Char | Tag::Err => {
                    let (x, _rest: [7]) = digest;
                    return x
                }
                Tag::Nil | Tag::U64 | Tag::Comm => {
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Builtin => {
                    let idx = call(ingress_builtin, digest);
                    return idx
                }
                Tag::Str | Tag::Sym | Tag::Key => {
                    if !digest {
                        let zero = 0;
                        return zero
                    }
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash_32_8, digest);
                    let fst_ptr = call(ingress, fst_tag_full, fst_digest);
                    let snd_ptr = call(ingress, snd_tag_full, snd_digest);
                    let (fst_tag, _rest: [7]) = fst_tag_full;
                    let (snd_tag, _rest: [7]) = snd_tag_full;
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return ptr
                }
                Tag::Cons | Tag::Thunk => {
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash_32_8, digest);
                    let fst_ptr = call(ingress, fst_tag_full, fst_digest);
                    let snd_ptr = call(ingress, snd_tag_full, snd_digest);
                    let (fst_tag, _rest: [7]) = fst_tag_full;
                    let (snd_tag, _rest: [7]) = snd_tag_full;
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return ptr
                }
                Tag::Fun | Tag::Env => {
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8],
                         trd_tag_full: [8], trd_digest: [8]) = preimg(hash_48_8, digest);
                    let fst_ptr = call(ingress, fst_tag_full, fst_digest);
                    let snd_ptr = call(ingress, snd_tag_full, snd_digest);
                    let trd_ptr = call(ingress, trd_tag_full, trd_digest);
                    let (fst_tag, _rest: [7]) = fst_tag_full;
                    let (snd_tag, _rest: [7]) = snd_tag_full;
                    let (trd_tag, _rest: [7]) = trd_tag_full;
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr, trd_tag, trd_ptr);
                    return ptr
                }
            }
        }
    )
}

pub fn ingress_builtin<F: PrimeField>(builtins: &[Vec<F>]) -> FuncE<F> {
    let input_var = Var {
        name: "digest",
        size: 8,
    };
    let ret_var = Var {
        name: "res",
        size: 1,
    };
    let branch = |i: usize| BlockE {
        ops: [OpE::Const(ret_var, F::from_canonical_usize(i))].into(),
        ctrl: CtrlE::<F>::Return([ret_var].into()),
    };
    let branches = Map::from_vec(
        builtins
            .iter()
            .enumerate()
            .map(|(i, arr)| (arr.clone().into(), branch(i)))
            .collect(),
    );
    let cases = CasesE {
        branches,
        default: None,
    };
    let ops = [].into();
    let ctrl = CtrlE::<F>::MatchMany(input_var, cases);

    FuncE {
        name: Name("ingress_builtin"),
        invertible: false,
        input_params: [input_var].into(),
        output_size: 1,
        body: BlockE { ops, ctrl },
    }
}

pub fn egress<F: PrimeField>() -> FuncE<F> {
    func!(
        fn egress(tag, val): [8] {
            match tag {
                Tag::Num | Tag::Char | Tag::Err => {
                    let padding = [0; 7];
                    let digest: [8] = (val, padding);
                    return digest
                }
                Tag::Nil | Tag::U64 | Tag::Comm => {
                    let digest: [8] = load(val);
                    return digest
                }
                Tag::Builtin => {
                    let digest: [8] = call(egress_builtin, val);
                    return digest
                }
                Tag::Str | Tag::Sym | Tag::Key => {
                    if !val {
                        let digest = [0; 8];
                        return digest
                    }
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash_32_8, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return digest
                }
                Tag::Cons | Tag::Thunk => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash_32_8, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return digest
                }
                Tag::Fun | Tag::Env => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr, trd_tag, trd_ptr) = load(val);
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);
                    let trd_digest: [8] = call(egress, trd_tag, trd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let trd_tag_full: [8] = (trd_tag, padding);
                    let digest: [8] = call(hash_48_8, fst_tag_full, fst_digest, snd_tag_full, snd_digest, trd_tag_full, trd_digest);
                    return digest
                }
            }
        }
    )
}

pub fn egress_builtin<F: PrimeField>(builtins: &[Vec<F>]) -> FuncE<F> {
    let input_var = Var {
        name: "val",
        size: 1,
    };
    let ret_var = Var {
        name: "digest",
        size: 8,
    };
    let branch = |arr: Vec<F>| BlockE {
        ops: [OpE::Array(ret_var, arr)].into(),
        ctrl: CtrlE::<F>::Return([ret_var].into()),
    };
    let branches = Map::from_vec(
        builtins
            .iter()
            .enumerate()
            .map(|(i, arr)| (F::from_canonical_usize(i), branch(arr.clone())))
            .collect(),
    );
    let cases = CasesE {
        branches,
        default: None,
    };
    let ops = [].into();
    let ctrl = CtrlE::<F>::Match(input_var, cases);

    FuncE {
        name: Name("egress_builtin"),
        invertible: false,
        input_params: [input_var].into(),
        output_size: 8,
        body: BlockE { ops, ctrl },
    }
}

pub fn hash_32_8<F: PrimeField>() -> FuncE<F> {
    func!(
        invertible fn hash_32_8(preimg: [32]): [8] {
            let (img: [8]) = hash(preimg);
            return img
        }
    )
}

pub fn hash_48_8<F: PrimeField>() -> FuncE<F> {
    func!(
        invertible fn hash_48_8(preimg: [48]): [8] {
            let (img: [8]) = hash(preimg);
            return img
        }
    )
}

pub fn eval<F: PrimeField, H: HasherTemp<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    func!(
        fn eval(expr_tag, expr, env): [2] {
            // Constants, tags, etc
            let t = Sym("t", mem, store);
            let nil = Sym("nil", mem, store);
            let nil_tag = Tag::Nil;
            let cons_tag = Tag::Cons;
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;

            match expr_tag {
                Tag::Sym => {
                    let not_t = sub(expr, t);
                    let not_nil = sub(expr, nil);
                    let not_t_or_nil = mul(not_t, not_nil);
                    if !not_t_or_nil {
                        return (expr_tag, expr)
                    }
                    let (res_tag, res) = call(env_lookup, expr, env);
                    match res_tag {
                        Tag::Thunk => {
                            // In the case the result is a thunk we extend
                            // its environment with itself and reduce its
                            // body in the extended environment
                            let (body_tag, body, body_env) = load(res);
                            // `expr` is the symbol
                            let thunk_env = store(expr, res_tag, res, body_env);
                            let (res_tag, res) = call(eval, body_tag, body, thunk_env);
                            return (res_tag, res)
                        }
                    };
                    return (res_tag, res)
                }
                Tag::Cons => {
                    let (head_tag, head, rest_tag, rest) = load(expr);
                    match head_tag {
                        Tag::Sym => {
                            match_sym(mem, store) head {
                                "lambda" => {
                                    // A lambda expression is a 3 element list
                                    // first element: lambda symbol
                                    // second element: parameter list
                                    // third element: body
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (params_tag, params, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (body_tag, body, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    // A function (more precisely, a closure) is an object with a
                                    // parameter list, a body and an environment
                                    let res_tag = Tag::Fun;
                                    let res = store(params_tag, params, body_tag, body, env);
                                    return (res_tag, res)
                                }
                                "let" => {
                                    // A let expression is a 3 element list
                                    // first element: let symbol
                                    // second element: binding list
                                    // third element: body
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (binds_tag, binds, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (body_tag, body, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let (res_tag, res) = call(eval_let, binds_tag, binds, body_tag, body, env);
                                    return (res_tag, res)
                                }
                                "letrec" => {
                                    // A letrec expression is analogous to a let expression
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (binds_tag, binds, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (body_tag, body, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let (res_tag, res) = call(eval_letrec, binds_tag, binds, body_tag, body, env);
                                    return (res_tag, res)
                                }
                                "eval" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    match rest_tag {
                                        Tag::Nil => {
                                            let env = 0;
                                            // Eval must be called twice
                                            let (res_tag, res) = call(eval, expr_tag, expr, env);
                                            let (res_tag, res) = call(eval, res_tag, res, env);
                                            return (res_tag, res)
                                        }
                                        Tag::Cons => {
                                            let (env_expr_tag, env_expr, rest_tag, _rest) = load(rest);
                                            let rest_not_nil = sub(rest_tag, nil_tag);
                                            if rest_not_nil {
                                                return (err_tag, invalid_form)
                                            }
                                            let (res_tag, res) = call(eval, expr_tag, expr, env);
                                            let (env_tag, new_env) = call(eval, env_expr_tag, env_expr, env);
                                            match env_tag {
                                                Tag::Env => {
                                                    let (res_tag, res) = call(eval, res_tag, res, new_env);
                                                    return (res_tag, res)
                                                }
                                            };
                                            let err = EvalErr::NotEnv;
                                            return (err_tag, err)
                                        }
                                    };
                                    let not_env = EvalErr::NotEnv;
                                    return (err_tag, not_env)
                                }
                                "quote" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    return (expr_tag, expr)
                                }
                                "begin" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    let (val_tag, val) = call(eval, expr_tag, expr, env);
                                    match val_tag {
                                        Tag::Err => {
                                            return (val_tag, val)
                                        }
                                    };
                                    match rest_tag {
                                        Tag::Nil => {
                                            return (val_tag, val)
                                        }
                                        Tag::Cons => {
                                            let smaller_expr = store(head_tag, head, rest_tag, rest);
                                            let (val_tag, val) = call(eval, cons_tag, smaller_expr, env);
                                            return (val_tag, val)
                                        }
                                    };
                                    return (err_tag, invalid_form)
                                }
                                "empty-env" => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let env_tag = Tag::Env;
                                    let env = 0;
                                    return (env_tag, env)
                                }
                                "current-env" => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let env_tag = Tag::Env;
                                    return (env_tag, env)
                                }
                                "if" => {
                                    // An if expression is a list of 4 elements
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (t_branch_tag, t_branch, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (f_branch_tag, f_branch, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }

                                    let (val_tag, val) = call(eval, expr_tag, expr, env);
                                    match val_tag {
                                        Tag::Nil => {
                                            let (res_tag, res) = call(eval, f_branch_tag, f_branch, env);
                                            return (res_tag, res)
                                        }
                                        Tag::Err => {
                                            return (val_tag, val)
                                        }
                                    };
                                    let (res_tag, res) = call(eval, t_branch_tag, t_branch, env);
                                    return (res_tag, res)
                                }
                                "+"
                                | "-"
                                | "*"
                                | "/"
                                | "=" => {
                                    let (res_tag, res) = call(eval_binop_num, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                "cons"
                                | "strcons"
                                | "hide"
                                | "eq" => {
                                    let (res_tag, res) = call(eval_binop_misc, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                "car" => {
                                    let (car_tag, car, _cdr_tag, _cdr) = call(car_cdr, rest_tag, rest, env);
                                    return (car_tag, car)
                                }
                                "cdr" => {
                                    let (_car_tag, _car, cdr_tag, cdr) = call(car_cdr, rest_tag, rest, env);
                                    return (cdr_tag, cdr)
                                }
                                "commit"
                                | "num"
                                | "u64"
                                | "comm"
                                | "char"
                                | "open"
                                | "secret"
                                | "atom"
                                | "emit" => {
                                    let (res_tag, res) = call(eval_unop, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                // TODO: other builtins
                            };
                            let (head_tag, head) = call(eval, head_tag, head, env);
                            let (res_tag, res) = call(apply, head_tag, head, rest_tag, rest, env);
                            return (res_tag, res)
                        }
                    };
                    let (head_tag, head) = call(eval, head_tag, head, env);
                    let (res_tag, res) = call(apply, head_tag, head, rest_tag, rest, env);
                    return (res_tag, res)
                }
            };
            return (expr_tag, expr)
        }
    )
}

pub fn car_cdr<F: PrimeField, H: HasherTemp<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    func!(
        fn car_cdr(rest_tag, rest, env): [4] {
            let nil = Sym("nil", mem, store);
            let nil_tag = Tag::Nil;
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
            let invalid_form = EvalErr::InvalidForm;
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form, err_tag, invalid_form)
            }
            let (expr_tag, expr, rest_tag, _rest) = load(rest);
            let rest_not_nil = sub(rest_tag, nil_tag);
            if rest_not_nil {
                return (err_tag, invalid_form, err_tag, invalid_form)
            }
            let (val_tag, val) = call(eval, expr_tag, expr, env);
            match val_tag {
                Tag::Err => {
                    return (val_tag, val, val_tag, val)
                }
                Tag::Cons => {
                    let (car_tag, car, cdr_tag, cdr) = load(val);
                    return (car_tag, car, cdr_tag, cdr)
                }
                Tag::Nil => {
                    return (nil_tag, nil, nil_tag, nil)
                }
                Tag::Str => {
                    let empty = 0;
                    let not_empty = sub(val, empty);
                    if not_empty {
                        let (car_tag, car, cdr_tag, cdr) = load(val);
                        return (car_tag, car, cdr_tag, cdr)
                    }
                    let str_tag = Tag::Str;
                    return (nil_tag, nil, str_tag, empty)
                }
            };
            let not_cons = EvalErr::NotCons;
            return (err_tag, not_cons, err_tag, not_cons)

        }
    )
}

pub fn eval_binop_num<F: PrimeField, H: HasherTemp<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    func!(
        fn eval_binop_num(head, rest_tag, rest, env): [2] {
            let err_tag = Tag::Err;
            let num_tag = Tag::Num;
            let cons_tag = Tag::Cons;
            let nil_tag = Tag::Nil;
            let invalid_form = EvalErr::InvalidForm;
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form)
            }
            let (exp1_tag, exp1, rest_tag, rest) = load(rest);
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form)
            }
            let (exp2_tag, exp2, rest_tag, _rest) = load(rest);
            let rest_not_nil = sub(rest_tag, nil_tag);
            if rest_not_nil {
                return (err_tag, invalid_form)
            }
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
            // Both must be numbers
            let not_num = sub(val1_tag, num_tag);
            if not_num {
                let err = EvalErr::ArgNotNumber;
                return (err_tag, err)
            }
            let not_num = sub(val2_tag, num_tag);
            if not_num {
                let err = EvalErr::ArgNotNumber;
                return (err_tag, err)
            }
            match_sym(mem, store) head {
                "+" => {
                    let res = add(val1, val2);
                    return (num_tag, res)
                }
                "-" => {
                    let res = sub(val1, val2);
                    return (num_tag, res)
                }
                "*" => {
                    let res = mul(val1, val2);
                    return (num_tag, res)
                }
                "/" => {
                    let res = div(val1, val2);
                    if !val2 {
                        let err = EvalErr::DivByZero;
                        return (err_tag, err)
                    }
                    return (num_tag, res)
                }
                "=" => {
                    let diff = sub(val1, val2);
                    if !diff {
                        let sym_tag = Tag::Sym;
                        let t = Sym("t", mem, store);
                        return (sym_tag, t)
                    }
                    let nil = Sym("nil", mem, store);
                    return (nil_tag, nil)
                }
            }
        }
    )
}

pub fn eval_binop_misc<F: PrimeField, H: HasherTemp<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    func!(
        fn eval_binop_misc(head, rest_tag, rest, env): [2] {
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
            let nil_tag = Tag::Nil;
            let invalid_form = EvalErr::InvalidForm;
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form)
            }
            let (exp1_tag, exp1, rest_tag, rest) = load(rest);
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form)
            }
            let (exp2_tag, exp2, rest_tag, _rest) = load(rest);
            let rest_not_nil = sub(rest_tag, nil_tag);
            if rest_not_nil {
                return (err_tag, invalid_form)
            }
            let (val1_tag, val1) = call(eval, exp1_tag, exp1, env);
            let (val2_tag, val2) = call(eval, exp2_tag, exp2, env);
            match val1_tag {
                Tag::Err => {
                    return (val1_tag, val1)
                }
            };
            match val2_tag {
                Tag::Err => {
                    return (val2_tag, val2)
                }
            };
            match_sym(mem, store) head {
                "cons" => {
                    let cons = store(val1_tag, val1, val2_tag, val2);
                    return (cons_tag, cons)
                }
                "strcons" => {
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
                "hide" => {
                    match val1_tag {
                        Tag::Num => {
                            let comm_tag = Tag::Comm;
                            let comm = store(val1, val2_tag, val2);
                            return (comm_tag, comm)
                        }
                    };
                    return (err_tag, invalid_form)
                }
                "eq" => {
                    let sym_tag = Tag::Sym;
                    let t = Sym("t", mem, store);
                    let nil = Sym("nil", mem, store);
                    let eq_tag = eq(val1_tag, val2_tag);
                    let eq_val = eq(val1, val2);
                    let eq = mul(eq_tag, eq_val);
                    if eq {
                        return (sym_tag, t)
                    }
                    return (nil_tag, nil)
               }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn eval_unop<F: PrimeField, H: HasherTemp<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    func!(
        fn eval_unop(head, rest_tag, rest, env): [2] {
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
            let num_tag = Tag::Num;
            let comm_tag = Tag::Comm;
            let nil_tag = Tag::Nil;
            let invalid_form = EvalErr::InvalidForm;
            let todo = EvalErr::Todo;
            let rest_not_cons = sub(rest_tag, cons_tag);
            if rest_not_cons {
                return (err_tag, invalid_form)
            }
            let (expr_tag, expr, rest_tag, _rest) = load(rest);
            let rest_not_nil = sub(rest_tag, nil_tag);
            if rest_not_nil {
                return (err_tag, invalid_form)
            }
            let (val_tag, val) = call(eval, expr_tag, expr, env);
            match val_tag {
                Tag::Err => {
                    return (val_tag, val)
                }
            };

            match_sym(mem, store) head {
                "commit" => {
                    let zero = 0;
                    let comm = store(zero, val_tag, val);
                    return (comm_tag, comm)
                }
                "num" => {
                    let char_tag = Tag::Char;
                    let u64_tag = Tag::U64;
                    let val_not_char = sub(val_tag, char_tag);
                    let val_not_u64 = sub(val_tag, u64_tag);
                    let val_not_num = sub(val_tag, num_tag);

                    // Commitments cannot be cast to numbers anymore
                    let acc = mul(val_not_char, val_not_num);
                    let cannot_cast = mul(acc, val_not_u64);
                    if cannot_cast {
                        let err = EvalErr::CannotCastToNum;
                        return(err_tag, err)
                    }
                    return(num_tag, val)
                }
                "open" => {
                    let val_not_comm = sub(val_tag, comm_tag);
                    if val_not_comm {
                        let not_comm = EvalErr::NotComm;
                        return (err_tag, not_comm)
                    }
                    let (_secret, res_tag, res) = load(val);
                    return (res_tag, res)
                }
                "secret" => {
                    let val_not_comm = sub(val_tag, comm_tag);
                    if val_not_comm {
                        let not_comm = EvalErr::NotComm;
                        return (err_tag, not_comm)
                    }
                    let (secret, _res_tag, _res) = load(val);
                    return (num_tag, secret)
                }
                "atom" => {
                    let val_not_cons = sub(val_tag, cons_tag);
                    if val_not_cons {
                        let sym_tag = Tag::Sym;
                        let t = Sym("t", mem, store);
                        return (sym_tag, t)
                    }
                    let nil = Sym("nil", mem, store);
                    return (nil_tag, nil)
                }
                "emit" => {
                    // TODO emit
                    return (val_tag, val)
                }
                "u64" => {
                    return(err_tag, todo)
                }
                "comm" => {
                    // Can you really cast field elements to commitments?
                    return (err_tag, todo)
                }
                "char" => {
                    return (err_tag, todo)
                }
             }
        }
    )
}

pub fn eval_let<F: PrimeField>() -> FuncE<F> {
    func!(
        fn eval_let(binds_tag, binds, body_tag, body, env): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match binds_tag {
                Tag::Nil => {
                    let (res_tag, res) = call(eval, body_tag, body, env);
                    return (res_tag, res)
                }
                Tag::Cons => {
                    let cons_tag = Tag::Cons;
                    let nil_tag = Tag::Nil;
                    let sym_tag = Tag::Sym;
                    // `binds` is a list of bindings
                    let (bind_tag, bind, rest_binds_tag, rest_binds) = load(binds);
                    let bind_not_cons = sub(bind_tag, cons_tag);
                    if bind_not_cons {
                        return (err_tag, invalid_form)
                    }
                    // each binding is in turn a 2 element list
                    let (param_tag, param, rest_tag, rest) = load(bind);
                    let rest_not_cons = sub(rest_tag, cons_tag);
                    if rest_not_cons {
                        return (err_tag, invalid_form)
                    }
                    let param_not_sym = sub(param_tag, sym_tag);
                    if param_not_sym {
                        return (err_tag, invalid_form)
                    }
                    let (expr_tag, expr, rest_tag, _rest) = load(rest);
                    let rest_not_nil = sub(rest_tag, nil_tag);
                    if rest_not_nil {
                        return (err_tag, invalid_form)
                    }

                    let (val_tag, val) = call(eval, expr_tag, expr, env);
                    let ext_env = store(param, val_tag, val, env);
                    match rest_binds_tag {
                        Tag::Nil => {
                            let (res_tag, res) = call(eval, body_tag, body, ext_env);
                            return (res_tag, res)
                        }
                    };
                    let (res_tag, res) = call(eval_let, rest_binds_tag, rest_binds, body_tag, body, ext_env);
                    return (res_tag, res)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn eval_letrec<F: PrimeField>() -> FuncE<F> {
    func!(
        fn eval_letrec(binds_tag, binds, body_tag, body, env): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match binds_tag {
                Tag::Nil => {
                    let (res_tag, res) = call(eval, body_tag, body, env);
                    return (res_tag, res)
                }
                Tag::Cons => {
                    let cons_tag = Tag::Cons;
                    let nil_tag = Tag::Nil;
                    let sym_tag = Tag::Sym;
                    // `binds` is a list of bindings
                    let (bind_tag, bind, rest_binds_tag, rest_binds) = load(binds);
                    let bind_not_cons = sub(bind_tag, cons_tag);
                    if bind_not_cons {
                        return (err_tag, invalid_form)
                    }
                    // each binding is in turn a 2 element list
                    let (param_tag, param, rest_tag, rest) = load(bind);
                    let rest_not_cons = sub(rest_tag, cons_tag);
                    if rest_not_cons {
                        return (err_tag, invalid_form)
                    }
                    let param_not_sym = sub(param_tag, sym_tag);
                    if param_not_sym {
                        return (err_tag, invalid_form)
                    }
                    let (expr_tag, expr, rest_tag, _rest) = load(rest);
                    let rest_not_nil = sub(rest_tag, nil_tag);
                    if rest_not_nil {
                        return (err_tag, invalid_form)
                    }

                    let thunk_tag = Tag::Thunk;
                    let thunk = store(expr_tag, expr, env);
                    let ext_env = store(param, thunk_tag, thunk, env);
                    match rest_binds_tag {
                        Tag::Nil => {
                            let (res_tag, res) = call(eval, body_tag, body, ext_env);
                            return (res_tag, res)
                        }
                    };
                    let (res_tag, res) = call(eval_letrec, rest_binds_tag, rest_binds, body_tag, body, ext_env);
                    return (res_tag, res)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn apply<F: PrimeField>() -> FuncE<F> {
    func!(
        fn apply(head_tag, head, args_tag, args, args_env): [2] {
            // Constants, tags, etc
            let err_tag = Tag::Err;
            let fun_tag = Tag::Fun;
            // Expression must be a function
            let head_not_fun = sub(head_tag, fun_tag);
            if head_not_fun {
                let err = EvalErr::ApplyNonFunc;
                return (err_tag, err)
            }

            let (params_tag, params, body_tag, body, func_env) = load(head);

            match params_tag {
                Tag::Nil => {
                    match args_tag {
                        Tag::Nil => {
                            let (res_tag, res) = call(eval, body_tag, body, func_env);
                            return (res_tag, res)
                        }
                        Tag::Cons => {
                            // Oversaturated application
                            let (res_tag, res) = call(eval, body_tag, body, func_env);
                            let (app_res_tag, app_res) = call(apply, res_tag, res, args_tag, args, args_env);
                            return (app_res_tag, app_res)
                        }
                    };
                    let err = EvalErr::ArgsNotList;
                    return (err_tag, err)
                }
                Tag::Cons => {
                    match args_tag {
                        Tag::Nil => {
                            // Undersaturated application
                            return (head_tag, head)
                        }
                        Tag::Cons => {
                            let (param_tag, param, rest_params_tag, rest_params) = load(params);
                            let (arg_tag, arg, rest_args_tag, rest_args) = load(args);
                            let sym_tag = Tag::Sym;
                            let param_not_sym = sub(param_tag, sym_tag);
                            if param_not_sym {
                                let err = EvalErr::ParamNotSymbol;
                                return (err_tag, err)
                            }
                            // evaluate the argument
                            let (arg_tag, arg) = call(eval, arg_tag, arg, args_env);
                            // and store it in the environment
                            let ext_env = store(param, arg_tag, arg, func_env);
                            let ext_fun = store(rest_params_tag, rest_params, body_tag, body, ext_env);
                            let (res_tag, res) = call(apply, fun_tag, ext_fun, rest_args_tag, rest_args, args_env);

                            return (res_tag, res)
                        }
                    };
                    let err = EvalErr::ArgsNotList;
                    return (err_tag, err)
                }
            };
            let err = EvalErr::ParamsNotList;
            return (err_tag, err)
        }
    )
}

pub fn env_lookup<F: Field>() -> FuncE<F> {
    func!(
        fn env_lookup(x, env): [2] {
            if !env {
                let err_tag = Tag::Err;
                let err = EvalErr::UnboundVar;
                return (err_tag, err)
            }
            let (y, val_tag, val, tail_env) = load(env);
            let not_eq = sub(x, y);
            if !not_eq {
                return (val_tag, val)
            }
            let (res_tag, res) = call(env_lookup, x, tail_env);
            return (res_tag, res)
        }
    )
}

pub fn list_to_env<F: PrimeField>() -> FuncE<F> {
    func!(
        fn list_to_env(list_tag, list): [2] {
            let err_tag = Tag::Err;
            let generic_err = EvalErr::GenericError;
            let env_tag = Tag::Env;
            match list_tag {
                Tag::Nil => {
                    let env = 0;
                    return (env_tag, env)
                }
                Tag::Cons => {
                    let (head_tag, head, tail_tag, tail) = load(list);
                    match head_tag {
                        Tag::Cons => {
                            let (y_tag, y, val_tag, val) = load(head);
                            match y_tag {
                                Tag::Sym => {
                                    let (tail_tag, tail_env) = call(list_to_env, tail_tag, tail);
                                    let not_env = sub(env_tag, tail_tag);
                                    if not_env {
                                        return (err_tag, generic_err)
                                    }
                                    let env = store(y, val_tag, val, tail_env);
                                    return (env_tag, env)
                                }
                            };
                            return (err_tag, generic_err)
                        }
                    };
                    return (err_tag, generic_err)
                }
            };
            return (err_tag, generic_err)
        }
    )
}

#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    use crate::{
        air::debug::debug_constraints_collecting_queries,
        lair::{
            execute::QueryRecord, func_chip::FuncChip, hasher::LurkHasher, toplevel::Toplevel, List,
        },
        lurk::{
            reader::{read, ReadData},
            state::State,
            zstore::{PoseidonBabyBearHasher, Tag},
        },
    };

    use super::*;

    #[test]
    fn list_lookup_test() {
        let list_lookup = func!(
            fn list_lookup(x, list_tag, list): [2] {
                match list_tag {
                    Tag::Nil => {
                        let err_tag = Tag::Err;
                        let err = EvalErr::UnboundVar;
                        return (err_tag, err)
                    }
                    Tag::Cons => {
                        let (_head_tag, head, tail_tag, tail) = load(list);
                        let (_y_tag, y, val_tag, val) = load(head);
                        let diff = sub(x, y);
                        if !diff {
                            return (val_tag, val)
                        }
                        let (res_tag, res) = call(list_lookup, x, tail_tag, tail);
                        return (res_tag, res)
                    }
                }
            }
        );
        let to_env_lookup = func!(
            fn to_env_lookup(x, list_tag, list): [2] {
                let (status, env) = call(list_to_env, list_tag, list);
                if !status {
                    return (status, status)
                }
                let (res_tag, res) = call(env_lookup, x, env);
                return (res_tag, res)
            }
        );
        let toplevel = Toplevel::<_, LurkHasher>::new(&[
            list_lookup,
            to_env_lookup,
            env_lookup(),
            list_to_env(),
        ]);
        let list_lookup = FuncChip::from_name("list_lookup", &toplevel);
        let to_env_lookup = FuncChip::from_name("to_env_lookup", &toplevel);

        let mut mem = Memory::init();
        let store = &ZStore::<F, PoseidonBabyBearHasher>::new();
        let list = mem
            .read_and_ingress("((x . 10) (y . 20) (z . 30) (w . 40))", store)
            .unwrap();
        let y = mem.read_and_ingress("y", store).unwrap();
        let z = mem.read_and_ingress("z", store).unwrap();

        let queries = &mut QueryRecord::new_with_init_mem(&toplevel, mem.map);

        let args: List<_> = [y.raw, list.tag, list.raw].into();
        list_lookup.execute(args.clone(), queries);
        let result = queries.func_queries[list_lookup.func.index]
            .get(&args)
            .unwrap();
        let expected = [Tag::Num.to_field(), F::from_canonical_u32(20)].into();
        assert_eq!(result.output, expected);

        let args: List<_> = [z.raw, list.tag, list.raw].into();
        to_env_lookup.execute(args.clone(), queries);
        let result = queries.func_queries[to_env_lookup.func.index]
            .get(&args)
            .unwrap();
        let expected = [Tag::Num.to_field(), F::from_canonical_u32(30)].into();
        assert_eq!(result.output, expected);
    }

    #[test]
    fn eval_test() {
        use std::mem::take;

        let mem = &mut Memory::init();
        let store = &ZStore::<F, PoseidonBabyBearHasher>::new();
        let toplevel = &build_lurk_toplevel::<_, LurkHasher>(mem, store);
        let queries = &mut QueryRecord::new_with_init_mem(toplevel, take(&mut mem.map));

        // Chips
        let ingress = FuncChip::from_name("ingress", toplevel);
        let egress = FuncChip::from_name("egress", toplevel);
        let eval = FuncChip::from_name("eval", toplevel);
        let eval_unop = FuncChip::from_name("eval_unop", toplevel);
        let eval_binop_num = FuncChip::from_name("eval_binop_num", toplevel);
        let eval_binop_misc = FuncChip::from_name("eval_binop_misc", toplevel);
        let eval_let = FuncChip::from_name("eval_let", toplevel);
        let eval_letrec = FuncChip::from_name("eval_letrec", toplevel);
        let car_cdr = FuncChip::from_name("car_cdr", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let env_lookup = FuncChip::from_name("env_lookup", toplevel);

        // Widths
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(eval.width(), expect!["106"]);
        expect_eq(eval_unop.width(), expect!["33"]);
        expect_eq(eval_binop_num.width(), expect!["38"]);
        expect_eq(eval_binop_misc.width(), expect!["41"]);
        expect_eq(eval_let.width(), expect!["34"]);
        expect_eq(eval_letrec.width(), expect!["33"]);
        expect_eq(car_cdr.width(), expect!["27"]);
        expect_eq(apply.width(), expect!["36"]);
        expect_eq(env_lookup.width(), expect!["16"]);
        expect_eq(ingress.width(), expect!["87"]);
        expect_eq(egress.width(), expect!["66"]);

        let all_chips = [
            &eval,
            &eval_unop,
            &eval_binop_num,
            &eval_binop_misc,
            &eval_let,
            &eval_letrec,
            &car_cdr,
            &apply,
            &env_lookup,
        ];

        let mut eval_aux = |expr: &str, res: &str| {
            mem.map = take(&mut queries.mem_queries);
            let expr = mem.read_and_ingress(expr, store).unwrap();
            let res = mem.read_and_ingress(res, store).unwrap();
            let env = F::zero();
            let args: List<_> = [expr.tag, expr.raw, env].into();
            queries.mem_queries = take(&mut mem.map);
            eval.execute(args.clone(), queries);
            let result = queries.func_queries[eval.func.index].get(&args).unwrap();
            let expected = [res.tag, res.raw].into();
            assert_eq!(result.output, expected);
            all_chips.into_par_iter().for_each(|chip| {
                let trace = chip.generate_trace_parallel(queries);
                debug_constraints_collecting_queries(chip, &[], &trace);
            });
        };

        eval_aux("t", "t");
        eval_aux("nil", "nil");
        eval_aux("((lambda (x) x) 1)", "1");
        eval_aux("((lambda (x y z) x) 1 2 3)", "1");
        eval_aux("((lambda (x y z) z) 1 2 3)", "3");
        eval_aux("((lambda (x) (lambda (y) x)) 1 2)", "1");
        eval_aux("(if 1 2 3)", "2");
        eval_aux("(if nil 2 3)", "3");
        eval_aux("(let ((x 1) (y 2) (z 3)) y)", "2");
        eval_aux("(letrec ((x 1) (y 2) (z 3)) y)", "2");
        eval_aux("(+ 1 2)", "3");
        eval_aux("(+ (* 2 2) (* 2 3))", "10");
        eval_aux("(= 0 1)", "nil");
        eval_aux("(= 0 0)", "t");
        eval_aux("(begin 1 2 3)", "3");
        eval_aux("'x", "x");
        eval_aux("'(+ 1 2)", "(+ 1 2)");
        eval_aux("(eval 'x (let ((x 1)) (current-env)))", "1");
        eval_aux("(eval '(+ 1 2) (empty-env))", "3");
        eval_aux("(cons 1 2)", "(1 . 2)");
        eval_aux("(strcons 'a' \"bc\")", "\"abc\"");
        eval_aux("'a'", "'a'");
        eval_aux("(eq (cons 1 2) '(1 . 2))", "t");
        eval_aux("(eq (cons 1 3) '(1 . 2))", "nil");
        eval_aux("(car (cons 1 2))", "1");
        eval_aux("(cdr (cons 1 (cons 2 3)))", "(2 . 3)");
        eval_aux(
            "
        (letrec ((factorial
                  (lambda (n)
                    (if (= n 0) 1
                      (* n (factorial (- n 1)))))))
          (factorial 5))
        ",
            "120",
        );
        eval_aux(
            "
        (letrec ((fib
                  (lambda (n)
                    (if (= n 0) 1
                      (if (= n 1) 1
                        (+ (fib (- n 1)) (fib (- n 2))))))))
          (fib 50))
        ",
            "20365011074",
        );
    }

    #[test]
    fn test_ingress_egress() {
        let builtins = builtin_digests();
        let toplevel = Toplevel::<F, LurkHasher>::new(&[
            ingress(),
            ingress_builtin(builtins),
            egress(),
            egress_builtin(builtins),
            hash_32_8(),
            hash_48_8(),
        ]);

        let ingress_chip = FuncChip::from_name("ingress", &toplevel);
        let egress_chip = FuncChip::from_name("egress", &toplevel);
        let hash_32_8_chip = FuncChip::from_name("hash_32_8", &toplevel);

        let assert_ingress_egress_correctness = |code| {
            let ReadData {
                tag,
                digest,
                hashes,
            } = read(State::init_lurk_state().rccell(), code).unwrap();

            let digest: List<_> = digest.into();

            let queries = &mut QueryRecord::new(&toplevel);
            queries.inject_queries("hash_32_8", &toplevel, hashes);

            let mut ingress_args = [F::zero(); 16];
            ingress_args[0] = tag;
            ingress_args[8..].copy_from_slice(&digest);

            let ingress_args: List<_> = ingress_args.into();
            ingress_chip.execute_iter(ingress_args.clone(), queries);
            let ingress_out_ptr = queries.func_queries[ingress_chip.func.index]
                .get(&ingress_args)
                .unwrap()
                .output[0];

            let egress_args: List<_> = [tag, ingress_out_ptr].into();
            egress_chip.execute_iter(egress_args.clone(), queries);
            let egress_out = &queries.func_queries[egress_chip.func.index]
                .get(&egress_args)
                .unwrap()
                .output;

            assert_eq!(egress_out, &digest, "ingress -> egress doesn't roundtrip");

            let hash_32_8_trace = hash_32_8_chip.generate_trace_parallel(queries);
            debug_constraints_collecting_queries(&hash_32_8_chip, &[], &hash_32_8_trace);
        };

        assert_ingress_egress_correctness("~()");
        assert_ingress_egress_correctness("~:()");
        assert_ingress_egress_correctness("()");
        assert_ingress_egress_correctness("'c'");
        assert_ingress_egress_correctness("5u64");
        assert_ingress_egress_correctness("\"\"");
        assert_ingress_egress_correctness("\"a\"");
        assert_ingress_egress_correctness("\"test string\"");
        assert_ingress_egress_correctness(".a");
        assert_ingress_egress_correctness("TestSymbol");
        assert_ingress_egress_correctness(":keyword");
        assert_ingress_egress_correctness("(+ 1 2)");
        assert_ingress_egress_correctness("(a 'b c)");
    }
}
