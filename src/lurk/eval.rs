use p3_field::{Field, PrimeField};

use crate::{func, lair::expr::FuncE, lurk::store::Tag};

use super::{
    memory::Memory,
    store::{Hasher, ZStore},
};

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
}

impl EvalErr {
    fn to_field<F: Field>(self) -> F {
        F::from_canonical_u8(self as u8)
    }
}

pub fn eval<F: PrimeField, H: Hasher<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    let t = mem.read_and_ingress("t", store).unwrap().raw;
    let nil = mem.read_and_ingress("nil", store).unwrap().raw;
    let lambda = mem.read_and_ingress("lambda", store).unwrap().raw;
    let let_ = mem.read_and_ingress("let", store).unwrap().raw;
    let letrec = mem.read_and_ingress("letrec", store).unwrap().raw;
    let if_ = mem.read_and_ingress("if", store).unwrap().raw;
    let quote = mem.read_and_ingress("quote", store).unwrap().raw;
    let eval = mem.read_and_ingress("eval", store).unwrap().raw;
    let begin = mem.read_and_ingress("begin", store).unwrap().raw;
    let empty_env = mem.read_and_ingress("empty-env", store).unwrap().raw;
    let current_env = mem.read_and_ingress("current-env", store).unwrap().raw;
    let add = mem.read_and_ingress("+", store).unwrap().raw;
    let sub = mem.read_and_ingress("-", store).unwrap().raw;
    let mul = mem.read_and_ingress("*", store).unwrap().raw;
    let div = mem.read_and_ingress("/", store).unwrap().raw;
    let equal = mem.read_and_ingress("=", store).unwrap().raw;
    func!(
        fn eval(expr_tag, expr, env): 2 {
            // Constants, tags, etc
            let t = Const(t);
            let nil = Const(nil);
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
                            match head {
                                Const(lambda) => {
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
                                Const(let_) => {
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
                                Const(letrec) => {
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
                                Const(eval) => {
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
                                            return (err_tag, invalid_form)
                                        }
                                    };
                                    let not_env = EvalErr::NotEnv;
                                    return (err_tag, not_env)
                                }
                                Const(quote) => {
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
                                Const(begin) => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    let (val_tag, val) = call(eval, expr_tag, expr, env);
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
                                Const(empty_env) => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let env_tag = Tag::Env;
                                    let env = 0;
                                    return (env_tag, env)
                                }
                                Const(current_env) => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let env_tag = Tag::Env;
                                    return (env_tag, env)
                                }
                                Const(add)
                                | Const(sub)
                                | Const(mul)
                                | Const(div)
                                | Const(equal) => {
                                    let (res_tag, res) = call(eval_binop_num, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                Const(if_) => {
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
                                // TODO: other keywords
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

pub fn eval_binop_num<F: PrimeField, H: Hasher<F = F>>(
    mem: &mut Memory<F, H>,
    store: &ZStore<F, H>,
) -> FuncE<F> {
    let nil = mem.read_and_ingress("nil", store).unwrap().raw;
    let t = mem.read_and_ingress("t", store).unwrap().raw;
    let add = mem.read_and_ingress("+", store).unwrap().raw;
    let sub = mem.read_and_ingress("-", store).unwrap().raw;
    let mul = mem.read_and_ingress("*", store).unwrap().raw;
    let div = mem.read_and_ingress("/", store).unwrap().raw;
    let equal = mem.read_and_ingress("=", store).unwrap().raw;
    func!(
        fn eval_binop_num(head, rest_tag, rest, env): 2 {
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
                Tag::Sym => {
                    let err = EvalErr::ArgNotNumber;
                    return (err_tag, err)
                }
            };
            let (val2_tag, val2) = call(eval, exp2_tag, exp2, env);
            match val2_tag {
                Tag::Err => {
                    return (val2_tag, val2)
                }
                Tag::Sym => {
                    let err = EvalErr::ArgNotNumber;
                    return (err_tag, err)
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
            match head {
                Const(add) => {
                    let res = add(val1, val2);
                    return (num_tag, res)
                }
                Const(sub) => {
                    let res = sub(val1, val2);
                    return (num_tag, res)
                }
                Const(mul) => {
                    let res = mul(val1, val2);
                    return (num_tag, res)
                }
                Const(div) => {
                    let res = div(val1, val2);
                    if !val2 {
                        let err = EvalErr::DivByZero;
                        return (err_tag, err)
                    }
                    return (num_tag, res)
                }
                Const(equal) => {
                    let diff = sub(val1, val2);
                    if !diff {
                        let sym_tag = Tag::Sym;
                        let t = Const(t);
                        return (sym_tag, t)
                    }
                    let nil = Const(nil);
                    return (nil_tag, nil)
                }
            }
        }
    )
}

pub fn eval_let<F: PrimeField>() -> FuncE<F> {
    func!(
        fn eval_let(binds_tag, binds, body_tag, body, env): 2 {
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
        fn eval_letrec(binds_tag, binds, body_tag, body, env): 2 {
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
        fn apply(head_tag, head, args_tag, args, args_env): 2 {
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
        fn env_lookup(x, env): 2 {
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
        fn list_to_env(list_tag, list): 2 {
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

    use crate::{
        lair::{chip::FuncChip, execute::QueryRecord, toplevel::Toplevel, List},
        lurk::store::{PoseidonBabyBearHasher, Tag},
    };

    use super::*;

    #[test]
    fn list_lookup_test() {
        let list_lookup = func!(
            fn list_lookup(x, list_tag, list): 2 {
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
            fn to_env_lookup(x, list_tag, list): 2 {
                let (status, env) = call(list_to_env, list_tag, list);
                if !status {
                    return (status, status)
                }
                let (res_tag, res) = call(env_lookup, x, env);
                return (res_tag, res)
            }
        );
        let toplevel = Toplevel::new(&[list_lookup, to_env_lookup, env_lookup(), list_to_env()]);
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
        let toplevel = &Toplevel::new(&[
            eval(mem, store),
            eval_binop_num(mem, store),
            eval_let(),
            eval_letrec(),
            apply(),
            env_lookup(),
        ]);
        let queries = &mut QueryRecord::new_with_init_mem(toplevel, take(&mut mem.map));

        // Chips
        let eval = FuncChip::from_name("eval", toplevel);
        let eval_binop_num = FuncChip::from_name("eval_binop_num", toplevel);
        let eval_let = FuncChip::from_name("eval_let", toplevel);
        let eval_letrec = FuncChip::from_name("eval_letrec", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let env_lookup = FuncChip::from_name("env_lookup", toplevel);

        // Widths
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(eval.width(), expect!["75"]);
        expect_eq(eval_binop_num.width(), expect!["42"]);
        expect_eq(eval_let.width(), expect!["34"]);
        expect_eq(eval_letrec.width(), expect!["33"]);
        expect_eq(apply.width(), expect!["36"]);
        expect_eq(env_lookup.width(), expect!["16"]);

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
}
