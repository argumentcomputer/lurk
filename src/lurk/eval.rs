use indexmap::{map::Iter, IndexMap};
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rustc_hash::FxBuildHasher;

use crate::{
    func,
    lair::{
        expr::{BlockE, CasesE, CtrlE, FuncE, OpE, Var},
        hasher::LurkHasher,
        map::Map,
        toplevel::Toplevel,
        List, Name,
    },
};

use super::{
    state::{State, StateRcCell, LURK_PACKAGE_SYMBOLS_NAMES},
    tag::Tag,
    zstore::ZStore,
};

pub struct BuiltinIndex(usize);

impl BuiltinIndex {
    fn to_field<F: AbstractField>(&self) -> F {
        F::from_canonical_usize(self.0)
    }
}

pub struct BuiltinMemo<'a, F>(IndexMap<&'a str, List<F>, FxBuildHasher>);

impl<'a> BuiltinMemo<'a, BabyBear> {
    fn new(state: &StateRcCell, zstore: &mut ZStore<BabyBear, LurkHasher>) -> Self {
        Self(
            LURK_PACKAGE_SYMBOLS_NAMES
                .into_iter()
                .filter(|sym| sym != &"nil")
                .map(|name| {
                    (
                        name,
                        zstore
                            .read_with_state(state.clone(), name)
                            .unwrap()
                            .digest
                            .into(),
                    )
                })
                .collect(),
        )
    }
}

impl<'a, F> BuiltinMemo<'a, F> {
    fn index(&self, builtin: &'a str) -> BuiltinIndex {
        BuiltinIndex(self.0.get_index_of(builtin).expect("Unknown builtin"))
    }

    fn iter(&self) -> Iter<'_, &str, Box<[F]>> {
        self.0.iter()
    }
}

/// Creates a `Toplevel` with the functions used for Lurk evaluation
#[inline]
pub fn build_lurk_toplevel() -> Toplevel<BabyBear, LurkHasher> {
    let state = State::init_lurk_state().rccell();
    let zstore = &mut ZStore::default();
    let builtins = BuiltinMemo::new(&state, zstore);
    let nil = zstore.read_with_state(state, "nil").unwrap().digest.into();
    Toplevel::new(&[
        lurk_main(),
        eval(&builtins),
        eval_unop(&builtins),
        eval_binop_num(&builtins),
        eval_binop_misc(&builtins),
        car_cdr(),
        eval_let(),
        eval_letrec(),
        apply(),
        env_lookup(),
        ingress(),
        ingress_builtin(&builtins),
        egress(nil),
        egress_builtin(&builtins),
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
    NotEnv,
    NotChar,
    NotCons,
    NotComm,
    NotString,
    CannotCastToNum,
    NonConstantBuiltin,
    Todo,
}

impl EvalErr {
    fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u8(self as u8)
    }
}

pub fn lurk_main<F: AbstractField>() -> FuncE<F> {
    func!(
        fn lurk_main(full_expr_tag: [8], expr_digest: [8], env_digest: [8]): [16] {
            // Ingress on expr
            let expr = call(ingress, full_expr_tag, expr_digest);
            // Ingress on env
            let padding = [0; 7];
            let env_tag = Tag::Env;
            let full_env_tag: [8] = (env_tag, padding);
            let env = call(ingress, full_env_tag, env_digest);
            // Evaluate expr, env
            let (expr_tag, _rest: [7]) = full_expr_tag;
            let (val_tag, val) = call(eval, expr_tag, expr, env);
            // Egress on val
            let val_digest: [8] = call(egress, val_tag, val);
            let full_val_tag: [8] = (val_tag, padding);
            return (full_val_tag, val_digest)
        }
    )
}

pub fn ingress<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn ingress(tag_full: [8], digest: [8]): [1] {
            let (tag, _rest: [7]) = tag_full;
            match tag {
                Tag::Num, Tag::Char, Tag::Err => {
                    let (x, _rest: [7]) = digest;
                    return x
                }
                Tag::Nil => {
                    let zero = 0;
                    return zero
                }
                Tag::U64, Tag::Comm => {
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Builtin => {
                    let idx = call(ingress_builtin, digest);
                    return idx
                }
                Tag::Str, Tag::Sym, Tag::Key => {
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
                Tag::Cons, Tag::Thunk => {
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash_32_8, digest);
                    let fst_ptr = call(ingress, fst_tag_full, fst_digest);
                    let snd_ptr = call(ingress, snd_tag_full, snd_digest);
                    let (fst_tag, _rest: [7]) = fst_tag_full;
                    let (snd_tag, _rest: [7]) = snd_tag_full;
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return ptr
                }
                Tag::Fun => {
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
                Tag::Env => {
                    if !digest {
                        let zero = 0;
                        return zero
                    }
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

fn ingress_builtin<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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
            .map(|(i, (_, digest))| (digest.clone(), branch(i)))
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

pub fn egress<F: AbstractField + Ord>(nil: List<F>) -> FuncE<F> {
    func!(
        fn egress(tag, val): [8] {
            match tag {
                Tag::Num, Tag::Char, Tag::Err => {
                    let padding = [0; 7];
                    let digest: [8] = (val, padding);
                    return digest
                }
                Tag::Nil => {
                    let digest = Array(nil);
                    return digest
                }
                Tag::U64, Tag::Comm => {
                    let digest: [8] = load(val);
                    return digest
                }
                Tag::Builtin => {
                    let digest: [8] = call(egress_builtin, val);
                    return digest
                }
                Tag::Str, Tag::Sym, Tag::Key => {
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
                Tag::Thunk => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash_32_8, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return digest
                }
                Tag::Cons => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash_32_8, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return digest
                }
                Tag::Fun => {
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
                Tag::Env => {
                    if !val {
                        let digest = [0; 8];
                        return digest
                    }
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

fn egress_builtin<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    let input_var = Var {
        name: "val",
        size: 1,
    };
    let ret_var = Var {
        name: "digest",
        size: 8,
    };
    let branch = |arr: List<F>| BlockE {
        ops: [OpE::Array(ret_var, arr)].into(),
        ctrl: CtrlE::<F>::Return([ret_var].into()),
    };
    let branches = Map::from_vec(
        builtins
            .iter()
            .enumerate()
            .map(|(i, (_, digest))| (F::from_canonical_usize(i), branch(digest.clone())))
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

pub fn hash_32_8<F>() -> FuncE<F> {
    func!(
        invertible fn hash_32_8(preimg: [32]): [8] {
            let img: [8] = hash(preimg);
            return img
        }
    )
}

pub fn hash_48_8<F>() -> FuncE<F> {
    func!(
        invertible fn hash_48_8(preimg: [48]): [8] {
            let (img: [8]) = hash(preimg);
            return img
        }
    )
}

pub fn eval<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        fn eval(expr_tag, expr, env): [2] {
            // Constants, tags, etc
            let t = builtins.index("t");
            let nil_tag = Tag::Nil;
            let cons_tag = Tag::Cons;
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;

            match expr_tag {
                Tag::Builtin => {
                    let not_t = sub(expr, t);
                    if !not_t {
                        return (expr_tag, expr)
                    }
                    let non_constant_builtin = EvalErr::NonConstantBuiltin;
                    return (err_tag, non_constant_builtin)
                }
                Tag::Sym => {
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
                        Tag::Builtin => {
                            match head [|sym| builtins.index(sym).to_field()] {
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
                                "+", "-", "*", "/", "=" => {
                                    let (res_tag, res) = call(eval_binop_num, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                "cons", "strcons", "hide", "eq" => {
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
                                "commit", "num", "u64", "comm", "char", "open", "secret", "atom", "emit" => {
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

pub fn car_cdr<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn car_cdr(rest_tag, rest, env): [4] {
            let nil = 0;
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

pub fn eval_binop_num<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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
            match head [|sym| builtins.index(sym).to_field()] {
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
                        let builtin_tag = Tag::Builtin;
                        let t = builtins.index("t");
                        return (builtin_tag, t)
                    }
                    let nil = 0;
                    return (nil_tag, nil)
                }
            }
        }
    )
}

pub fn eval_binop_misc<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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
            match head [|sym| builtins.index(sym).to_field()] {
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
                    let t = builtins.index("t");
                    let nil = 0;
                    let eq_tag = eq(val1_tag, val2_tag);
                    let eq_val = eq(val1, val2);
                    let eq = mul(eq_tag, eq_val);
                    if eq {
                        let builtin_tag = Tag::Builtin;
                        return (builtin_tag, t)
                    }
                    return (nil_tag, nil)
               }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn eval_unop<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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

            match head [|sym| builtins.index(sym).to_field()] {
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
                        let builtin_tag = Tag::Builtin;
                        let t = builtins.index("t");
                        return (builtin_tag, t)
                    }
                    let nil = 0;
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

pub fn eval_let<F: AbstractField + Ord>() -> FuncE<F> {
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

pub fn eval_letrec<F: AbstractField + Ord>() -> FuncE<F> {
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
                    // this will preemptively evaluate the thunk, so that we do not skip evaluation in case
                    // the variable is not used inside the letrec body, and furthermore it follows a strict
                    // evaluation order
                    let (_val_tag, _val) = call(eval, expr_tag, expr, ext_env);
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

pub fn apply<F: AbstractField + Ord>() -> FuncE<F> {
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

pub fn env_lookup<F: AbstractField>() -> FuncE<F> {
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

#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};
    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use rayon::iter::{IntoParallelIterator, ParallelIterator};

    use crate::{
        air::debug::debug_constraints_collecting_queries,
        lair::{execute::QueryRecord, func_chip::FuncChip, hasher::LurkHasher, List},
        lurk::{
            state::State,
            zstore::{ZPtr, ZStore},
        },
    };

    use super::*;

    #[test]
    fn eval_test() {
        let toplevel = &build_lurk_toplevel();

        // Chips
        let lurk_main = FuncChip::from_name("lurk_main", toplevel);
        let eval = FuncChip::from_name("eval", toplevel);
        let eval_unop = FuncChip::from_name("eval_unop", toplevel);
        let eval_binop_num = FuncChip::from_name("eval_binop_num", toplevel);
        let eval_binop_misc = FuncChip::from_name("eval_binop_misc", toplevel);
        let eval_let = FuncChip::from_name("eval_let", toplevel);
        let eval_letrec = FuncChip::from_name("eval_letrec", toplevel);
        let car_cdr = FuncChip::from_name("car_cdr", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let env_lookup = FuncChip::from_name("env_lookup", toplevel);
        let ingress = FuncChip::from_name("ingress", toplevel);
        let ingress_builtin = FuncChip::from_name("ingress_builtin", toplevel);
        let egress = FuncChip::from_name("egress", toplevel);
        let egress_builtin = FuncChip::from_name("egress_builtin", toplevel);
        let hash_32_8 = FuncChip::from_name("hash_32_8", toplevel);
        let hash_48_8 = FuncChip::from_name("hash_48_8", toplevel);

        // Widths
        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(lurk_main.width(), expect!["38"]);
        expect_eq(eval.width(), expect!["105"]);
        expect_eq(eval_unop.width(), expect!["31"]);
        expect_eq(eval_binop_num.width(), expect!["36"]);
        expect_eq(eval_binop_misc.width(), expect!["39"]);
        expect_eq(eval_let.width(), expect!["32"]);
        expect_eq(eval_letrec.width(), expect!["33"]);
        expect_eq(car_cdr.width(), expect!["23"]);
        expect_eq(apply.width(), expect!["34"]);
        expect_eq(env_lookup.width(), expect!["14"]);
        expect_eq(ingress.width(), expect!["95"]);
        expect_eq(ingress_builtin.width(), expect!["44"]);
        expect_eq(egress.width(), expect!["60"]);
        expect_eq(egress_builtin.width(), expect!["37"]);
        expect_eq(hash_32_8.width(), expect!["645"]);
        expect_eq(hash_48_8.width(), expect!["965"]);

        let all_chips = [
            &lurk_main,
            &eval,
            &eval_unop,
            &eval_binop_num,
            &eval_binop_misc,
            &eval_let,
            &eval_letrec,
            &car_cdr,
            &apply,
            &env_lookup,
            &ingress,
            &ingress_builtin,
            &egress,
            &egress_builtin,
            &hash_32_8,
            &hash_48_8,
        ];

        let state = State::init_lurk_state().rccell();

        let eval_aux = |expr: &str, res: &str| {
            let zstore = &mut ZStore::<_, LurkHasher>::default();

            let ZPtr {
                tag: expr_tag,
                digest: expr_digest,
            } = zstore.read_with_state(state.clone(), expr).unwrap();

            let queries = &mut QueryRecord::new(toplevel);
            queries.inject_queries("hash_32_8", toplevel, zstore.tuple2_hashes());

            let ZPtr {
                tag: expected_tag,
                digest: expected_digest,
            } = zstore.read_with_state(state.clone(), res).unwrap();

            let mut full_input = [F::zero(); 24];
            full_input[0] = expr_tag.to_field();
            full_input[8..16].copy_from_slice(&expr_digest);

            let full_input: List<_> = full_input.into();
            lurk_main.execute_iter(full_input.clone(), queries);
            let result = queries.get_output(lurk_main.func, &full_input);

            assert_eq!(&result[0], &expected_tag.to_field());
            assert_eq!(&result[8..], &expected_digest);

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
        eval_aux(
            "
(letrec ((ones (cons 1 (lambda () ones))))
  (car ((cdr ones))))

",
            "1",
        );
    }

    #[test]
    fn test_ingress_egress() {
        let toplevel = &build_lurk_toplevel();

        let ingress_chip = FuncChip::from_name("ingress", toplevel);
        let egress_chip = FuncChip::from_name("egress", toplevel);
        let hash_32_8_chip = FuncChip::from_name("hash_32_8", toplevel);

        let state = State::init_lurk_state().rccell();

        let assert_ingress_egress_correctness = |code| {
            let zstore = &mut ZStore::<_, LurkHasher>::default();
            let ZPtr { tag, digest } = zstore.read_with_state(state.clone(), code).unwrap();
            let tag = tag.to_field();

            let digest: List<_> = digest.into();

            let queries = &mut QueryRecord::new(toplevel);
            queries.inject_queries("hash_32_8", toplevel, zstore.tuple2_hashes());

            let mut ingress_args = [F::zero(); 16];
            ingress_args[0] = tag;
            ingress_args[8..].copy_from_slice(&digest);

            let ingress_args: List<_> = ingress_args.into();
            ingress_chip.execute_iter(ingress_args.clone(), queries);
            let ingress_out_ptr = queries.get_output(ingress_chip.func, &ingress_args)[0];

            let egress_args: List<_> = [tag, ingress_out_ptr].into();
            egress_chip.execute_iter(egress_args.clone(), queries);
            let egress_out = queries.get_output(egress_chip.func, &egress_args);

            assert_eq!(
                egress_out,
                digest.as_ref(),
                "ingress -> egress doesn't roundtrip"
            );

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
