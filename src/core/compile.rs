use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField32};

use crate::{
    core::{error::EvalErr, ingress::InternalTag},
    func,
    lair::{chipset::NoChip, expr::FuncE, toplevel::Toplevel},
};

use super::{ingress::SymbolsDigests, tag::Tag};

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, FromPrimitive)]
pub enum Op {
    // If statement
    If = 0x00001000,
    // Local (recursive) definition
    Let,
    Letrec,
    // Functions
    MkFun,
    MkThunk,
    MkRestFun,
    App,
    Apply,
    // Equality
    Eq,
    Eqq,
    TypeEq,
    TypeEqq,
    NumEq,
    // Boolean
    And,
    Or,
    Not,
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Less,
    LessEq,
    Great,
    GreatEq,
    // Lists and strings
    MkCons,
    Car,
    Cdr,
    Atom,
    MkStrcons,
    // Commitments
    Hide,
    Open,
    Secret,
    // Eval
    Eval,
    Quote,
    // Environments
    CurrentEnv,
    EmptyEnv,
    // Conversions
    U64,
    Char,
    Comm,
    Bignum,
    // Misc
    Emit,
    Begin,
    Fail,
    Breakpoint,
}

impl Op {
    #[inline]
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    #[inline]
    pub fn from_field<F: PrimeField32>(f: &F) -> Op {
        Op::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a tag")
    }
}

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, FromPrimitive)]
pub enum Val {
    Fun = 0x00010000,
    Thunk,
    RestFun,
    Fix,
}

impl Val {
    #[inline]
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    #[inline]
    pub fn from_field<F: PrimeField32>(f: &F) -> Val {
        Val::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a tag")
    }
}

pub fn compile<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        invertible fn compile(expr_tag, expr): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match expr_tag {
                Tag::Cons => {
                    let nil_tag = InternalTag::Nil;
                    let cons_tag = Tag::Cons;
                    let (head_tag, head, rest_tag, rest) = load(expr);
                    match head_tag {
                        Tag::Builtin => {
                            let op = call(symbol_to_op, head);
                            match head [|sym| digests.builtin_symbol_ptr(sym).to_field()] {
                                // zero elements
                                "current-env", "empty-env", "fail" => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let null = 0;
                                    return (op, null)
                                }
                                // one element
                                "car", "cdr", "u64", "char", "atom", "emit", "commit", "comm", "open", "secret", "bignum" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
                                    match cexpr_tag {
                                        Tag::Err => {
                                            return (cexpr_tag, cexpr)
                                        }
                                    };
                                    match head [|sym| digests.builtin_symbol_ptr(sym).to_field()] {
                                        "commit" => {
                                            let bignum_content = [0; 8];
                                            let bignum = store(bignum_content);
                                            let bignum_tag = Tag::BigNum;
                                            let ptr = store(bignum_tag, bignum, cexpr_tag, cexpr);
                                            return (op, ptr)
                                        }
                                    };
                                    let ptr = store(cexpr_tag, cexpr);
                                    return (op, ptr)
                                }
                                // two elements
                                "apply", "cons", "strcons", "hide", "eq", "eqq", "type-eq", "type-eqq"  => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (fst_tag, fst, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (snd_tag, snd, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let (cfst_tag, cfst) = call(compile, fst_tag, fst);
                                    match cfst_tag {
                                        Tag::Err => {
                                            return (cfst_tag, cfst)
                                        }
                                    };
                                    let (csnd_tag, csnd) = call(compile, snd_tag, snd);
                                    match csnd_tag {
                                        Tag::Err => {
                                            return (csnd_tag, csnd)
                                        }
                                    };
                                    let ptr = store(cfst_tag, cfst, csnd_tag, csnd);
                                    return (op, ptr)
                                }
                                // variadic
                                "begin", "+", "-", "*", "/", "%" => {
                                    let u64_tag = Tag::U64;
                                    let o = 0;
                                    match rest_tag {
                                        InternalTag::Nil => {
                                            match head [|sym| digests.builtin_symbol_ptr(sym).to_field()] {
                                                "+", "-", "*" => {
                                                    let zero = store(o, o, o, o, o, o, o, o);
                                                    return (u64_tag, zero)
                                                }
                                                "/", "%" => {
                                                    let i = 1;
                                                    let one = store(i, o, o, o, o, o, o, o);
                                                    return (u64_tag, one)
                                                }
                                                "begin" => {
                                                    let nil_tag = InternalTag::Nil;
                                                    let nil = digests.lurk_symbol_ptr("nil");
                                                    return (nil_tag, nil)
                                                }
                                            }
                                        }
                                        Tag::Cons => {
                                            let (init_tag, init, rest_tag, rest) = load(rest);
                                            let (init_tag, init) = call(compile, init_tag, init);
                                            match init_tag {
                                                Tag::Err => {
                                                    return (init_tag, init)
                                                }
                                            };
                                            let (res_tag, res) = call(compile_fold_left, op, init_tag, init, rest_tag, rest);
                                            return (res_tag, res)
                                        }
                                    };
                                    return (err_tag, invalid_form)
                                }
                                "=", "<", ">", "<=", ">=" => {
                                    let (res_tag, res) = call(compile_fold_rel, op, rest_tag, rest);
                                    return (res_tag, res)
                                }
                                "list" => {
                                    let nil_tag = InternalTag::Nil;
                                    let nil = digests.lurk_symbol_ptr("nil");
                                    let (res_tag, res) = call(compile_fold_right, op, nil_tag, nil, rest_tag, rest);
                                    return (res_tag, res)
                                }
                                // miscellaneous
                                "lambda", "let", "letrec" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (fst_tag, fst, rest_tag, rest) = load(rest);
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (snd_tag, snd, rest_tag, _rest) = load(rest);
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let (cbody_tag, cbody) = call(compile, snd_tag, snd);
                                    match cbody_tag {
                                        Tag::Err => {
                                            return (cbody_tag, cbody)
                                        }
                                    };
                                    match head [|sym| digests.builtin_symbol_ptr(sym).to_field()] {
                                        "lambda" => {
                                            let (res_tag, res) = call(compile_lambda, fst_tag, fst, cbody_tag, cbody);
                                            return (res_tag, res)
                                        }
                                        "let" => {
                                            let (res_tag, res) = call(compile_let, fst_tag, fst, cbody_tag, cbody);
                                            return (res_tag, res)
                                        }
                                        "letrec" => {
                                            match fst_tag {
                                                InternalTag::Nil => {
                                                    return (cbody_tag, cbody)
                                                }
                                            };
                                            let (binds_tag, binds) = call(compile_mutual_binds, fst_tag, fst);
                                            match binds_tag {
                                                Tag::Err => {
                                                    return (binds_tag, binds)
                                                }
                                            };
                                            let ptr = store(binds, cbody_tag, cbody);
                                            return (op, ptr)
                                        }
                                    }
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
                                    let (cexpr_tag, cexpr) = call(convert_data, expr_tag, expr);
                                    match cexpr_tag {
                                        Tag::Err => {
                                            return (cexpr_tag, cexpr)
                                        }
                                    };
                                    let tag = Op::Quote;
                                    let ptr = store(cexpr_tag, cexpr);
                                    return (tag, ptr)
                                }
                                "eval" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
                                    match cexpr_tag {
                                        Tag::Err => {
                                            return (cexpr_tag, cexpr)
                                        }
                                    };
                                    let tag = Op::Eval;
                                    match rest_tag {
                                        InternalTag::Nil => {
                                            let env_tag = Tag::Env;
                                            let env = 0;
                                            let ptr = store(cexpr_tag, cexpr, env_tag, env);
                                            return (tag, ptr)
                                        }
                                        Tag::Cons => {
                                            let (env_expr_tag, env_expr, rest_tag, _rest) = load(rest);
                                            let rest_not_nil = sub(rest_tag, nil_tag);
                                            if rest_not_nil {
                                                return (err_tag, invalid_form)
                                            }
                                            let (env_cexpr_tag, env_cexpr) = call(compile, env_expr_tag, env_expr);
                                            match env_cexpr_tag {
                                                Tag::Err => {
                                                    return (env_cexpr_tag, env_cexpr)
                                                }
                                            };
                                            let ptr = store(cexpr_tag, cexpr, env_cexpr_tag, env_cexpr);
                                            return (tag, ptr)
                                        }
                                    };
                                    let not_env = EvalErr::InvalidForm;
                                    return (err_tag, not_env)
                                }
                                "if" => {
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (expr_tag, expr, rest_tag, rest) = load(rest);
                                    let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
                                    match cexpr_tag {
                                        Tag::Err => {
                                            return (cexpr_tag, cexpr)
                                        }
                                    };
                                    let rest_not_cons = sub(rest_tag, cons_tag);
                                    if rest_not_cons {
                                        return (err_tag, invalid_form)
                                    }
                                    let (t_branch_tag, t_branch, rest_tag, rest) = load(rest);
                                    let (ct_branch_tag, ct_branch) = call(compile, t_branch_tag, t_branch);
                                    match ct_branch_tag {
                                        Tag::Err => {
                                            return (ct_branch_tag, ct_branch)
                                        }
                                    };
                                    let tag = Op::If;
                                    match rest_tag {
                                        InternalTag::Nil => {
                                            let nil_tag = InternalTag::Nil;
                                            let nil = digests.lurk_symbol_ptr("nil");
                                            let ptr = store(cexpr_tag, cexpr, ct_branch_tag, ct_branch, nil_tag, nil);
                                            return (tag, ptr)
                                        }
                                        Tag::Cons => {
                                            let (f_branch_tag, f_branch, rest_tag, _rest) = load(rest);
                                            let rest_not_nil = sub(rest_tag, nil_tag);
                                            if rest_not_nil {
                                                return (err_tag, invalid_form)
                                            }
                                            let (cf_branch_tag, cf_branch) = call(compile, f_branch_tag, f_branch);
                                            match cf_branch_tag {
                                                Tag::Err => {
                                                    return (cf_branch_tag, cf_branch)
                                                }
                                            };
                                            let ptr = store(cexpr_tag, cexpr, ct_branch_tag, ct_branch, cf_branch_tag, cf_branch);
                                            return (tag, ptr)
                                        }
                                    };
                                    return (err_tag, invalid_form)
                                }
                                "breakpoint" => {
                                    // TODO
                                    return (err_tag, invalid_form)
                                }
                            }
                        }
                    };
                    let (chead_tag, chead) = call(compile, head_tag, head);
                    match chead_tag {
                        Tag::Err => {
                            return (chead_tag, chead)
                        }
                    };
                    let nil_tag = InternalTag::Nil;
                    let nil = digests.lurk_symbol_ptr("nil");
                    let mkcons = Op::MkCons;
                    let (cargs_tag, cargs) = call(compile_fold_right, mkcons, nil_tag, nil, rest_tag, rest);
                    let op = Op::App;
                    let ptr = store(chead_tag, chead, cargs_tag, cargs);
                    return (op, ptr)
                }
                Tag::Env, Tag::Fix, Tag::Fun, Tag::Builtin => {
                    let (cexpr_tag, cexpr) = call(convert_data, expr_tag, expr);
                    return (cexpr_tag, cexpr)
                }
            };
            return (expr_tag, expr)
        }
    )
}

pub fn symbol_to_op<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn symbol_to_op(builtin): [1] {
            match builtin [|sym| digests.builtin_symbol_ptr(sym).to_field()] {
                // list and lambda do not have a direct representation
                "list" => {
                    let tag = Op::MkCons;
                    return tag
                }
                "lambda" => {
                    let tag = Op::MkFun;
                    return tag
                }
                // but the rest has
                "atom" => {
                    let tag = Op::Atom;
                    return tag
                }
                "apply" => {
                    let tag = Op::Apply;
                    return tag
                }
                "begin" => {
                    let tag = Op::Begin;
                    return tag
                }
                "car" => {
                    let tag = Op::Car;
                    return tag
                }
                "cdr" => {
                    let tag = Op::Cdr;
                    return tag
                }
                "char" => {
                    let tag = Op::Char;
                    return tag
                }
                "commit" => {
                    let tag = Op::Hide;
                    return tag
                }
                "comm" => {
                    let tag = Op::Comm;
                    return tag
                }
                "bignum" => {
                    let tag = Op::Bignum;
                    return tag
                }
                "cons" => {
                    let tag = Op::MkCons;
                    return tag
                }
                "current-env" => {
                    let tag = Op::CurrentEnv;
                    return tag
                }
                "emit" => {
                    let tag = Op::Emit;
                    return tag
                }
                "empty-env" => {
                    let tag = Op::EmptyEnv;
                    return tag
                }
                "eval" => {
                    let tag = Op::Eval;
                    return tag
                }
                "eq" => {
                    let tag = Op::Eq;
                    return tag
                }
                "eqq" => {
                    let tag = Op::Eqq;
                    return tag
                }
                "type-eq" => {
                    let tag = Op::TypeEq;
                    return tag
                }
                "type-eqq" => {
                    let tag = Op::TypeEqq;
                    return tag
                }
                "hide" => {
                    let tag = Op::Hide;
                    return tag
                }
                "if" => {
                    let tag = Op::If;
                    return tag
                }
                "let" => {
                    let tag = Op::Let;
                    return tag
                }
                "letrec" => {
                    let tag = Op::Letrec;
                    return tag
                }
                "u64" => {
                    let tag = Op::U64;
                    return tag
                }
                "open" => {
                    let tag = Op::Open;
                    return tag
                }
                "quote" => {
                    let tag = Op::Quote;
                    return tag
                }
                "secret" => {
                    let tag = Op::Secret;
                    return tag
                }
                "strcons" => {
                    let tag = Op::MkStrcons;
                    return tag
                }
                "+" => {
                    let tag = Op::Add;
                    return tag
                }
                "-" => {
                    let tag = Op::Sub;
                    return tag
                }
                "*" => {
                    let tag = Op::Mul;
                    return tag
                }
                "/" => {
                    let tag = Op::Div;
                    return tag
                }
                "%" => {
                    let tag = Op::Mod;
                    return tag
                }
                "=" => {
                    let tag = Op::NumEq;
                    return tag
                }
                "<" => {
                    let tag = Op::Less;
                    return tag
                }
                ">" => {
                    let tag = Op::Great;
                    return tag
                }
                "<=" => {
                    let tag = Op::LessEq;
                    return tag
                }
                ">=" => {
                    let tag = Op::GreatEq;
                    return tag
                }
                "breakpoint" => {
                    let tag = Op::Breakpoint;
                    return tag
                }
                "fail" => {
                    let tag = Op::Fail;
                    return tag
                }
            }

        }
    )
}

pub fn compile_lambda<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        invertible fn compile_lambda(vars_tag, vars, cbody_tag, cbody): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match vars_tag {
                InternalTag::Nil => {
                    let tag = Op::MkThunk;
                    let ptr = store(cbody_tag, cbody);
                    return (tag, ptr)
                }
                Tag::Cons => {
                    let (var_tag, var, rest_vars_tag, rest_vars) = load(vars);
                    match var_tag {
                        Tag::Sym, Tag::Builtin, Tag::Coroutine => {
                            let rest_sym = digests.lurk_symbol_ptr("&rest");
                            let is_not_rest_sym = sub(var, rest_sym);
                            if is_not_rest_sym {
                                match rest_vars_tag {
                                    InternalTag::Nil => {
                                        let ptr = store(var_tag, var, cbody_tag, cbody);
                                        let tag = Op::MkFun;
                                        return (tag, ptr)
                                    }
                                };
                                let (fbody_tag, fbody) = call(compile_lambda, rest_vars_tag, rest_vars, cbody_tag, cbody);
                                match fbody_tag {
                                    Tag::Err => {
                                        return (fbody_tag, fbody)
                                    }
                                };
                                let ptr = store(var_tag, var, fbody_tag, fbody);
                                let tag = Op::MkFun;
                                return (tag, ptr)
                            }
                            match rest_vars_tag {
                                InternalTag::Nil => {
                                    return (err_tag, invalid_form)
                                }
                                Tag::Cons => {
                                    let (var_tag, var, rest_vars_tag, _rest_vars) = load(rest_vars);
                                    match var_tag {
                                        Tag::Sym, Tag::Builtin, Tag::Coroutine => {
                                            let nil_tag = InternalTag::Nil;
                                            let rest_vars_not_nil = sub(rest_vars_tag, nil_tag);
                                            if rest_vars_not_nil {
                                                return (err_tag, invalid_form)
                                            }
                                            let ptr = store(var_tag, var, cbody_tag, cbody);
                                            let tag = Op::MkRestFun;
                                            return (tag, ptr)
                                        }
                                    };
                                    return (err_tag, invalid_form)
                                }
                            };
                            return (err_tag, invalid_form)
                        }
                    };
                    return (err_tag, invalid_form)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_let<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_let(binds_tag, binds, cbody_tag, cbody): [2] {
            // You can only call this function on let tags

            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match binds_tag {
                InternalTag::Nil => {
                    return (cbody_tag, cbody)
                }
                Tag::Cons => {
                    let cons_tag = Tag::Cons;
                    let nil_tag = InternalTag::Nil;
                    let (bind_tag, bind, rest_binds_tag, rest_binds) = load(binds);
                    let bind_not_cons = sub(bind_tag, cons_tag);
                    if bind_not_cons {
                        return (err_tag, invalid_form)
                    }
                    let (var_tag, var, rest_tag, rest) = load(bind);
                    let rest_not_cons = sub(rest_tag, cons_tag);
                    if rest_not_cons {
                        return (err_tag, invalid_form)
                    }
                    let (val_tag, val, rest_tag, _rest) = load(rest);
                    let rest_not_nil = sub(rest_tag, nil_tag);
                    if rest_not_nil {
                        return (err_tag, invalid_form)
                    }
                    match var_tag {
                        Tag::Sym, Tag::Builtin, Tag::Coroutine => {
                            let (cval_tag, cval) = call(compile, val_tag, val);
                            match cval_tag {
                                Tag::Err => {
                                    return (cval_tag, cval)
                                }
                            };
                            let (lbody_tag, lbody) = call(compile_let, rest_binds_tag, rest_binds, cbody_tag, cbody);
                            match lbody_tag {
                                Tag::Err => {
                                    return (lbody_tag, lbody)
                                }
                            };
                            let ptr = store(var_tag, var, cval_tag, cval, lbody_tag, lbody);
                            let let_op = Op::Let;
                            return (let_op, ptr)
                        }
                    };
                    return (err_tag, invalid_form)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_mutual_binds<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_mutual_binds(binds_tag, binds): [2] {
            let err_tag = Tag::Err;
            let env_tag = Tag::Env;
            let invalid_form_err = EvalErr::InvalidForm;
            match binds_tag {
                InternalTag::Nil => {
                    let cbinds = 0;
                    return (env_tag, cbinds)
                }
                Tag::Cons => {
                    let cons_tag = Tag::Cons;
                    let (binding_tag, binding, binds_tag, binds) = load(binds);
                    let binding_not_cons = sub(binding_tag, cons_tag);
                    if binding_not_cons {
                        return (err_tag, invalid_form_err)
                    }
                    let (var_tag, var, rest_tag, rest) = load(binding);
                    let rest_tag_not_cons = sub(rest_tag, cons_tag);
                    if rest_tag_not_cons {
                        return (err_tag, invalid_form_err)
                    }
                    let (expr_tag, expr, rest_tag, _rest) = load(rest);
                    let nil_tag = InternalTag::Nil;
                    let rest_tag_not_nil = sub(rest_tag, nil_tag);
                    if rest_tag_not_nil {
                        return (err_tag, invalid_form_err)
                    }
                    match var_tag {
                        Tag::Sym, Tag::Builtin, Tag::Coroutine => {
                            let (cexpr_tag, cexpr) = call(compile, expr_tag, expr);
                            match cexpr_tag {
                                Tag::Err => {
                                    return (cexpr_tag, cexpr)
                                }
                            };
                            let (cbinds_tag, cbinds) = call(compile_mutual_binds, binds_tag, binds);
                            match cbinds_tag {
                                Tag::Err => {
                                    return (cbinds_tag, cbinds)
                                }
                            };
                            let cbinds = store(var_tag, var, cexpr_tag, cexpr, cbinds);
                            return (env_tag, cbinds)
                        }
                    };
                    return (err_tag, invalid_form_err)
                }
            };
            return (err_tag, invalid_form_err)
        }
    )
}

pub fn compile_fold_right<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_fold_right(op, init_tag, init, exprs_tag, exprs): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match exprs_tag {
                InternalTag::Nil => {
                    return (init_tag, init)
                }
                Tag::Cons => {
                    let (val_tag, val, rest_tag, rest) = load(exprs);
                    let (cval_tag, cval) = call(compile, val_tag, val);
                    match cval_tag {
                        Tag::Err => {
                            return (cval_tag, cval)
                        }
                    };
                    match rest_tag {
                        InternalTag::Nil => {
                            let ptr = store(cval_tag, cval, init_tag, init);
                            return (op, ptr)
                        }
                    };
                    let (rest_body_tag, rest_body) = call(compile_fold_right, op, init_tag, init, rest_tag, rest);
                    match rest_body_tag {
                        Tag::Err => {
                            return (rest_body_tag, rest_body)
                        }
                    };
                    let ptr = store(cval_tag, cval, rest_body_tag, rest_body);
                    return (op, ptr)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_fold_left<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_fold_left(op, acc_tag, acc, exprs_tag, exprs): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            match exprs_tag {
                InternalTag::Nil => {
                    return (acc_tag, acc)
                }
                Tag::Cons => {
                    let (val_tag, val, rest_tag, rest) = load(exprs);
                    let (cval_tag, cval) = call(compile, val_tag, val);
                    match cval_tag {
                        Tag::Err => {
                            return (cval_tag, cval)
                        }
                    };
                    let new_acc = store(acc_tag, acc, cval_tag, cval);
                    match rest_tag {
                        InternalTag::Nil => {
                            return (op, new_acc)
                        }
                    };
                    let (res_tag, res) = call(compile_fold_left, op, op, new_acc, rest_tag, rest);
                    return (res_tag, res)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_fold_rel<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn compile_fold_rel(op, exprs_tag, exprs): [2] {
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;
            let t_tag = InternalTag::T;
            let t = digests.lurk_symbol_ptr("t");
            match exprs_tag {
                InternalTag::Nil => {
                    return (t_tag, t)
                }
                Tag::Cons => {
                    let (a_tag, a, rest_tag, rest) = load(exprs);
                    let (ca_tag, ca) = call(compile, a_tag, a);
                    match ca_tag {
                        Tag::Err => {
                            return (ca_tag, ca)
                        }
                    };
                    match rest_tag {
                        InternalTag::Nil => {
                            return (t_tag, t)
                        }
                        Tag::Cons => {
                            let (b_tag, b, rest_tag, rest) = load(rest);
                            let (cb_tag, cb) = call(compile, b_tag, b);
                            match cb_tag {
                                Tag::Err => {
                                    return (cb_tag, cb)
                                }
                            };
                            let op_body = store(ca_tag, ca, cb_tag, cb);
                            match rest_tag {
                                InternalTag::Nil => {
                                    return (op, op_body)
                                }
                            };
                            let (rest_body_tag, rest_body) = call(compile_fold_rel, op, rest_tag, rest);
                            match rest_body_tag {
                                Tag::Err => {
                                    return (rest_body_tag, rest_body)
                                }
                            };
                            let ptr = store(op, op_body, rest_body_tag, rest_body);
                            let and = Op::And;
                            return (and, ptr)
                        }
                    };
                    return (err_tag, invalid_form)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

// Converts internal decompiled data (funcs, etc) into compiled counterparts
pub fn convert_data<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn convert_data(expr_tag, expr): [2] {
            match expr_tag {
                Tag::Cons => {
                    let (car_tag, car, cdr_tag, cdr) = load(expr);
                    let (ccar_tag, ccar) = call(convert_data, car_tag, car);
                    match ccar_tag {
                        Tag::Err => {
                            return (ccar_tag, ccar)
                        }
                    };
                    let (ccdr_tag, ccdr) = call(convert_data, cdr_tag, cdr);
                    match ccdr_tag {
                        Tag::Err => {
                            return (ccdr_tag, ccdr)
                        }
                    };
                    let cons_tag = Tag::Cons;
                    let ptr = store(car_tag, car, cdr_tag, cdr);
                    return (cons_tag, ptr)
                }
                Tag::Env => {
                    if !expr {
                        return (expr_tag, expr)
                    }
                    let (var, val_tag, val, env) = load(expr);
                    let (cval_tag, cval) = call(convert_data, val_tag, val);
                    match cval_tag {
                        Tag::Err => {
                            return (cval_tag, cval)
                        }
                    };
                    let env_tag = Tag::Env;
                    let (cenv_tag, cenv) = call(convert_data, env_tag, env);
                    match cenv_tag {
                        Tag::Err => {
                            return (cenv_tag, cenv)
                        }
                    };
                    let ptr = store(var, cval_tag, cval, cenv);
                    return (env_tag, ptr)
                }
                Tag::Fun => {
                    let (vars_tag, vars, body_tag, body, env) = load(expr);
                    let env_tag = Tag::Env;
                    let (cenv_tag, cenv) = call(convert_data, env_tag, env);
                    match cenv_tag {
                        Tag::Err => {
                            return (cenv_tag, cenv)
                        }
                        Tag::Env => {
                            let builtin_tag = Tag::Builtin;
                            let lambda = digests.builtin_symbol_ptr("lambda");
                            let nil_tag = InternalTag::Nil;
                            let nil = digests.lurk_symbol_ptr("nil");
                            let cons_tag = Tag::Cons;
                            let cons1 = store(body_tag, body, nil_tag, nil);
                            let cons2 = store(vars_tag, vars, cons_tag, cons1);
                            let lambda = store(builtin_tag, lambda, cons_tag, cons2);
                            let (mkfun_tag, mkfun) = call(compile, cons_tag, lambda);
                            match mkfun_tag {
                                Tag::Err => {
                                    return (mkfun_tag, mkfun)
                                }
                                Op::MkFun => {
                                    let (var_tag, var, cbody_tag, cbody) = load(mkfun);
                                    let tag = Val::Fun;
                                    let ptr = store(var_tag, var, cbody_tag, cbody, cenv);
                                    return (tag, ptr)
                                }
                                Op::MkThunk => {
                                    let (cbody_tag, cbody) = load(mkfun);
                                    let tag = Val::Thunk;
                                    let ptr = store(cbody_tag, cbody, cenv);
                                    return (tag, ptr)
                                }
                            }
                        }
                    }
                }
                Tag::Fix => {
                    let (body_tag, body, env) = load(expr);
                    let (cbody_tag, cbody) = call(compile, body_tag, body);
                    match cbody_tag {
                        Tag::Err => {
                            return (cbody_tag, cbody)
                        }
                    };
                    let env_tag = Tag::Env;
                    let (cenv_tag, cenv) = call(convert_data, env_tag, env);
                    match cenv_tag {
                        Tag::Err => {
                            return (cenv_tag, cenv)
                        }
                    };
                    let tag = Val::Fix;
                    let ptr = store(cbody_tag, cbody, cenv);
                    return (tag, ptr)
                }
            };
            return (expr_tag, expr)
        }
    )
}

pub fn deconvert_data<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn deconvert_data(cexpr_tag, cexpr): [2] {
            match cexpr_tag {
                Tag::Cons => {
                    let (ccar_tag, ccar, ccdr_tag, ccdr) = load(cexpr);
                    let (car_tag, car) = call(deconvert_data, ccar_tag, ccar);
                    let (cdr_tag, cdr) = call(deconvert_data, ccdr_tag, ccdr);
                    let tag = Tag::Cons;
                    let ptr = store(car_tag, car, cdr_tag, cdr);
                    return (tag, ptr)
                }
                Tag::Env => {
                    if !cexpr {
                        return (cexpr_tag, cexpr)
                    }
                    let (var_tag, var, cval_tag, cval, cenv) = load(cexpr);
                    let (val_tag, val) = call(deconvert_data, cval_tag, cval);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let ptr = store(var_tag, var, val_tag, val, env);
                    return (env_tag, ptr)
                }
                Val::Fun => {
                    let (var_tag, var, cbody_tag, cbody, cenv) = load(cexpr);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let mkfun_tag = Op::MkFun;
                    let mkfun = store(var_tag, var, cbody_tag, cbody);
                    let (vars_tag, vars, cbody_tag, cbody) = preimg(compile_lambda, mkfun_tag, mkfun);
                    let (body_tag, body) = preimg(compile, cbody_tag, cbody);
                    let tag = Tag::Fun;
                    let ptr = store(vars_tag, vars, body_tag, body, env);
                    return (tag, ptr)
                }
                Val::RestFun => {
                    let (var_tag, var, cbody_tag, cbody, cenv) = load(cexpr);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let mkfun_tag = Op::MkRestFun;
                    let mkfun = store(var_tag, var, cbody_tag, cbody);
                    let (vars_tag, vars, cbody_tag, cbody) = preimg(compile_lambda, mkfun_tag, mkfun);
                    let (body_tag, body) = preimg(compile, cbody_tag, cbody);
                    let tag = Tag::Fun;
                    let ptr = store(vars_tag, vars, body_tag, body, env);
                    return (tag, ptr)
                }
                Val::Thunk => {
                    let (cbody_tag, cbody, cenv) = load(cexpr);
                    let (body_tag, body) = preimg(compile, cbody_tag, cbody);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let tag = Tag::Fun;
                    let nil_tag = InternalTag::Nil;
                    let nil = digests.lurk_symbol_ptr("nil");
                    let ptr = store(nil_tag, nil, body_tag, body, env);
                    return (tag, ptr)
                }
                Val::Fix => {
                    let (cbody_tag, cbody, cenv) = load(cexpr);
                    let (body_tag, body) = preimg(compile, cbody_tag, cbody);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let tag = Tag::Fix;
                    let ptr = store(body_tag, body, env);
                    return (tag, ptr)
                }
                InternalTag::T, InternalTag::Nil, Tag::Sym, Tag::Num, Tag::Str,
                Tag::Char, Tag::Comm, Tag::U64, Tag::Key, Tag::Err, Tag::Builtin => {
                    return (cexpr_tag, cexpr)
                }
            }
        }
    )
}

pub fn compile_funcs<F: PrimeField32>(digests: &SymbolsDigests<F>) -> Vec<FuncE<F>> {
    vec![
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
    ]
}

pub fn build_compile_toplevel_native() -> Toplevel<BabyBear, NoChip, NoChip> {
    use super::zstore::lurk_zstore;

    let mut zstore = lurk_zstore();
    let digests = SymbolsDigests::new(&Default::default(), &mut zstore);
    let funcs_exprs = compile_funcs(&digests);
    Toplevel::new_pure(&funcs_exprs)
}

#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};

    use crate::lair::func_chip::FuncChip;

    use super::*;

    #[test]
    fn test_widths() {
        let toplevel = &build_compile_toplevel_native();

        let compile = FuncChip::from_name_main("compile", toplevel);
        let symbol_to_op = FuncChip::from_name_main("symbol_to_op", toplevel);
        let compile_lambda = FuncChip::from_name_main("compile_lambda", toplevel);
        let compile_let = FuncChip::from_name_main("compile_let", toplevel);
        let compile_mutual_binds = FuncChip::from_name_main("compile_mutual_binds", toplevel);
        let compile_fold_right = FuncChip::from_name_main("compile_fold_right", toplevel);
        let compile_fold_left = FuncChip::from_name_main("compile_fold_left", toplevel);
        let compile_fold_rel = FuncChip::from_name_main("compile_fold_rel", toplevel);
        let convert_data = FuncChip::from_name_main("convert_data", toplevel);
        let deconvert_data = FuncChip::from_name_main("deconvert_data", toplevel);

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(compile.width(), expect!["116"]);
        expect_eq(symbol_to_op.width(), expect!["46"]);
        expect_eq(compile_lambda.width(), expect!["42"]);
        expect_eq(compile_let.width(), expect!["57"]);
        expect_eq(compile_mutual_binds.width(), expect!["55"]);
        expect_eq(compile_fold_right.width(), expect!["40"]);
        expect_eq(compile_fold_left.width(), expect!["38"]);
        expect_eq(compile_fold_rel.width(), expect!["58"]);
        expect_eq(convert_data.width(), expect!["63"]);
        expect_eq(deconvert_data.width(), expect!["48"]);
    }
}
