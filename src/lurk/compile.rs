use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_field::{AbstractField, PrimeField32};

use crate::{func, lair::expr::FuncE, lurk::ingress::InternalTag};

use super::{ingress::SymbolsDigests, tag::Tag};

#[derive(Clone, Copy, FromPrimitive, Debug)]
#[repr(u32)]
pub enum CompileErr {
    InvalidForm = 0x00100000,
}

impl CompileErr {
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    pub fn from_field<F: PrimeField32>(f: &F) -> Self {
        Self::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a CompileErr")
    }
}

#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, FromPrimitive)]
pub enum CTag {
    // If statement
    If = 0x00001000,
    // Local (recursive) definition
    Let,
    Letrec,
    // Function and thunks
    CFun,
    MkFun,
    App,
    Apply,
    CThunk,
    MkThunk,
    Force,
    CFix,
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
    Commit,
    Open,
    Secret,
    // Eval
    Eval,
    Quote,
    // Environments
    CurrentEnv,
    EmptyEnv,
    // Conversions
    Num,
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

impl CTag {
    #[inline]
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    #[inline]
    pub fn from_field<F: PrimeField32>(f: &F) -> CTag {
        CTag::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a Tag")
    }
}

pub fn compile<F: AbstractField + Ord>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        invertible fn compile(expr_tag, expr): [2] {
            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
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
                                                    return (nil_tag, o)
                                                }
                                            }
                                        }
                                        Tag::Cons => {
                                            let (init_tag, init, rest_tag, rest) = load(rest);
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
                                    let nil = 0;
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
                                        "let", "letrec" => {
                                            let (res_tag, res) = call(compile_let, op, fst_tag, fst, cbody_tag, cbody);
                                            return (res_tag, res)
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
                                    let tag = CTag::Quote;
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
                                    let tag = CTag::Eval;
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
                                    let not_env = CompileErr::InvalidForm;
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
                                    let tag = CTag::If;
                                    match rest_tag {
                                        InternalTag::Nil => {
                                            let nil_tag = InternalTag::Nil;
                                            let nil = 0;
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
                    match rest_tag {
                        InternalTag::Nil => {
                            let tag = CTag::Force;
                            let ptr = store(chead_tag, chead);
                            return (tag, ptr)
                        }
                    };
                    let (res_tag, res) = call(compile_app, chead_tag, chead, rest_tag, rest);
                    return (res_tag, res)
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
                    let tag = CTag::MkCons;
                    return tag
                }
                "lambda" => {
                    let tag = CTag::MkFun;
                    return tag
                }
                // but the rest has
                "atom" => {
                    let tag = CTag::Atom;
                    return tag
                }
                "apply" => {
                    let tag = CTag::Apply;
                    return tag
                }
                "begin" => {
                    let tag = CTag::Begin;
                    return tag
                }
                "car" => {
                    let tag = CTag::Car;
                    return tag
                }
                "cdr" => {
                    let tag = CTag::Cdr;
                    return tag
                }
                "char" => {
                    let tag = CTag::Char;
                    return tag
                }
                "commit" => {
                    let tag = CTag::Commit;
                    return tag
                }
                "comm" => {
                    let tag = CTag::Comm;
                    return tag
                }
                "bignum" => {
                    let tag = CTag::Bignum;
                    return tag
                }
                "cons" => {
                    let tag = CTag::MkCons;
                    return tag
                }
                "current-env" => {
                    let tag = CTag::CurrentEnv;
                    return tag
                }
                "emit" => {
                    let tag = CTag::Emit;
                    return tag
                }
                "empty-env" => {
                    let tag = CTag::EmptyEnv;
                    return tag
                }
                "eval" => {
                    let tag = CTag::Eval;
                    return tag
                }
                "eq" => {
                    let tag = CTag::Eq;
                    return tag
                }
                "eqq" => {
                    let tag = CTag::Eqq;
                    return tag
                }
                "type-eq" => {
                    let tag = CTag::TypeEq;
                    return tag
                }
                "type-eqq" => {
                    let tag = CTag::TypeEqq;
                    return tag
                }
                "hide" => {
                    let tag = CTag::Hide;
                    return tag
                }
                "if" => {
                    let tag = CTag::If;
                    return tag
                }
                "let" => {
                    let tag = CTag::Let;
                    return tag
                }
                "letrec" => {
                    let tag = CTag::Letrec;
                    return tag
                }
                "u64" => {
                    let tag = CTag::U64;
                    return tag
                }
                "open" => {
                    let tag = CTag::Open;
                    return tag
                }
                "quote" => {
                    let tag = CTag::Quote;
                    return tag
                }
                "secret" => {
                    let tag = CTag::Secret;
                    return tag
                }
                "strcons" => {
                    let tag = CTag::MkStrcons;
                    return tag
                }
                "+" => {
                    let tag = CTag::Add;
                    return tag
                }
                "-" => {
                    let tag = CTag::Sub;
                    return tag
                }
                "*" => {
                    let tag = CTag::Mul;
                    return tag
                }
                "/" => {
                    let tag = CTag::Div;
                    return tag
                }
                "%" => {
                    let tag = CTag::Mod;
                    return tag
                }
                "=" => {
                    let tag = CTag::Eq;
                    return tag
                }
                "<" => {
                    let tag = CTag::Less;
                    return tag
                }
                ">" => {
                    let tag = CTag::Great;
                    return tag
                }
                "<=" => {
                    let tag = CTag::LessEq;
                    return tag
                }
                ">=" => {
                    let tag = CTag::GreatEq;
                    return tag
                }
                "breakpoint" => {
                    let tag = CTag::Breakpoint;
                    return tag
                }
                "fail" => {
                    let tag = CTag::Fail;
                    return tag
                }
            }

        }
    )
}

pub fn compile_app<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_app(chead_tag, chead, args_tag, args): [2] {
            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
            match args_tag {
                InternalTag::Nil => {
                    return (chead_tag, chead)
                }
                Tag::Cons => {
                    let (arg_tag, arg, rest_args_tag, rest_args) = load(args);
                    let (carg_tag, carg) = call(compile, arg_tag, arg);
                    match carg_tag {
                        Tag::Err => {
                            return (carg_tag, carg)
                        }
                    };
                    let new_head_tag = CTag::App;
                    let new_head = store(chead_tag, chead, carg_tag, carg);
                    let (capp_tag, capp) = call(compile_app, new_head_tag, new_head, rest_args_tag, rest_args);
                    return (capp_tag, capp)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_lambda<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        invertible fn compile_lambda(vars_tag, vars, cbody_tag, cbody): [2] {
            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
            match vars_tag {
                InternalTag::Nil => {
                    let tag = CTag::MkThunk;
                    let ptr = store(cbody_tag, cbody);
                    return (tag, ptr)
                }
                Tag::Cons => {
                    let (var_tag, var, rest_vars_tag, rest_vars) = load(vars);
                    let sym_tag = Tag::Sym;
                    let var_not_sym = sub(var_tag, sym_tag);
                    if var_not_sym {
                        return (err_tag, invalid_form)
                    }
                    match rest_vars_tag {
                        InternalTag::Nil => {
                            let ptr = store(var, cbody_tag, cbody);
                            let tag = CTag::MkFun;
                            return (tag, ptr)
                        }
                    };
                    let (fbody_tag, fbody) = call(compile_lambda, rest_vars_tag, rest_vars, cbody_tag, cbody);
                    match fbody_tag {
                        Tag::Err => {
                            return (fbody_tag, fbody)
                        }
                    };
                    let ptr = store(var, fbody_tag, fbody);
                    let tag = CTag::MkFun;
                    return (tag, ptr)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_let<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_let(let_tag, binds_tag, binds, cbody_tag, cbody): [2] {
            // You can only call this function on let tags
            // let let_tag1 = CTag::Let;
            // let let_tag2 = CTag::Letrec;
            // let let_tags: [2] = (let_tag1, let_tag2);
            // contains!(let_tags, let_tag);

            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
            match binds_tag {
                InternalTag::Nil => {
                    return (cbody_tag, cbody)
                }
                Tag::Cons => {
                    let cons_tag = Tag::Cons;
                    let nil_tag = InternalTag::Nil;
                    let sym_tag = Tag::Sym;
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
                    let var_not_sym = sub(var_tag, sym_tag);
                    if var_not_sym {
                        return (err_tag, invalid_form)
                    }
                    let (cval_tag, cval) = call(compile, val_tag, val);
                    match cval_tag {
                        Tag::Err => {
                            return (cval_tag, cval)
                        }
                    };
                    let (lbody_tag, lbody) = call(compile_let, let_tag, rest_binds_tag, rest_binds, cbody_tag, cbody);
                    match lbody_tag {
                        Tag::Err => {
                            return (lbody_tag, lbody)
                        }
                    };
                    let ptr = store(var, cval_tag, cval, lbody_tag, lbody);
                    return (let_tag, ptr)
                }
            };
            return (err_tag, invalid_form)
        }
    )
}

pub fn compile_fold_right<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_fold_right(op, init_tag, init, exprs_tag, exprs): [2] {
            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
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
            let invalid_form = CompileErr::InvalidForm;
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

pub fn compile_fold_rel<F: AbstractField + Ord>() -> FuncE<F> {
    func!(
        fn compile_fold_rel(op, exprs_tag, exprs): [2] {
            let err_tag = Tag::Err;
            let invalid_form = CompileErr::InvalidForm;
            let t_tag = InternalTag::T;
            let t = 0;
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
                            let and = CTag::And;
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
                            let nil = 0;
                            let cons_tag = Tag::Cons;
                            let cons1 = store(body_tag, body, nil_tag, nil);
                            let cons2 = store(vars_tag, vars, cons_tag, cons1);
                            let lambda = store(builtin_tag, lambda, cons_tag, cons2);
                            let (mkfun_tag, mkfun) = call(compile, cons_tag, lambda);
                            match mkfun_tag {
                                Tag::Err => {
                                    return (mkfun_tag, mkfun)
                                }
                                CTag::MkFun => {
                                    let (var, cbody_tag, cbody) = load(mkfun);
                                    let tag = CTag::CFun;
                                    let ptr = store(var, cbody_tag, cbody, cenv);
                                    return (tag, ptr)
                                }
                                CTag::MkThunk => {
                                    let (cbody_tag, cbody) = load(mkfun);
                                    let tag = CTag::CThunk;
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
                    let tag = CTag::CFix;
                    let ptr = store(cbody_tag, cbody, cenv);
                    return (tag, ptr)
                }
            };
            return (expr_tag, expr)
        }
    )
}

pub fn deconvert_data<F: AbstractField + Ord>() -> FuncE<F> {
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
                    let (var, cval_tag, cval, cenv) = load(cexpr);
                    let (val_tag, val) = call(deconvert_data, cval_tag, cval);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let ptr = store(var, val_tag, val, env);
                    return (env_tag, ptr)
                }
                CTag::CFun => {
                    let (var, cbody_tag, cbody, cenv) = load(cexpr);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let mkfun_tag = CTag::MkFun;
                    let mkfun = store(var, cbody_tag, cbody);
                    let (_cons_tag, lambda) = preimg(compile, mkfun_tag, mkfun);
                    let (_head_tag, _head, _cons_tag, cons1) = load(lambda);
                    let (vars_tag, vars, _cons_tag, cons2) = load(cons1);
                    let (body_tag, body, _nil_tag, _nil) = load(cons2);
                    let tag = Tag::Fun;
                    let ptr = store(vars_tag, vars, body_tag, body, env);
                    return (tag, ptr)
                }
                CTag::CThunk => {
                    let (cbody_tag, cbody, cenv) = load(cexpr);
                    let (body_tag, body) = preimg(compile, cbody_tag, cbody);
                    let env_tag = Tag::Env;
                    let (_env_tag, env) = call(deconvert_data, env_tag, cenv);
                    let tag = Tag::Fun;
                    let nil_tag = InternalTag::Nil;
                    let nil = 0;
                    let ptr = store(nil_tag, nil, body_tag, body, env);
                    return (tag, ptr)
                }
                CTag::CFix => {
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
