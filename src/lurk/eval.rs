use indexmap::{map::Iter, IndexMap};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field, PrimeField32};
use rustc_hash::FxBuildHasher;

use crate::{
    func,
    lair::{
        expr::{BlockE, CasesE, CtrlE, FuncE, OpE, Var, VarList},
        toplevel::Toplevel,
        List, Name,
    },
};

use super::{
    chipset::{lurk_chip_map, LurkChip},
    state::{State, StateRcCell, LURK_PACKAGE_SYMBOLS_NAMES},
    tag::Tag,
    zstore::{lurk_zstore, ZStore},
};

pub struct BuiltinIndex(usize);

impl BuiltinIndex {
    fn to_field<F: Field>(&self) -> F {
        F::from_canonical_usize(self.0)
    }
}

pub struct BuiltinMemo<'a, F>(IndexMap<&'a str, List<F>, FxBuildHasher>);

impl<'a> BuiltinMemo<'a, BabyBear> {
    fn new(state: &StateRcCell, zstore: &mut ZStore<BabyBear, LurkChip>) -> Self {
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
    fn len(&self) -> usize {
        self.0.len()
    }

    fn index(&self, builtin: &'a str) -> BuiltinIndex {
        BuiltinIndex(self.0.get_index_of(builtin).expect("Unknown builtin") + 1)
    }

    fn iter(&self) -> Iter<'_, &str, Box<[F]>> {
        self.0.iter()
    }
}

/// Creates a `Toplevel` with the functions used for Lurk evaluation, also returning
/// a `ZStore` with the Lurk builtins already interned.
#[inline]
pub fn build_lurk_toplevel() -> (Toplevel<BabyBear, LurkChip>, ZStore<BabyBear, LurkChip>) {
    let state = State::init_lurk_state().rccell();
    let mut zstore = lurk_zstore();
    let builtins = BuiltinMemo::new(&state, &mut zstore);
    let nil = zstore.read_with_state(state, "nil").unwrap().digest.into();
    let funcs = &[
        lurk_main(),
        eval(&builtins),
        eval_opening_unop(&builtins),
        eval_hide(),
        eval_unop(&builtins),
        eval_binop_num(&builtins),
        eval_binop_misc(&builtins),
        eval_begin(),
        eval_list(),
        open_comm(),
        equal(&builtins),
        equal_inner(),
        car_cdr(),
        eval_let(),
        eval_letrec(),
        apply(),
        env_lookup(),
        ingress(),
        ingress_sym(&builtins),
        populate_builtin(&builtins),
        egress(nil),
        hash_24_8(),
        hash_32_8(),
        hash_48_8(),
        u64_add(),
        u64_sub(),
        u64_mul(),
        u64_divrem(),
        u64_lessthan(),
        u64_iszero(),
        digest_equal(),
        big_num_lessthan(),
    ];
    let lurk_chip_map = lurk_chip_map();
    let toplevel = Toplevel::new(funcs, lurk_chip_map);
    (toplevel, zstore)
}

#[derive(Clone, Copy, FromPrimitive, Debug)]
#[repr(u32)]
pub enum EvalErr {
    UnboundVar = 0,
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
    NotString,
    NonConstantBuiltin,
    NotU64,
    NotBigNum,
    CantOpen,
    CantCastToChar,
    CantCastToU64,
    CantCastToBigNum,
    CantCastToComm,
}

impl EvalErr {
    pub(crate) fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_u32(self as u32)
    }

    pub(crate) fn from_field<F: PrimeField32>(f: &F) -> Self {
        Self::from_u32(f.as_canonical_u32()).expect("Field element doesn't map to a EvalErr")
    }
}

pub fn lurk_main<F: Field>() -> FuncE<F> {
    func!(
        partial fn lurk_main(full_expr_tag: [8], expr_digest: [8], env_digest: [8]): [16] {
            // Populate builtins
            let () = call(populate_builtin,);
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

pub fn ingress<F: Field + Ord>() -> FuncE<F> {
    func!(
        fn ingress(tag_full: [8], digest: [8]): [1] {
            let zeros = [0; 7];
            let (tag, rest: [7]) = tag_full;
            assert_eq!(rest, zeros);
            match tag {
                Tag::Num => {
                    let (x, rest: [7]) = digest;
                    assert_eq!(rest, zeros);
                    return x
                }
                Tag::Nil => {
                    let zero = 0;
                    return zero
                }
                Tag::Char => {
                    let (bytes: [4], rest: [4]) = digest;
                    range_u8!(bytes);
                    let zeros = [0; 4];
                    assert_eq!(rest, zeros);
                    let ptr = store(bytes);
                    return ptr
                }
                Tag::U64 => {
                    range_u8!(digest);
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Key, Tag::BigNum, Tag::Comm => {
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Sym => {
                    let ptr = call(ingress_sym, digest);
                    return ptr
                }
                Tag::Str => {
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
                Tag::Cons => {
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash_32_8, digest);
                    let fst_ptr = call(ingress, fst_tag_full, fst_digest);
                    let snd_ptr = call(ingress, snd_tag_full, snd_digest);
                    let (fst_tag, _rest: [7]) = fst_tag_full;
                    let (snd_tag, _rest: [7]) = snd_tag_full;
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return ptr
                }
                Tag::Thunk => {
                    let (fst_tag, padding: [7], fst_digest: [8], snd_digest: [8]) = preimg(hash_24_8, digest);
                    assert_eq!(padding, zeros);
                    let env_tag = Tag::Env;
                    let fst_ptr = call(ingress, fst_tag, padding, fst_digest);
                    let snd_ptr = call(ingress, env_tag, padding, snd_digest);
                    let ptr = store(fst_tag, fst_ptr, snd_ptr);
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
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr, trd_ptr);
                    return ptr
                }
                Tag::Env => {
                    if !digest {
                        let zero = 0;
                        return zero
                    }
                    let (sym_digest: [8],
                         val_tag, padding: [7],
                         val_digest: [8],
                         env_digest: [8]) = preimg(hash_32_8, digest);
                    assert_eq!(padding, zeros);
                    let sym_tag = Tag::Sym;
                    let env_tag = Tag::Env;
                    let sym_ptr = call(ingress, sym_tag, padding, sym_digest);
                    let val_ptr = call(ingress, val_tag, padding, val_digest);
                    let env_ptr = call(ingress, env_tag, padding, env_digest);
                    let ptr = store(sym_ptr, val_tag, val_ptr, env_ptr);
                    return ptr
                }
            }
        }
    )
}

fn populate_builtin<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    let mut ops = Vec::with_capacity(builtins.len());
    let digest_var = Var {
        name: "digest",
        size: 8,
    };
    let idx_var = Var {
        name: "idx",
        size: 1,
    };
    let ptr_var = Var {
        name: "ptr",
        size: 1,
    };
    for (i, (_, digest)) in builtins.iter().enumerate() {
        ops.push(OpE::Const(idx_var, F::from_canonical_usize(i + 1)));
        ops.push(OpE::Array(digest_var, digest.clone()));
        ops.push(OpE::Store(ptr_var, VarList([digest_var].into())));
        ops.push(OpE::AssertEq(ptr_var, idx_var));
    }
    let ops = ops.into();
    let ctrl = CtrlE::<F>::Return([].into());

    FuncE {
        name: Name("populate_builtin"),
        invertible: false,
        partial: false,
        input_params: [].into(),
        output_size: 0,
        body: BlockE { ops, ctrl },
    }
}

fn ingress_sym<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    let input_var = Var {
        name: "digest",
        size: 8,
    };
    let idx_var = Var {
        name: "idx",
        size: 1,
    };
    let ret_var = Var {
        name: "res",
        size: 1,
    };
    let branch = |i: usize| BlockE {
        ops: [
            OpE::Const(idx_var, F::from_canonical_usize(i + 1)),
        ]
        .into(),
        ctrl: CtrlE::<F>::Return([idx_var].into()),
    };
    let branches = builtins
        .iter()
        .enumerate()
        .map(|(i, (_, digest))| (digest.clone(), branch(i)))
        .collect();
    let def_branch = BlockE {
        ops: [OpE::Store(ret_var, VarList([input_var].into()))].into(),
        ctrl: CtrlE::<F>::Return([ret_var].into()),
    };
    let cases = CasesE {
        branches,
        default: Some(def_branch.into()),
    };
    let ops = [].into();
    let ctrl = CtrlE::<F>::MatchMany(input_var, cases);

    FuncE {
        name: Name("ingress_sym"),
        invertible: false,
        partial: false,
        input_params: [input_var].into(),
        output_size: 1,
        body: BlockE { ops, ctrl },
    }
}

pub fn egress<F: Field + Ord>(nil: List<F>) -> FuncE<F> {
    func!(
        fn egress(tag, val): [8] {
            match tag {
                Tag::Num, Tag::Err => {
                    let padding = [0; 7];
                    let digest: [8] = (val, padding);
                    return digest
                }
                Tag::Nil => {
                    let digest = Array(nil);
                    return digest
                }
                Tag::Char => {
                    let padding = [0; 4];
                    let bytes: [4] = load(val);
                    return (bytes, padding)
                }
                Tag::Sym, Tag::Key, Tag::U64, Tag::BigNum, Tag::Comm => {
                    let digest: [8] = load(val);
                    return digest
                }
                Tag::Str => {
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
                Tag::Thunk => {
                    let (fst_tag, fst_ptr, snd_ptr) = load(val);
                    let snd_tag = Tag::Env;
                    let fst_digest: [8] = call(egress, fst_tag, fst_ptr);
                    let snd_digest: [8] = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let digest: [8] = call(hash_24_8, fst_tag_full, fst_digest, snd_digest);
                    return digest
                }
                Tag::Fun => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr, trd_ptr) = load(val);
                    let trd_tag = Tag::Env;
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
                    let (sym_ptr, val_tag, val_ptr, env_ptr) = load(val);
                    let sym_tag = Tag::Sym;
                    let env_tag = Tag::Env;
                    let sym_digest: [8] = call(egress, sym_tag, sym_ptr);
                    let val_digest: [8] = call(egress, val_tag, val_ptr);
                    let env_digest: [8] = call(egress, env_tag, env_ptr);

                    let padding = [0; 7];
                    let val_tag_full: [8] = (val_tag, padding);
                    let digest: [8] = call(hash_32_8, sym_digest, val_tag_full, val_digest, env_digest);
                    return digest
                }
            }
        }
    )
}

pub fn hash_24_8<F>() -> FuncE<F> {
    func!(
        invertible fn hash_24_8(preimg: [24]): [8] {
            let img: [8] = extern_call(hash_24_8, preimg);
            return img
        }
    )
}

pub fn hash_32_8<F>() -> FuncE<F> {
    func!(
        invertible fn hash_32_8(preimg: [32]): [8] {
            let img: [8] = extern_call(hash_32_8, preimg);
            return img
        }
    )
}

pub fn hash_48_8<F>() -> FuncE<F> {
    func!(
        invertible fn hash_48_8(preimg: [48]): [8] {
            let img: [8] = extern_call(hash_48_8, preimg);
            return img
        }
    )
}

pub fn u64_add<F>() -> FuncE<F> {
    func!(
        fn u64_add(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_add, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_sub<F>() -> FuncE<F> {
    func!(
        fn u64_sub(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_sub, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_mul<F>() -> FuncE<F> {
    func!(
        fn u64_mul(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_mul, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_divrem<F>() -> FuncE<F> {
    func!(
        fn u64_divrem(a, b): [2] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (q: [8], r: [8]) = extern_call(u64_divrem, a, b);
            let q = store(q);
            let r = store(r);
            return (q, r)
        }
    )
}

pub fn u64_lessthan<F>() -> FuncE<F> {
    func!(
        fn u64_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c = extern_call(u64_lessthan, a, b);
            return c
        }
    )
}

pub fn u64_iszero<F>() -> FuncE<F> {
    func!(
        fn u64_iszero(a): [1] {
            let a: [8] = load(a);
            // this is slightly cheaper than doing it in Lair itself
            let b = extern_call(u64_iszero, a);
            return b
        }
    )
}

pub fn digest_equal<F: Field>() -> FuncE<F> {
    func!(
        fn digest_equal(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let diff = sub(a, b);
            if diff {
                let zero = 0;
                return zero
            }
            let one = 1;
            return one
        }
    )
}

pub fn big_num_lessthan<F>() -> FuncE<F> {
    func!(
        fn big_num_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c = extern_call(big_num_lessthan, a, b);
            return c
        }
    )
}

pub fn eval<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn eval(expr_tag, expr, env): [2] {
            // Constants, tags, etc
            let t = builtins.index("t");
            let nil_tag = Tag::Nil;
            let cons_tag = Tag::Cons;
            let err_tag = Tag::Err;
            let invalid_form = EvalErr::InvalidForm;

            match expr_tag {
                Tag::Sym => {
                    let not_t = sub(expr, t);
                    if !not_t {
                        return (expr_tag, expr)
                    }
                    let expr_digest: [8] = load(expr);
                    let (res_tag, res) = call(env_lookup, expr_digest, env);
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
                            match head [|sym| builtins.index(sym).to_field()] {
                                "let", "letrec", "lambda", "cons", "strcons", "type-eq", "type-eqq" => {
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
                                    match head [|sym| builtins.index(sym).to_field()] {
                                        "let" => {
                                            // first element: let symbol
                                            // second element: binding list
                                            // third element: body
                                            let (res_tag, res) = call(eval_let, fst_tag, fst, snd_tag, snd, env);
                                            return (res_tag, res)
                                        }
                                        "letrec" => {
                                            // analogous to `let`
                                            let (res_tag, res) = call(eval_letrec, fst_tag, fst, snd_tag, snd, env);
                                            return (res_tag, res)
                                        }
                                        "lambda" => {
                                            // first element: lambda symbol
                                            // second element: parameter list
                                            // third element: body
                                            // A function (more precisely, a closure) is an object with a
                                            // parameter list, a body and an environment
                                            let res_tag = Tag::Fun;
                                            let res = store(fst_tag, fst, snd_tag, snd, env);
                                            return (res_tag, res)
                                        }
                                        "cons", "strcons" => {
                                            let (res_tag, res) = call(eval_binop_misc, head, fst_tag, fst, snd_tag, snd, env);
                                            return (res_tag, res)
                                        }
                                        "type-eq" => {
                                            let (fst_tag, fst) = call(eval, fst_tag, fst, env);
                                            match fst_tag {
                                                Tag::Err => {
                                                    return (fst_tag, fst)
                                                }
                                            };
                                            let (snd_tag, snd) = call(eval, snd_tag, snd, env);
                                            match snd_tag {
                                                Tag::Err => {
                                                    return (snd_tag, snd)
                                                }
                                            };
                                            let type_not_eq = sub(fst_tag, snd_tag);
                                            if type_not_eq {
                                                let nil = 0;
                                                return (nil_tag, nil)
                                            }
                                            return (head_tag, t) // head_tag is Tag::Sym
                                        }
                                        "type-eqq" => {
                                            let (snd_tag, snd) = call(eval, snd_tag, snd, env);
                                            match snd_tag {
                                                Tag::Err => {
                                                    return (snd_tag, snd)
                                                }
                                            };
                                            let type_not_eqq = sub(fst_tag, snd_tag);
                                            if type_not_eqq {
                                                let nil = 0;
                                                return (nil_tag, nil)
                                            }
                                            return (head_tag, t) // head_tag is Tag::Sym
                                        }
                                    }
                                }
                                "list" => {
                                    let (expr_tag, expr) = call(eval_list, rest_tag, rest, env);
                                    return (expr_tag, expr)
                                }
                                "+", "-", "*", "/", "%", "=", "<", ">", "<=", ">=" => {
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
                                    let (res_tag, res) = call(eval_binop_num, head, fst_tag, fst, snd_tag, snd, env);
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
                                            // Eval must be called twice, first with the original env and then
                                            // with an empty env
                                            let (res_tag, res) = call(eval, expr_tag, expr, env);
                                            match res_tag {
                                                Tag::Err => {
                                                    return (res_tag, res)
                                                }
                                            };
                                            let env = 0;
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
                                            match res_tag {
                                                Tag::Err => {
                                                    return (res_tag, res)
                                                }
                                            };
                                            let (env_tag, new_env) = call(eval, env_expr_tag, env_expr, env);
                                            match env_tag {
                                                Tag::Err => {
                                                    return (env_tag, new_env)
                                                }
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
                                    let (expr_tag, expr) = call(eval_begin, rest_tag, rest, env);
                                    return (expr_tag, expr)
                                }
                                "current-env", "empty-env" => {
                                    let rest_not_nil = sub(rest_tag, nil_tag);
                                    if rest_not_nil {
                                        return (err_tag, invalid_form)
                                    }
                                    let env_tag = Tag::Env;
                                    match head [|sym| builtins.index(sym).to_field()] {
                                        "current-env" => {
                                            return (env_tag, env)
                                        }
                                        "empty-env" => {
                                            let env = 0;
                                            return (env_tag, env)
                                        }
                                    }
                                }
                                "breakpoint" => {
                                    breakpoint;
                                    match rest_tag {
                                        Tag::Nil => {
                                            let nil = 0;
                                            return (nil_tag, nil)
                                        }
                                        Tag::Cons => {
                                            let (expr_tag, expr, rest_tag, _rest) = load(rest);
                                            let rest_not_nil = sub(rest_tag, nil_tag);
                                            if rest_not_nil {
                                                return (err_tag, invalid_form)
                                            }
                                            let (val_tag, val) = call(eval, expr_tag, expr, env);
                                            return (val_tag, val)
                                        }
                                    }
                                }
                                "if" => {
                                    // An if expression is a list of 3 or 4 elements
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
                                    match rest_tag {
                                        Tag::Nil => {
                                            let (val_tag, val) = call(eval, expr_tag, expr, env);
                                            match val_tag {
                                                Tag::Nil, Tag::Err => {
                                                    return (val_tag, val)
                                                }
                                            };
                                            let (res_tag, res) = call(eval, t_branch_tag, t_branch, env);
                                            return (res_tag, res)
                                        }
                                        Tag::Cons => {
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
                                    };
                                    return (err_tag, invalid_form)
                                }
                                "eq" => {
                                    let res: [2] = call(equal, rest_tag, rest, env);
                                    return res
                                }
                                "hide" => {
                                    let (res_tag, res) = call(eval_hide, rest_tag, rest, env);
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
                                "u64", "char", "atom", "emit", "bignum", "comm" => {
                                    let (res_tag, res) = call(eval_unop, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                "commit", "open", "secret" => {
                                    let (res_tag, res) = call(eval_opening_unop, head, rest_tag, rest, env);
                                    return (res_tag, res)
                                }
                                // TODO: other builtins
                            }
                        }
                    };
                    let (head_tag, head) = call(eval, head_tag, head, env);
                    match head_tag {
                        Tag::BigNum, Tag::Comm => {
                            let (head_tag, head) = call(open_comm, head);
                            let (res_tag, res) = call(apply, head_tag, head, rest_tag, rest, env);
                            return (res_tag, res)
                        }
                        Tag::Err => {
                            return (head_tag, head)
                        }
                    };
                    let (res_tag, res) = call(apply, head_tag, head, rest_tag, rest, env);
                    return (res_tag, res)
                }
            };
            return (expr_tag, expr)
        }
    )
}

pub fn open_comm<F: Field + Ord>() -> FuncE<F> {
    func!(
        fn open_comm(hash_ptr): [2] {
            let comm_hash: [8] = load(hash_ptr);
            let (_secret: [8], payload_tag, padding: [7], val_digest: [8]) = preimg(hash_24_8, comm_hash);
            let payload_ptr = call(ingress, payload_tag, padding, val_digest);
            return (payload_tag, payload_ptr)
        }
    )
}

pub fn car_cdr<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn car_cdr(rest_tag, rest, env): [4] {
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

pub fn equal<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn equal(rest_tag, rest, env): [2] {
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
            let is_equal_inner = call(equal_inner, val1_tag, val1, val2_tag, val2);
            if is_equal_inner {
                let sym_tag = Tag::Sym;
                let t = builtins.index("t");
                return (sym_tag, t)
            }
            return (nil_tag, is_equal_inner) // `is_equal_inner` is zero
        }
    )
}

pub fn equal_inner<F: Field + Ord>() -> FuncE<F> {
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
                Tag::Key, Tag::Sym, Tag::U64, Tag::BigNum, Tag::Comm => {
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
                Tag::Thunk => {
                    let snd_tag = Tag::Env;
                    let (a_fst: [2], a_snd) = load(a);
                    let (b_fst: [2], b_snd) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, snd_tag, a_snd, snd_tag, b_snd);
                    let eq = mul(fst_eq, snd_eq);
                    return eq
                }
                Tag::Fun => {
                    let trd_tag = Tag::Env;
                    let (a_fst: [2], a_snd: [2], a_trd) = load(a);
                    let (b_fst: [2], b_snd: [2], b_trd) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, a_snd, b_snd);
                    let trd_eq = call(equal_inner, trd_tag, a_trd, trd_tag, b_trd);
                    let eq = mul(fst_eq, snd_eq);
                    let eq = mul(eq, trd_eq);
                    return eq
                }
                Tag::Env => {
                    let a_and_b = mul(a, b);
                    if !a_and_b {
                        return zero
                    }
                    let (a_fst: [2], a_snd: [2], a_trd: [2]) = load(a);
                    let (b_fst: [2], b_snd: [2], b_trd: [2]) = load(b);
                    let fst_eq = call(equal_inner, a_fst, b_fst);
                    let snd_eq = call(equal_inner, a_snd, b_snd);
                    let trd_eq = call(equal_inner, a_trd, b_trd);
                    let eq = mul(fst_eq, snd_eq);
                    let eq = mul(eq, trd_eq);
                    return eq
                }
            }
        }
    )
}

pub fn eval_list<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn eval_list(rest_tag, rest, env): [2] {
            match rest_tag {
                Tag::Nil => {
                    return (rest_tag, rest)
                }
                Tag::Cons => {
                    let (head_tag, head, rest_tag, rest) = load(rest);
                    let (head_tag, head) = call(eval, head_tag, head, env);
                    match head_tag {
                        Tag::Err => {
                            return (head_tag, head)
                        }
                    };
                    let (rest_tag, rest) = call(eval_list, rest_tag, rest, env);
                    match rest_tag {
                        Tag::Err => {
                            return (rest_tag, rest)
                        }
                    };
                    let cons_tag = Tag::Cons;
                    let cons = store(head_tag, head, rest_tag, rest);
                    return (cons_tag, cons)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::InvalidForm;
            return (err_tag, err)
        }
    )
}

pub fn eval_begin<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn eval_begin(rest_tag, rest, env): [2] {
            match rest_tag {
                Tag::Nil => {
                    return (rest_tag, rest)
                }
                Tag::Cons => {
                    let (head_tag, head, rest_tag, rest) = load(rest);
                    let (head_tag, head) = call(eval, head_tag, head, env);
                    match head_tag {
                        Tag::Err => {
                            return (head_tag, head)
                        }
                    };
                    match rest_tag {
                        Tag::Nil => {
                            return (head_tag, head)
                        }
                    };
                    let (res_tag, res) = call(eval_begin, rest_tag, rest, env);
                    return (res_tag, res)
                }
            };
            let err_tag = Tag::Err;
            let err = EvalErr::InvalidForm;
            return (err_tag, err)
        }
    )
}

pub fn eval_binop_num<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn eval_binop_num(head, exp1_tag, exp1, exp2_tag, exp2, env): [2] {
            let err_tag = Tag::Err;
            let num_tag = Tag::Num;
            let u64_tag = Tag::U64;
            let nil_tag = Tag::Nil;
            let err_div_zero = EvalErr::DivByZero;
            let sym_tag = Tag::Sym;
            let t = builtins.index("t");
            let nil = 0;
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
                    match head [|sym| builtins.index(sym).to_field()] {
                        "+" => {
                            let res = call(u64_add, val1, val2);
                            return (u64_tag, res)
                        }
                        "-" => {
                            let res = call(u64_sub, val1, val2);
                            return (u64_tag, res)
                        }
                        "*" => {
                            let res = call(u64_mul, val1, val2);
                            return (u64_tag, res)
                        }
                        "/", "%" => {
                            let is_zero = call(u64_iszero, val2);
                            if is_zero {
                                return (err_tag, err_div_zero)
                            }
                            let (quot, rem) = call(u64_divrem, val1, val2);
                            match head [|sym| builtins.index(sym).to_field()] {
                                "/" => {
                                    return (u64_tag, quot)
                                }
                                "%" => {
                                    return (u64_tag, rem)
                                }
                            }
                        }
                        "<" => {
                            let res = call(u64_lessthan, val1, val2);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                        ">=" => {
                            let res = call(u64_lessthan, val1, val2);
                            if res {
                                return (nil_tag, nil)
                            }
                            return (sym_tag, t)

                        }
                        ">" => {
                            let res = call(u64_lessthan, val2, val1);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                        "<=" => {
                            let res = call(u64_lessthan, val2, val1);
                            if res {
                                return (nil_tag, nil)
                            }
                            return (sym_tag, t)
                        }
                        "=" => {
                            let res = call(digest_equal, val1, val2);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                    }
                }
                [Tag::Num, Tag::Num] => {
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
                            if !val2 {
                                return (err_tag, err_div_zero)
                            }
                            let res = div(val1, val2);
                            return (num_tag, res)
                        }
                        "=" => {
                            let diff = sub(val1, val2);
                            if diff {
                                return (nil_tag, nil)
                            }
                            return (sym_tag, t)
                        }
                        "%", "<", ">", "<=", ">=" => {
                            let err = EvalErr::NotU64;
                            return (err_tag, err)
                        }
                    }
                }
                [Tag::BigNum, Tag::BigNum] => {
                    match head [|sym| builtins.index(sym).to_field()] {
                        "<" => {
                            let res = call(big_num_lessthan, val1, val2);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                        ">=" => {
                            let res = call(big_num_lessthan, val1, val2);
                            if res {
                                return (nil_tag, nil)
                            }
                            return (sym_tag, t)

                        }
                        ">" => {
                            let res = call(big_num_lessthan, val2, val1);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                        "<=" => {
                            let res = call(big_num_lessthan, val2, val1);
                            if res {
                                return (nil_tag, nil)
                            }
                            return (sym_tag, t)
                        }
                        "=" => {
                            let res = call(digest_equal, val2, val1);
                            if res {
                                return (sym_tag, t)
                            }
                            return (nil_tag, nil)
                        }
                        "+", "-", "*", "/", "%" => {
                            let err = EvalErr::ArgNotNumber;
                            return (err_tag, err)
                        }
                    }
                }
            };
            let err = EvalErr::ArgNotNumber;
            return (err_tag, err)
        }
    )
}

pub fn eval_binop_misc<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn eval_binop_misc(head, exp1_tag, exp1, exp2_tag, exp2, env): [2] {
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
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
            }
        }
    )
}

pub fn eval_unop<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn eval_unop(head, rest_tag, rest, env): [2] {
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
            let nil_tag = Tag::Nil;
            let invalid_form = EvalErr::InvalidForm;
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
                "atom" => {
                    let val_not_cons = sub(val_tag, cons_tag);
                    if val_not_cons {
                        let sym_tag = Tag::Sym;
                        let t = builtins.index("t");
                        return (sym_tag, t)
                    }
                    let nil = 0;
                    return (nil_tag, nil)
                }
                "emit" => {
                    emit(val_tag, val);
                    return (val_tag, val)
                }
                "u64" => {
                    match val_tag {
                        Tag::U64 => {
                            return (val_tag, val)
                        }
                        Tag::Char => {
                            let bytes: [4] = load(val);
                            let padding = [0; 4];
                            let val = store(bytes, padding);
                            let val_tag = Tag::U64;
                            return (val_tag, val)
                        }
                    };
                    let err = EvalErr::CantCastToU64;
                    return(err_tag, err)
                }
                "char" => {
                    match val_tag {
                        Tag::Char => {
                            return (val_tag, val)
                        }
                        Tag::U64 => {
                            let (bytes: [4], _ignored: [4]) = load(val);
                            let val = store(bytes);
                            let val_tag = Tag::Char;
                            return (val_tag, val)
                        }
                    };
                    let err = EvalErr::CantCastToChar;
                    return(err_tag, err)
                }
                "bignum" => {
                    match val_tag {
                        Tag::BigNum => {
                            return (val_tag, val)
                        }
                        Tag::Comm => {
                            let big_num_tag = Tag::BigNum;
                            return (big_num_tag, val)
                        }
                    };
                    let err = EvalErr::CantCastToBigNum;
                    return(err_tag, err)
                }
                "comm" => {
                    match val_tag {
                        Tag::BigNum => {
                            let comm_tag = Tag::Comm;
                            return (comm_tag, val)
                        }
                        Tag::Comm => {
                            return (val_tag, val)
                        }
                    };
                    let err = EvalErr::CantCastToComm;
                    return(err_tag, err)
                }
             }
        }
    )
}

pub fn eval_opening_unop<F: Field + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
    func!(
        partial fn eval_opening_unop(head, rest_tag, rest, env): [2] {
            let err_tag = Tag::Err;
            let cons_tag = Tag::Cons;
            let nil_tag = Tag::Nil;
            let invalid_form = EvalErr::InvalidForm;
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
                    let val_digest: [8] = call(egress, val_tag, val);
                    let padding = [0; 7];
                    let zero = 0;
                    let comm_hash: [8] = call(hash_24_8, zero, padding, val_tag, padding, val_digest);
                    let comm_tag = Tag::Comm;
                    let comm_ptr = store(comm_hash);
                    return (comm_tag, comm_ptr)
                }
                "open" => {
                    match val_tag {
                        Tag::Comm, Tag::BigNum => {
                            let comm_hash: [8] = load(val);
                            let (_secret: [8], tag, padding: [7], val_digest: [8]) = preimg(hash_24_8, comm_hash);
                            let ptr = call(ingress, tag, padding, val_digest);
                            return (tag, ptr)
                        }
                    };
                    let cant_open = EvalErr::CantOpen;
                    return (err_tag, cant_open)
                }
                "secret" => {
                    match val_tag {
                        Tag::Comm, Tag::BigNum => {
                            let comm_hash: [8] = load(val);
                            let (secret: [8], _payload: [16]) = preimg(hash_24_8, comm_hash);
                            let ptr = store(secret);
                            let big_num_tag = Tag::BigNum;
                            return (big_num_tag, ptr)
                        }
                    };
                    let cant_open = EvalErr::CantOpen;
                    return (err_tag, cant_open)
                }
             }
        }
    )
}

pub fn eval_hide<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn eval_hide(rest_tag, rest, env): [2] {
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
            match val1_tag {
                Tag::BigNum => {
                    let secret: [8] = load(val1);
                    let val2_digest: [8] = call(egress, val2_tag, val2);
                    let padding = [0; 7];
                    let comm_hash: [8] = call(hash_24_8, secret, val2_tag, padding, val2_digest);
                    let comm_ptr = store(comm_hash);
                    let comm_tag = Tag::Comm;
                    return (comm_tag, comm_ptr)
                }
            };
            let not_comm = EvalErr::NotBigNum;
            return (err_tag, not_comm)
        }
    )
}

pub fn eval_let<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn eval_let(binds_tag, binds, body_tag, body, env): [2] {
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
                    match val_tag {
                        Tag::Err => {
                            return (val_tag, val)
                        }
                    };
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

pub fn eval_letrec<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn eval_letrec(binds_tag, binds, body_tag, body, env): [2] {
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
                    let (val_tag, val) = call(eval, expr_tag, expr, ext_env);
                    match val_tag {
                        Tag::Err => {
                            return (val_tag, val)
                        }
                    };
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

pub fn apply<F: Field + Ord>() -> FuncE<F> {
    func!(
        partial fn apply(head_tag, head, args_tag, args, args_env): [2] {
            // Constants, tags, etc
            let err_tag = Tag::Err;
            let fun_tag = Tag::Fun;
            // Expression must be a function
            let head_not_fun = sub(head_tag, fun_tag);
            if head_not_fun {
                let head_not_err = sub(head_tag, fun_tag);
                if head_not_err {
                    let err = EvalErr::ApplyNonFunc;
                    return (err_tag, err)
                }
                return (err_tag, head)
            }

            let (params_tag, params, body_tag, body, func_env) = load(head);

            match params_tag {
                Tag::Nil => {
                    let (res_tag, res) = call(eval, body_tag, body, func_env);
                    match res_tag {
                        Tag::Err => {
                            return (res_tag, res)
                        }
                    };
                    match args_tag {
                        Tag::Nil => {
                            return (res_tag, res)
                        }
                        Tag::Cons => {
                            // Oversaturated application
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
                            match arg_tag {
                                Tag::Err => {
                                    return (arg_tag, arg)
                                }
                            };
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
        fn env_lookup(x_digest: [8], env): [2] {
            if !env {
                let err_tag = Tag::Err;
                let err = EvalErr::UnboundVar;
                return (err_tag, err)
            }
            let (y, val_tag, val, tail_env) = load(env);
            let y_digest: [8] = load(y);
            let not_eq = sub(x_digest, y_digest);
            if !not_eq {
                return (val_tag, val)
            }
            let (res_tag, res) = call(env_lookup, x_digest, tail_env);
            return (res_tag, res)
        }
    )
}

#[cfg(test)]
mod test {
    use expect_test::{expect, Expect};
    use p3_baby_bear::BabyBear as F;

    use crate::{
        air::debug::debug_constraints_collecting_queries,
        lair::{
            execute::{QueryRecord, Shard},
            func_chip::FuncChip,
            List,
        },
        lurk::{state::State, zstore::ZPtr},
    };

    use super::*;

    #[test]
    fn test_widths() {
        let (toplevel, _) = &build_lurk_toplevel();

        let lurk_main = FuncChip::from_name("lurk_main", toplevel);
        let eval = FuncChip::from_name("eval", toplevel);
        let eval_opening_unop = FuncChip::from_name("eval_opening_unop", toplevel);
        let eval_hide = FuncChip::from_name("eval_hide", toplevel);
        let eval_unop = FuncChip::from_name("eval_unop", toplevel);
        let eval_binop_num = FuncChip::from_name("eval_binop_num", toplevel);
        let eval_binop_misc = FuncChip::from_name("eval_binop_misc", toplevel);
        let eval_begin = FuncChip::from_name("eval_begin", toplevel);
        let eval_list = FuncChip::from_name("eval_list", toplevel);
        let eval_let = FuncChip::from_name("eval_let", toplevel);
        let eval_letrec = FuncChip::from_name("eval_letrec", toplevel);
        let open_comm = FuncChip::from_name("open_comm", toplevel);
        let equal = FuncChip::from_name("equal", toplevel);
        let equal_inner = FuncChip::from_name("equal_inner", toplevel);
        let car_cdr = FuncChip::from_name("car_cdr", toplevel);
        let apply = FuncChip::from_name("apply", toplevel);
        let env_lookup = FuncChip::from_name("env_lookup", toplevel);
        let ingress = FuncChip::from_name("ingress", toplevel);
        let ingress_sym = FuncChip::from_name("ingress_sym", toplevel);
        let populate_builtin = FuncChip::from_name("populate_builtin", toplevel);
        let egress = FuncChip::from_name("egress", toplevel);
        let hash_24_8 = FuncChip::from_name("hash_24_8", toplevel);
        let hash_32_8 = FuncChip::from_name("hash_32_8", toplevel);
        let hash_48_8 = FuncChip::from_name("hash_48_8", toplevel);
        let u64_add = FuncChip::from_name("u64_add", toplevel);
        let u64_sub = FuncChip::from_name("u64_sub", toplevel);
        let u64_mul = FuncChip::from_name("u64_mul", toplevel);
        let u64_divrem = FuncChip::from_name("u64_divrem", toplevel);
        let u64_lessthan = FuncChip::from_name("u64_lessthan", toplevel);
        let u64_iszero = FuncChip::from_name("u64_iszero", toplevel);
        let digest_equal = FuncChip::from_name("digest_equal", toplevel);
        let big_num_lessthan = FuncChip::from_name("big_num_lessthan", toplevel);

        let expect_eq = |computed: usize, expected: Expect| {
            expected.assert_eq(&computed.to_string());
        };
        expect_eq(lurk_main.width(), expect!["94"]);
        expect_eq(eval.width(), expect!["154"]);
        expect_eq(eval_opening_unop.width(), expect!["96"]);
        expect_eq(eval_hide.width(), expect!["114"]);
        expect_eq(eval_unop.width(), expect!["78"]);
        expect_eq(eval_binop_num.width(), expect!["107"]);
        expect_eq(eval_binop_misc.width(), expect!["70"]);
        expect_eq(eval_begin.width(), expect!["68"]);
        expect_eq(eval_list.width(), expect!["72"]);
        expect_eq(eval_let.width(), expect!["92"]);
        expect_eq(eval_letrec.width(), expect!["96"]);
        expect_eq(open_comm.width(), expect!["49"]);
        expect_eq(equal.width(), expect!["82"]);
        expect_eq(equal_inner.width(), expect!["57"]);
        expect_eq(car_cdr.width(), expect!["61"]);
        expect_eq(apply.width(), expect!["99"]);
        expect_eq(env_lookup.width(), expect!["49"]);
        expect_eq(ingress.width(), expect!["100"]);
        expect_eq(ingress_sym.width(), expect!["368"]);
        expect_eq(populate_builtin.width(), expect!["160"]);
        expect_eq(egress.width(), expect!["76"]);
        expect_eq(hash_24_8.width(), expect!["493"]);
        expect_eq(hash_32_8.width(), expect!["655"]);
        expect_eq(hash_48_8.width(), expect!["975"]);
        expect_eq(u64_add.width(), expect!["53"]);
        expect_eq(u64_sub.width(), expect!["53"]);
        expect_eq(u64_mul.width(), expect!["85"]);
        expect_eq(u64_divrem.width(), expect!["166"]);
        expect_eq(u64_lessthan.width(), expect!["44"]);
        expect_eq(u64_iszero.width(), expect!["26"]);
        expect_eq(digest_equal.width(), expect!["38"]);
        expect_eq(big_num_lessthan.width(), expect!["78"]);
    }

    #[test]
    fn test_ingress_egress() {
        let (toplevel, zstore) = &build_lurk_toplevel();

        let ingress = toplevel.get_by_name("ingress");
        let egress = toplevel.get_by_name("egress");
        let hash_32_8_chip = FuncChip::from_name("hash_32_8", toplevel);

        let state = State::init_lurk_state().rccell();

        let assert_ingress_egress_correctness = |code| {
            let zstore = &mut zstore.clone();
            let ZPtr { tag, digest } = zstore.read_with_state(state.clone(), code).unwrap();
            let tag = tag.to_field();

            let digest: List<_> = digest.into();

            let mut queries = QueryRecord::new(toplevel);
            queries.inject_inv_queries("hash_32_8", toplevel, &zstore.hashes4);

            let mut ingress_args = [F::zero(); 16];
            ingress_args[0] = tag;
            ingress_args[8..].copy_from_slice(&digest);

            toplevel
                .execute(ingress, &ingress_args, &mut queries, None)
                .unwrap();
            let ingress_out_ptr = queries.get_output(ingress, &ingress_args)[0];

            let egress_args = &[tag, ingress_out_ptr];
            toplevel
                .execute(egress, egress_args, &mut queries, None)
                .unwrap();
            let egress_out = queries.get_output(egress, egress_args);

            assert_eq!(
                egress_out,
                digest.as_ref(),
                "ingress -> egress doesn't roundtrip"
            );

            let hash_32_8_trace = hash_32_8_chip.generate_trace(&Shard::new(&queries));
            debug_constraints_collecting_queries(&hash_32_8_chip, &[], None, &hash_32_8_trace);
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
