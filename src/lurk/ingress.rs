use indexmap::{map::Iter, IndexMap};
use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rustc_hash::FxBuildHasher;

use crate::{
    func,
    lair::{
        expr::{BlockE, CasesE, CtrlE, FuncE, OpE, Var},
        List, Name,
    },
};

use super::{
    chipset::LurkChip,
    state::{StateRcCell, LURK_PACKAGE_SYMBOLS_NAMES},
    tag::Tag,
    zstore::ZStore,
};

pub struct BuiltinIndex(usize);

impl BuiltinIndex {
    pub fn to_field<F: AbstractField>(&self) -> F {
        F::from_canonical_usize(self.0)
    }
}

pub struct BuiltinMemo<'a, F>(IndexMap<&'a str, List<F>, FxBuildHasher>);

impl<'a> BuiltinMemo<'a, BabyBear> {
    pub fn new(state: &StateRcCell, zstore: &mut ZStore<BabyBear, LurkChip>) -> Self {
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
    pub fn index(&self, builtin: &'a str) -> BuiltinIndex {
        BuiltinIndex(self.0.get_index_of(builtin).expect("Unknown builtin"))
    }

    pub fn iter(&self) -> Iter<'_, &str, Box<[F]>> {
        self.0.iter()
    }
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
                Tag::U64 => {
                    range_u8!(digest);
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Sym, Tag::Key, Tag::Comm => {
                    let ptr = store(digest);
                    return ptr
                }
                Tag::Builtin => {
                    let idx = call(ingress_builtin, digest);
                    return idx
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
                    let snd_tag = Tag::Env;
                    let fst_ptr = call(ingress, fst_tag, padding, fst_digest);
                    let snd_ptr = call(ingress, snd_tag, padding, snd_digest);
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
                    let (_trd_tag, _rest: [7]) = trd_tag_full;
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

pub fn ingress_builtin<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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
    let branches = builtins
        .iter()
        .enumerate()
        .map(|(i, (_, digest))| (digest.clone(), branch(i)))
        .collect();
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
                Tag::Sym, Tag::Key, Tag::U64, Tag::Comm => {
                    let digest: [8] = load(val);
                    return digest
                }
                Tag::Builtin => {
                    let digest: [8] = call(egress_builtin, val);
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

pub fn egress_builtin<F: AbstractField + Ord>(builtins: &BuiltinMemo<'_, F>) -> FuncE<F> {
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
    let branches = builtins
        .iter()
        .enumerate()
        .map(|(i, (_, digest))| ([F::from_canonical_usize(i)].into(), branch(digest.clone())))
        .collect();
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
