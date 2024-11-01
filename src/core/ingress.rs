use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use rustc_hash::FxHashSet;
use strum::{EnumCount, EnumIter};

use crate::{
    func,
    lair::{
        expr::{BlockE, CtrlE, FuncE, Ident, OpE, Var},
        FxIndexMap, List, Name,
    },
};

use super::{
    chipset::LurkChip,
    state::{builtin_sym, lurk_sym, BUILTIN_SYMBOLS, LURK_SYMBOLS},
    symbol::Symbol,
    tag::Tag,
    zstore::{ZStore, DIGEST_SIZE},
};

/// `usize` wrapper in order to implement `to_field`
pub struct DigestIndex(usize);

impl DigestIndex {
    pub fn to_field<F: AbstractField>(&self) -> F {
        F::from_canonical_usize(self.0)
    }
}

/// Keeps track of symbols digests to be allocated in memory, following the same
/// order of insertion (hence an `IndexMap`)
pub struct SymbolsDigests<F>(pub FxIndexMap<Symbol, List<F>>);

impl SymbolsDigests<BabyBear> {
    pub fn new(lang_symbols: &FxHashSet<Symbol>, zstore: &mut ZStore<BabyBear, LurkChip>) -> Self {
        let mut map = FxIndexMap::default();
        for name in LURK_SYMBOLS {
            let symbol = lurk_sym(name);
            let zptr = zstore.intern_symbol(&symbol, lang_symbols);
            assert_eq!(zptr.tag, Tag::Sym);
            map.insert(symbol, zptr.digest.into());
        }
        for name in BUILTIN_SYMBOLS {
            let symbol = builtin_sym(name);
            let zptr = zstore.intern_symbol(&symbol, lang_symbols);
            assert_eq!(zptr.tag, Tag::Builtin);
            map.insert(symbol, zptr.digest.into());
        }
        for symbol in lang_symbols {
            let zptr = zstore.intern_symbol(symbol, lang_symbols);
            assert_eq!(zptr.tag, Tag::Coroutine);
            assert!(
                map.insert(symbol.clone(), zptr.digest.into()).is_none(),
                "{symbol} conflicts with Lurk's native symbols"
            );
        }
        Self(map)
    }
}

impl<F> SymbolsDigests<F> {
    pub fn symbol_ptr(&self, symbol: &Symbol) -> DigestIndex {
        // + 1 because available memory starts from 1 (0 is reserved)
        DigestIndex(self.0.get_index_of(symbol).expect("Unknown symbol name") + 1)
    }

    pub fn lurk_symbol_ptr(&self, name: &str) -> DigestIndex {
        self.symbol_ptr(&lurk_sym(name))
    }

    pub fn builtin_symbol_ptr(&self, name: &str) -> DigestIndex {
        self.symbol_ptr(&builtin_sym(name))
    }

    pub fn symbol_digest(&self, symbol: &Symbol) -> &List<F> {
        self.0.get(symbol).expect("Unknown symbol name")
    }

    pub fn lurk_symbol_digest(&self, name: &str) -> &List<F> {
        self.symbol_digest(&lurk_sym(name))
    }
}

/// Tags that are internal to the VM
#[repr(usize)]
#[derive(Clone, Copy, EnumIter)]
pub enum InternalTag {
    Nil = 0,
    T,
}

impl InternalTag {
    /// Starts from where `Tag` ends
    pub fn to_field<F: AbstractField>(self) -> F {
        F::from_canonical_usize(Tag::COUNT + self as usize)
    }
}

/// ```ignore
/// fn preallocate_symbols(): [0] {
///     let arr: [8] = Array(<symbol 0 digest>);
///     let ptr = store(arr);
///     let addr = <symbol 0 address>;
///     assert_eq!(ptr, addr);
///     let arr: [8] = Array(<symbol 1 digest>);
///     let ptr = store(arr);
///     let addr = <symbol 1 address>;
///     assert_eq!(ptr, addr);
///     ...
///     return
/// }
/// ```
pub fn preallocate_symbols<F: AbstractField>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    let mut ops = Vec::with_capacity(2 * digests.0.len());
    let name = Ident::User("arr");
    let arr_var = Var {
        name,
        size: DIGEST_SIZE,
    };
    let ptr_var = Var::atom("ptr");
    let addr_var = Var::atom("addr");
    for (symbol, digest) in &digests.0 {
        let addr = digests.symbol_ptr(symbol).to_field();
        ops.push(OpE::Array(arr_var, digest.clone()));
        ops.push(OpE::Store(ptr_var, [arr_var].into()));
        ops.push(OpE::Const(addr_var, addr));
        ops.push(OpE::AssertEq(ptr_var, addr_var, None));
    }
    let ops = ops.into();
    let ctrl = CtrlE::return_vars([], 0);
    FuncE {
        name: Name("preallocate_symbols"),
        invertible: false,
        partial: false,
        input_params: [].into(),
        output_size: 0,
        body: BlockE { ops, ctrl },
    }
}

pub fn ingress<F: AbstractField>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn ingress(tag_full: [8], digest: [8]): [2] {
            let zeros = [0; 7];
            let (tag, rest: [7]) = tag_full;
            assert_eq!(rest, zeros);
            match tag {
                Tag::Num => {
                    let (x, rest: [7]) = digest;
                    assert_eq!(rest, zeros);
                    return (tag, x)
                }
                Tag::Char => {
                    let (bytes: [4], rest: [4]) = digest;
                    range_u8!(bytes);
                    let zeros = [0; 4];
                    assert_eq!(rest, zeros);
                    let ptr = store(bytes);
                    return (tag, ptr)
                }
                Tag::U64 => {
                    range_u8!(digest);
                    let ptr = store(digest);
                    return (tag, ptr)
                }
                Tag::Sym => {
                    let nil_digest = Array(digests.lurk_symbol_digest("nil").clone());
                    let not_nil = sub(digest, nil_digest);
                    if !not_nil {
                        let nil_tag = InternalTag::Nil;
                        let ptr = digests.lurk_symbol_ptr("nil");
                        return (nil_tag, ptr)
                    }
                    let t_digest = Array(digests.lurk_symbol_digest("t").clone());
                    let not_t = sub(digest, t_digest);
                    if !not_t {
                        let t_tag = InternalTag::T;
                        let ptr = digests.lurk_symbol_ptr("t");
                        return (t_tag, ptr)
                    }
                    let ptr = store(digest);
                    return (tag, ptr)
                }
                Tag::Builtin, Tag::Coroutine, Tag::Key, Tag::BigNum, Tag::Comm => {
                    let ptr = store(digest);
                    return (tag, ptr)
                }
                Tag::Str => {
                    if !digest {
                        let zero = 0;
                        return (tag, zero)
                    }
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash4, digest);
                    let (fst_tag, fst_ptr) = call(ingress, fst_tag_full, fst_digest);
                    let (snd_tag, snd_ptr) = call(ingress, snd_tag_full, snd_digest);
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return (tag, ptr)
                }
                Tag::Cons => {
                    let (fst_tag_full: [8], fst_digest: [8],
                         snd_tag_full: [8], snd_digest: [8]) = preimg(hash4, digest);
                    let (fst_tag, fst_ptr) = call(ingress, fst_tag_full, fst_digest);
                    let (snd_tag, snd_ptr) = call(ingress, snd_tag_full, snd_digest);
                    let ptr = store(fst_tag, fst_ptr, snd_tag, snd_ptr);
                    return (tag, ptr)
                }
                Tag::Fun, Tag::Fix => {
                    let (args_tag_full: [8], args_digest: [8],
                         body_tag_full: [8], body_digest: [8],
                                             env_digest:  [8]) = preimg(hash5, digest);
                    let env_tag = Tag::Env;
                    let (args_tag, args_ptr) = call(ingress, args_tag_full, args_digest);
                    let (body_tag, body_ptr) = call(ingress, body_tag_full, body_digest);
                    let (_env_tag, env_ptr) = call(ingress, env_tag, zeros, env_digest);
                    let ptr = store(args_tag, args_ptr, body_tag, body_ptr, env_ptr);
                    return (tag, ptr)
                }
                Tag::Env => {
                    if !digest {
                        let zero = 0;
                        return (tag, zero)
                    }
                    let (var_tag_full: [8], var_digest: [8],
                         val_tag_full: [8], val_digest: [8],
                                            env_digest: [8]) = preimg(hash5, digest);
                    let (var_tag, var_ptr) = call(ingress, var_tag_full, var_digest);
                    let (val_tag, val_ptr) = call(ingress, val_tag_full, val_digest);
                    let (_tag, env_ptr) = call(ingress, tag, zeros, env_digest); // `tag` is `Tag::Env`
                    let ptr = store(var_tag, var_ptr, val_tag, val_ptr, env_ptr);
                    return (tag, ptr)
                }
            }
        }
    )
}

pub fn egress<F: AbstractField>(digests: &SymbolsDigests<F>) -> FuncE<F> {
    func!(
        fn egress(tag, val): [9] {
            match tag {
                Tag::Num, Tag::Err => {
                    let padding = [0; 7];
                    let digest: [8] = (val, padding);
                    return (tag, digest)
                }
                Tag::Char => {
                    let padding = [0; 4];
                    let bytes: [4] = load(val);
                    return (tag, bytes, padding)
                }
                InternalTag::Nil => {
                    let sym_tag = Tag::Sym;
                    let digest = Array(digests.lurk_symbol_digest("nil").clone());
                    return (sym_tag, digest)
                }
                InternalTag::T => {
                    let sym_tag = Tag::Sym;
                    let digest = Array(digests.lurk_symbol_digest("t").clone());
                    return (sym_tag, digest)
                }
                Tag::Sym, Tag::Builtin, Tag::Coroutine, Tag::Key, Tag::U64, Tag::BigNum, Tag::Comm => {
                    let digest: [8] = load(val);
                    return (tag, digest)
                }
                Tag::Str => {
                    if !val {
                        let digest = [0; 8];
                        return (tag, digest)
                    }
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let (fst_tag, fst_digest: [8]) = call(egress, fst_tag, fst_ptr);
                    let (snd_tag, snd_digest: [8]) = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash4, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return (tag, digest)
                }
                Tag::Cons => {
                    let (fst_tag, fst_ptr, snd_tag, snd_ptr) = load(val);
                    let (fst_tag, fst_digest: [8]) = call(egress, fst_tag, fst_ptr);
                    let (snd_tag, snd_digest: [8]) = call(egress, snd_tag, snd_ptr);

                    let padding = [0; 7];
                    let fst_tag_full: [8] = (fst_tag, padding);
                    let snd_tag_full: [8] = (snd_tag, padding);
                    let digest: [8] = call(hash4, fst_tag_full, fst_digest, snd_tag_full, snd_digest);
                    return (tag, digest)
                }
                Tag::Fun, Tag::Fix => {
                    let (args_tag, args_ptr, body_tag, body_ptr, env_ptr) = load(val);
                    let (args_tag, args_digest: [8]) = call(egress, args_tag, args_ptr);
                    let (body_tag, body_digest: [8]) = call(egress, body_tag, body_ptr);
                    let env_tag = Tag::Env;
                    let (_env_tag, env_digest: [8]) = call(egress, env_tag, env_ptr);

                    let padding = [0; 7];
                    let args_tag_full: [8] = (args_tag, padding);
                    let body_tag_full: [8] = (body_tag, padding);
                    let digest: [8] = call(hash5, args_tag_full, args_digest, body_tag_full, body_digest, env_digest);
                    return (tag, digest)
                }
                Tag::Env => {
                    if !val {
                        let digest = [0; 8];
                        return (tag, digest)
                    }
                    let (var_tag, var_ptr, val_tag, val_ptr, env_ptr) = load(val);
                    let (var_tag, var_digest: [8]) = call(egress, var_tag, var_ptr);
                    let (val_tag, val_digest: [8]) = call(egress, val_tag, val_ptr);
                    let (_tag, env_digest: [8]) = call(egress, tag, env_ptr); // `tag` is `Tag::Env`

                    let padding = [0; 7];
                    let var_tag_full: [8] = (var_tag, padding);
                    let val_tag_full: [8] = (val_tag, padding);
                    let digest: [8] = call(hash5, var_tag_full, var_digest, val_tag_full, val_digest, env_digest);
                    return (tag, digest)
                }
            }
        }
    )
}
