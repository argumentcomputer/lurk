use anyhow::{bail, Result};
use core::str;
use indexmap::IndexSet;
use itertools::Itertools;
use nom::{sequence::preceded, Parser};
use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field, PrimeField32};
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

use crate::{
    lair::{chipset::Chipset, List},
    lurk::{
        parser::{
            syntax::{parse_maybe_meta, parse_space},
            Error, Span,
        },
        state::{lurk_sym, State, StateRcCell, BUILTIN_SYMBOLS},
        symbol::Symbol,
        syntax::Syntax,
        tag::Tag,
    },
};

use super::{
    big_num::field_elts_to_biguint,
    chipset::{lurk_hasher, LurkChip},
    eval::EvalErr,
    state::builtin_sym,
};

pub(crate) const DIGEST_SIZE: usize = 8;

pub(crate) const ZPTR_SIZE: usize = 2 * DIGEST_SIZE;
pub(crate) const HASH3_SIZE: usize = 3 * DIGEST_SIZE;
pub(crate) const HASH4_SIZE: usize = 4 * DIGEST_SIZE;
pub(crate) const HASH5_SIZE: usize = 5 * DIGEST_SIZE;

fn digest_from_field<F: AbstractField + Copy>(f: F) -> [F; DIGEST_SIZE] {
    let mut digest = [F::zero(); DIGEST_SIZE];
    digest[0] = f;
    digest
}

struct SizedBuffer<const N: usize, F> {
    data: [F; N],
    pos: usize,
}

impl<const N: usize, F: AbstractField + Copy> Default for SizedBuffer<N, F> {
    fn default() -> Self {
        Self {
            data: [F::zero(); N],
            pos: 0,
        }
    }
}

impl<const N: usize, F> SizedBuffer<N, F> {
    fn write_slice(&mut self, slice: &[F])
    where
        F: Copy,
    {
        self.data[self.pos..self.pos + slice.len()].copy_from_slice(slice);
        self.pos += slice.len();
    }

    fn extract(self) -> [F; N] {
        let Self { data, pos: _ } = self;
        data
    }

    fn write_tag(&mut self, tag: Tag)
    where
        F: AbstractField + Copy,
    {
        self.write_slice(&digest_from_field(F::from_canonical_u32(tag as u32)));
    }
}

#[inline]
fn into_sized<F: AbstractField + Copy, const N: usize>(slice: &[F]) -> [F; N] {
    let mut buffer = SizedBuffer::default();
    buffer.write_slice(slice);
    buffer.extract()
}

fn get_char<F: PrimeField32>(digest: &[F; DIGEST_SIZE]) -> char {
    let u8s = digest.map(|f| f.as_canonical_u32().try_into().expect("Invalid char limb"));
    let (bytes, rest) = u8s.split_at(4);
    assert_eq!(rest, [0; 4]);
    let mut chars = std::str::from_utf8(bytes).expect("Invalid UTF-8").chars();
    let c = chars.next().expect("Original slice was not empty");
    assert!(chars.all(|c| c == '\0'));
    c
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ZPtr<F> {
    pub tag: Tag,
    pub digest: [F; DIGEST_SIZE],
}

impl<F: AbstractField + Copy> ZPtr<F> {
    #[inline]
    pub fn into_inner(self) -> (Tag, [F; DIGEST_SIZE]) {
        let ZPtr { tag, digest } = self;
        (tag, digest)
    }

    #[inline]
    pub fn null(tag: Tag) -> Self {
        Self {
            tag,
            digest: [F::zero(); DIGEST_SIZE],
        }
    }

    #[inline]
    pub fn num(f: F) -> Self {
        Self {
            tag: Tag::Num,
            digest: digest_from_field(f),
        }
    }

    #[inline]
    pub fn char(c: char) -> Self {
        let mut bytes = [0; DIGEST_SIZE];
        c.encode_utf8(&mut bytes);
        Self {
            tag: Tag::Char,
            digest: bytes.map(F::from_canonical_u8),
        }
    }

    #[inline]
    pub fn u64(u: u64) -> Self {
        Self {
            tag: Tag::U64,
            digest: u.to_le_bytes().map(F::from_canonical_u8),
        }
    }

    #[inline]
    pub fn err(err: EvalErr) -> Self {
        Self {
            tag: Tag::Err,
            digest: digest_from_field(err.to_field()),
        }
    }

    #[inline]
    pub fn big_num(digest: [F; DIGEST_SIZE]) -> Self {
        Self {
            tag: Tag::BigNum,
            digest,
        }
    }

    #[inline]
    pub fn comm(digest: [F; DIGEST_SIZE]) -> Self {
        Self {
            tag: Tag::Comm,
            digest,
        }
    }

    #[inline]
    pub fn from_flat_digest(tag: Tag, digest: &[F]) -> Self {
        Self {
            tag,
            digest: into_sized(digest),
        }
    }

    #[inline]
    pub fn from_flat_data(data: &[F]) -> Self
    where
        F: PrimeField32,
    {
        Self {
            tag: Tag::from_field(&data[0]),
            digest: into_sized(&data[8..]),
        }
    }
}

impl<F: AbstractField + Copy> ZPtr<F> {
    pub fn flatten(&self) -> [F; ZPTR_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_tag(self.tag);
        buffer.write_slice(&self.digest);
        buffer.extract()
    }

    pub fn flatten2(a: &ZPtr<F>, b: &ZPtr<F>) -> [F; HASH4_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&a.flatten());
        buffer.write_slice(&b.flatten());
        buffer.extract()
    }

    pub fn flatten_compact10(a: &ZPtr<F>, b: &ZPtr<F>) -> [F; HASH3_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&a.flatten());
        buffer.write_slice(&b.digest);
        buffer.extract()
    }

    pub fn flatten_compact110(a: &ZPtr<F>, b: &ZPtr<F>, c: &ZPtr<F>) -> [F; HASH5_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&a.flatten());
        buffer.write_slice(&b.flatten());
        buffer.write_slice(&c.digest);
        buffer.extract()
    }
}

/// Specifies the dependencies of a `ZPtr` in a Merkle DAG for content-addressing
#[derive(Clone, Copy, Serialize, Deserialize)]
pub enum ZPtrType<F> {
    /// A leaf datum without children
    Atom,
    /// Consumes the tag and digest of two children `ZPtr`s
    Tuple2(ZPtr<F>, ZPtr<F>),
    /// Ignores the tag of the second `ZPtr`
    Compact10(ZPtr<F>, ZPtr<F>),
    /// Ignores the tag of the third `ZPtr`
    Compact110(ZPtr<F>, ZPtr<F>, ZPtr<F>),
}

/// This struct selects what the hash functions are in a given chipset
#[derive(Clone)]
pub struct Hasher<F, C: Chipset<F>> {
    hash3: C,
    hash4: C,
    hash5: C,
    _p: PhantomData<F>,
}

impl<F, C: Chipset<F>> Hasher<F, C> {
    #[inline]
    pub fn new(hash3: C, hash4: C, hash5: C) -> Self {
        Self {
            hash3,
            hash4,
            hash5,
            _p: PhantomData,
        }
    }

    #[inline]
    pub fn hash(&self, preimg: &[F]) -> Vec<F> {
        match preimg.len() {
            HASH3_SIZE => self.hash3.execute_simple(preimg),
            HASH4_SIZE => self.hash4.execute_simple(preimg),
            HASH5_SIZE => self.hash5.execute_simple(preimg),
            _ => panic!("Preimage size not supported"),
        }
    }
}

#[derive(Clone)]
pub struct ZStore<F, C: Chipset<F>> {
    hasher: Hasher<F, C>,
    pub(crate) dag: FxHashMap<ZPtr<F>, ZPtrType<F>>,
    pub hashes3: FxHashMap<[F; HASH3_SIZE], [F; DIGEST_SIZE]>,
    pub hashes4: FxHashMap<[F; HASH4_SIZE], [F; DIGEST_SIZE]>,
    pub hashes5: FxHashMap<[F; HASH5_SIZE], [F; DIGEST_SIZE]>,
    pub hashes3_diff: FxHashMap<[F; HASH3_SIZE], [F; DIGEST_SIZE]>,
    pub hashes4_diff: FxHashMap<[F; HASH4_SIZE], [F; DIGEST_SIZE]>,
    pub hashes5_diff: FxHashMap<[F; HASH5_SIZE], [F; DIGEST_SIZE]>,
    str_cache: FxHashMap<String, ZPtr<F>>,
    sym_cache: FxHashMap<Symbol, ZPtr<F>>,
    syn_cache: FxHashMap<Syntax<F>, ZPtr<F>>,
    nil: ZPtr<F>,
    t: ZPtr<F>,
}

impl Default for ZStore<BabyBear, LurkChip> {
    fn default() -> Self {
        let mut zstore = Self {
            hasher: lurk_hasher(),
            dag: Default::default(),
            hashes3: Default::default(),
            hashes4: Default::default(),
            hashes5: Default::default(),
            hashes3_diff: Default::default(),
            hashes4_diff: Default::default(),
            hashes5_diff: Default::default(),
            str_cache: Default::default(),
            sym_cache: Default::default(),
            syn_cache: Default::default(),
            nil: ZPtr::null(Tag::Sym),
            t: ZPtr::null(Tag::Sym),
        };
        zstore.nil = zstore.intern_symbol_no_lang(&lurk_sym("nil"));
        zstore.t = zstore.intern_symbol_no_lang(&lurk_sym("t"));
        zstore
    }
}

static QUOTE: OnceCell<Symbol> = OnceCell::new();
fn quote() -> &'static Symbol {
    QUOTE.get_or_init(|| builtin_sym("quote"))
}

static BUILTIN_SET: OnceCell<IndexSet<Symbol, FxBuildHasher>> = OnceCell::new();
pub(crate) fn builtin_set() -> &'static IndexSet<Symbol, FxBuildHasher> {
    BUILTIN_SET.get_or_init(|| BUILTIN_SYMBOLS.into_iter().map(builtin_sym).collect())
}

impl<F: Field, C: Chipset<F>> ZStore<F, C> {
    #[inline]
    pub fn hasher(&self) -> &Hasher<F, C> {
        &self.hasher
    }

    pub(crate) fn hash3(&mut self, preimg: [F; HASH3_SIZE]) -> [F; DIGEST_SIZE] {
        if let Some(img) = self.hashes3.get(&preimg) {
            return *img;
        }
        let digest = into_sized(&self.hasher.hash3.execute_simple(&preimg));
        self.hashes3.insert(preimg, digest);
        self.hashes3_diff.insert(preimg, digest);
        digest
    }

    fn hash4(&mut self, preimg: [F; HASH4_SIZE]) -> [F; DIGEST_SIZE] {
        if let Some(img) = self.hashes4.get(&preimg) {
            return *img;
        }
        let digest = into_sized(&self.hasher.hash4.execute_simple(&preimg));
        self.hashes4.insert(preimg, digest);
        self.hashes4_diff.insert(preimg, digest);
        digest
    }

    fn hash5(&mut self, preimg: [F; HASH5_SIZE]) -> [F; DIGEST_SIZE] {
        if let Some(img) = self.hashes5.get(&preimg) {
            return *img;
        }
        let digest = into_sized(&self.hasher.hash5.execute_simple(&preimg));
        self.hashes5.insert(preimg, digest);
        self.hashes5_diff.insert(preimg, digest);
        digest
    }

    pub fn intern_tuple2(&mut self, tag: Tag, a: ZPtr<F>, b: ZPtr<F>) -> ZPtr<F> {
        let preimg = ZPtr::flatten2(&a, &b);
        let digest = self.hash4(preimg);
        let zptr = ZPtr { tag, digest };
        self.dag.insert(zptr, ZPtrType::Tuple2(a, b));
        zptr
    }

    fn intern_compact10(&mut self, tag: Tag, a: ZPtr<F>, b: ZPtr<F>) -> ZPtr<F> {
        let preimg = ZPtr::flatten_compact10(&a, &b);
        let digest = self.hash3(preimg);
        let zptr = ZPtr { tag, digest };
        self.dag.insert(zptr, ZPtrType::Compact10(a, b));
        zptr
    }

    fn intern_compact110(&mut self, tag: Tag, a: ZPtr<F>, b: ZPtr<F>, c: ZPtr<F>) -> ZPtr<F> {
        let preimg = ZPtr::flatten_compact110(&a, &b, &c);
        let digest = self.hash5(preimg);
        let zptr = ZPtr { tag, digest };
        self.dag.insert(zptr, ZPtrType::Compact110(a, b, c));
        zptr
    }

    #[inline]
    fn memoize_atom_dag(&mut self, zptr: ZPtr<F>) -> ZPtr<F> {
        self.dag.insert(zptr, ZPtrType::Atom);
        zptr
    }

    #[inline]
    pub fn intern_null(&mut self, tag: Tag) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::null(tag))
    }

    #[inline]
    pub fn intern_empty_env(&mut self) -> ZPtr<F> {
        self.intern_null(Tag::Env)
    }

    #[inline]
    pub fn intern_num(&mut self, f: F) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::num(f))
    }

    #[inline]
    pub fn intern_char(&mut self, c: char) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::char(c))
    }

    #[inline]
    pub fn intern_u64(&mut self, u: u64) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::u64(u))
    }

    #[inline]
    pub fn intern_big_num(&mut self, c: [F; DIGEST_SIZE]) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::big_num(c))
    }

    #[inline]
    pub fn intern_comm(&mut self, c: [F; DIGEST_SIZE]) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::comm(c))
    }

    #[inline]
    pub fn intern_error(&mut self, err: EvalErr) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::err(err))
    }

    pub fn intern_string(&mut self, s: &str) -> ZPtr<F> {
        if let Some(zptr) = self.str_cache.get(s).copied() {
            return zptr;
        }
        let zptr = s.chars().rev().fold(self.intern_null(Tag::Str), |acc, c| {
            let char_zptr = self.intern_char(c);
            self.intern_tuple2(Tag::Str, char_zptr, acc)
        });
        self.str_cache.insert(s.to_string(), zptr);
        zptr
    }

    pub fn intern_symbol(&mut self, sym: &Symbol, lang_symbols: &FxHashSet<Symbol>) -> ZPtr<F> {
        if let Some(zptr) = self.sym_cache.get(sym).copied() {
            return zptr;
        }
        let is_keyword = sym.is_keyword();
        let zptr = {
            if sym.path().is_empty() {
                let tag = if is_keyword { Tag::Key } else { Tag::Sym };
                self.intern_null(tag)
            } else {
                let mut zptr = self.intern_null(Tag::Sym);
                let mut iter = sym.path().iter().peekable();
                while let Some(s) = iter.next() {
                    let is_last = iter.peek().is_none();
                    let str_zptr = self.intern_string(s);
                    let tag = if is_last {
                        if builtin_set().contains(sym) {
                            Tag::Builtin
                        } else if lang_symbols.contains(sym) {
                            Tag::Coroutine
                        } else if is_keyword {
                            Tag::Key
                        } else {
                            Tag::Sym
                        }
                    } else {
                        Tag::Sym
                    };
                    zptr = self.intern_tuple2(tag, str_zptr, zptr);
                }
                zptr
            }
        };
        self.sym_cache.insert(sym.clone(), zptr);
        zptr
    }

    #[inline]
    pub fn intern_symbol_no_lang(&mut self, sym: &Symbol) -> ZPtr<F> {
        self.intern_symbol(sym, &Default::default())
    }

    #[inline]
    pub fn nil(&self) -> &ZPtr<F> {
        &self.nil
    }

    #[inline]
    pub fn t(&self) -> &ZPtr<F> {
        &self.t
    }

    #[inline]
    pub fn intern_list_full<I: IntoIterator<Item = ZPtr<F>>>(
        &mut self,
        xs: I,
        y: ZPtr<F>,
    ) -> ZPtr<F>
    where
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        xs.into_iter()
            .rev()
            .fold(y, |acc, x| self.intern_tuple2(Tag::Cons, x, acc))
    }

    #[inline]
    pub fn intern_list<I: IntoIterator<Item = ZPtr<F>>>(&mut self, xs: I) -> ZPtr<F>
    where
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        self.intern_list_full(xs, self.nil)
    }

    #[inline]
    pub fn intern_cons(&mut self, car: ZPtr<F>, cdr: ZPtr<F>) -> ZPtr<F> {
        self.intern_tuple2(Tag::Cons, car, cdr)
    }

    #[inline]
    pub fn intern_thunk(&mut self, body: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        self.intern_compact10(Tag::Thunk, body, env)
    }

    #[inline]
    pub fn intern_fun(&mut self, args: ZPtr<F>, body: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        self.intern_compact110(Tag::Fun, args, body, env)
    }

    #[inline]
    pub fn intern_env(&mut self, sym: ZPtr<F>, val: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        self.intern_compact110(Tag::Env, sym, val, env)
    }

    fn intern_syntax(
        &mut self,
        syn: &Syntax<F>,
        lang_symbols: &FxHashSet<Symbol>,
    ) -> Result<ZPtr<F>> {
        if let Some(zptr) = self.syn_cache.get(syn).copied() {
            return Ok(zptr);
        }
        let zptr = match syn {
            Syntax::Num(_, f) => self.intern_num(*f),
            Syntax::Char(_, c) => self.intern_char(*c),
            Syntax::U64(_, u) => self.intern_u64(*u),
            Syntax::I64(..) => bail!("Transient error: Signed integers are not yet supported. Using `(- 0 x)` instead of `-x` might work as a temporary workaround."),
            Syntax::BigNum(_, c) => self.intern_big_num(*c),
            Syntax::Comm(_, c) => self.intern_comm(*c),
            Syntax::String(_, s) => self.intern_string(s),
            Syntax::Symbol(_, s) => self.intern_symbol(s, lang_symbols),
            Syntax::List(_, xs) => {
                let xs = xs
                    .iter()
                    .map(|x| self.intern_syntax(x, lang_symbols))
                    .collect::<Result<Vec<_>>>()?;
                self.intern_list(xs)
            }
            Syntax::Improper(_, xs, y) => {
                let xs = xs
                    .iter()
                    .map(|x| self.intern_syntax(x, lang_symbols))
                    .collect::<Result<Vec<_>>>()?;
                let y = self.intern_syntax(y, lang_symbols)?;
                self.intern_list_full(xs, y)
            }
            Syntax::Quote(_, x) => {
                let quote = self.intern_symbol(quote(), lang_symbols);
                let x = self.intern_syntax(x, lang_symbols)?;
                self.intern_list([quote, x])
            }
        };
        self.syn_cache.insert(syn.clone(), zptr);
        Ok(zptr)
    }

    #[inline]
    pub fn read_maybe_meta_with_state<'a>(
        &mut self,
        state: StateRcCell,
        input: &'a str,
        lang_symbols: &FxHashSet<Symbol>,
    ) -> Result<(usize, Span<'a>, bool, ZPtr<F>), Error> {
        match preceded(parse_space, parse_maybe_meta(state, false)).parse(Span::new(input)) {
            Ok((_, None)) => Err(Error::NoInput),
            Err(e) => Err(Error::Syntax(format!("{e}"))),
            Ok((rest, Some((is_meta, syn)))) => {
                let offset = syn
                    .get_pos()
                    .get_from_offset()
                    .expect("Parsed syntax should have its Pos set");
                let syn = self
                    .intern_syntax(&syn, lang_symbols)
                    .map_err(|e| Error::Syntax(format!("{e}")))?;
                Ok((offset, rest, is_meta, syn))
            }
        }
    }

    #[inline]
    pub fn read_maybe_meta<'a>(
        &mut self,
        input: &'a str,
        lang_symbols: &FxHashSet<Symbol>,
    ) -> Result<(usize, Span<'a>, bool, ZPtr<F>), Error> {
        self.read_maybe_meta_with_state(State::init_lurk_state().rccell(), input, lang_symbols)
    }

    #[inline]
    pub fn read_with_state(
        &mut self,
        state: StateRcCell,
        input: &str,
        lang_symbols: &FxHashSet<Symbol>,
    ) -> Result<ZPtr<F>> {
        let (.., is_meta, zptr) = self.read_maybe_meta_with_state(state, input, lang_symbols)?;
        assert!(!is_meta);
        Ok(zptr)
    }

    #[inline]
    pub fn read(&mut self, input: &str, lang_symbols: &FxHashSet<Symbol>) -> Result<ZPtr<F>> {
        self.read_with_state(State::init_lurk_state().rccell(), input, lang_symbols)
    }

    /// Memoizes the Lurk data dependencies of a tag/digest pair
    pub fn memoize_dag<'a>(
        &mut self,
        tag: Tag,
        mut digest: &'a [F],
        hashes3_inv: &'a FxHashMap<List<F>, List<F>>,
        hashes4_inv: &'a FxHashMap<List<F>, List<F>>,
        hashes5_inv: &'a FxHashMap<List<F>, List<F>>,
    ) where
        F: PrimeField32,
    {
        let mut zptr = ZPtr {
            tag,
            digest: into_sized(digest),
        };
        if self.dag.contains_key(&zptr) {
            return;
        };
        let zeros = [F::zero(); DIGEST_SIZE];
        macro_rules! recurse {
            ($tag:expr, $digest:expr) => {
                self.memoize_dag($tag, $digest, hashes3_inv, hashes4_inv, hashes5_inv);
            };
        }
        macro_rules! memoize_tuple2_or_compact {
            ($fst_tag:expr, $fst_digest:expr, $snd_tag:expr, $snd_digest:expr, $tuple2:expr) => {
                let fst = ZPtr {
                    tag: $fst_tag,
                    digest: into_sized($fst_digest),
                };
                let snd = ZPtr {
                    tag: $snd_tag,
                    digest: into_sized($snd_digest),
                };
                if $tuple2 {
                    self.dag.insert(zptr, ZPtrType::Tuple2(fst, snd));
                } else {
                    self.dag.insert(zptr, ZPtrType::Compact10(fst, snd));
                }
            };
        }
        macro_rules! memoize_tuple2 {
            ($fst_tag:expr, $fst_digest:expr, $snd_tag:expr, $snd_digest:expr) => {
                memoize_tuple2_or_compact!($fst_tag, $fst_digest, $snd_tag, $snd_digest, true);
            };
        }
        macro_rules! memoize_compact10 {
            ($fst_tag:expr, $fst_digest:expr, $snd_tag:expr, $snd_digest:expr) => {
                memoize_tuple2_or_compact!($fst_tag, $fst_digest, $snd_tag, $snd_digest, false);
            };
        }
        macro_rules! memoize_compact110 {
            ($fst_tag:expr, $fst_digest:expr, $snd_tag:expr, $snd_digest:expr, $trd_tag:expr, $trd_digest:expr) => {
                let fst = ZPtr {
                    tag: $fst_tag,
                    digest: into_sized($fst_digest),
                };
                let snd = ZPtr {
                    tag: $snd_tag,
                    digest: into_sized($snd_digest),
                };
                let trd = ZPtr {
                    tag: $trd_tag,
                    digest: into_sized($trd_digest),
                };
                self.dag.insert(zptr, ZPtrType::Compact110(fst, snd, trd));
            };
        }
        match tag {
            Tag::Str => loop {
                if digest == zeros {
                    self.memoize_atom_dag(ZPtr { tag, digest: zeros });
                    break;
                }
                let preimg = hashes4_inv.get(digest).expect("Hash32 preimg not found");
                let (head, tail) = preimg.split_at(ZPTR_SIZE);
                let head_digest = &head[DIGEST_SIZE..];
                let tail_digest = &tail[DIGEST_SIZE..];
                memoize_tuple2!(Tag::Char, head_digest, Tag::Str, tail_digest);
                digest = tail_digest;
                zptr = ZPtr::from_flat_data(tail);
            },
            Tag::Cons => loop {
                let preimg = hashes4_inv.get(digest).expect("Hash32 preimg not found");
                let (car, cdr) = preimg.split_at(ZPTR_SIZE);
                let (car_tag, car_digest) = car.split_at(DIGEST_SIZE);
                let (cdr_tag, cdr_digest) = cdr.split_at(DIGEST_SIZE);
                let car_tag = Tag::from_field(&car_tag[0]);
                let cdr_tag = Tag::from_field(&cdr_tag[0]);
                recurse!(car_tag, car_digest);
                memoize_tuple2!(car_tag, car_digest, cdr_tag, cdr_digest);
                if cdr_tag != Tag::Cons {
                    recurse!(cdr_tag, cdr_digest);
                    break;
                }
                digest = cdr_digest;
                zptr = ZPtr::from_flat_data(cdr);
            },
            Tag::Thunk => {
                let preimg = hashes3_inv.get(digest).expect("Hash24 preimg not found");
                let (fst, snd_digest) = preimg.split_at(ZPTR_SIZE);
                let (fst_tag, fst_digest) = fst.split_at(DIGEST_SIZE);
                let fst_tag = Tag::from_field(&fst_tag[0]);
                let snd_tag = Tag::Env;
                recurse!(fst_tag, fst_digest);
                recurse!(snd_tag, snd_digest);
                memoize_compact10!(fst_tag, fst_digest, snd_tag, snd_digest);
            }
            Tag::Env => loop {
                if digest == zeros {
                    self.memoize_atom_dag(ZPtr { tag, digest: zeros });
                    break;
                }
                let preimg = hashes5_inv.get(digest).expect("Hash40 preimg not found");
                let (var, rst) = preimg.split_at(ZPTR_SIZE);
                let (val, env_digest) = rst.split_at(ZPTR_SIZE);
                let (var_tag, var_digest) = var.split_at(DIGEST_SIZE);
                let (val_tag, val_digest) = val.split_at(DIGEST_SIZE);
                let var_tag = Tag::from_field(&var_tag[0]);
                let val_tag = Tag::from_field(&val_tag[0]);
                let env_tag = Tag::Env;
                recurse!(var_tag, var_digest);
                recurse!(val_tag, val_digest);
                memoize_compact110!(var_tag, var_digest, val_tag, val_digest, env_tag, env_digest);
                digest = env_digest;
                zptr = ZPtr {
                    tag: Tag::Env,
                    digest: into_sized(env_digest),
                };
            },
            Tag::Fun | Tag::Macro => {
                let preimg = hashes5_inv.get(digest).expect("Hash40 preimg not found");
                let (args, rest) = preimg.split_at(ZPTR_SIZE);
                let (body, env_digest) = rest.split_at(ZPTR_SIZE);
                let (args_tag, args_digest) = args.split_at(DIGEST_SIZE);
                let (body_tag, body_digest) = body.split_at(DIGEST_SIZE);
                let args_tag = Tag::from_field(&args_tag[0]);
                let body_tag = Tag::from_field(&body_tag[0]);
                let env_tag = Tag::Env;
                recurse!(args_tag, args_digest);
                recurse!(body_tag, body_digest);
                recurse!(env_tag, env_digest);
                memoize_compact110!(
                    args_tag,
                    args_digest,
                    body_tag,
                    body_digest,
                    env_tag,
                    env_digest
                );
            }
            Tag::Sym | Tag::Key | Tag::Builtin | Tag::Coroutine => (), // these should be already memoized
            Tag::Num | Tag::U64 | Tag::Char | Tag::Err | Tag::BigNum | Tag::Comm => {
                self.memoize_atom_dag(ZPtr {
                    tag,
                    digest: into_sized(digest),
                });
            }
        }
    }

    #[inline]
    pub fn fetch_tuple2(&self, zptr: &ZPtr<F>) -> (&ZPtr<F>, &ZPtr<F>) {
        let Some(ZPtrType::Tuple2(a, b)) = self.dag.get(zptr) else {
            panic!("Tuple2 data not found on DAG: {:?}", zptr)
        };
        (a, b)
    }

    #[inline]
    pub fn fetch_compact10(&self, zptr: &ZPtr<F>) -> (&ZPtr<F>, &ZPtr<F>) {
        let Some(ZPtrType::Compact10(a, b)) = self.dag.get(zptr) else {
            panic!("Compact10 data not found on DAG: {:?}", zptr)
        };
        (a, b)
    }

    #[inline]
    pub fn fetch_compact110(&self, zptr: &ZPtr<F>) -> (&ZPtr<F>, &ZPtr<F>, &ZPtr<F>) {
        let Some(ZPtrType::Compact110(a, b, c)) = self.dag.get(zptr) else {
            panic!("Compact3 data not found on DAG: {:?}", zptr)
        };
        (a, b, c)
    }

    pub fn fetch_string<'a>(&'a self, mut zptr: &'a ZPtr<F>) -> String
    where
        F: PrimeField32,
    {
        assert_eq!(zptr.tag, Tag::Str);
        let mut string = String::new();
        let zeros = [F::zero(); DIGEST_SIZE];
        while zptr.digest != zeros {
            let (car, cdr) = self.fetch_tuple2(zptr);
            string.push(get_char(&car.digest));
            zptr = cdr;
        }
        string
    }

    pub fn fetch_symbol_path<'a>(&'a self, mut zptr: &'a ZPtr<F>) -> Vec<String>
    where
        F: PrimeField32,
    {
        let mut path = vec![];
        let zeros = [F::zero(); DIGEST_SIZE];
        while zptr.digest != zeros {
            let (car, cdr) = self.fetch_tuple2(zptr);
            path.push(self.fetch_string(car));
            zptr = cdr;
        }
        path.reverse();
        path
    }

    #[inline]
    pub fn fetch_symbol(&self, zptr: &ZPtr<F>) -> Symbol
    where
        F: PrimeField32,
    {
        assert!(matches!(zptr.tag, Tag::Sym | Tag::Builtin | Tag::Key));
        Symbol::new_from_vec(self.fetch_symbol_path(zptr), zptr.tag == Tag::Key)
    }

    pub fn fetch_list<'a>(&'a self, mut zptr: &'a ZPtr<F>) -> (Vec<&ZPtr<F>>, Option<&'a ZPtr<F>>) {
        assert!(zptr.tag == Tag::Cons || zptr == &self.nil);
        let mut elts = vec![];
        while zptr.tag == Tag::Cons {
            let (car, cdr) = self.fetch_tuple2(zptr);
            elts.push(car);
            zptr = cdr;
        }
        if zptr == &self.nil {
            (elts, None)
        } else {
            (elts, Some(zptr))
        }
    }

    pub fn fetch_env<'a>(&'a self, mut zptr: &'a ZPtr<F>) -> Vec<(&ZPtr<F>, &ZPtr<F>)>
    where
        F: PrimeField32,
    {
        assert_eq!(zptr.tag, Tag::Env);
        let mut env = vec![];
        let zeros = [F::zero(); DIGEST_SIZE];
        while zptr.digest != zeros {
            let (var, val, tail) = self.fetch_compact110(zptr);
            env.push((var, val));
            zptr = tail;
        }
        env
    }

    pub fn property_map<'a>(&'a self, list: &'a ZPtr<F>) -> Result<FxHashMap<String, &'a ZPtr<F>>>
    where
        F: PrimeField32,
    {
        let (elts, None) = self.fetch_list(list) else {
            bail!("Property list must be proper");
        };
        let mut map = FxHashMap::default();
        let mut i = 0;
        loop {
            if i >= elts.len() {
                break;
            }
            let property_key = elts[i];
            if property_key.tag != Tag::Key {
                bail!("Property name must be a keyword");
            }
            let mut path = self.fetch_symbol_path(property_key);
            let Some(property_name) = path.pop() else {
                bail!("Property name can't be the root keyword")
            };
            let Some(property_val) = elts.get(i + 1) else {
                bail!("Missing value for property {i}")
            };
            map.insert(property_name, *property_val);
            i += 2;
        }
        Ok(map)
    }

    pub fn fmt_with_state(&self, state: &StateRcCell, zptr: &ZPtr<F>) -> String
    where
        F: PrimeField32,
    {
        match zptr.tag {
            Tag::Num => format!("{}n", zptr.digest[0]),
            Tag::U64 => format!(
                "{}",
                u64::from_le_bytes(
                    zptr.digest
                        .map(|f| u8::try_from(f.as_canonical_u32()).expect("invalid u64 limbs"))
                )
            ),
            Tag::Char => format!("'{}'", get_char(&zptr.digest)),
            Tag::BigNum => format!("#{:#x}", field_elts_to_biguint(&zptr.digest)),
            Tag::Comm => format!("#c{:#x}", field_elts_to_biguint(&zptr.digest)),
            Tag::Str => format!("\"{}\"", self.fetch_string(zptr)),
            Tag::Builtin | Tag::Sym | Tag::Key | Tag::Coroutine => {
                state.borrow().fmt_to_string(&self.fetch_symbol(zptr))
            }
            Tag::Cons => {
                let (elts, last) = self.fetch_list(zptr);
                let elts_str = elts.iter().map(|z| self.fmt_with_state(state, z)).join(" ");
                if let Some(last) = last {
                    format!("({elts_str} . {})", self.fmt_with_state(state, last))
                } else {
                    format!("({elts_str})")
                }
            }
            Tag::Fun | Tag::Macro => {
                let name = if zptr.tag == Tag::Fun { "Fun" } else { "Macro" };
                let (args, body, _) = self.fetch_compact110(zptr);
                if args == &self.nil {
                    format!("<{} () {}>", name, self.fmt_with_state(state, body))
                } else {
                    format!(
                        "<{} {} {}>",
                        name,
                        self.fmt_with_state(state, args),
                        self.fmt_with_state(state, body)
                    )
                }
            }
            Tag::Env => {
                let pairs_str = self
                    .fetch_env(zptr)
                    .iter()
                    .map(|(sym, val)| {
                        format!(
                            "({} . {})",
                            self.fmt_with_state(state, sym),
                            self.fmt_with_state(state, val)
                        )
                    })
                    .join(" ");
                format!("<Env ({})>", pairs_str)
            }
            Tag::Thunk => {
                let (body, _) = self.fetch_compact10(zptr);
                format!("<Thunk {}>", self.fmt_with_state(state, body))
            }
            Tag::Err => format!("<Err {:?}>", EvalErr::from_field(&zptr.digest[0])),
        }
    }

    #[inline]
    pub fn fmt(&self, zptr: &ZPtr<F>) -> String
    where
        F: PrimeField32,
    {
        let state = State::init_lurk_state().rccell();
        self.fmt_with_state(&state, zptr)
    }
}

#[inline]
pub fn lurk_zstore() -> ZStore<BabyBear, LurkChip> {
    ZStore::default()
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;

    use crate::{
        lair::execute::QueryRecord,
        lurk::{
            chipset::lurk_hasher,
            eval::build_lurk_toplevel_native,
            state::{builtin_sym, user_sym, State},
            symbol::Symbol,
            tag::Tag,
            zstore::lurk_zstore,
        },
    };

    use super::{into_sized, ZPtr};

    #[test]
    fn test_sym_key_hash_equivalence() {
        let mut zstore = lurk_zstore();
        let mut symbol = Symbol::sym(&["foo", "bar", "baz"]);
        let sym = zstore.intern_symbol_no_lang(&symbol);
        assert_eq!(sym.tag, Tag::Sym);

        symbol.set_as_keyword();
        let key = zstore.intern_symbol_no_lang(&symbol);
        assert_eq!(key.tag, Tag::Key);

        assert_eq!(sym.digest, key.digest);
    }

    #[test]
    fn test_dag_memoization() {
        let (toplevel, mut zstore, lang_symbols) = build_lurk_toplevel_native();

        let ZPtr {
            tag: expr_tag,
            digest: expr_digest,
        } = zstore
            .read("(cons \"hi\" (lambda (x) x))", &lang_symbols)
            .unwrap();

        let record = &mut QueryRecord::new(&toplevel);
        record.inject_inv_queries("hash4", &toplevel, &zstore.hashes4);

        let mut input = [BabyBear::zero(); 24];
        input[0] = expr_tag.to_field();
        input[8..16].copy_from_slice(&expr_digest);

        let output = toplevel
            .execute_by_name("lurk_main", &input, record, None)
            .unwrap();

        let output_tag = Tag::from_field(&output[0]);
        let output_digest = &output[8..];

        zstore.memoize_dag(
            output_tag,
            output_digest,
            record.get_inv_queries("hash3", &toplevel),
            record.get_inv_queries("hash4", &toplevel),
            record.get_inv_queries("hash5", &toplevel),
        );

        let zptr = ZPtr {
            tag: output_tag,
            digest: into_sized(output_digest),
        };

        let hi = zstore.intern_string("hi");
        let x = zstore.intern_symbol(&user_sym("x"), &lang_symbols);
        let expected_args = zstore.intern_list([x]);
        let expected_env = zstore.intern_empty_env();

        let (car, cdr) = zstore.fetch_tuple2(&zptr);
        let (args, body, env) = zstore.fetch_compact110(cdr);

        assert_eq!(car, &hi);
        assert_eq!(args, &expected_args);
        assert_eq!(body, &x);
        assert_eq!(env, &expected_env);
    }

    #[test]
    fn test_fmt() {
        let mut zstore = lurk_zstore();
        let state = &State::init_lurk_state().rccell();

        assert_eq!(zstore.fmt_with_state(state, &zstore.nil), "nil");

        let a_char = ZPtr::char('a');
        assert_eq!(zstore.fmt_with_state(state, &a_char), "'a'");

        let one = ZPtr::num(BabyBear::one());
        assert_eq!(zstore.fmt_with_state(state, &one), "1n");

        let one_u64 = ZPtr::u64(1);
        assert_eq!(zstore.fmt_with_state(state, &one_u64), "1");

        let zero_big_num = ZPtr::big_num([BabyBear::zero(); 8]);
        assert_eq!(zstore.fmt_with_state(state, &zero_big_num), "#0x0");

        let zero_comm = ZPtr::comm([BabyBear::zero(); 8]);
        assert_eq!(zstore.fmt_with_state(state, &zero_comm), "#c0x0");

        let mut one_comm = ZPtr::comm([BabyBear::zero(); 8]);
        one_comm.digest[0] = BabyBear::one();
        assert_eq!(zstore.fmt_with_state(state, &one_comm), "#c0x1");

        let mut preimg = Vec::with_capacity(24);
        preimg.extend([BabyBear::zero(); 8]);
        preimg.extend(ZPtr::num(BabyBear::from_canonical_u32(123)).flatten());
        let digest = lurk_hasher().hash(&preimg).try_into().unwrap();
        assert_eq!(
            zstore.fmt_with_state(state, &ZPtr::big_num(digest)),
            "#0xaa8db8504fa55b480f3da7a75f3480174f28d683f4c3ac451b7cee488d2fe"
        );
        assert_eq!(
            zstore.fmt_with_state(state, &ZPtr::comm(digest)),
            "#c0xaa8db8504fa55b480f3da7a75f3480174f28d683f4c3ac451b7cee488d2fe"
        );

        let empty_str = zstore.intern_string("");
        assert_eq!(zstore.fmt_with_state(state, &empty_str), "\"\"");

        let abc_str = zstore.intern_string("abc");
        assert_eq!(zstore.fmt_with_state(state, &abc_str), "\"abc\"");

        let x = zstore.intern_symbol_no_lang(&state.borrow_mut().intern("x"));
        assert_eq!(zstore.fmt_with_state(state, &x), "x");

        let lambda = zstore.intern_symbol_no_lang(&builtin_sym("lambda"));
        assert_eq!(zstore.fmt_with_state(state, &lambda), "lambda");

        let mlambda = zstore.intern_symbol_no_lang(&builtin_sym("mlambda"));
        assert_eq!(zstore.fmt_with_state(state, &mlambda), "mlambda");

        let hi = zstore.intern_symbol_no_lang(&Symbol::key(&["hi"]));
        assert_eq!(zstore.fmt_with_state(state, &hi), ":hi");

        let pair = zstore.intern_cons(x, hi);
        assert_eq!(zstore.fmt_with_state(state, &pair), "(x . :hi)");

        let list = zstore.intern_list([x, hi]);
        assert_eq!(zstore.fmt_with_state(state, &list), "(x :hi)");

        let args = zstore.intern_list([x]);
        let empty_env = zstore.intern_empty_env();
        let fun = zstore.intern_fun(args, x, empty_env);
        assert_eq!(zstore.fmt_with_state(state, &fun), "<Fun (x) x>");

        assert_eq!(zstore.fmt_with_state(state, &empty_env), "<Env ()>");
        let env = zstore.intern_env(x, one, empty_env);
        assert_eq!(zstore.fmt_with_state(state, &env), "<Env ((x . 1n))>");
    }
}
