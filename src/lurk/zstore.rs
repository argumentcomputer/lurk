use anyhow::{bail, Result};
use nom::{sequence::preceded, Parser};
use once_cell::sync::OnceCell;
use p3_field::{AbstractField, Field};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use crate::{
    lair::hasher::Hasher,
    lurk::{
        parser::{
            syntax::{parse_maybe_meta, parse_space},
            Span,
        },
        state::{lurk_sym, State, StateRcCell, LURK_PACKAGE_SYMBOLS_NAMES},
        symbol::Symbol,
        syntax::Syntax,
        tag::Tag,
    },
};

const DIGEST_SIZE: usize = 8;

const ZPTR_SIZE: usize = 2 * DIGEST_SIZE;
// const COMM_PREIMG_SIZE: usize = DIGEST_SIZE + ZPTR_SIZE;
const TUPLE2_SIZE: usize = 2 * ZPTR_SIZE;
const TUPLE3_SIZE: usize = 3 * ZPTR_SIZE;

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

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ZPtr<F> {
    pub tag: Tag,
    pub digest: [F; DIGEST_SIZE],
}

impl<F: AbstractField + Copy> ZPtr<F> {
    pub fn into_inner(self) -> (Tag, [F; DIGEST_SIZE]) {
        let ZPtr { tag, digest } = self;
        (tag, digest)
    }

    fn null(tag: Tag) -> Self {
        Self {
            tag,
            digest: [F::zero(); DIGEST_SIZE],
        }
    }

    fn num(f: F) -> Self {
        Self {
            tag: Tag::Num,
            digest: digest_from_field(f),
        }
    }

    fn char(c: char) -> Self {
        Self {
            tag: Tag::Char,
            digest: digest_from_field(F::from_canonical_u32(c as u32)),
        }
    }

    fn u64(u: u64) -> Self {
        Self {
            tag: Tag::U64,
            digest: u.to_le_bytes().map(F::from_canonical_u8),
        }
    }
}

impl<F: AbstractField + Copy> ZPtr<F> {
    fn flatten(&self) -> [F; ZPTR_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_tag(self.tag);
        buffer.write_slice(&self.digest);
        buffer.extract()
    }

    fn flatten2(a: &ZPtr<F>, b: &ZPtr<F>) -> [F; TUPLE2_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&a.flatten());
        buffer.write_slice(&b.flatten());
        buffer.extract()
    }

    fn flatten3(a: &ZPtr<F>, b: &ZPtr<F>, c: &ZPtr<F>) -> [F; TUPLE3_SIZE] {
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&a.flatten());
        buffer.write_slice(&b.flatten());
        buffer.write_slice(&c.flatten());
        buffer.extract()
    }
}

#[derive(Serialize, Deserialize)]
pub enum ZPtrType<F> {
    Atom,
    Tuple2(ZPtr<F>, ZPtr<F>),
    Tuple3(ZPtr<F>, ZPtr<F>, ZPtr<F>),
}

#[derive(Default)]
pub struct ZStore<F, H: Hasher<F>> {
    hasher: H,
    dag: FxHashMap<ZPtr<F>, ZPtrType<F>>,
    // comms: FxHashMap<[F; DIGEST_SIZE], ([F; DIGEST_SIZE], ZPtr<F>)>,
    // comm_hashes: FxHashMap<[F; COMM_PREIMG_SIZE], [F; DIGEST_SIZE]>,
    tuple2_hashes: FxHashMap<[F; TUPLE2_SIZE], [F; DIGEST_SIZE]>,
    tuple3_hashes: FxHashMap<[F; TUPLE3_SIZE], [F; DIGEST_SIZE]>,
    str_cache: FxHashMap<String, ZPtr<F>>,
    sym_cache: FxHashMap<Symbol, ZPtr<F>>,
    syn_cache: FxHashMap<Syntax<F>, ZPtr<F>>,
}

static NIL: OnceCell<Symbol> = OnceCell::new();
fn nil() -> &'static Symbol {
    NIL.get_or_init(|| lurk_sym("nil"))
}

static QUOTE: OnceCell<Symbol> = OnceCell::new();
fn quote() -> &'static Symbol {
    QUOTE.get_or_init(|| lurk_sym("quote"))
}

static BUILTIN_VEC: OnceCell<Vec<Symbol>> = OnceCell::new();
fn builtin_vec() -> &'static Vec<Symbol> {
    BUILTIN_VEC.get_or_init(|| {
        LURK_PACKAGE_SYMBOLS_NAMES
            .into_iter()
            .filter(|sym| sym != &"nil")
            .map(lurk_sym)
            .collect()
    })
}

impl<F: Field, H: Hasher<F>> ZStore<F, H> {
    fn hash2(&mut self, preimg: [F; TUPLE2_SIZE]) -> [F; DIGEST_SIZE] {
        if let Some(img) = self.tuple2_hashes.get(&preimg) {
            return *img;
        }
        let img = self.hasher.hash(&preimg);
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&img);
        let digest = buffer.extract();
        self.tuple2_hashes.insert(preimg, digest);
        digest
    }

    fn hash3(&mut self, preimg: [F; TUPLE3_SIZE]) -> [F; DIGEST_SIZE] {
        if let Some(limbs) = self.tuple3_hashes.get(&preimg) {
            return *limbs;
        }
        let img = self.hasher.hash(&preimg);
        let mut buffer = SizedBuffer::default();
        buffer.write_slice(&img);
        let digest = buffer.extract();
        self.tuple3_hashes.insert(preimg, digest);
        digest
    }

    fn intern_tuple2(&mut self, tag: Tag, a: ZPtr<F>, b: ZPtr<F>) -> ZPtr<F> {
        let preimg = ZPtr::flatten2(&a, &b);
        let digest = self.hash2(preimg);
        let zptr = ZPtr { tag, digest };
        self.dag.insert(zptr, ZPtrType::Tuple2(a, b));
        zptr
    }

    fn intern_tuple3(&mut self, tag: Tag, a: ZPtr<F>, b: ZPtr<F>, c: ZPtr<F>) -> ZPtr<F> {
        let preimg = ZPtr::flatten3(&a, &b, &c);
        let digest = self.hash3(preimg);
        let zptr = ZPtr { tag, digest };
        self.dag.insert(zptr, ZPtrType::Tuple3(a, b, c));
        zptr
    }

    #[inline]
    pub fn memoize_atom_dag(&mut self, zptr: ZPtr<F>) -> ZPtr<F> {
        self.dag.insert(zptr, ZPtrType::Atom);
        zptr
    }

    #[inline]
    pub fn intern_null(&mut self, tag: Tag) -> ZPtr<F> {
        self.memoize_atom_dag(ZPtr::null(tag))
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

    pub fn intern_string(&mut self, s: &str) -> ZPtr<F> {
        if let Some(zptr) = self.str_cache.get(s).copied() {
            return zptr;
        }
        let zptr = s.chars().rev().fold(self.intern_null(Tag::Str), |acc, c| {
            self.intern_tuple2(Tag::Str, ZPtr::char(c), acc)
        });
        self.str_cache.insert(s.to_string(), zptr);
        zptr
    }

    pub fn intern_symbol(&mut self, sym: &Symbol) -> ZPtr<F> {
        if let Some(zptr) = self.sym_cache.get(sym).copied() {
            return zptr;
        }
        let is_keyword = sym.is_keyword();
        let zptr = {
            if sym.path().is_empty() {
                let tag = if is_keyword { Tag::Key } else { Tag::Sym };
                self.intern_null(tag)
            } else {
                let is_nil = sym == nil();
                let is_builtin = builtin_vec().contains(sym);
                let mut zptr = self.intern_null(Tag::Sym);
                let mut iter = sym.path().iter().peekable();
                while let Some(s) = iter.next() {
                    let is_last = iter.peek().is_none();
                    let str_zptr = self.intern_string(s);
                    let tag = if is_last {
                        if is_nil {
                            Tag::Nil
                        } else if is_builtin {
                            Tag::Builtin
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
    pub fn intern_nil(&mut self) -> ZPtr<F> {
        self.intern_symbol(nil())
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
        let nil = self.intern_nil();
        self.intern_list_full(xs, nil)
    }

    #[inline]
    pub fn intern_fun(&mut self, args: ZPtr<F>, body: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        self.intern_tuple3(Tag::Fun, args, body, env)
    }

    fn intern_syntax(&mut self, syn: &Syntax<F>) -> ZPtr<F> {
        if let Some(zptr) = self.syn_cache.get(syn).copied() {
            return zptr;
        }
        let zptr = match syn {
            Syntax::Num(_, f) => self.intern_num(*f),
            Syntax::Char(_, c) => self.intern_char(*c),
            Syntax::U64(_, u) => self.intern_u64(*u),
            Syntax::String(_, s) => self.intern_string(s),
            Syntax::Symbol(_, s) => self.intern_symbol(s),
            Syntax::List(_, xs) => {
                let xs = xs.iter().map(|x| self.intern_syntax(x)).collect::<Vec<_>>();
                self.intern_list(xs)
            }
            Syntax::Improper(_, xs, y) => {
                let xs = xs.iter().map(|x| self.intern_syntax(x)).collect::<Vec<_>>();
                let y = self.intern_syntax(y);
                self.intern_list_full(xs, y)
            }
            Syntax::Quote(_, x) => {
                let quote = self.intern_symbol(quote());
                let x = self.intern_syntax(x);
                self.intern_list([quote, x])
            }
        };
        self.syn_cache.insert(syn.clone(), zptr);
        zptr
    }

    #[inline]
    pub fn read_maybe_meta_with_state(
        &mut self,
        state: StateRcCell,
        input: &str,
    ) -> Result<(bool, ZPtr<F>)> {
        match preceded(parse_space, parse_maybe_meta(state, false)).parse(Span::new(input)) {
            Err(e) => bail!("{}", e),
            Ok((_, None)) => bail!("Read EOF error"),
            Ok((_, Some((is_meta, syn)))) => Ok((is_meta, self.intern_syntax(&syn))),
        }
    }

    #[inline]
    pub fn read_maybe_meta(&mut self, input: &str) -> Result<(bool, ZPtr<F>)> {
        self.read_maybe_meta_with_state(State::init_lurk_state().rccell(), input)
    }

    #[inline]
    pub fn read_with_state(&mut self, state: StateRcCell, input: &str) -> Result<ZPtr<F>> {
        let (is_meta, zptr) = self.read_maybe_meta_with_state(state, input)?;
        assert!(!is_meta);
        Ok(zptr)
    }

    #[inline]
    pub fn read(&mut self, input: &str) -> Result<ZPtr<F>> {
        self.read_with_state(State::init_lurk_state().rccell(), input)
    }

    #[inline]
    pub fn tuple2_hashes(&self) -> &FxHashMap<[F; TUPLE2_SIZE], [F; DIGEST_SIZE]> {
        &self.tuple2_hashes
    }

    #[inline]
    pub fn tuple3_hashes(&self) -> &FxHashMap<[F; TUPLE3_SIZE], [F; DIGEST_SIZE]> {
        &self.tuple3_hashes
    }
}
