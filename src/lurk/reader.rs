use anyhow::{bail, Result};
use fxhash::FxHashMap;
use nom::{sequence::preceded, Parser};
use once_cell::sync::OnceCell;
use p3_baby_bear::BabyBear as F;
use p3_field::AbstractField;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use crate::poseidon::{
    config::{BabyBearConfig32, InternalDiffusion},
    Poseidon2Chip,
};

use super::{
    parser::{
        syntax::{parse_space, parse_syntax},
        Span,
    },
    state::{lurk_sym, StateRcCell},
    symbol::Symbol,
    syntax::Syntax,
    zstore::Tag,
};

const PREIMG_SIZE: usize = 32;
const IMG_SIZE: usize = 8;

struct SizedBuffer<const N: usize> {
    data: [F; N],
    pos: usize,
}

impl<const N: usize> Default for SizedBuffer<N> {
    fn default() -> Self {
        Self {
            data: [F::zero(); N],
            pos: 0,
        }
    }
}

impl<const N: usize> SizedBuffer<N> {
    fn advance(&mut self, n: usize) {
        self.pos += n;
    }

    fn read_f(&mut self, f: F) {
        self.data[self.pos] = f;
        self.advance(1);
    }

    fn read_tag(&mut self, tag: Tag) {
        self.read_f(tag.to_field());
        self.advance(7);
    }

    fn read_iter<I: IntoIterator<Item = F>>(&mut self, iter: I) {
        iter.into_iter().for_each(|f| self.read_f(f))
    }

    fn read_u64(&mut self, u: u64) {
        self.read_iter(u.to_le_bytes().map(F::from_canonical_u8))
    }

    fn read_char(&mut self, c: char) {
        self.read_iter((c as u32).to_le_bytes().map(F::from_canonical_u8));
        self.advance(4);
    }

    fn extract(self) -> [F; N] {
        let Self { data, pos: _ } = self;
        data
    }
}

struct Reader {
    hasher: Poseidon2<F, Poseidon2ExternalMatrixGeneral, InternalDiffusion, PREIMG_SIZE, 7>,
    hashes: FxHashMap<[F; PREIMG_SIZE], [F; IMG_SIZE]>,
    syn_cache: FxHashMap<Syntax<F>, (Tag, [F; IMG_SIZE])>,
    str_cache: FxHashMap<String, [F; IMG_SIZE]>,
    sym_cache: FxHashMap<Symbol, [F; IMG_SIZE]>,
}

impl Default for Reader {
    fn default() -> Self {
        Self {
            hasher: Poseidon2Chip::<BabyBearConfig32>::default().hasher(),
            hashes: FxHashMap::default(),
            syn_cache: FxHashMap::default(),
            str_cache: FxHashMap::default(),
            sym_cache: FxHashMap::default(),
        }
    }
}

static NIL: OnceCell<Symbol> = OnceCell::new();
fn nil() -> &'static Symbol {
    NIL.get_or_init(|| lurk_sym("nil"))
}

fn get_symbol_tag(symbol: &Symbol) -> Tag {
    if symbol.is_keyword() {
        Tag::Key
    } else if symbol == nil() {
        Tag::Nil
    } else {
        Tag::Sym
    }
}

impl Reader {
    fn hash(&mut self, fs: [F; PREIMG_SIZE]) -> [F; IMG_SIZE] {
        if let Some(digest) = self.hashes.get(&fs) {
            return *digest;
        }
        let mut buffer = SizedBuffer::<IMG_SIZE>::default();
        buffer.read_iter(self.hasher.permute(fs).into_iter().take(IMG_SIZE));
        let digest = buffer.extract();
        self.hashes.insert(fs, digest);
        digest
    }

    fn read_string(&mut self, s: &str) -> [F; IMG_SIZE] {
        if let Some(digest) = self.str_cache.get(s) {
            return *digest;
        }
        let digest = s.chars().rev().fold([F::zero(); IMG_SIZE], |acc, c| {
            let mut buffer = SizedBuffer::<PREIMG_SIZE>::default();
            buffer.read_tag(Tag::Char);
            buffer.read_char(c);
            buffer.read_tag(Tag::Str);
            buffer.read_iter(acc);
            let preimg = buffer.extract();
            let img = self.hash(preimg);
            self.hashes.insert(preimg, img);
            img
        });
        self.str_cache.insert(s.to_string(), digest);
        digest
    }

    fn read_symbol(&mut self, s: &Symbol) -> [F; IMG_SIZE] {
        if let Some(digest) = self.sym_cache.get(s) {
            return *digest;
        }
        let digest = s.path().iter().fold([F::zero(); IMG_SIZE], |acc, s| {
            let mut buffer = SizedBuffer::<PREIMG_SIZE>::default();
            buffer.read_tag(Tag::Str);
            buffer.read_iter(self.read_string(s));
            buffer.read_tag(Tag::Sym);
            buffer.read_iter(acc);
            let preimg = buffer.extract();
            let img = self.hash(preimg);
            self.hashes.insert(preimg, img);
            img
        });
        self.sym_cache.insert(s.clone(), digest);
        digest
    }

    fn hash_list(
        &mut self,
        list: Vec<(Tag, [F; IMG_SIZE])>,
        last: (Tag, [F; IMG_SIZE]),
    ) -> (Tag, [F; IMG_SIZE]) {
        list.into_iter()
            .rev()
            .fold(last, |(tag_acc, digest_acc), (tag, digest)| {
                let mut buffer = SizedBuffer::<PREIMG_SIZE>::default();
                buffer.read_tag(tag);
                buffer.read_iter(digest);
                buffer.read_tag(tag_acc);
                buffer.read_iter(digest_acc);
                let preimg = buffer.extract();
                let img = self.hash(preimg);
                self.hashes.insert(preimg, img);
                (Tag::Cons, img)
            })
    }

    fn read_syntax(&mut self, syn: &Syntax<F>) -> (Tag, [F; IMG_SIZE]) {
        if let Some(res) = self.syn_cache.get(syn) {
            return *res;
        }
        let res = match syn {
            Syntax::Num(_, f) => {
                let mut buffer = SizedBuffer::<IMG_SIZE>::default();
                buffer.read_f(*f);
                (Tag::Num, buffer.extract())
            }
            Syntax::U64(_, u) => {
                let mut buffer = SizedBuffer::<IMG_SIZE>::default();
                buffer.read_u64(*u);
                (Tag::U64, buffer.extract())
            }
            Syntax::Char(_, c) => {
                let mut buffer = SizedBuffer::<IMG_SIZE>::default();
                buffer.read_char(*c);
                (Tag::Char, buffer.extract())
            }
            Syntax::String(_, s) => (Tag::Str, self.read_string(s)),
            Syntax::Symbol(_, s) => (get_symbol_tag(s), self.read_symbol(s)),
            Syntax::List(_, xs) => {
                let nil_hash = self.read_symbol(nil());
                let limbs = xs.iter().map(|x| self.read_syntax(x)).collect();
                self.hash_list(limbs, (Tag::Nil, nil_hash))
            }
            Syntax::Improper(_, xs, y) => {
                let last = self.read_syntax(y);
                let limbs = xs.iter().map(|x| self.read_syntax(x)).collect();
                self.hash_list(limbs, last)
            }
            Syntax::Quote(_, x) => {
                let nil_hash = self.read_symbol(nil());
                let quote_hash = self.read_symbol(&lurk_sym("quote"));
                let x_hash = self.read_syntax(x);
                self.hash_list(vec![(Tag::Sym, quote_hash), x_hash], (Tag::Nil, nil_hash))
            }
        };
        self.syn_cache.insert(syn.clone(), res);
        res
    }
}

pub struct ReadData {
    pub tag: F,
    pub digest: [F; IMG_SIZE],
    pub hashes: FxHashMap<[F; PREIMG_SIZE], [F; IMG_SIZE]>,
}

pub fn read(state: StateRcCell, input: &str) -> Result<ReadData> {
    match preceded(parse_space, parse_syntax(state, false, false)).parse(Span::new(input)) {
        Err(e) => bail!("{}", e),
        Ok((_, x)) => {
            let mut reader = Reader::default();
            let (tag, digest) = reader.read_syntax(&x);
            let read_data = ReadData {
                tag: tag.to_field(),
                digest,
                hashes: reader.hashes,
            };
            Ok(read_data)
        }
    }
}