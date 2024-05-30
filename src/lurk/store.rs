use elsa::sync::FrozenBTreeMap;
use std::marker::PhantomData;

use anyhow::{bail, Result};
use nom::{sequence::preceded, Parser};
use p3_baby_bear::{BabyBear as F, DiffusionMatrixBabyBear};
use p3_field::{AbstractField, Field};
use p3_poseidon2::{self, Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;
use rand::SeedableRng;
use rand_xoshiro::Xoroshiro128Plus;

use super::{
    parser::{
        syntax::{parse_space, parse_syntax},
        Span,
    },
    state::{lurk_sym, State, StateRcCell},
    symbol::Symbol,
    syntax::Syntax,
};

// Unfortunately these cannot be defined inside `Hasher` because
// of a limitation of const generics
pub const DIGEST: usize = 8;
pub const WIDTH: usize = 24;

pub trait Hasher {
    type F: Field;
    fn hash(fs: &[Self::F]) -> [Self::F; DIGEST] {
        let mut state = [Self::F::zero(); WIDTH];
        for chunk in fs.chunks(WIDTH) {
            for (f, g) in state.iter_mut().zip(chunk.iter()) {
                *f += *g;
            }
            Self::hash_aux(&mut state);
        }
        let mut digest = [Self::F::zero(); DIGEST];
        digest.copy_from_slice(&state[0..DIGEST]);
        digest
    }

    fn hash_ptrs(ptrs: Vec<ZPtr<Self::F>>) -> Payload<Self::F> {
        let mut vec = Vec::with_capacity(ptrs.len() * (1 + DIGEST));
        for ptr in ptrs {
            vec.push(ptr.tag.to_field());
            vec.extend(&ptr.raw.0);
        }
        Payload(Self::hash(&vec))
    }

    fn hash_aux(state: &mut [Self::F; WIDTH]);
}

pub const EXPR_TAG_INIT: u16 = 0b0000_0000_0000_0000;

#[repr(u16)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tag {
    Nil = EXPR_TAG_INIT,
    Cons,
    Sym,
    Fun,
    Num,
    Str,
    Char,
    Comm,
    U64,
    Key,
    Env,
    Err,
    Thunk,
}

impl Tag {
    pub fn to_field<F: Field>(self) -> F {
        F::from_canonical_u16(self as u16)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Payload<F>(pub(crate) [F; DIGEST]);

impl<F: Field> Payload<F> {
    pub fn from_field(f: F) -> Self {
        let mut pay = [F::zero(); DIGEST];
        pay[0] = f;
        Self(pay)
    }

    #[allow(clippy::assertions_on_constants)]
    pub fn from_u64(n: u64) -> Self {
        assert!(DIGEST >= 8);
        let mut pay = [F::zero(); DIGEST];
        let bytes = n.to_le_bytes();
        for i in 0..8 {
            pay[i] = F::from_canonical_u8(bytes[i]);
        }
        Self(pay)
    }

    #[allow(clippy::assertions_on_constants)]
    pub fn from_char(c: char) -> Self {
        assert!(DIGEST >= 4);
        let mut pay = [F::zero(); DIGEST];
        let bytes = (c as u32).to_le_bytes();
        for i in 0..4 {
            pay[i] = F::from_canonical_u8(bytes[i]);
        }
        Self(pay)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ZPtr<F> {
    pub tag: Tag,
    pub raw: Payload<F>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ZExpr<F> {
    // Atoms
    Num(F),
    U64(u64),
    Char(char),
    Nil,
    EmptyStr,
    RootSym,
    RootKey,
    // TODO better error value
    Err(F),
    // Compound data
    Cons {
        head: ZPtr<F>,
        tail: ZPtr<F>,
    },
    Sym {
        head: ZPtr<F>,
        tail: ZPtr<F>,
    },
    Key {
        head: ZPtr<F>,
        tail: ZPtr<F>,
    },
    Str {
        head: ZPtr<F>,
        tail: ZPtr<F>,
    },
    Comm {
        secret: F,
        payload: ZPtr<F>,
    },
    Fun {
        arg: ZPtr<F>,
        body: ZPtr<F>,
        env: ZPtr<F>,
    },
    Env {
        sym: ZPtr<F>,
        val: ZPtr<F>,
        env: ZPtr<F>,
    },
    Thunk {
        body: ZPtr<F>,
        env: ZPtr<F>,
    },
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct ZStore<F: Ord + Clone, H: Hasher<F = F>> {
    pub(crate) map: FrozenBTreeMap<ZPtr<F>, Box<ZExpr<F>>>,
    _p: PhantomData<H>,
}

impl<F: Field + Ord, H: Hasher<F = F>> ZStore<F, H> {
    pub fn new() -> Self {
        ZStore {
            map: FrozenBTreeMap::new(),
            _p: PhantomData,
        }
    }

    pub fn intern_syntax(&self, syn: &Syntax<F>) -> ZPtr<F> {
        match syn {
            Syntax::Num(_, x) => {
                let tag = Tag::Num;
                let raw = Payload::from_field(*x);
                let ptr = ZPtr { tag, raw };
                let expr = ZExpr::Num(*x);
                self.map.insert(ptr, expr.into());
                ptr
            }
            Syntax::U64(_, x) => {
                let tag = Tag::U64;
                let raw = Payload::from_u64(*x);
                let ptr = ZPtr { tag, raw };
                let expr = ZExpr::U64(*x);
                self.map.insert(ptr, expr.into());
                ptr
            }
            Syntax::Char(_, x) => self.intern_char(*x),
            Syntax::Symbol(_, x) => self.intern_symbol(x),
            Syntax::String(_, x) => self.intern_string(x),
            Syntax::Quote(_, x) => {
                let nil = self.intern_nil();
                let sym = self.intern_symbol(&lurk_sym("quote"));
                let x = self.intern_syntax(x);
                self.intern_list(vec![sym, x], nil)
            }
            Syntax::List(_, xs) => {
                let nil = self.intern_nil();
                let xs = xs.iter().map(|x| self.intern_syntax(x)).collect::<Vec<_>>();
                self.intern_list(xs, nil)
            }
            Syntax::Improper(_, xs, y) => {
                let y = self.intern_syntax(y);
                let xs = xs.iter().map(|x| self.intern_syntax(x)).collect::<Vec<_>>();
                self.intern_list(xs, y)
            }
        }
    }

    pub fn intern_list(&self, xs: Vec<ZPtr<F>>, y: ZPtr<F>) -> ZPtr<F> {
        xs.into_iter()
            .rev()
            .fold(y, |acc, elt| self.intern_cons(Tag::Cons, elt, acc))
    }

    pub fn intern_cons(&self, tag: Tag, head: ZPtr<F>, tail: ZPtr<F>) -> ZPtr<F> {
        let expr = match tag {
            Tag::Cons => ZExpr::Cons { head, tail },
            Tag::Sym => ZExpr::Sym { head, tail },
            Tag::Str => ZExpr::Str { head, tail },
            Tag::Nil => ZExpr::Nil,
            _ => panic!("Not a cons tag"),
        };
        let raw = H::hash_ptrs(vec![head, tail]);
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_nil(&self) -> ZPtr<F> {
        self.intern_symbol(&lurk_sym("nil"))
    }

    pub fn intern_symbol(&self, sym: &Symbol) -> ZPtr<F> {
        if sym.path().is_empty() {
            let tag = if sym.is_keyword() { Tag::Key } else { Tag::Sym };
            return self.intern_null(tag);
        };
        let is_nil = sym == &lurk_sym("nil");
        let mut ptr = self.intern_null(Tag::Sym);
        let mut iter = sym.path().iter().rev().peekable();
        while let Some(s) = iter.next() {
            let s = self.intern_string(s);
            if sym.is_keyword() && iter.peek().is_none() {
                ptr = self.intern_cons(Tag::Key, s, ptr);
            } else if is_nil && iter.peek().is_none() {
                ptr = self.intern_cons(Tag::Nil, s, ptr);
            } else {
                ptr = self.intern_cons(Tag::Sym, s, ptr);
            }
        }
        ptr
    }

    pub fn intern_char(&self, c: char) -> ZPtr<F> {
        let tag = Tag::Char;
        let raw = Payload::from_char(c);
        let ptr = ZPtr { tag, raw };
        let expr = ZExpr::Char(c);
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_null(&self, tag: Tag) -> ZPtr<F> {
        let expr = match tag {
            Tag::Str => ZExpr::EmptyStr,
            Tag::Sym => ZExpr::RootSym,
            Tag::Key => ZExpr::RootKey,
            _ => panic!("Not a string/symbol tag"),
        };
        let raw = Payload([F::zero(); DIGEST]);
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_string(&self, s: &str) -> ZPtr<F> {
        let tag = Tag::Str;
        let empty_str = self.intern_null(tag);
        s.chars().rev().fold(empty_str, |acc, c| {
            let c = self.intern_char(c);
            self.intern_cons(tag, c, acc)
        })
    }

    pub fn intern_comm(&self, secret: F, payload: ZPtr<F>) -> ZPtr<F> {
        let tag = Tag::Comm;
        let expr = ZExpr::Comm { secret, payload };
        let mut vec = Vec::with_capacity(2 + DIGEST);
        vec.push(secret);
        vec.push(payload.tag.to_field());
        vec.extend(&payload.raw.0);
        let raw = Payload(H::hash(&vec));
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_fun(&self, arg: ZPtr<F>, body: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        let tag = Tag::Fun;
        let expr = ZExpr::Fun { arg, body, env };
        let raw = H::hash_ptrs(vec![arg, body, env]);
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_thunk(&self, body: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        let tag = Tag::Thunk;
        let expr = ZExpr::Thunk { body, env };
        let raw = H::hash_ptrs(vec![body, env]);
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn intern_env(&self, sym: ZPtr<F>, val: ZPtr<F>, env: ZPtr<F>) -> ZPtr<F> {
        let tag = Tag::Env;
        let expr = ZExpr::Env { sym, val, env };
        let raw = H::hash_ptrs(vec![sym, val, env]);
        let ptr = ZPtr { tag, raw };
        self.map.insert(ptr, expr.into());
        ptr
    }

    pub fn read_with_state(&self, state: StateRcCell, input: &str) -> Result<ZPtr<F>> {
        match preceded(parse_space, parse_syntax(state, false, false)).parse(Span::new(input)) {
            Ok((_, x)) => Ok(self.intern_syntax(&x)),
            Err(e) => bail!("{}", e),
        }
    }

    pub fn read(&self, input: &str) -> Result<ZPtr<F>> {
        let state = State::init_lurk_state().rccell();
        self.read_with_state(state, input)
    }
}

pub struct PoseidonBabyBearHasher();

impl Hasher for PoseidonBabyBearHasher {
    type F = F;
    fn hash_aux(state: &mut [F; WIDTH]) {
        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let external_linear_layer = Poseidon2ExternalMatrixGeneral;
        let internal_linear_layer = DiffusionMatrixBabyBear;

        let poseidon = Poseidon2::<_, _, _, WIDTH, 7>::new_from_rng_128(
            external_linear_layer,
            internal_linear_layer,
            &mut rng,
        );
        poseidon.permute_mut(state);
    }
}
