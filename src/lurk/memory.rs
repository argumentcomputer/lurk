use std::{collections::BTreeMap, marker::PhantomData};

use p3_field::PrimeField;

use crate::{
    lair::{
        execute::{mem_init, mem_load, mem_store, MemMap},
        List,
    },
    lurk::store::ZExpr,
};

use super::store::{Hasher, Payload, Tag, ZPtr, ZStore, DIGEST};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MPtr<F> {
    pub(crate) tag: F,
    pub(crate) raw: F,
}

pub struct Memory<F, H> {
    pub map: Vec<MemMap<F>>,
    pub cache: BTreeMap<ZPtr<F>, MPtr<F>>,
    pub _p: PhantomData<H>,
}

impl<F: PrimeField, H: Hasher<F = F>> Memory<F, H> {
    pub fn init() -> Self {
        let map = mem_init();
        let cache = BTreeMap::new();
        let _p = PhantomData;
        Self { map, cache, _p }
    }

    pub fn load(&mut self, len: usize, ptr: F) -> &[F] {
        mem_load(&mut self.map, len, ptr)
    }

    pub fn store(&mut self, args: List<F>) -> F {
        mem_store(&mut self.map, args)
    }

    pub fn read_and_ingress(&mut self, input: &str, store: &ZStore<F, H>) -> Option<MPtr<F>> {
        let ptr = store.read(input).ok()?;
        Some(self.ingress(ptr, store))
    }

    pub fn ingress(&mut self, ptr: ZPtr<F>, store: &ZStore<F, H>) -> MPtr<F> {
        if let Some(mptr) = self.cache.get(&ptr) {
            return *mptr;
        }
        let tag = ptr.tag.to_field();
        let Some(expr) = store.map.get(&ptr) else {
            // Opaque pointers have a negative tag to distinguish them from non-opaques
            // and points to the hash digest in memory
            let tag = F::neg_one() - tag;
            let raw = self.store(ptr.raw.0.into());
            return MPtr { tag, raw };
        };
        let mptr = match expr {
            ZExpr::Num(x) | ZExpr::Err(x) => MPtr { tag, raw: *x },
            ZExpr::EmptyStr | ZExpr::RootSym | ZExpr::RootKey => MPtr {
                tag,
                raw: F::zero(),
            },
            ZExpr::Char(_) | ZExpr::Nil | ZExpr::U64(_) => {
                let raw = self.store(ptr.raw.0.into());
                MPtr { tag, raw }
            }
            ZExpr::Cons { head, tail } => {
                let head = self.ingress(*head, store);
                let tail = self.ingress(*tail, store);
                let args = [head.tag, head.raw, tail.tag, tail.raw].into();
                let raw = self.store(args);
                MPtr { tag, raw }
            }
            ZExpr::Key { head, tail } | ZExpr::Str { head, tail } | ZExpr::Sym { head, tail } => {
                // Keys, strings and symbols have null pointers. We add one
                // to the memory address so that we can differentiate null
                // pointers from actual pointers
                let head = self.ingress(*head, store);
                let tail = self.ingress(*tail, store);
                let args = [head.tag, head.raw, tail.tag, tail.raw].into();
                let raw = self.store(args) + F::one();
                assert_ne!(raw, F::zero());
                MPtr { tag, raw }
            }
            ZExpr::Comm { secret, payload } => {
                let payload = self.ingress(*payload, store);
                let args = [*secret, payload.tag, payload.raw].into();
                let raw = self.store(args);
                MPtr { tag, raw }
            }
            ZExpr::Fun { arg, body, env } => {
                let arg = self.ingress(*arg, store);
                let body = self.ingress(*body, store);
                let env = self.ingress(*env, store);
                let args = [arg.tag, arg.raw, body.tag, body.raw, env.tag, env.raw];
                let raw = self.store(args.into());
                MPtr { tag, raw }
            }
            ZExpr::Thunk { body, env } => {
                let body = self.ingress(*body, store);
                let env = self.ingress(*env, store);
                let args = [body.tag, body.raw, env.tag, env.raw];
                let raw = self.store(args.into());
                MPtr { tag, raw }
            }
            ZExpr::Env { sym, val, env } => {
                let sym = self.ingress(*sym, store);
                let val = self.ingress(*val, store);
                let env = self.ingress(*env, store);
                let args = [sym.tag, sym.raw, val.tag, val.raw, env.tag, env.raw];
                let raw = self.store(args.into());
                MPtr { tag, raw }
            }
        };
        self.cache.insert(ptr, mptr);
        mptr
    }

    fn load_immediate(&mut self, tag: Tag, idx: F) -> ZPtr<F> {
        let mut digest = [F::zero(); DIGEST];
        digest.copy_from_slice(self.load(DIGEST, idx));
        let raw = Payload(digest);
        ZPtr { tag, raw }
    }

    pub fn egress(&mut self, ptr: MPtr<F>, store: &ZStore<F, H>) -> ZPtr<F> {
        let (is_opaque, tag) = Tag::from_field_maybe_opaque(ptr.tag).unwrap();
        if is_opaque {
            return self.load_immediate(tag, ptr.raw);
        }
        match tag {
            Tag::Num | Tag::Err => {
                let raw = Payload::from_field(ptr.raw);
                ZPtr { tag, raw }
            }
            Tag::Nil | Tag::Char | Tag::U64 => self.load_immediate(tag, ptr.raw),
            Tag::Cons => {
                let [head_tag, head_raw, tail_tag, tail_raw] =
                    self.load(4, ptr.raw).try_into().unwrap();
                let head = self.egress(
                    MPtr {
                        tag: head_tag,
                        raw: head_raw,
                    },
                    store,
                );
                let tail = self.egress(
                    MPtr {
                        tag: tail_tag,
                        raw: tail_raw,
                    },
                    store,
                );
                store.intern_cons(tag, head, tail)
            }
            Tag::Str | Tag::Key | Tag::Sym => {
                if ptr.raw.is_zero() {
                    let raw = Payload::from_field(F::zero());
                    return ZPtr { tag, raw };
                }
                let idx = ptr.raw - F::one();
                let [head_tag, head_raw, tail_tag, tail_raw] =
                    self.load(4, idx).try_into().unwrap();
                let head = self.egress(
                    MPtr {
                        tag: head_tag,
                        raw: head_raw,
                    },
                    store,
                );
                let tail = self.egress(
                    MPtr {
                        tag: tail_tag,
                        raw: tail_raw,
                    },
                    store,
                );
                store.intern_cons(tag, head, tail)
            }
            Tag::Comm => {
                let [secret, payload_tag, payload_raw] = self.load(3, ptr.raw).try_into().unwrap();
                let payload = self.egress(
                    MPtr {
                        tag: payload_tag,
                        raw: payload_raw,
                    },
                    store,
                );
                store.intern_comm(secret, payload)
            }
            Tag::Fun => {
                let [arg_tag, arg_raw, body_tag, body_raw, env_tag, env_raw] =
                    self.load(6, ptr.raw).try_into().unwrap();
                let arg = self.egress(
                    MPtr {
                        tag: arg_tag,
                        raw: arg_raw,
                    },
                    store,
                );
                let body = self.egress(
                    MPtr {
                        tag: body_tag,
                        raw: body_raw,
                    },
                    store,
                );
                let env = self.egress(
                    MPtr {
                        tag: env_tag,
                        raw: env_raw,
                    },
                    store,
                );
                store.intern_fun(arg, body, env)
            }
            Tag::Thunk => {
                let [body_tag, body_raw, env_tag, env_raw] =
                    self.load(4, ptr.raw).try_into().unwrap();
                let body = self.egress(
                    MPtr {
                        tag: body_tag,
                        raw: body_raw,
                    },
                    store,
                );
                let env = self.egress(
                    MPtr {
                        tag: env_tag,
                        raw: env_raw,
                    },
                    store,
                );
                store.intern_thunk(body, env)
            }
            Tag::Env => {
                let [sym_tag, sym_raw, val_tag, val_raw, env_tag, env_raw] =
                    self.load(6, ptr.raw).try_into().unwrap();
                let sym = self.egress(
                    MPtr {
                        tag: sym_tag,
                        raw: sym_raw,
                    },
                    store,
                );
                let val = self.egress(
                    MPtr {
                        tag: val_tag,
                        raw: val_raw,
                    },
                    store,
                );
                let env = self.egress(
                    MPtr {
                        tag: env_tag,
                        raw: env_raw,
                    },
                    store,
                );
                store.intern_env(sym, val, env)
            }
        }
    }
}

impl Tag {
    pub fn from_field<F: PrimeField>(f: F) -> Option<Self> {
        // TODO use try_from
        let f: u16 = f.as_canonical_biguint().try_into().ok()?;
        const NIL: u16 = Tag::Nil as u16;
        const CONS: u16 = Tag::Cons as u16;
        const SYM: u16 = Tag::Sym as u16;
        const FUN: u16 = Tag::Fun as u16;
        const NUM: u16 = Tag::Num as u16;
        const STR: u16 = Tag::Str as u16;
        const CHAR: u16 = Tag::Char as u16;
        const COMM: u16 = Tag::Comm as u16;
        const U64: u16 = Tag::U64 as u16;
        const KEY: u16 = Tag::Key as u16;
        const ENV: u16 = Tag::Env as u16;
        const ERR: u16 = Tag::Err as u16;
        const THUNK: u16 = Tag::Thunk as u16;
        match f {
            NIL => Some(Tag::Nil),
            CONS => Some(Tag::Cons),
            SYM => Some(Tag::Sym),
            FUN => Some(Tag::Fun),
            NUM => Some(Tag::Num),
            STR => Some(Tag::Str),
            CHAR => Some(Tag::Char),
            COMM => Some(Tag::Comm),
            U64 => Some(Tag::U64),
            KEY => Some(Tag::Key),
            ENV => Some(Tag::Env),
            ERR => Some(Tag::Err),
            THUNK => Some(Tag::Thunk),
            _ => None,
        }
    }

    pub fn from_field_maybe_opaque<F: PrimeField>(f: F) -> Option<(bool, Self)> {
        Tag::from_field(f)
            .map(|t| (false, t))
            .or(Tag::from_field(F::neg_one() - f).map(|t| (true, t)))
    }
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::lurk::store::PoseidonBabyBearHasher;

    use super::*;
    #[test]
    fn ingress_egress_test() {
        let store = &ZStore::<BabyBear, PoseidonBabyBearHasher>::new();
        let ptr1 = store.read("()").unwrap();
        let ptr2 = store.read("(+ 1 2)").unwrap();
        let ptr3 = store.read("\"test string\"").unwrap();
        let ptr4 = store.read("TestSymbol").unwrap();

        let mem = &mut Memory::init();
        let mptr1 = mem.ingress(ptr1, store);
        let mptr2 = mem.ingress(ptr2, store);
        let mptr3 = mem.ingress(ptr3, store);
        let mptr4 = mem.ingress(ptr4, store);

        assert_eq!(ptr1, mem.egress(mptr1, store));
        assert_eq!(ptr2, mem.egress(mptr2, store));
        assert_eq!(ptr3, mem.egress(mptr3, store));
        assert_eq!(ptr4, mem.egress(mptr4, store));
    }
}
