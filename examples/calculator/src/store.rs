use p3_field::Field;

use loam::{
    pointers::GPtr,
    store_core::{StoreCore, StoreHasher},
};

use super::{
    dummy_hasher::DummyHasher,
    pointers::{Ptr, Tag},
};

impl<F: Field> StoreHasher<Tag, F> for DummyHasher {
    fn hash_ptrs(&self, ptrs: Vec<GPtr<Tag, F>>) -> F {
        assert_eq!(ptrs.len(), 2);
        Self::hash([
            ptrs[0].tag().field(),
            ptrs[0].val,
            ptrs[1].tag().field(),
            ptrs[1].val,
        ])
    }

    fn hash_compact(&self, _: F, _: Tag, _: F, _: F) -> F {
        todo!()
    }

    fn hash_commitment(&self, _: F, _: GPtr<Tag, F>) -> F {
        todo!()
    }
}

#[derive(Default)]
pub(crate) struct Store<F: Field> {
    pub(crate) core: StoreCore<Tag, F, DummyHasher>,
}

impl<F: Field> Store<F> {
    #[inline]
    pub(crate) fn nil(&self) -> Ptr {
        self.core.intern_atom(Tag::Nil, F::zero())
    }

    #[inline]
    pub(crate) fn get_num(&self, ptr: &Ptr) -> &F {
        self.core.expect_digest(ptr.val().get_atom_idx().unwrap())
    }

    #[inline]
    pub(crate) fn num(&self, f: F) -> Ptr {
        self.core.intern_atom(Tag::Num, f)
    }

    #[inline]
    pub(crate) fn cons(&self, car: Ptr, cdr: Ptr) -> Ptr {
        self.core.intern_tuple2([car, cdr], Tag::Cons, None)
    }

    #[inline]
    pub(crate) fn decons(&self, ptr: &Ptr) -> &[Ptr; 2] {
        self.core.expect_tuple2(ptr.val().get_tuple2_idx().unwrap())
    }

    pub(crate) fn to_scalar_vector(&self, ptrs: &[Ptr]) -> Vec<F> {
        ptrs.iter()
            .fold(Vec::with_capacity(2 * ptrs.len()), |mut acc, ptr| {
                let z_ptr = self.core.hash_ptr(ptr);
                let tag = z_ptr.tag().field();
                let payload = *z_ptr.val();
                acc.push(tag);
                acc.push(payload);
                acc
            })
    }

    pub(crate) fn parse(&self, input: &str) -> Ptr {
        input.split_whitespace().rev().fold(self.nil(), |acc, elt| {
            if let Ok(n) = elt.parse::<u32>() {
                self.cons(self.num(F::from_canonical_u32(n)), acc)
            } else if elt == "+" {
                self.cons(self.core.intern_atom(Tag::OpAdd, F::zero()), acc)
            } else {
                panic!("Invalid input")
            }
        })
    }
}
