// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]
use std::hash::Hash;
use std::sync::{Mutex, MutexGuard, OnceLock};

use ascent::{ascent, Dual};
use p3_field::{AbstractField, Field, PrimeField32};
use rustc_hash::FxHashMap;

use crate::loam::{LEWrap, Ptr, Wide, WidePtr, LE};
use crate::lurk::chipset::{lurk_hasher, LurkHasher};
use crate::lurk::tag::Tag;
use crate::lurk::zstore::{DIGEST_SIZE, TUPLE2_SIZE};

// Because of how the macros work, it's not easy (or possible) to pass a per-invocation structure like the `Allocator`
// into the program, while also having access to the program struct itself. However, that access is extremely useful
// both before and after running the program -- while developing and testing.
//
// Eventually, we can switch to using `ascent_run!` or `ascent_run_par!`, and then we can wrap the definition in a
// function to which the desired allocator and other inputs will be sent. However, this will require somewhat heavy
// mechanism for accessing inputs and outputs. Until then, we use a global `Allocator` and reinitialize it before each
// use.
pub fn allocator() -> MutexGuard<'static, Allocator> {
    static ALLOCATOR: OnceLock<Mutex<Allocator>> = OnceLock::new();
    ALLOCATOR
        .get_or_init(Default::default)
        .lock()
        .expect("poisoned")
}

pub struct Allocator {
    allocation_map: FxHashMap<LE, LE>,
    digest_cache: FxHashMap<Vec<Wide>, Wide>,
    preimage_cache: FxHashMap<Wide, Vec<Wide>>,
    hasher: LurkHasher,
}

impl Default for Allocator {
    fn default() -> Self {
        Self {
            allocation_map: Default::default(),
            digest_cache: Default::default(),
            preimage_cache: Default::default(),
            hasher: lurk_hasher(),
        }
    }
}

impl Allocator {
    pub fn init(&mut self) {
        self.allocation_map = Default::default();
        self.hasher = lurk_hasher();
        self.digest_cache = Default::default();
        self.preimage_cache = Default::default();
    }

    pub fn reset_allocation(&mut self) {
        self.allocation_map = Default::default();
    }

    pub fn import_hashes(&mut self, hashes: &FxHashMap<[LE; TUPLE2_SIZE], [LE; DIGEST_SIZE]>) {
        for (preimage, digest) in hashes {
            let preimage_vec = preimage
                .chunks(8)
                .map(|chunk| Wide::from_slice(chunk))
                .collect::<Vec<_>>();
            let digest_wide = Wide(digest.clone());

            self.digest_cache
                .insert(preimage_vec.clone(), digest_wide.clone());

            self.preimage_cache.insert(digest_wide, preimage_vec);
        }
    }

    pub fn alloc_addr(&mut self, tag: LE, initial_addr: LE) -> LE {
        let idx = *self
            .allocation_map
            .entry(tag)
            .and_modify(|x| *x += LE::from_canonical_u32(1))
            .or_insert(initial_addr);
        idx
    }

    pub fn hash4(&mut self, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        let mut preimage = Vec::with_capacity(32);

        preimage.extend(&a.0);
        preimage.extend(&b.0);
        preimage.extend(&c.0);
        preimage.extend(&d.0);

        let preimage_vec = vec![a, b, c, d];

        if let Some(digest) = self.digest_cache.get(&preimage_vec) {
            return digest.clone();
        };

        let mut digest0 = [LE::zero(); 8];
        let digest1 = self.hasher.hash(&preimage);

        digest0.copy_from_slice(&digest1);
        let digest = Wide(digest0);

        self.digest_cache.insert(preimage_vec.clone(), digest);
        self.preimage_cache.insert(digest, preimage_vec);

        digest
    }
    // TODO: refactor to share code with hash4
    pub fn hash6(&mut self, a: Wide, b: Wide, c: Wide, d: Wide, e: Wide, f: Wide) -> Wide {
        let mut preimage = Vec::with_capacity(32);

        preimage.extend(&a.0);
        preimage.extend(&b.0);
        preimage.extend(&c.0);
        preimage.extend(&d.0);
        preimage.extend(&e.0);
        preimage.extend(&f.0);

        let preimage_vec = vec![a, b, c, d];

        if let Some(digest) = self.digest_cache.get(&preimage_vec) {
            return digest.clone();
        };

        let mut digest0 = [LE::zero(); 8];
        let digest1 = self.hasher.hash(&preimage);

        digest0.copy_from_slice(&digest1);
        let digest = Wide(digest0);

        self.digest_cache.insert(preimage_vec.clone(), digest);
        self.preimage_cache.insert(digest, preimage_vec);

        digest
    }
    pub fn unhash4(&mut self, digest: &Wide) -> Option<[Wide; 4]> {
        let mut preimage = [Wide::widen(LE::from_canonical_u32(0)); 4];

        self.preimage_cache.get(digest).map(|digest| {
            preimage.copy_from_slice(&digest[..4]);
            preimage
        })
    }

    pub fn unhash6(&mut self, digest: &Wide) -> Option<[Wide; 6]> {
        let mut preimage = [Wide::widen(LE::from_canonical_u32(0)); 6];

        self.preimage_cache.get(digest).map(|digest| {
            preimage.copy_from_slice(&digest[..6]);
            preimage
        })
    }
}

#[cfg(feature = "loam")]
ascent! {
    struct AllocationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = Tag::wide_relation(); // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)}
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    // relation input_cons(Ptr, Ptr); // (car, cdr)

    relation input_expr(WidePtr); // (wide-ptr)
    relation output_expr(WidePtr); // (wide-ptr)
    relation input_ptr(Ptr); // (ptr)
    relation output_ptr(Ptr); // (ptr)

    // triggers allocation once per unique cons
    relation cons(Ptr, Ptr); // (car, cdr)
    relation car(Ptr, Ptr); // (cons, car)
    relation cdr(Ptr, Ptr); // (cons, cdr)
    relation hash4(Ptr, Wide, Wide, Wide, Wide); // (ptr, a, b, c, d)
    relation unhash4(LE, Wide); // (tag, digest)
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)

    // inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    relation f_value(Ptr, Wide); // (ptr, immediate-wide-value)
    relation cons_value(Ptr, Wide); // (cons, value)

    // all known `Ptr`s should be added to ptr.
    relation ptr(Ptr); // (ptr)
    relation ptr_tag(Ptr, Wide); // (ptr, tag)
    relation ptr_value(Ptr, Wide); // (ptr, value)

    // supporting ingress
    // inclusion triggers *_value relations.
    relation ingress(Ptr); // (ptr)



    relation alloc(LE, Wide); // (tag, value)

    ////////////////////////////////////////////////////////////////////////////////
    // Memory

    ////////////////////////////////////////////////////////////////////////////////
    // Cons

    // The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)

    // Memory to support conses allocated by digest or contents.
    lattice cons_digest_mem(Wide, Dual<LEWrap>); // (digest, addr)
    lattice cons_mem(Ptr, Ptr, Dual<LEWrap>); // (car, cdr, addr)

    // Populating alloc(...) triggers allocation in cons_digest_mem.
    cons_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Cons.elt(), LE::from_canonical_u32(0))))) <-- alloc(Tag::Cons.elt(), value);

    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Cons.value()), ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(LEWrap(allocator().alloc_addr(Tag::Cons.elt(), LE::from_canonical_u32(0))))) <-- cons(car, cdr);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    cons_digest_mem(digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, Tag::Cons.value()) <-- cons_rel(car, cdr, cons);

    ////////////////////////////////////////////////////////////////////////////////

    // Provide ptr_tag and ptr_value when known.
    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), cons_value(ptr, value);
    ptr_value(ptr, value) <-- ptr(ptr), f_value(ptr, value);

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    alloc(tag, wide_ptr.1) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    // Populate input_ptr and mark for ingress.
    ingress(ptr),
    input_ptr(ptr) <-- input_expr(wide_ptr), ptr_value(ptr, wide_ptr.1), ptr_tag(ptr, wide_ptr.0);

    // mark ingress conses for unhashing.
    unhash4(Tag::Cons.elt(), digest) <--
        ingress(ptr), if ptr.is_cons(),
        ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(&Tag::Cons.elt(), digest),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    f_value(Ptr(Tag::Num.elt(), value.f()), value) <-- alloc(&Tag::Num.elt(), value);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        cons_digest_mem(digest, addr),
        ptr_tag(car, wide_car_tag), ptr_tag(cdr, wide_cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.is_num();
    ptr(ptr) <-- f_value(ptr, _);

    // Provide cons_value when known.
    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path


    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    ptr_tag(ptr, Tag::Num.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), ptr_value(ptr, value), ptr_tag(ptr, wide_tag);

    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag),
        ptr_value(car, car_value),
        ptr_tag(cdr, cdr_tag),
        ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, allocator().hash4(*a, *b, *c, *d)) <-- hash4(ptr, a, b, c, d);

    ptr(car), ptr(cdr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, _),
        ptr_tag(car, wide_car_tag), ptr_tag(cdr, wide_cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    ////////////////////////////////////////////////////////////////////////////////
    // map_double
    //
    // This is just a silly input->output function that maps f(x)->2x over the input tree,
    // for use as a development example. This will be replaced by e.g. Lurk eval.

    relation map_double_input(Ptr); // (input)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)

    ptr(doubled),
    map_double(ptr, doubled) <-- map_double_input(ptr), if ptr.is_num(), let doubled = Ptr(Tag::Num.elt(), ptr.1.double());

    map_double_input(ptr) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr);

    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr) <--
        map_double_input(ptr),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    output_ptr(output) <-- input_ptr(input), map_double(input, output);

    // For now, just copy input straight to output. Later, we will evaluate.
    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);

    ////////////////////////////////////////////////////////////////////////////////
}

#[cfg(feature = "loam")]
impl AllocationProgram {
    fn cons_mem_is_contiguous(&self) -> bool {
        let mut addrs1 = self
            .cons_mem
            .iter()
            .map(|(_, _, addr)| addr.0)
            .collect::<Vec<_>>();

        let mut addrs2 = self
            .cons_digest_mem
            .iter()
            .map(|(_, addr)| addr.0)
            .collect::<Vec<_>>();

        addrs1.sort();
        addrs2.sort();

        let len1 = addrs1.len();
        let len2 = addrs2.len();
        addrs1.dedup();
        addrs2.dedup();

        let no_duplicates = addrs1.len() == len1 && addrs2.len() == len2;

        let mut addrs = Vec::with_capacity(addrs1.len() + addrs2.len());

        addrs.extend(addrs1);
        addrs.extend(addrs2);
        addrs.sort();
        addrs.dedup();

        let len = addrs.len();
        no_duplicates
            && addrs[0].0.is_zero()
            && LE::as_canonical_u32(&addrs[len - 1].0) as usize == len - 1
    }
}

#[cfg(test)]
#[cfg(feature = "loam")]
mod test {
    use super::*;

    #[test]
    fn new_test_cons() {
        allocator().init();

        // (1 . 2)
        let c1_2 = allocator().hash4(
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(1)),
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(2)),
        );
        // (2 . 3)
        let c2_3 = allocator().hash4(
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(2)),
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(3)),
        );
        // (2 . 4)
        let c2_4 = allocator().hash4(
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(2)),
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(4)),
        );
        // (4 . 6)
        let c4_6 = allocator().hash4(
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(4)),
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(6)),
        );
        // (4 . 8)
        let c4_8 = allocator().hash4(
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(4)),
            Tag::Num.value(),
            Wide::widen(LE::from_canonical_u32(8)),
        );
        // ((1 . 2) . (2 . 4))
        let c1_2__2_4 = allocator().hash4(Tag::Cons.value(), c1_2, Tag::Cons.value(), c2_4);
        // ((1 . 2) . (2 . 3))
        let c1_2__2_3 = allocator().hash4(Tag::Cons.value(), c1_2, Tag::Cons.value(), c2_3);
        // ((2 . 4) . (4 . 8))
        let c2_4__4_8 = allocator().hash4(Tag::Cons.value(), c2_4, Tag::Cons.value(), c4_8);
        // ((2 . 4) . (4 . 6))
        let c2_4__4_6 = allocator().hash4(Tag::Cons.value(), c2_4, Tag::Cons.value(), c4_6);

        let mut test = |input, expected_output, cons_count| {
            let mut prog = AllocationProgram::default();

            prog.input_expr = vec![(WidePtr(Tag::Cons.value(), input),)];
            prog.run();

            println!("{}", prog.relation_sizes_summary());

            assert_eq!(
                vec![(WidePtr(Tag::Cons.value(), expected_output),)],
                prog.output_expr
            );
            assert_eq!(cons_count, prog.cons_mem.len());
            assert_eq!(cons_count, prog.cons_digest_mem.len());

            // This will often fail in the first pass. We need to fix up the memory and provide it as a hint to the
            // second pass.
            //assert!(prog.cons_mem_is_contiguous());

            prog
        };

        // Mapping (lambda (x) (* 2 x)) over ((1 . 2) . (2 . 3))) yields ((2 . 4) . (4 . 6)).
        // We expect 6 total conses.
        test(c1_2__2_3, c2_4__4_6, 6);

        // Mapping (lambda (x) (* 2 x)) over ((1 . 2) . (2 . 4))) yields ((2 . 4) . (4 . 8)).
        // We expect only 5 total conses, because (2 . 4) is duplicated in the input and output,
        // so the allocation should be memoized.
        let prog = test(c1_2__2_4, c2_4__4_8, 5);

        // debugging

        println!("{}", prog.relation_sizes_summary());

        let AllocationProgram {
            car,
            cdr,
            ptr_tag,
            mut ptr_value,
            cons,
            cons_rel,
            cons_value,
            cons_mem,
            cons_digest_mem,
            ptr,
            hash4,
            hash4_rel,
            ingress,
            egress,
            input_expr,
            output_expr,
            f_value,
            alloc,
            input_ptr,
            output_ptr,
            map_double_input,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            ingress,
            ptr_value,
            map_double_input,
            cons_rel,
            cons_digest_mem,
        );
    }
}
