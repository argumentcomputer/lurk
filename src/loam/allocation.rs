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
use crate::lurk::zstore::{DIGEST_SIZE, HASH4_SIZE};

use crate::lurk::{
    chipset::LurkChip,
    zstore::{ZPtr, ZStore},
};

pub struct Allocator {
    allocation_map: FxHashMap<LE, LE>,
}

impl Default for Allocator {
    fn default() -> Self {
        Self {
            allocation_map: Default::default(),
        }
    }
}

impl Allocator {
    pub fn init(&mut self) {
        self.allocation_map = Default::default();
    }

    pub fn reset_allocation(&mut self) {
        self.allocation_map = Default::default();
    }

    pub fn alloc_addr(&mut self, tag: LE, initial_addr: LE) -> LE {
        let idx = *self
            .allocation_map
            .entry(tag)
            .and_modify(|x| *x += LE::from_canonical_u32(1))
            .or_insert(initial_addr);
        idx
    }
}

// #[cfg(feature = "loam")]
ascent! {
    // #![trace]
    struct AllocationProgram {
        allocator: Allocator,
        zstore: ZStore<LE, LurkChip>,
    }

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
    #[trace("#0:")]
    cons_digest_mem(value, Dual(LEWrap(_self.allocator.alloc_addr(Tag::Cons.elt(), LE::zero())))) <-- alloc(Tag::Cons.elt(), value);

    // Convert addr to ptr and register ptr relations.
    #[trace("#1:")]
    ptr(ptr), ptr_tag(ptr, Tag::Cons.value()), ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);

    // Populating cons(...) triggers allocation in cons mem.
    #[trace("#2: cons_mem {:?}, {:?}", car, cdr)]
    cons_mem(car, cdr, Dual(LEWrap(_self.allocator.alloc_addr(Tag::Cons.elt(), LE::zero())))) <-- cons(car, cdr);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    #[trace("#3:")]
    cons_digest_mem(digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    #[trace("#4:")]
    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)) <-- cons_mem(car, cdr, addr);

    // ptr(cons), ptr_tag(cons, Tag::Cons.value()) <-- cons_rel(car, cdr, cons);

    ////////////////////////////////////////////////////////////////////////////////

    // Provide ptr_tag and ptr_value when known.
    #[trace("#5:")]
    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    #[trace("#6:")]
    ptr_value(ptr, value) <-- ptr(ptr), cons_value(ptr, value);
    #[trace("#7:")]
    ptr_value(ptr, value) <-- ptr(ptr), f_value(ptr, value);

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    #[trace("#8: alloc {:?}", wide_ptr.1)]
    alloc(tag, wide_ptr.1) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    // Populate input_ptr and mark for ingress.
    #[trace("#9: intro ingress input")]
    ingress(ptr),
    input_ptr(ptr) <-- input_expr(wide_ptr), ptr_value(ptr, wide_ptr.1), ptr_tag(ptr, wide_ptr.0);

    // mark ingress conses for unhashing.
    #[trace("#10: apply ingress unhash4")]
    unhash4(Tag::Cons.elt(), digest) <--
        ingress(ptr), if ptr.is_cons(),
        ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    #[trace("#11: hash4_rel <-- unhash4")]
    hash4_rel(a, b, c, d, digest) <-- unhash4(tag, digest), let [a, b, c, d] = _self.unhash4(*tag, *digest);

    #[trace("#12: alloc unhash4")]
    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(&Tag::Cons.elt(), digest),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    #[trace("#13:")]
    f_value(Ptr(Tag::Num.elt(), value.f()), value) <-- alloc(&Tag::Num.elt(), value);

    #[trace("#14:")]
    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        cons_digest_mem(digest, addr),
        ptr_tag(car, wide_car_tag), ptr_tag(cdr, wide_cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    #[trace("#15:")]
    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    #[trace("#16:")]
    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.is_num();
    ptr(ptr) <-- f_value(ptr, _);

    // Provide cons_value when known.
    #[trace("#17:")]
    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path


    // The output_ptr is marked for egress.
    // #[trace("#18: intro egress output")]
    egress(ptr) <-- output_ptr(ptr);

    // consume egress of cons pointer to trigger egress of car, cdr
    #[trace("#19: apply egress cons {:?}", cons)]
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // consume egress of num ptr into num value
    #[trace("#20: apply egress num")]
    ptr_tag(ptr, Tag::Num.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    #[trace("#21:")]
    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), ptr_value(ptr, value), ptr_tag(ptr, wide_tag);

    // consome egress of
    #[trace("#22: apply egress hash4 {:?}", cons)]
    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag),
        ptr_value(car, car_value),
        ptr_tag(cdr, cdr_tag),
        ptr_value(cdr, cdr_value);

    #[trace("#23:")]
    hash4_rel(a, b, c, d, digest) <-- 
        hash4(ptr, a, b, c, d), let digest = _self.hash4(ptr.0, *a, *b, *c, *d);

    #[trace("#24:")]
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

    #[trace("#25:")]
    ptr(doubled),
    map_double(ptr, doubled) <-- map_double_input(ptr), if ptr.is_num(), let doubled = Ptr(Tag::Num.elt(), ptr.1.double());

    #[trace("#26:")]
    map_double_input(ptr) <-- input_ptr(ptr);

    #[trace("#27: intro ingress map_double")]
    ingress(ptr) <-- map_double_input(ptr);

    #[trace("#28: map_double_input car, cdr <-- cons")]
    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    #[trace("#29: map_double_input intro cont")]
    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr) <--
        map_double_input(ptr),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    #[trace("#30: map_double_input apply cont")]
    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    // For now, just copy input straight to output. Later, we will evaluate.
    #[trace("#31: output <-- input")]
    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);

    ////////////////////////////////////////////////////////////////////////////////
}

// #[cfg(feature = "loam")]
impl AllocationProgram {
    fn cons_mem_is_contiguous(&self) -> bool {
        println!("{:?}", self.cons_mem);
        println!("{:?}", self.cons_digest_mem);
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

    fn unhash4(&mut self, tag: LE, digest: Wide) -> [Wide; 4] {
        let zptr = ZPtr {
            tag: Tag::from_field(&tag),
            digest: digest.0,
        };
        let (a, b) = self.zstore.fetch_tuple2(&zptr);
        [Wide::widen(a.tag.elt()), Wide(a.digest), Wide::widen(b.tag.elt()), Wide(b.digest)]
    }

    fn hash4(&mut self, tag: LE, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        let a_zptr = ZPtr {
            tag: Tag::from_field(&a.f()),
            digest: b.0,
        };
        let b_zptr = ZPtr {
            tag: Tag::from_field(&c.f()),
            digest: d.0,
        };
        let zptr = self.zstore.intern_tuple2(Tag::from_field(&tag), a_zptr, b_zptr);
        Wide(zptr.digest)
    }

    fn fmt(&self, tag: Tag, digest: &Wide) -> String {
        let zptr = ZPtr {
            tag,
            digest: digest.0,
        };
        self.zstore.fmt(&zptr)
    }

    fn fmt2(&self, wide_ptr: &WidePtr) -> String {
        let zptr = ZPtr {
            tag: Tag::from_field(&wide_ptr.0.f()),
            digest: wide_ptr.1 .0,
        };
        self.zstore.fmt(&zptr)
    }

    fn deref(&self, ptr: &Ptr) -> Option<String> {
        let ptr = &(*ptr,);
        let tag = Tag::from_field(&self.ptr_tag_indices_0.0.get(ptr)?[0].0.f());
        let digest = self.ptr_value_indices_0.0.get(ptr)?[0].0 .0;
        if tag == Tag::Thunk {
            return Some("skip cuz bad impl".into());
        }
        Some(self.zstore.fmt(&ZPtr { tag, digest }))
    }

    fn print_memory_tables(&self) {
        const FULL_SEP: &str = "=====================================================================================================";

        println!("{}", FULL_SEP);
        println!("== cons memory digest");

        for (i, (digest, Dual(LEWrap(ptr)))) in self.cons_digest_mem.iter().enumerate() {
            println!("#{}, cons={}:", i, ptr.as_canonical_u32());
            println!("\t{}", self.fmt(Tag::Cons, digest));
            println!("\n");
        }

        println!("{}", FULL_SEP);
        println!("== cons memory");

        for (i, (car, cdr, Dual(LEWrap(ptr)))) in self.cons_mem.iter().enumerate() {
            println!(
                "#{}, cons={}, car={}, cdr={}:",
                i,
                ptr.as_canonical_u32(),
                car.1.as_canonical_u32(),
                cdr.1.as_canonical_u32()
            );
            println!("\t{:?}", self.deref(car));
            println!("\t{:?}", self.deref(cdr));
            println!("\n");
        }
    }
}

ascent! {
    #![trace]

    struct DistilledAllocationProgram {
        zstore: ZStore<LE, LurkChip>,
    }

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

    relation car(Ptr, Ptr); // (cons, car)
    relation cdr(Ptr, Ptr); // (cons, cdr)

    relation ptr_tag(Ptr, Wide); // (ptr, tag)
    relation ptr_value(Ptr, Wide); // (ptr, value)

    ////////////////////////////////////////////////////////////////////////////////
    // Memory

    ////////////////////////////////////////////////////////////////////////////////
    // Cons

    // The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)

    // Memory to support conses allocated by digest or contents.
    lattice cons_digest_mem(Wide, Dual<LEWrap>); // (digest, addr)
    lattice cons_mem(Ptr, Ptr, Dual<LEWrap>); // (car, cdr, addr)

    // Convert addr to ptr and register ptr relations.
    ptr_tag(ptr, Tag::Cons.value()), ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)) <-- cons_mem(car, cdr, addr);

    car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    ////////////////////////////////////////////////////////////////////////////////
    // IO (originally ingress/egress paths)

    input_ptr(ptr) <-- input_expr(wide_ptr), ptr_value(ptr, wide_ptr.1), ptr_tag(ptr, wide_ptr.0);
    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), ptr_value(ptr, value), ptr_tag(ptr, wide_tag);

    ////////////////////////////////////////////////////////////////////////////////
    // map_double
    //
    // This is just a silly input->output function that maps f(x)->2x over the input tree,
    // for use as a development example. This will be replaced by e.g. Lurk eval.

    relation map_double_input(Ptr); // (input)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)

    map_double(ptr, doubled) <-- map_double_input(ptr), if ptr.is_num(), let doubled = Ptr(Tag::Num.elt(), ptr.1.double());

    map_double_input(ptr) <-- input_ptr(ptr);

    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    map_double_cont(ptr, double_car, double_cdr) <--
        map_double_input(ptr),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    // For now, just copy input straight to output. Later, we will evaluate.
    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);

    ////////////////////////////////////////////////////////////////////////////////
}

#[cfg(test)]
// #[cfg(feature = "loam")]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::lurk::{
        chipset::LurkChip,
        zstore::{lurk_zstore, ZPtr, ZStore},
    };

    use super::*;

    fn wide_ptr(tag: LE, digest: [LE; 8]) -> WidePtr {
        WidePtr(Wide::widen(tag), Wide(digest))
    }

    fn read_wideptr(zstore: &mut ZStore<BabyBear, LurkChip>, src: &str) -> WidePtr {
        let ZPtr { tag, digest } = zstore.read(src).unwrap();
        wide_ptr(tag.elt(), digest)
    }

    fn test_aux0(
        zstore: ZStore<BabyBear, LurkChip>,
        input: WidePtr,
        expected_output: WidePtr,
    ) -> AllocationProgram {
        let mut prog = AllocationProgram::default();

        prog.zstore = zstore;
        prog.input_expr = vec![(input,)];
        prog.run();

        println!("{}", prog.relation_sizes_summary());
        prog.print_memory_tables();

        assert_eq!(expected_output, prog.output_expr[0].0);
        assert!(prog.cons_mem_is_contiguous());
        prog
    }

    fn test_aux(input: &str, expected_output: &str) -> AllocationProgram {
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        let expected_output = read_wideptr(&mut zstore, expected_output);
        test_aux0(zstore, input, expected_output)
    }

    fn test_aux1(input: &str, expected_output: WidePtr) -> AllocationProgram {
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        test_aux0(zstore, input, expected_output)
    }

    fn test_distilled(original_program: &AllocationProgram) {
        let mut prog = DistilledAllocationProgram::default();

        prog.zstore = original_program.zstore.clone();
        prog.input_expr = original_program.input_expr.clone();

        // transfer over the memory (assume it's been distilled)
        prog.cons_digest_mem = original_program.cons_digest_mem.clone();
        prog.cons_mem = original_program.cons_mem.clone();

        prog.run();

        println!("{}", prog.relation_sizes_summary());

        assert_eq!(prog.output_expr, original_program.output_expr);
    }

    #[test]
    fn new_test_cons() {
        // let prog = test_aux("((1 . 2) (1 . 2) . (2 . 4))", "((2 . 4) (2 . 4) . (4 . 8))");
        // test_distilled(&prog);

        let prog = test_aux("((1 . 2) . (2 . 3))", "((2 . 4) . (4 . 6))");
        test_distilled(&prog);
    }
}
