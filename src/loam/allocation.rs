// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]
use std::hash::Hash;
use std::sync::{Mutex, MutexGuard, OnceLock};

use ascent::{ascent, Dual};
use p3_field::{AbstractField, Field, PrimeField32};
use rustc_hash::FxHashMap;

use crate::loam::memory::{Memory, VPtr, VirtualMemory};
use crate::loam::{LEWrap, Ptr, Wide, WidePtr, LE};

use crate::core::chipset::{lurk_hasher, LurkHasher};
use crate::core::tag::Tag;
use crate::core::zstore::{DIGEST_SIZE, HASH3_SIZE, HASH4_SIZE, HASH5_SIZE};

use crate::core::{
    chipset::LurkChip,
    zstore::{ZPtr, ZStore},
};

use super::LoamProgram;

#[derive(Clone)]
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

    /// TODO: reorg for duplicate code
    pub fn import_hashes3(&mut self, hashes3: &FxHashMap<[LE; HASH3_SIZE], [LE; DIGEST_SIZE]>) {
        for (preimage, digest) in hashes3 {
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

    /// TODO: reorg for duplicate code
    pub fn import_hashes4(&mut self, hashes4: &FxHashMap<[LE; HASH4_SIZE], [LE; DIGEST_SIZE]>) {
        for (preimage, digest) in hashes4 {
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

    // /// TODO: reorg for duplicate code
    pub fn import_hashes5(&mut self, hashes5: &FxHashMap<[LE; HASH5_SIZE], [LE; DIGEST_SIZE]>) {
        for (preimage, digest) in hashes5 {
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

    pub fn import_zstore(&mut self, zstore: &ZStore<LE, LurkChip>) {
        self.import_hashes3(&zstore.comms);
        self.import_hashes4(&zstore.hashes4);
        self.import_hashes5(&zstore.hashes5);
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

    pub fn hash5(&mut self, a: Wide, b: Wide, c: Wide, d: Wide, e: Wide) -> Wide {
        let mut preimage = Vec::with_capacity(40);

        preimage.extend(&a.0);
        preimage.extend(&b.0);
        preimage.extend(&c.0);
        preimage.extend(&d.0);
        preimage.extend(&e.0);

        let preimage_vec = vec![a, b, c, d, e];

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

    pub fn unhash4(&mut self, digest: &Wide) -> [Wide; 4] {
        let mut preimage = [Wide::widen(LE::from_canonical_u32(0)); 4];

        self.preimage_cache
            .get(digest)
            .map(|preimg| {
                preimage.copy_from_slice(&preimg[..4]);
                preimage
            })
            .unwrap()
    }

    pub fn unhash5(&mut self, digest: &Wide) -> [Wide; 5] {
        let mut preimage = [Wide::widen(LE::from_canonical_u32(0)); 5];

        self.preimage_cache
            .get(digest)
            .map(|preimg| {
                preimage.copy_from_slice(&preimg[..5]);
                preimage
            })
            .unwrap()
    }
}

#[cfg(feature = "loam")]
ascent! {
    // #![trace]

    struct AllocationProgram {
        allocator: Allocator,
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = Tag::wide_relation(); // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)

    relation thunk_rel(Ptr, Ptr, Ptr);
    relation fun_rel(Ptr, Ptr, Ptr, Ptr);

    relation input_expr(WidePtr); // (wide-ptr)
    relation output_expr(WidePtr); // (wide-ptr)
    relation input_ptr(Ptr); // (ptr)
    relation output_ptr(Ptr); // (ptr)

    // triggers allocation once per unique cons
    relation cons(Ptr, Ptr); // (car, cdr)
    relation hash4(Wide, Wide, Wide, Wide); // (a, b, c, d)
    relation unhash4(Wide); // (tag, digest)
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)

    // inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    relation ingress(Ptr); // (ptr)

    relation alloc(LE, Wide); // (tag, value)

    ////////////////////////////////////////////////////////////////////////////////
    // Memory

    ////////////////////////////////////////////////////////////////////////////////
    // Cons

    // Final: The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)
    // Final: Memory to support conses allocated by digest or contents.
    lattice cons_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
    // Final
    lattice cons_mem(Ptr, Ptr, Dual<LEWrap>); // (car, cdr, addr)

    // Populating alloc(...) triggers allocation in cons_digest_mem.
    cons_digest_mem(value, Dual(addr)) <--
        alloc(tag, value), if *tag == Tag::Cons.elt(),
        let addr = LEWrap(_self.alloc_addr(Tag::Cons.elt(), LE::zero()));
    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(addr)) <--
        cons(car, cdr),
        let addr = LEWrap(_self.alloc_addr(Tag::Cons.elt(), LE::zero()));

    // Register cons value.
    ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);
    // Register cons relation.
    cons_rel(car, cdr, cons) <-- cons_mem(car, cdr, addr), let cons = Ptr(Tag::Cons.elt(), addr.0.0);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    cons_digest_mem(digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        hash4_rel(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value, digest);
    // Other way around
    cons_mem(car, cdr, addr) <--
        cons_digest_mem(digest, addr),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        if car.wide_tag() == *car_tag && cdr.wide_tag() == *cdr_tag;

    ////////////////////////////////////////////////////////////////////////////////
    // Num

    ptr_value(ptr, digest) <--
        alloc(tag, digest), if *tag == Tag::Num.elt(), let ptr = Ptr(Tag::Num.elt(), digest.f());

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    alloc(tag, wide_ptr.1) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    // Populate input_ptr and mark for ingress.
    ingress(ptr), input_ptr(ptr) <--
        input_expr(wide_ptr), ptr_value(ptr, wide_ptr.1), if ptr.tag() == wide_ptr.tag();

    // mark ingress conses for unhashing.
    unhash4(digest) <-- ingress(ptr), if ptr.is_cons(), ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(digest), let [a, b, c, d] = _self.unhash4(digest);

    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(digest),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    // Cons
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // Num
    ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    output_expr(WidePtr(ptr.wide_tag(), *value)) <-- output_ptr(ptr), ptr_value(ptr, value);

    hash4(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, digest) <--
        hash4(a, b, c, d), let digest = _self.hash4(*a, *b, *c, *d);

    ////////////////////////////////////////////////////////////////////////////////
    // map_double

    relation map_double_input(Ptr); // (input)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)
    relation map_double_cont(Ptr, Ptr, Ptr);

    map_double(ptr, doubled) <-- map_double_input(ptr), if ptr.is_num(), let doubled = Ptr(Tag::Num.elt(), ptr.1.double());

    map_double_input(ptr) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr);

    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr) <--
        map_double_input(ptr),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);

    ////////////////////////////////////////////////////////////////////////////////
}

#[cfg(feature = "loam")]
impl LoamProgram for AllocationProgram {
    fn allocator(&self) -> &Allocator {
        &self.allocator
    }
    fn allocator_mut(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    fn ptr_value(&self) -> &Vec<(Ptr, Wide)> {
        &self.ptr_value
    }
    fn cons_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)> {
        &self.cons_rel
    }
    fn fun_rel(&self) -> &Vec<(Ptr, Ptr, Ptr, Ptr)> {
        &self.fun_rel
    }
    fn thunk_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)> {
        &self.thunk_rel
    }
}

#[cfg(feature = "loam")]
ascent! {
    // #![trace]
    struct DistilledAllocationProgram {
        allocator: Allocator,
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = Tag::wide_relation(); // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)

    relation thunk_rel(Ptr, Ptr, Ptr);
    relation fun_rel(Ptr, Ptr, Ptr, Ptr);

    relation input_expr(WidePtr); // (wide-ptr)
    relation output_expr(WidePtr); // (wide-ptr)
    relation input_ptr(Ptr); // (ptr)
    relation output_ptr(Ptr); // (ptr)

    relation cons(Ptr, Ptr); // (car, cdr)
    relation hash4(Wide, Wide, Wide, Wide); // (a, b, c, d)
    relation unhash4(Wide); // (tag, digest)
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)

    // inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    relation ingress(Ptr); // (ptr)

    relation alloc(LE, Wide); // (tag, value)

    ////////////////////////////////////////////////////////////////////////////////
    // Memory

    ////////////////////////////////////////////////////////////////////////////////
    // Cons

    // Final: The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)
    // Final: Memory to support conses allocated by digest or contents.
    relation cons_digest_mem(Wide, LE); // (value, addr)
    // Final
    relation cons_mem(Ptr, Ptr, LE); // (car, cdr, addr)

    relation initial_cons_digest_mem(Wide, LE); // (value, addr)
    relation initial_cons_mem(Ptr, Ptr, LE); // (car, cdr, addr)
    cons_digest_mem(digest, addr) <-- initial_cons_digest_mem(digest, addr);
    cons_mem(car, cdr, addr) <-- initial_cons_mem(car, cdr, addr);

    // Register cons value.
    ptr_value(cons, value) <--
        alloc(tag, value), if *tag == Tag::Cons.elt(),
        cons_digest_mem(value, addr),
        let cons = Ptr(Tag::Cons.elt(), *addr);
    // Register cons relation.
    cons_rel(car, cdr, cons) <-- cons(car, cdr), cons_mem(car, cdr, addr), let cons = Ptr(Tag::Cons.elt(), *addr);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    ptr_value(cons, digest) <--
        cons_rel(car, cdr, cons),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        hash4_rel(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value, digest);
    cons_rel(car, cdr, cons) <--
        ptr_value(cons, digest), if cons.tag() == Tag::Cons,
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        if car.wide_tag() == *car_tag && cdr.wide_tag() == *cdr_tag;

    ////////////////////////////////////////////////////////////////////////////////
    // Num

    ptr_value(num, value) <-- alloc(tag, value), if *tag == Tag::Num.elt(), let num = Ptr(Tag::Num.elt(), value.f());

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    alloc(tag, wide_ptr.1) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    // Populate input_ptr and mark for ingress.
    ingress(ptr), input_ptr(ptr) <--
        input_expr(wide_ptr), ptr_value(ptr, wide_ptr.1), if ptr.tag() == wide_ptr.tag();

    // mark ingress conses for unhashing.
    unhash4(digest) <-- ingress(ptr), if ptr.is_cons(), ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(digest), let [a, b, c, d] = _self.unhash4(digest);

    alloc(x_tag, x_value),
    alloc(y_tag, y_value) <--
        unhash4(digest),
        hash4_rel(wide_x_tag, x_value, wide_y_tag, y_value, digest),
        tag(x_tag, wide_x_tag),
        tag(y_tag, wide_y_tag);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    // Cons
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // Num
    ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    output_expr(WidePtr(ptr.wide_tag(), *value)) <-- output_ptr(ptr), ptr_value(ptr, value);

    hash4(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, digest) <--
        hash4(a, b, c, d), let digest = _self.hash4(*a, *b, *c, *d);

    ////////////////////////////////////////////////////////////////////////////////
    // map_double

    relation map_double_input(Ptr); // (input)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)
    relation map_double_cont(Ptr, Ptr, Ptr);

    map_double(ptr, doubled) <-- map_double_input(ptr), if ptr.is_num(), let doubled = Ptr(Tag::Num.elt(), ptr.1.double());

    map_double_input(ptr) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr);

    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    map_double_cont(ptr, double_car, double_cdr), cons(double_car, double_cdr) <--
        map_double_input(ptr),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);

    ////////////////////////////////////////////////////////////////////////////////
}

#[cfg(feature = "loam")]
impl LoamProgram for DistilledAllocationProgram {
    fn allocator(&self) -> &Allocator {
        &self.allocator
    }
    fn allocator_mut(&mut self) -> &mut Allocator {
        &mut self.allocator
    }

    fn ptr_value(&self) -> &Vec<(Ptr, Wide)> {
        &self.ptr_value
    }
    fn cons_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)> {
        &self.cons_rel
    }
    fn fun_rel(&self) -> &Vec<(Ptr, Ptr, Ptr, Ptr)> {
        &self.fun_rel
    }
    fn thunk_rel(&self) -> &Vec<(Ptr, Ptr, Ptr)> {
        &self.thunk_rel
    }
}

#[cfg(feature = "loam")]
impl DistilledAllocationProgram {
    pub fn import_memory(&mut self, memory: Memory) {
        self.initial_cons_digest_mem = memory.cons_digest_mem;
        self.initial_cons_mem = memory.cons_mem;
    }
}

#[cfg(test)]
#[cfg(feature = "loam")]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::{
        core::{
            chipset::LurkChip,
            zstore::{lurk_zstore, ZPtr, ZStore},
        },
        loam::memory::{DistillationOptions, PPtr, Store},
    };

    use super::*;

    fn wide_ptr(tag: LE, digest: [LE; 8]) -> WidePtr {
        WidePtr(Wide::widen(tag), Wide(digest))
    }

    fn read_wideptr(zstore: &mut ZStore<BabyBear, LurkChip>, src: &str) -> WidePtr {
        let ZPtr { tag, digest } = zstore.read(src, &Default::default());
        wide_ptr(tag.elt(), digest)
    }

    fn test_aux0(
        zstore: &ZStore<BabyBear, LurkChip>,
        input: WidePtr,
        expected_output: WidePtr,
    ) -> AllocationProgram {
        let mut prog = AllocationProgram::default();

        prog.import_zstore(zstore);
        prog.input_expr = vec![(input,)];
        prog.run();

        println!("{}", prog.relation_sizes_summary());

        assert_eq!(expected_output, prog.output_expr[0].0);
        prog
    }

    fn test_aux(input: &str, expected_output: &str) -> AllocationProgram {
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        let expected_output = read_wideptr(&mut zstore, expected_output);
        test_aux0(&zstore, input, expected_output)
    }

    fn test_aux1(input: &str, expected_output: WidePtr) -> AllocationProgram {
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        test_aux0(&zstore, input, expected_output)
    }

    fn test_second_phase(
        input: &str,
        expected_output: &str,
        bad_input_output: Option<(&str, &str)>,
    ) {
        // Run the first phase
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        let expected_output = read_wideptr(&mut zstore, expected_output);
        let original_program = test_aux0(&zstore, input, expected_output);

        // Start the second phase
        let mut prog = DistilledAllocationProgram::default();

        // Move the hashes (stored in the allocator) and input over
        prog.allocator = original_program.allocator.clone();
        prog.input_expr = original_program.input_expr.clone();

        let raw_memory = original_program.export_memory();
        let mut store = Store::default();
        let options = DistillationOptions::new().with_summary(0.9);
        let memory = raw_memory.distill_with_store(&mut store, &options);

        prog.import_memory(memory);

        // Determine whether we want to use the intended in/out, or attack the program with the bad in/out
        if let Some((bad_input, bad_output)) = bad_input_output {
            let bad_zptr = zstore.read(bad_input, &Default::default());
            let bad_input = store.zptr_ptr(&bad_zptr).unwrap();
            let bad_output = vec![(read_wideptr(&mut zstore, bad_output),)];

            // Inject the bad input pointer into memory with the intended input's digest.
            // If the prover is not correctly checking the hashes, this will slip through
            // and cause the prover to believe that the bad input pointer is correct and
            // evaluate it.
            let input_digest = prog.input_expr[0].0 .1;
            prog.cons_digest_mem.push((input_digest, bad_input.1));
            prog.run();

            // Check if we get the bad output. Assuming our program is correctly constrained,
            // this `assert_eq` should never be true, so in our tests, we `#[should_panic]`.
            assert_eq!(prog.output_expr, bad_output);
        } else {
            // Otherwise, we don't inject any bad pointers, and just run everything as normal,
            // and then check that the expected output is correct.
            prog.run();
            assert_eq!(prog.output_expr, original_program.output_expr);
        };

        println!("{}", prog.relation_sizes_summary());
    }

    #[test]
    fn test_cons_simple() {
        test_aux("(1n . 2n)", "(2n . 4n)");
    }

    #[test]
    fn test_cons() {
        test_aux("((1n . 2n) . (2n . 4n))", "((2n . 4n) . (4n . 8n))");
        test_aux("((1n . 2n) . (2n . 4n))", "((2n . 4n) . (4n . 8n))");
    }

    #[test]
    fn new_test_cons() {
        test_second_phase("((1n . 2n) . (2n . 4n))", "((2n . 4n) . (4n . 8n))", None);
        test_second_phase("((1n . 2n) . (2n . 4n))", "((2n . 4n) . (4n . 8n))", None);
    }

    #[test]
    #[should_panic]
    fn new_test_cons_bad() {
        // This test tries to attack the program by injecting bad memory.
        // If the program is correctly constrained, the test should fail (and panic).
        test_second_phase(
            "((1n . 2n) . (2n . 4n))",
            "((2n . 4n) . (4n . 8n))",
            Some(("(1n . 2n)", "(2n . 4n)")),
        );
        test_second_phase(
            "((1n . 2n) . (2n . 4n))",
            "((2n . 4n) . (4n . 8n))",
            Some(("(2n . 4n)", "(4n . 8n)")),
        );
    }
}
