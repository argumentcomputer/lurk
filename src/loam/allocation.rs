use std::collections::BTreeMap;
use std::hash::Hash;
use std::sync::{Mutex, MutexGuard, OnceLock};

use ascent::{ascent, Dual};

type LE = u32;

const F_TAG: LE = 0;
const CONS_TAG: LE = 1;

const F_WIDE_TAG: Wide = Wide([F_TAG, 0, 0, 0, 0, 0, 0, 0]);
const CONS_WIDE_TAG: Wide = Wide([CONS_TAG, 0, 0, 0, 0, 0, 0, 0]);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
struct F(LE);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
struct Ptr(LE, LE);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
struct Wide([LE; 8]);

impl Wide {
    fn widen(elt: LE) -> Wide {
        let mut v = [0u32; 8];
        v[0] = elt;
        Wide(v)
    }

    fn f(&self) -> LE {
        //        assert_eq!(&[0, 0, 0, 0, 0, 0, 0], &self.0[1..]);
        self.0[0]
    }
}

// Because of how the macros work, it's not easy (or possible) to pass a per-invocation structure like the `Allocator`
// into the program, while also having access to the program struct itself. However, that access is extremely useful
// both before and after running the program -- while developing and testing.
//
// Eventually, we can switch to using `ascent_run!` or `ascent_run_par!`, and then we can wrap the definition in a
// function to which the desired allocator and other inputs will be sent. However, this will require somewhat heavy
// mechanism for accessing inputs and outputs. Until then, we use a global `Allocator` and reinitialize it before each
// use.
fn allocator() -> MutexGuard<'static, Allocator> {
    static ALLOCATOR: OnceLock<Mutex<Allocator>> = OnceLock::new();
    ALLOCATOR
        .get_or_init(Default::default)
        .lock()
        .expect("poisoned")
}

#[derive(Debug, Default, Hash)]
struct Allocator {
    allocation_map: BTreeMap<LE, LE>,
    digest_cache: BTreeMap<Vec<Wide>, Wide>,
    preimage_cache: BTreeMap<Wide, Vec<Wide>>,
}

impl Allocator {
    pub fn init(&mut self) {
        self.allocation_map = Default::default();
        self.digest_cache = Default::default();
        self.preimage_cache = Default::default();
    }

    pub fn alloc(&mut self, tag: LE) -> Ptr {
        let idx = self
            .allocation_map
            .entry(tag)
            .and_modify(|x| *x += 1)
            .or_insert(0);

        Ptr(tag, *idx)
    }

    pub fn hash4(&mut self, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        use sha2::{Digest, Sha256};

        let preimage = vec![a, b, c, d];

        let mut h = Sha256::new();
        if let Some(found) = self.digest_cache.get(&preimage) {
            return *found;
        }

        for elt in a.0.iter() {
            h.update(elt.to_le_bytes());
        }
        for elt in b.0.iter() {
            h.update(elt.to_le_bytes());
        }
        for elt in c.0.iter() {
            h.update(elt.to_le_bytes());
        }
        for elt in d.0.iter() {
            h.update(elt.to_le_bytes());
        }
        let hash: [u8; 32] = h.finalize().into();

        let mut buf = [0u8; 4];

        let x: Vec<u32> = hash
            .chunks(4)
            .map(|chunk| {
                buf.copy_from_slice(chunk);
                u32::from_le_bytes(buf)
            })
            .collect();

        let digest = Wide(x.try_into().unwrap());

        self.digest_cache.insert(preimage.clone(), digest);
        self.preimage_cache.insert(digest, preimage);

        digest
    }
    pub fn unhash4(&mut self, digest: &Wide) -> Option<[Wide; 4]> {
        let mut preimage = [Wide::widen(0); 4];

        self.preimage_cache.get(digest).map(|digest| {
            preimage.copy_from_slice(&digest[..4]);
            preimage
        })
    }
}

ascent! {
    struct AllocationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = vec![(F_TAG, F_WIDE_TAG), (CONS_TAG, CONS_WIDE_TAG)]; // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)}
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    // relation input_cons(Ptr, Ptr); // (car, cdr)

    relation input_expr(Wide, Wide); // (tag, value)
    relation output_expr(Wide, Wide); // (tag, value)
    relation input_ptr(Ptr); // (ptr)
    relation output_ptr(Ptr); // (ptr)

    // triggers allocation once per unique cons
    relation cons(Ptr, Ptr, LE); // (car, cdr, priority)
    relation car(Ptr, Ptr); // (cons, car)
    relation cdr(Ptr, Ptr); // (cons, cdr)
    relation hash4(Ptr, Wide, Wide, Wide, Wide); // (a, b, c, d)
    relation unhash4(LE, Wide, Ptr); // (tag, digest, ptr)
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



    relation alloc(LE, Wide, LE); // (tag, value, priority)

    ////////////////////////////////////////////////////////////////////////////////
    // Rules

    // memory

    // These two lattices and the following rule are a pattern.
    // TODO: make an ascent macro for this?
    lattice primary_mem(LE, Wide, Wide, Dual<LE>); // (tag, wide-tag, value, primary-addr)
    lattice primary_counter(LE) = vec![(0,)]; // addr
    // Memory counter must always holds largest address.
    primary_counter(addr.0) <-- primary_mem(_, _, _, addr);


    // Populating alloc(...) triggers allocation in primary_mem.
    primary_mem(tag, wide_tag, value, Dual(addr + 1 + priority)) <--
        alloc(tag, value, priority),
        if *tag != F_TAG, // F is immediate
        tag(tag, wide_tag),
        primary_counter(addr);

    relation primary_rel(LE, Wide, Wide, Ptr); // (tag, wide-tag, value, ptr)

    // Convert addr to ptr.
    primary_rel(tag, wide_tag, value, Ptr(*tag, addr.0)) <-- primary_mem(tag, wide_tag, value, addr);
    primary_rel(F_TAG, F_WIDE_TAG, value, ptr) <-- f_value(ptr, value);

    // Register ptr.
    ptr(ptr), ptr_tag(ptr, wide_tag), ptr_value(ptr, value) <-- primary_rel(_tag, wide_tag, value, ptr);

    // cons-addr is for this cons type-specific memory.
    lattice cons_mem(Ptr, Ptr, Dual<LE>); // (car, cdr, cons-addr)
    // Cons
    primary_counter(addr.0) <-- cons_mem(_, _, addr);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(counter + 1 + priority)) <-- cons(car, cdr, priority), primary_counter(counter);

    primary_mem(CONS_TAG, CONS_WIDE_TAG, digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    // If cons_mem was populated otherwise, still populate cons(...).
    cons(car, cdr, 0), cons_rel(car, cdr, Ptr(CONS_TAG, addr.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, CONS_WIDE_TAG) <-- cons_rel(car, cdr, cons);
    ptr_value(cons, value) <-- cons_rel(car, cdr, cons), cons_value(cons, value);

    // Provide ptr_tag and ptr_value when known.
    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), cons_value(ptr, value);
    ptr_value(ptr, value) <-- ptr(ptr), f_value(ptr, value);

    // The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)

    cons(car, cdr, 0) <-- cons_rel(car, cdr, _);

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    alloc(tag, value, 0) <-- input_expr(wide_tag, value), tag(tag, wide_tag);

    // Populate input_ptr.
    input_ptr(ptr) <-- input_expr(wide_tag, value), primary_rel(_, wide_tag, value, ptr);

    // Mark input for ingress.
    ingress(ptr) <-- input_expr(wide_tag, value), primary_rel(_, wide_tag, value, ptr);

    // mark ingress conses for unhashing.
    unhash4(CONS_TAG, digest, ptr) <--
        ingress(ptr), if ptr.0 == CONS_TAG,
        ptr_value(ptr, digest),
        primary_mem(&CONS_TAG, _, digest, _);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest, ptr), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    // Allocate the car and cdr with appropriate priorities to avoid address conflict.
    alloc(car_tag, car_value, 0),
    alloc(cdr_tag, cdr_value, 1) <--
        unhash4(&CONS_TAG, digest, _),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    f_value(Ptr(F_TAG, f), Wide::widen(f)) <-- alloc(&F_TAG, value, _), let f = value.f();

    cons_rel(car, cdr, Ptr(CONS_TAG, addr.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        primary_mem(&CONS_TAG, _, digest, addr),
        primary_rel(_, wide_car_tag, car_value, car),
        primary_rel(_, wide_cdr_tag, cdr_value, cdr);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.0 == F_TAG;
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

    output_expr(wide_tag, value) <-- output_ptr(ptr), primary_rel(_, wide_tag, value, ptr);

    ////////////////////////////////////////////////////////////////////////////////
    // map_double
    //
    // This is just a silly input->output function that maps f(x)->2x over the input tree,
    // for use as a development example. This will be replaced by e.g. Lurk eval.

    relation map_double_input(Ptr, LE); // (input, priority)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)

    ptr(doubled),
    map_double(ptr, doubled) <-- map_double_input(ptr, _), if ptr.0 == F_TAG, let doubled = Ptr(F_TAG, ptr.1 * 2);

    map_double_input(ptr, 0) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr, _), if ptr.0 == CONS_TAG;

    map_double_input(car, 2*priority), map_double_input(cdr, (2*priority) + 1) <-- map_double_input(cons, priority), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr, priority) <--
        map_double_input(ptr, priority), if ptr.0 == CONS_TAG,
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


    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag),
        ptr_value(car, car_value),
        ptr_tag(cdr, cdr_tag),
        ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, allocator().hash4(*a, *b, *c, *d)) <-- hash4(ptr, a, b, c, d);

    ptr(car),
    ptr(cdr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, _),
        primary_rel(_, wide_car_tag, car_value, car) ,
        primary_rel(_, wide_cdr_tag, cdr_value, cdr);
}

// This simple allocation program demonstrates how we can use ascent's lattice feature to achieve memoized allocation
// with an incrementing counter but without mutable state held outside the program (as in the Allocator) above.
ascent! {
    struct SimpleAllocProgram;

    // Input must be added one element at a time, so we do it within the program.
    relation input(usize, usize); // (a, b)

    // Memory holds two elements, and an address allocated for each unique row. The Dual annotation ensures that if an
    // (a, b, addr) tuple is added when an (a, b, addr') tuple already exists, the lower (first-allocated) address will
    // be used.
    lattice mem(usize, usize, Dual<usize>); // (a, b, addr)

    // The counter holds the value of the most-recently allocated address, initially zero (so there will be no memory
    // with allocated address 0).
    lattice counter(usize) = vec![(0,)]; // (addr)

    // Add each new input to mem, using the next counter value as address.
    mem(a, b, Dual(counter + 1)) <-- input(a, b), counter(counter);

    // The address of every new tuple in mem is added to counter. Since counter has only a single lattice attribute, the
    // new value will replace the old if greater than the old.
    counter(max.0) <-- mem(_, _, max);

    // When counter is incremented, generate a new tuple. The generation rules will only produce six unique inputs.
    input(a, b) <-- counter(x) if *x < 100, let a = *x % 2, let b = *x % 3;

}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_test_cons() {
        allocator().init();

        // (1 . 2)
        let c1_2 = allocator().hash4(F_WIDE_TAG, Wide::widen(1), F_WIDE_TAG, Wide::widen(2));
        // (2 . 3)
        let c2_3 = allocator().hash4(F_WIDE_TAG, Wide::widen(2), F_WIDE_TAG, Wide::widen(3));
        // (2 . 4)
        let c2_4 = allocator().hash4(F_WIDE_TAG, Wide::widen(2), F_WIDE_TAG, Wide::widen(4));
        // (4 . 6)
        let c4_6 = allocator().hash4(F_WIDE_TAG, Wide::widen(4), F_WIDE_TAG, Wide::widen(6));
        // (4 . 8)
        let c4_8 = allocator().hash4(F_WIDE_TAG, Wide::widen(4), F_WIDE_TAG, Wide::widen(8));
        // ((1 . 2) . (2 . 4))
        let c1_2__2_4 = allocator().hash4(CONS_WIDE_TAG, c1_2, CONS_WIDE_TAG, c2_4);
        // ((1 . 2) . (2 . 3))
        let c1_2__2_3 = allocator().hash4(CONS_WIDE_TAG, c1_2, CONS_WIDE_TAG, c2_3);
        // ((2 . 4) . (4 . 8))
        let c2_4__4_8 = allocator().hash4(CONS_WIDE_TAG, c2_4, CONS_WIDE_TAG, c4_8);
        // ((2 . 4) . (4 . 6))
        let c2_4__4_6 = allocator().hash4(CONS_WIDE_TAG, c2_4, CONS_WIDE_TAG, c4_6);

        assert_eq!(
            Wide([
                4038165649, 752447834, 1060359009, 3812570985, 3368674057, 2161975811, 2601257232,
                1536661076
            ]),
            c1_2
        );
        assert_eq!(
            Wide([
                3612283221, 1832028404, 1497027099, 2489301282, 1316351861, 200274982, 901424954,
                3034146026
            ]),
            c2_4
        );

        assert_eq!(
            Wide([
                2025499267, 1838322365, 1110884429, 2931761435, 2978718557, 3907840380, 1112426582,
                1522367847
            ]),
            c1_2__2_4
        );

        let mut test = |input, expected_output, cons_count| {
            let mut prog = AllocationProgram::default();

            prog.input_expr = vec![(CONS_WIDE_TAG, input)];
            prog.run();

            assert_eq!(vec![(CONS_WIDE_TAG, expected_output)], prog.output_expr);
            assert_eq!(cons_count, prog.cons_mem.len());
            assert_eq!(cons_count, prog.primary_mem.len());
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

        // println!("{}", prog.relation_sizes_summary());

        // let AllocationProgram {
        //     car,
        //     cdr,
        //     ptr_tag,
        //     mut ptr_value,
        //     cons,
        //     cons_rel,
        //     cons_value,
        //     cons_mem,
        //     primary_mem,
        //     ptr,
        //     hash4,
        //     hash4_rel,
        //     ingress,
        //     egress,
        //     primary_rel,
        //     input_expr,
        //     output_expr,
        //     f_value,
        //     alloc,
        //     map_double_input,
        //     map_double,
        //     input_ptr,
        //     output_ptr,
        //     primary_counter,
        //     ..
        // } = prog;

        // ptr_value.sort_by_key(|(key, _)| *key);
    }

    #[test]
    fn test_simple_alloc() {
        let mut prog = SimpleAllocProgram::default();

        prog.run();

        println!("{}", prog.relation_sizes_summary());

        let SimpleAllocProgram {
            counter, mut mem, ..
        } = prog;

        mem.sort_by_key(|(_, _, c)| (*c));
        mem.reverse();

        assert_eq!(6, mem.len());
        // Counter relation never grows, but its single value evolves incrementally.
        assert_eq!(1, counter.len());
        assert_eq!((6,), counter[0]);
        assert_eq!((0, 0, Dual(1)), mem[0]);
        assert_eq!((1, 1, Dual(2)), mem[1]);
        assert_eq!((0, 2, Dual(3)), mem[2]);
        assert_eq!((1, 0, Dual(4)), mem[3]);
        assert_eq!((0, 1, Dual(5)), mem[4]);
        assert_eq!((1, 2, Dual(6)), mem[5]);

        // NOTE: If memoization were not working, we would expect (0, 1, Dual(7)) next.
        assert!(mem.get(6).is_none());
    }
}
