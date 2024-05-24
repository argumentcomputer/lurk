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
    relation cons(Ptr, Ptr); // (car, cdr)
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
    lattice cons_counter(LE) = vec![(0,)];
    // Cons counter must always hold largest address.
    cons_counter(addr.0) <-- cons_mem(_, _, addr);
    // Cons
    primary_counter(addr.0) <-- cons_mem(_, _, addr);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(counter + 1)) <-- cons(car, cdr), primary_counter(counter);

    // If cons_mem was populated otherwise, still populate cons(...).
    cons(car, cdr), cons_rel(car, cdr, Ptr(CONS_TAG, addr.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, CONS_WIDE_TAG) <-- cons_rel(car, cdr, cons);
    ptr_value(cons, value) <-- cons_rel(car, cdr, cons), cons_value(cons, value);

    // Provide ptr_tag and ptr_value when known.
    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), cons_value(ptr, value);
    ptr_value(ptr, value) <-- ptr(ptr), f_value(ptr, value);

    // The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)

    cons(car, cdr) <-- cons_rel(car, cdr, _);

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

    // Provide cons_value when known.
    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    relation map_double_input(Ptr); // (input)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)

    // This is just a silly input->output function that maps f(x)->2x over the input tree,
    // for use as a development example.
    map_double(ptr, Ptr(F_TAG, ptr.1 * 2)) <-- map_double_input(ptr), if ptr.0 == F_TAG;

    map_double_input(ptr) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr), if ptr.0 == CONS_TAG;

    map_double_input(car), map_double_input(cdr) <-- map_double_input(cons), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr) <--
        map_double_input(ptr), if ptr.0 == CONS_TAG,
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    output_ptr(output) <-- input_ptr(input), map_double(input, output);

    // For now, just copy input straight to output. Later, we will evaluate.
    output_ptr(out) <-- input_ptr(ptr), map_double(ptr, out);


    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    output_expr(wide_tag, value) <-- output_ptr(ptr), primary_rel(_, wide_tag, value, ptr);

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
        let mut prog = AllocationProgram::default();
        allocator().init();

        let (ptr0, ptr1, ptr2, ptr3, ptr4) = (
            Ptr(F_TAG, 0),
            Ptr(F_TAG, 1),
            Ptr(F_TAG, 2),
            Ptr(F_TAG, 3),
            Ptr(F_TAG, 4),
        );
        let (cons_ptr0, cons_ptr1, cons_ptr2, cons_ptr3, cons_ptr4) = (
            Ptr(CONS_TAG, 0),
            Ptr(CONS_TAG, 1),
            Ptr(CONS_TAG, 2),
            Ptr(CONS_TAG, 3),
            Ptr(CONS_TAG, 4),
        );

        // (3 . 4)
        let c0 = allocator().hash4(F_WIDE_TAG, Wide::widen(3), F_WIDE_TAG, Wide::widen(4));
        // (2 3 . 4)
        let c1 = allocator().hash4(F_WIDE_TAG, Wide::widen(2), CONS_WIDE_TAG, c0);
        // (1 2 3 . 4)
        let c2 = allocator().hash4(F_WIDE_TAG, Wide::widen(1), CONS_WIDE_TAG, c1);

        prog.input_expr = vec![(CONS_WIDE_TAG, c1)];

        assert_eq!(
            Wide([
                1293148110, 2402141028, 509705422, 782425695, 3078971211, 3971189782, 958090466,
                761772301
            ]),
            c0
        );
        assert_eq!(
            Wide([
                248144713, 2177838085, 3145750114, 4129543510, 1108271234, 3833440321, 1267237783,
                4259360553
            ]),
            c1
        );

        assert_eq!(
            Wide([
                2510325143, 2058981605, 3766814192, 1184441934, 4228369995, 3952767779, 3713191526,
                1219339775
            ]),
            c2
        );
        dbg!("Running: ------------------------------");
        prog.run();

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
            primary_mem,
            ptr,
            hash4,
            hash4_rel,
            ingress,
            egress,
            primary_rel,
            input_expr,
            output_expr,
            f_value,
            alloc,
            map_double_input,
            map_double,
            input_ptr,
            output_ptr,
            primary_counter,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            ingress,
            cons,
            cons_rel,
            cons_mem,
            ptr_value,
            primary_mem,
            // &primary_rel,
            // &ptr,
            // &cons_mem,
            egress,
            input_ptr,
            output_ptr,
            // &input_expr,
            // &output_expr,
            // &hash4,
            // &hash4_rel,
            // allocator().digest_cache.len(),
            // cons_value,
            // ptr,
            // f_value,
            // alloc,
            // cons_addr_primary_addr,
            map_double_input,
            map_double,
            primary_counter
        );

        panic!("uiop");
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
