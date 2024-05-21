use std::collections::BTreeMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::{Mutex, MutexGuard, OnceLock};

use ascent::ascent;

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
        Wide([elt; 8])
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
    // FIXME: make non-bogus versions
    pub fn bogus_hash4(&mut self, a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
        let mut h = DefaultHasher::new();
        let preimage = vec![a, b, c, d];

        // This is pure nonsense, but it should avoid collisions for testing.
        preimage.hash(&mut h);
        let hash = h.finish();
        let h1 = (hash & 0xFFFFFFFF) as u32;
        let h2 = (hash >> 32) as u32;
        let digest = Wide([h1, h2, h1, h2, h1, h2, h1, h2]);

        self.digest_cache.insert(preimage.clone(), digest);
        self.preimage_cache.insert(digest, preimage.clone());

        digest
    }
    pub fn bogus_unhash4(&mut self, digest: &Wide) -> Option<[Wide; 4]> {
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

    relation ptr_value(Ptr, Wide); // (ptr, value)}
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    relation input_cons(Ptr, Ptr); // (car, cdr)

    // triggers allocation once per unique cons
    relation cons(Ptr, Ptr); // (car, cdr)
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)
    relation car(Ptr, Ptr); // (cons, car)
    relation cdr(Ptr, Ptr); // (cons, cdr)
    relation hash4(Ptr, Wide, Wide, Wide, Wide); // (a, b, c, d)
    relation unhash4(LE, Wide); // (tag, digest)
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)

    // inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    relation f_value(Ptr, Wide); // (ptr, immediate-wide-value)
    relation cons_value(Ptr, Wide); // (cons, value)

    // all known `Ptr`s should be added to ptr.
    relation ptr(Ptr); // (ptr)
    relation ptr_tag(Ptr, Wide); // (ptr, tag)
    relation tag(LE, Wide); // (short-tag, wide-tag)
    relation ptr_value(Ptr, Wide); // (ptr, value)

    // supporting ingress
    // inclusion triggers *_value relations.
    relation ingress(LE, Wide); // (tag, value)
    relation tag_value_rel(LE, Wide, Wide, Ptr); // (tag, wide-tag, value, ptr)

    ////////////////////////////////////////////////////////////////////////////////
    // Rules

    // Mark input conses as conses. [Input may be wrong name. This is mainly to test egress.]
    cons(a, b) <-- input_cons(a, b);

    // When a pair is first marked as a cons (and only once), allocate a ptr for it, and populate its
    // constructor and projector relations.
    cons_rel(car, cdr, allocator().alloc(CONS_TAG)) <-- cons(car, cdr);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.0 == F_TAG;

    ptr(ptr) <-- egress(ptr);

    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag),
        ptr_value(car, car_value),
        ptr_tag(cdr, cdr_tag),
        ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, allocator().bogus_hash4(*a, *b, *c, *d)) <-- hash4(ptr, a, b, c, d);
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest), let [a, b, c, d] = allocator().bogus_unhash4(digest).unwrap();

    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    ptr(ptr) <-- tag_value_rel(_tag, _wide_tag, _value, ptr);

    unhash4(CONS_TAG, digest) <--
        ingress(tag, digest),
        tag_value_rel(tag, _, digest, ptr),
        if ptr.0 == CONS_TAG;

    tag_value_rel(car_tag, wide_car_tag, car_value, allocator().alloc(*car_tag)),
    tag_value_rel(cdr_tag, wide_cdr_tag, cdr_value, allocator().alloc(*cdr_tag)) <--
        unhash4(&CONS_TAG, digest),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    cons(car, cdr),
    ptr(car),
    ptr(cdr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, _),
        tag_value_rel(_, wide_car_tag, car_value, car),
        tag_value_rel(_, wide_cdr_tag, cdr_value, cdr);

    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), (f_value(ptr, value) || cons_value(ptr, value));
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cons() {
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

        let expected_cons0_value =
            allocator().bogus_hash4(F_WIDE_TAG, Wide::widen(1), F_WIDE_TAG, Wide::widen(2));

        assert_eq!(
            Wide([
                3816709126, 1874310961, 3816709126, 1874310961, 3816709126, 1874310961, 3816709126,
                1874310961,
            ],),
            expected_cons0_value
        );

        let expected_cons0 = (Ptr(CONS_TAG, 0), expected_cons0_value);

        // Note that input_cons has four pairs, but only three unique pairs. The car and cdr relations extracted below,
        // correctly show only three allocated conses. If we had naively placed four input pairs in the cons relation,
        // the car and cdr relations would show four allocated conses. That's because ascent doesn't try to deduplicate
        // relations concretely supplied from outside the program.
        prog.input_cons = vec![
            (ptr1, ptr2),           // cons_ptr0
            (ptr3, ptr4),           // cons_ptr1
            (ptr2, ptr1),           // cons_ptr2
            (ptr1, ptr2),           // cons_ptr0 (duplicate)
            (cons_ptr0, cons_ptr1), // cons_ptr3
        ];

        // This is actually important: we are providing the canonical tag mapping. TODO: make more explicit.
        prog.tag = vec![(F_TAG, F_WIDE_TAG), (CONS_TAG, CONS_WIDE_TAG)];

        prog.egress = vec![(cons_ptr3,)];

        prog.run();

        println!("{}", prog.relation_sizes_summary());

        let AllocationProgram {
            car,
            cdr,
            ptr_tag,
            mut ptr_value,
            cons_rel,
            cons_value,
            ptr,
            hash4,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        println!("car: {:?}", car);
        println!("cdr: {:?}", cdr);
        println!("ptr_value: {:?}", ptr_value);
        println!("ptr_tag: {:?}", ptr_tag);
        println!("cons_rel: {:?}", cons_rel);
        println!("cons_value: {:?}", cons_value);
        println!("ptr: {:?}", ptr);
        println!("hash4: {:?}", hash4);
        assert_eq!(
            vec![
                (cons_ptr0, ptr1),
                (cons_ptr1, ptr3),
                (cons_ptr2, ptr2),
                (cons_ptr3, cons_ptr0)
            ],
            car
        );
        assert_eq!(
            vec![
                (cons_ptr0, ptr2),
                (cons_ptr1, ptr4),
                (cons_ptr2, ptr1),
                (cons_ptr3, cons_ptr1)
            ],
            cdr
        );

        let cons_ptr0_hash =
            allocator().bogus_hash4(F_WIDE_TAG, Wide::widen(1), F_WIDE_TAG, Wide::widen(2));
        let cons_ptr1_hash =
            allocator().bogus_hash4(F_WIDE_TAG, Wide::widen(3), F_WIDE_TAG, Wide::widen(4));
        let cons_ptr3_hash =
            allocator().bogus_hash4(CONS_WIDE_TAG, cons_ptr0_hash, CONS_WIDE_TAG, cons_ptr1_hash);

        assert_eq!(
            vec![
                (ptr1, Wide::widen(1)),
                (ptr2, Wide::widen(2)),
                (ptr3, Wide::widen(3)),
                (ptr4, Wide::widen(4)),
                (cons_ptr0, cons_ptr0_hash),
                (cons_ptr1, cons_ptr1_hash),
                (cons_ptr3, cons_ptr3_hash)
            ],
            ptr_value
        );

        assert_eq!(expected_cons0, cons_value[0]);
    }
    #[test]
    fn test_ingress() {
        let mut prog = AllocationProgram::default();
        allocator().init();

        // Calculate the digest for (cons 1 2).
        let cons0_value =
            allocator().bogus_hash4(F_WIDE_TAG, Wide::widen(1), F_WIDE_TAG, Wide::widen(2));

        // Initialize the schema.
        prog.tag = vec![(F_TAG, F_WIDE_TAG), (CONS_TAG, CONS_WIDE_TAG)];

        // Allocate the pointer (outside of program).
        let ptr = allocator().alloc(CONS_TAG);
        // Identify a cons for ingress by its explicit content.
        prog.ingress = vec![(CONS_TAG, cons0_value)];
        // Associate this explicit (still-opaque) cons with the allocated pointer.
        prog.tag_value_rel = vec![(CONS_TAG, CONS_WIDE_TAG, cons0_value, ptr)];
        // Add pointer to ptr relation in database, giving the program access to the allocation.
        prog.ptr = vec![(ptr,)];

        // Before running the program, exactly one pointer has been allocated.
        assert_eq!(1, prog.ptr.len());

        prog.run();

        println!("{}", prog.relation_sizes_summary());

        let AllocationProgram {
            car,
            cdr,
            ptr_tag,
            mut ptr_value,
            cons_rel,
            cons_value,
            ptr,
            hash4,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        println!("car: {:?}", car);
        println!("cdr: {:?}", cdr);
        println!("ptr_value: {:?}", ptr_value);
        println!("ptr_tag: {:?}", ptr_tag);
        println!("cons_rel: {:?}", cons_rel);
        println!("cons_value: {:?}", cons_value);
        println!("ptr: {:?}", ptr);
        println!("hash4: {:?}", hash4);

        // Two new pointers were allocated. [FAILING]
        assert_eq!(3, ptr.len());
    }
}
