use std::collections::HashMap;
use std::sync::{Mutex, MutexGuard, OnceLock};

use ascent::aggregators::count;
use ascent::ascent;

type LE = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct F(LE);

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
struct Ptr(LE, LE);

#[derive(Debug)]
struct Allocator {}

fn get_allocation_map() -> MutexGuard<'static, HashMap<LE, LE>> {
    static MAP: OnceLock<Mutex<HashMap<LE, LE>>> = OnceLock::new();
    MAP.get_or_init(Default::default).lock().expect("poisoned")
}

impl Allocator {
    fn alloc(tag: LE) -> Ptr {
        let mut map = get_allocation_map();
        let idx = map.entry(tag).and_modify(|x| *x += 1).or_insert(0);
        Ptr(tag, *idx)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Wide([LE; 8]);

impl Wide {
    fn widen(elt: LE) -> Wide {
        Wide([elt; 8])
    }
}

const F_TAG: LE = 0;
const CONS_TAG: LE = 1;

const F_WIDE_TAG: Wide = Wide([F_TAG, 0, 0, 0, 0, 0, 0, 0]);
const CONS_WIDE_TAG: Wide = Wide([CONS_TAG, 0, 0, 0, 0, 0, 0, 0]);

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
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)
    relation unhash4(Ptr);

    // inclusion triggers *_value relations.
    relation ingress(Ptr); // (ptr)

    // inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    relation f_value(Ptr, Wide); // (ptr, immediate-wide-value)
    relation cons_value(Ptr, Wide); // (cons, value)

    // all known `Ptr`s should be added to ptr.
    relation ptr(Ptr); // (ptr)
    relation ptr_tag(Ptr, Wide); // (ptr, tag)
    relation tag(LE, Wide); // (short-tag, wide-tag)
    relation ptr_value(Ptr, Wide); // (ptr, value)

    ////////////////////////////////////////////////////////////////////////////////
    // Rules

    // Mark input conses as conses.
    cons(a, b) <-- input_cons(a, b);

    // When a pair is first marked as a cons (and only once), allocate a ptr for it, and populate its
    // constructor and projector relations.
    cons_rel(car, cdr, cons) <-- cons(car, cdr), let cons = Allocator::alloc(CONS_TAG);
    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, value) <-- ptr(ptr), if ptr.0 == F_TAG, let value = Wide::widen(ptr.1);

    ptr(ptr) <-- egress(ptr);

    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag),
        ptr_value(car, car_value),
        ptr_tag(cdr, cdr_tag),
        ptr_value(cdr, cdr_value);

    hash4_rel(a, b, c, d, digest) <--
        hash4(ptr, a, b, c, d),
        let digest = bogus_hash4(*a, *b, *c, *d);

    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    unhash4(ptr) <-- ingress(ptr), if ptr.0 == CONS_TAG;

    hash4_rel(a, b, c, d, digest) // TODO: cons_rel(car, cdr, ptr)
        <--
        unhash4(ptr),
        if ptr.0 == CONS_TAG,
        ptr_value(ptr, digest),
        let (a, b, c, d) = bogus_unhash4(digest),
        // TODO: Add relations to support allocating car and cdr based on their tags,
        let car = todo!(), let cdr = todo!();

    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), (f_value(ptr, value) || cons_value(ptr, value));
}

// FIXME
fn bogus_hash4(a: Wide, b: Wide, c: Wide, d: Wide) -> Wide {
    Wide([
        a.0[0], a.0[1], b.0[0], b.0[1], c.0[0], c.0[1], d.0[0], 999999,
    ])
}

fn bogus_unhash4(digest: &Wide) -> (Wide, Wide, Wide, Wide) {
    todo!();
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_cons() {
        let mut prog = AllocationProgram::default();

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
        prog.tag = vec![(F_TAG, F_WIDE_TAG), (CONS_TAG, CONS_WIDE_TAG)];
        prog.egress = vec![(cons_ptr3,)];
        //        prog.ptr = vec![(ptr1,), (ptr2,), (cons_ptr0,)];
        prog.run();

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

        let cons_ptr0_hash = bogus_hash4(F_WIDE_TAG, Wide::widen(1), F_WIDE_TAG, Wide::widen(2));
        let cons_ptr1_hash = bogus_hash4(F_WIDE_TAG, Wide::widen(3), F_WIDE_TAG, Wide::widen(4));
        let cons_ptr3_hash =
            bogus_hash4(CONS_WIDE_TAG, cons_ptr0_hash, CONS_WIDE_TAG, cons_ptr1_hash);

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
    }
}
