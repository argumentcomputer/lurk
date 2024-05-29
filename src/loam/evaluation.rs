use crate::loam::allocation::{allocator, Allocator};
use crate::loam::{Cons, Elemental, Ptr, Sexp, Sym, Tag, Valuable, Wide, WidePtr, F, LE};

use ascent::{ascent, Dual};

impl Sym {}

// Because it's hard to share code between ascent programs, this is a copy of `AllocationProgram`, replacing the `map_double` function
// with evaluation.
ascent! {
    struct EvaluationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = Tag::tag_wide_relation(); // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)}
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    // relation input_cons(Ptr, Ptr); // (car, cdr)

    relation input_expr(WidePtr); // (wide-ptr)
    relation output_expr(WidePtr); // (wide-ptr)
    relation input_ptr(Ptr); // (wide-ptr)
    relation output_ptr(Ptr); // (wide-ptr)
    // relation input_cek(CEK<WidePtr>); // (cek)
    // relation output_cek(CEK<WidePtr>); // (cek)
    // relation input_ptr_cek(CEK<Ptr>); // (cek)
    // relation output_ptr_cek(CEK<Ptr>); // (cek)

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
        if *tag != Tag::F.elt(), // F is immediate
        tag(tag, wide_tag),
        primary_counter(addr);

    relation primary_rel(LE, Wide, Wide, Ptr); // (tag, wide-tag, value, ptr)

    // Convert addr to ptr.
    primary_rel(tag, wide_tag, value, Ptr(*tag, addr.0)) <-- primary_mem(tag, wide_tag, value, addr);
    primary_rel(Tag::F.elt(), Tag::F.value(), value, ptr) <-- f_value(ptr, value);

    // Register ptr.
    ptr(ptr), ptr_tag(ptr, wide_tag), ptr_value(ptr, value) <-- primary_rel(_tag, wide_tag, value, ptr);

    // cons-addr is for this cons type-specific memory.
    lattice cons_mem(Ptr, Ptr, Dual<LE>); // (car, cdr, cons-addr)
    // Cons
    primary_counter(addr.0) <-- cons_mem(_, _, addr);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(counter + 1 + priority)) <-- cons(car, cdr, priority), primary_counter(counter);

    primary_mem(Tag::Cons.elt(), Tag::Cons.value(), digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    // If cons_mem was populated otherwise, still populate cons(...).
    cons(car, cdr, 0), cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, Tag::Cons.value()) <-- cons_rel(car, cdr, cons);
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
    alloc(tag, wide_ptr.1, 0) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    input_ptr(ptr) <-- input_expr(wide_ptr), primary_rel(_, wide_ptr.0, wide_ptr.1, ptr);

    // mark ingress conses for unhashing.
    unhash4(Tag::Cons.elt(), digest, ptr) <--
        ingress(ptr), if ptr.0 == Tag::Cons.elt(),
        ptr_value(ptr, digest),
        primary_mem(&Tag::Cons.elt(), _, digest, _);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest, ptr), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    // Allocate the car and cdr with appropriate priorities to avoid address conflict.
    alloc(car_tag, car_value, 0),
    alloc(cdr_tag, cdr_value, 1) <--
        unhash4(&Tag::Cons.elt(), digest, _),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    f_value(Ptr(Tag::F.elt(), f), Wide::widen(f)) <-- alloc(&Tag::F.elt(), value, _), let f = value.f();

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        primary_mem(&Tag::Cons.elt(), _, digest, addr),
        primary_rel(_, wide_car_tag, car_value, car),
        primary_rel(_, wide_cdr_tag, cdr_value, cdr);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.0 == Tag::F.elt();
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

    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), primary_rel(_, wide_tag, value, ptr);

    ////////////////////////////////////////////////////////////////////////////////
    // eval

    relation eval_input(Ptr, Ptr); // (expr, env)
    relation eval(Ptr, Ptr, Ptr); // (input-expr, env, output-expr)

    // FIXME: We need to actually allocate, or otherwise define this Nil Ptr.
    // It's fine for now, while env is unused.
    eval_input(expr, Ptr::nil()) <-- input_ptr(expr);

    // F is self-evaluating.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.0 == Tag::F.elt();

    // Nil is self-evaluating. TODO: check value == 0.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.0 == Tag::Nil.elt();

    // expr is CONS

    output_ptr(output) <-- input_ptr(input), eval(input, _, output);

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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_test_eval() {
        allocator().init();

        // (1 . 2)
        let c1_2 = allocator().hash4(
            Tag::F.value(),
            Wide::widen(1),
            Tag::F.value(),
            Wide::widen(2),
        );

        assert_eq!(
            Wide([
                4038165649, 752447834, 1060359009, 3812570985, 3368674057, 2161975811, 2601257232,
                1536661076
            ]),
            c1_2
        );

        let mut test = |input, expected_output: WidePtr| {
            let mut prog = EvaluationProgram::default();

            prog.input_expr = vec![(input,)];
            prog.run();

            println!("{}", prog.relation_sizes_summary());

            assert_eq!(vec![(expected_output,)], prog.output_expr);
            prog
        };

        let empty_env = WidePtr::nil();

        {
            // F is self-evaluating.
            let f = F(123);
            test(f.into(), f.into());
        }
        {
            // Nil is self-evaluating.
            let nil = WidePtr::nil();

            test(nil.into(), nil.into())
        };

        let prog = {
            // (+ 1 2)
            let plus = Cons::list(vec![
                Sexp::Sym(Sym::Char('+')),
                Sexp::F(F(1)),
                Sexp::F(F(2)),
            ]);

            // fixme
            test(plus.into(), plus.into())
        };

        println!("{}", prog.relation_sizes_summary());

        let EvaluationProgram {
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
            input_ptr,
            output_ptr,
            primary_counter,
            eval_input,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            input_expr,
            input_ptr,
            eval_input,
            output_ptr,
            output_expr,
            alloc
        );

        // panic!("uiop");
    }
}
