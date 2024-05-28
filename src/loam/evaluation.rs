use crate::loam::allocation::{allocator, Allocator, Ptr, Tag, Wide, WidePtr, F, LE};

use ascent::{ascent, Dual};

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Hash)]
pub struct CEK<T> {
    expr: T,
    env: T,
    cont: T, // for simplicity, let continuations be first-class data. make it an error to evaluate one, though.
}

// Because it's hard to share code between ascent programs, this is a copy of `AllocationProgram`, replacing the `map_double` function
// with evaluation.
ascent! {
    struct EvaluationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = vec![(Tag::F.elt(), Tag::F.wide()), (Tag::Cons.elt(), Tag::Cons.wide())]; // (short-tag, wide-tag)

    relation ptr_value(Ptr, Wide); // (ptr, value)}
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    // relation input_cons(Ptr, Ptr); // (car, cdr)

    relation input_cek(CEK<WidePtr>); // (cek)
    relation output_cek(CEK<WidePtr>); // (cek)
    relation input_ptr_cek(CEK<Ptr>); // (cek)
    relation output_ptr_cek(CEK<Ptr>); // (cek)

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
    primary_rel(Tag::F.elt(), Tag::F.wide(), value, ptr) <-- f_value(ptr, value);

    // Register ptr.
    ptr(ptr), ptr_tag(ptr, wide_tag), ptr_value(ptr, value) <-- primary_rel(_tag, wide_tag, value, ptr);

    // cons-addr is for this cons type-specific memory.
    lattice cons_mem(Ptr, Ptr, Dual<LE>); // (car, cdr, cons-addr)
    // Cons
    primary_counter(addr.0) <-- cons_mem(_, _, addr);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(counter + 1 + priority)) <-- cons(car, cdr, priority), primary_counter(counter);

    primary_mem(Tag::Cons.elt(), Tag::Cons.wide(), digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    // If cons_mem was populated otherwise, still populate cons(...).
    cons(car, cdr, 0), cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, Tag::Cons.wide()) <-- cons_rel(car, cdr, cons);
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

    // Ingress 1: mark input CEK for allocation.
    alloc(expr_tag, cek.expr.1, 0),
    alloc(env_tag, cek.env.1, 1),
    alloc(cont_tag, cek.cont.1, 2) <--
        input_cek(cek),
        tag(expr_tag, cek.expr.0),
        tag(env_tag, cek.env.0),
        tag(cont_tag, cek.cont.0);

    // Populate input_ptr_cek.
    //    ingress(expr), ingress(env), ingress(cont), // TODO: We can defer ingress. For example, no need to destructure an env if expr is self-evaluating.
    input_ptr_cek(CEK{expr: *expr, env: *env, cont: *cont}) <--
        input_cek(cek),
        primary_rel(_, cek.expr.0, cek.expr.1, expr),
        primary_rel(_, cek.env.0, cek.env.1, env),
        primary_rel(_, cek.cont.0, cek.cont.1, cont);


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


    // The output_ptr_cek is marked for egress.
    egress(cek.expr), egress(cek.env), egress(cek.cont) <-- output_ptr_cek(cek);

    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    output_cek(CEK { expr: WidePtr(*expr_wide_tag, *expr_value),
                     env: WidePtr(*env_wide_tag, *env_value),
                     cont: WidePtr(*cont_wide_tag, *cont_value)
                    }) <--
        output_ptr_cek(cek),
        primary_rel(cek.expr.0, expr_wide_tag, expr_value, cek.expr),
        primary_rel(cek.expr.0, env_wide_tag,  env_value, cek.env),
        primary_rel(cek.expr.0, cont_wide_tag, cont_value, cek.cont);

    ////////////////////////////////////////////////////////////////////////////////
    // eval

    relation eval_input(CEK<Ptr>, LE); // (input, priority)
    relation eval(CEK<Ptr>, CEK<Ptr>); // (input-ptr, output-ptr)

    eval_input(cek, 0) <-- input_ptr_cek(cek);

    // expr is F
    // F is self-evaluating.
    eval(cek, cek) <-- eval_input(cek, _), if cek.expr.0 == Tag::F.elt();

    // expr is CONS


    output_ptr_cek(output) <-- input_ptr_cek(input), eval(input, output);

    ////////////////////////////////////////////////////////////////////////////////


    ////////////////////////////////////////////////////////////////////////////////
    // map_double
    //
    // This is just a silly input->output function that maps f(x)->2x over the input tree,
    // for use as a development example. This will be replaced by e.g. Lurk eval.

    relation map_double_input(Ptr, LE); // (input, priority)
    relation map_double(Ptr, Ptr); // (input-ptr, output-ptr)

    ptr(doubled),
    map_double(ptr, doubled) <-- map_double_input(ptr, _), if ptr.0 == Tag::F.elt(), let doubled = Ptr(Tag::F.elt(), ptr.1 * 2);

    // map_double_input(ptr, 0) <-- input_ptr(ptr);

    ingress(ptr) <-- map_double_input(ptr, _), if ptr.0 == Tag::Cons.elt();

    map_double_input(car, 2*priority), map_double_input(cdr, (2*priority) + 1) <-- map_double_input(cons, priority), cons_rel(car, cdr, cons);

    relation map_double_cont(Ptr, Ptr, Ptr); //

    map_double_cont(ptr, double_car, double_cdr),
    cons(double_car, double_cdr, priority) <--
        map_double_input(ptr, priority), if ptr.0 == Tag::Cons.elt(),
        cons_rel(car, cdr, ptr),
        map_double(car, double_car),
        map_double(cdr, double_cdr);

    map_double(ptr, double_cons) <--
        map_double_cont(ptr, double_car, double_cdr),
        cons_rel(double_car, double_cdr, double_cons);

    // // For now, just copy input straight to output. Later, we will evaluate.
    // output_ptr(output) <-- input_ptr(input), map_double(input, output);

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
        let c1_2 = allocator().hash4(Tag::F.wide(), Wide::widen(1), Tag::F.wide(), Wide::widen(2));
        // (2 . 3)
        let c2_3 = allocator().hash4(Tag::F.wide(), Wide::widen(2), Tag::F.wide(), Wide::widen(3));
        // (2 . 4)
        let c2_4 = allocator().hash4(Tag::F.wide(), Wide::widen(2), Tag::F.wide(), Wide::widen(4));
        // (4 . 6)
        let c4_6 = allocator().hash4(Tag::F.wide(), Wide::widen(4), Tag::F.wide(), Wide::widen(6));
        // (4 . 8)
        let c4_8 = allocator().hash4(Tag::F.wide(), Wide::widen(4), Tag::F.wide(), Wide::widen(8));
        // ((1 . 2) . (2 . 4))
        let c1_2__2_4 = allocator().hash4(Tag::Cons.wide(), c1_2, Tag::Cons.wide(), c2_4);
        // ((1 . 2) . (2 . 3))
        let c1_2__2_3 = allocator().hash4(Tag::Cons.wide(), c1_2, Tag::Cons.wide(), c2_3);
        // ((2 . 4) . (4 . 8))
        let c2_4__4_8 = allocator().hash4(Tag::Cons.wide(), c2_4, Tag::Cons.wide(), c4_8);
        // ((2 . 4) . (4 . 6))
        let c2_4__4_6 = allocator().hash4(Tag::Cons.wide(), c2_4, Tag::Cons.wide(), c4_6);

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

        // let mut test = |input, expected_output, cons_count| {
        //     let mut prog = EvaluationProgram::default();

        //     prog.input_expr = vec![(Tag::Cons.wide(), input)];
        //     prog.run();

        //     assert_eq!(vec![(Tag::Cons.wide(), expected_output)], prog.output_expr);
        //     assert_eq!(cons_count, prog.cons_mem.len());
        //     assert_eq!(cons_count, prog.primary_mem.len());
        //     prog
        // };

        // // Mapping (lambda (x) (* 2 x)) over ((1 . 2) . (2 . 3))) yields ((2 . 4) . (4 . 6)).
        // // We expect 6 total conses.
        // test(c1_2__2_3, c2_4__4_6, 6);

        // // Mapping (lambda (x) (* 2 x)) over ((1 . 2) . (2 . 4))) yields ((2 . 4) . (4 . 8)).
        // // We expect only 5 total conses, because (2 . 4) is duplicated in the input and output,
        // // so the allocation should be memoized.
        // let prog = test(c1_2__2_4, c2_4__4_8, 5);

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
}
