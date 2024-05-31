use crate::loam::allocation::{allocator, Allocator};
use crate::loam::{Cons, Elemental, Ptr, Sexp, Sym, Tag, Valuable, Wide, WidePtr, F, LE};

use ascent::{ascent, Dual};

struct Memory {}

impl Memory {
    fn initial_sym_relation() -> Vec<(Wide, Dual<LE>)> {
        let syms = Sym::built_in();

        syms.iter()
            .enumerate()
            .map(|(i, sym)| (sym.value(), Dual(i as LE)))
            .collect()
    }
    fn initial_sym_counter() -> Vec<(LE,)> {
        vec![(Sym::built_in().len() as LE,)]
    }
    fn sym_ptr(sym: Sym) -> Ptr {
        let addr = Sym::built_in()
            .iter()
            .position(|s| *s == sym)
            .expect("not a built-in symbol");
        Ptr(Tag::Sym.elt(), addr as u32)
    }

    fn ptr_sym(ptr: Ptr) -> Sym {
        assert_eq!(Tag::Sym.elt(), ptr.0);

        Sym::built_in()[ptr.1 as usize]
    }

    fn initial_tag_relation() -> Vec<(LE, Wide)> {
        Tag::tag_wide_relation()
    }
}

impl Sym {
    fn is_arith(&self) -> bool {
        // Note, all of these will be variadic.
        matches!(self, Self::Char('+' | '-' | '*' | '/' | '%'))
    }

    fn neutral_element(&self) -> F {
        match self {
            Self::Char('+') => F(0),
            Self::Char('*') => F(1),
            _ => unimplemented!(),
        }
    }

    fn apply_op(&self, a: F, b: F) -> F {
        match self {
            Self::Char('+') => F(a.0 + b.0),
            Self::Char('*') => F(a.0 * b.0),
            _ => unimplemented!(),
        }
    }
}

// Because it's hard to share code between ascent programs, this is a copy of `AllocationProgram`, replacing the `map_double` function
// with evaluation.
ascent! {
    struct EvaluationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // The standard tag mapping.
    relation tag(LE, Wide) = Memory::initial_tag_relation(); // (short-tag, wide-tag)

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



    relation alloc(LE, Wide); // (tag, value)


    ////////////////////////////////////////////////////////////////////////////////
    // Memory

    ////////////////////////////////////////////////////////////////////////////////
    // Cons

    // The canonical cons Ptr relation.
    relation cons_rel(Ptr, Ptr, Ptr); // (car, cdr, cons)

    // Memory to support conses allocated by digest or contents.
    lattice cons_digest_mem(Wide, Dual<LE>); // (tag, wide-tag, value, addr)
    lattice cons_mem(Ptr, Ptr, Dual<LE>); // (car, cdr, addr)

    // Populating alloc(...) triggers allocation in cons_digest_mem.
    cons_digest_mem(value, Dual(allocator().alloc_addr(Tag::Cons.elt()))) <--
        alloc(tag, value),
        if *tag == Tag::Cons.elt(),
        tag(tag, wide_tag);

    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Cons.value()), ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(allocator().alloc_addr(Tag::Cons.elt()))) <-- cons(car, cdr);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    cons_digest_mem(digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, Tag::Cons.value()) <-- cons_rel(car, cdr, cons);

    ////////////////////////////////////////////////////////////////////////////////
    // Sym

    lattice sym_digest_mem(Wide, Dual<LE>) = Memory::initial_sym_relation(); // (digest, addr)
    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Sym.value()), ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), addr.0);
    // todo: sym_value


    ////////////////////////////////////////////////////////////////////////////////

    // Provide ptr_tag and ptr_value when known.
    ptr_tag(ptr, wide_tag) <-- ptr(ptr), tag(ptr.0, wide_tag);
    ptr_value(ptr, value) <-- ptr(ptr), cons_value(ptr, value);
    ptr_value(ptr, value) <-- ptr(ptr), f_value(ptr, value);
    // todo: sym_value

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    alloc(tag, wide_ptr.1) <-- input_expr(wide_ptr), tag(tag, wide_ptr.0);

    ingress(ptr),
    input_ptr(ptr) <-- input_expr(wide_ptr), ptr_tag(ptr, wide_ptr.0), ptr_value(ptr, wide_ptr.1);

    // mark ingress conses for unhashing.
    unhash4(Tag::Cons.elt(), digest, ptr) <--
        ingress(ptr), if ptr.is_cons(),
        ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest, ptr), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(&Tag::Cons.elt(), digest, _),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    f_value(Ptr(Tag::F.elt(),f), Wide::widen(f)) <-- alloc(&Tag::F.elt(), value), let f = value.f();
    ptr(ptr), ptr_value(ptr, Wide::widen(f)) <--
        alloc(&Tag::Nil.elt(), value), let f = value.f(), let ptr = Ptr(Tag::Nil.elt(), f);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        cons_digest_mem(digest, addr),
        ptr_tag(car, wide_car_tag), ptr_tag(cdr, wide_cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.is_f();
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

    ptr_tag(ptr, Tag::F.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_f();

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
    // eval

    relation eval_input(Ptr, Ptr); // (expr, env)
    relation eval(Ptr, Ptr, Ptr); // (input-expr, env, output-expr)

    // FIXME: We need to actually allocate, or otherwise define this Nil Ptr.
    // It's fine for now, while env is unused.
    eval_input(expr, Ptr::nil()) <-- input_ptr(expr);

    // expr is F: self-evaluating.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_f();

    // expr is Nil: self-evaluating. TODO: check value == 0.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_nil();

    // expr is CONS
    ingress(expr) <-- eval_input(expr, env), if expr.is_cons();

    relation reduce_arith(Ptr, Ptr, Sym, F, Ptr); // (expr, env, op, acc, tail)

    // If head is arithmetic op, reduce it with its neutral element.
    ingress(tail), reduce_arith(expr, env, op, op.neutral_element(), tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), let op = Memory::ptr_sym(*head), if op.is_arith();

    // When reducing arithmetic with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <--
        reduce_arith(expr, env, op, acc, tail), cons_rel(car, cdr, tail);

    // When reducing arithmetic, if car has been evaled and is F, apply the op to it and the acc, then recursively
    // reduce the acc and new tail.
    ingress(cdr), reduce_arith(expr, env, op, op.apply_op(*acc, F(evaled_car.1)), cdr) <--
        reduce_arith(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car), if evaled_car.is_f();

    // reducing arithmetic operation with an empty (nil) tail
    eval(expr, env, Ptr(Tag::F.elt(), acc.0)) <-- reduce_arith(expr, env, _, acc, tail), if tail.is_nil();

    // output
    output_ptr(output) <-- input_ptr(input), eval(input, Ptr::nil(), output);

    ////////////////////////////////////////////////////////////////////////////////

}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_test_eval() {
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
            allocator().init();

            // F is self-evaluating.
            let f = F(123);
            test(f.into(), f.into());
        }
        let prog = {
            allocator().init();

            // Nil is self-evaluating.
            let nil = WidePtr::nil();

            test(nil.into(), nil.into())
        };

        let prog = {
            allocator().init();

            // (+)
            let add = Cons::list(vec![Sexp::Sym(Sym::Char('+'))]);

            test(add.into(), F(0).into())
        };

        let prog = {
            allocator().init();

            // (+ 1)
            let add = Cons::list(vec![Sexp::Sym(Sym::Char('+')), Sexp::F(F(1))]);

            test(add.into(), F(1).into())
        };

        let prog = {
            allocator().init();

            // (+ 1 2)
            let add = Cons::list(vec![
                Sexp::Sym(Sym::Char('+')),
                Sexp::F(F(1)),
                Sexp::F(F(2)),
            ]);

            test(add.into(), F(3).into())
        };

        let prog = {
            allocator().init();

            // (+ 1 2 3)
            let add = Cons::list(vec![
                Sexp::Sym(Sym::Char('+')),
                Sexp::F(F(1)),
                Sexp::F(F(2)),
                Sexp::F(F(3)),
            ]);

            test(add.into(), F(6).into())
        };

        let prog = {
            allocator().init();

            // (*)
            let mul = Cons::list(vec![Sexp::Sym(Sym::Char('*'))]);

            test(mul.into(), F(1).into())
        };

        let prog = {
            allocator().init();

            // (* 2)
            let mul = Cons::list(vec![Sexp::Sym(Sym::Char('*')), Sexp::F(F(2))]);

            test(mul.into(), F(2).into())
        };

        let prog = {
            allocator().init();

            // (* 2 3)
            let mul = Cons::list(vec![
                Sexp::Sym(Sym::Char('*')),
                Sexp::F(F(2)),
                Sexp::F(F(3)),
            ]);

            test(mul.into(), F(6).into())
        };

        let prog = {
            allocator().init();

            // (+ 2 3 4)
            let mul = Cons::list(vec![
                Sexp::Sym(Sym::Char('*')),
                Sexp::F(F(2)),
                Sexp::F(F(3)),
                Sexp::F(F(4)),
            ]);

            test(mul.into(), F(24).into())
        };

        let prog = {
            allocator().init();

            // (+ 5 (* 3 4))
            let mul = Cons::list(vec![
                Sexp::Sym(Sym::Char('+')),
                Sexp::F(F(5)),
                Sexp::Cons(Cons::list_x(vec![
                    Sexp::Sym(Sym::Char('*')),
                    Sexp::F(F(3)),
                    Sexp::F(F(4)),
                ])),
            ]);

            test(mul.into(), F(17).into())
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
            ptr,
            hash4,
            unhash4,
            hash4_rel,
            ingress,
            egress,
            input_expr,
            output_expr,
            f_value,
            alloc,
            input_ptr,
            output_ptr,
            eval_input,
            eval,
            cons_digest_mem,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            input_expr,
            input_ptr,
            eval_input,
            eval,
            hash4,
            hash4_rel,
            output_ptr,
            output_expr,
            //ptr_value,
            cons_rel,
            cons_mem,
            cons_digest_mem,
            alloc,
            egress
        );

        // panic!("uiop");
    }
}
