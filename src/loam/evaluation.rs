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

    fn ptr_sym(ptr: Ptr, value: Wide) -> Sym {
        assert_eq!(Tag::Sym.elt(), ptr.0);

        let built_in = Sym::built_in();
        if (ptr.1 as usize) < built_in.len() {
            built_in[ptr.1 as usize]
        } else {
            Sym::Opaque(value)
        }
    }

    fn initial_tag_relation() -> Vec<(LE, Wide)> {
        Tag::tag_wide_relation()
    }
}

impl Sym {
    fn is_binding(&self) -> bool {
        matches!(self, Self::Char('l'))
    }

    fn is_left_foldable(&self) -> bool {
        // Note, all of these will be variadic.
        matches!(self, Self::Char('+' | '*'))
    }

    fn is_right_foldable(&self) -> bool {
        // Note, all of these will be variadic.
        matches!(self, Self::Char('-' | '/'))
    }

    fn is_built_in(ptr: &Ptr) -> bool {
        ptr.is_sym() && (ptr.1 as usize) < Self::built_in_count()
    }

    fn neutral_element(&self) -> F {
        match self {
            Self::Char('+' | '-') => F(0),
            Self::Char('*' | '/') => F(1),
            _ => unimplemented!(),
        }
    }

    fn apply_op(&self, a: F, b: F) -> F {
        match self {
            Self::Char('+') => F(a.0 + b.0),
            Self::Char('-') => F(a.0 - b.0),
            Self::Char('*') => F(a.0 * b.0),
            Self::Char('/') => F(a.0 / b.0),
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

    relation toplevel_input(WidePtr, WidePtr); // (expr, env)
    relation output_expr(WidePtr); // (expr)
    relation input_ptr(Ptr, Ptr); // (expr, env)
    relation output_ptr(Ptr); // (wide-ptr)

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
    alloc(expr_tag, expr.1), alloc(env_tag, env.1) <-- toplevel_input(expr, env), tag(expr_tag, expr.0), tag(env_tag, env.0);

    ingress(expr_ptr),
    input_ptr(expr_ptr, env_ptr) <--
        toplevel_input(expr, env),
        ptr_tag(expr_ptr, expr.0), ptr_value(expr_ptr, expr.1),
        ptr_tag(env_ptr, env.0), ptr_value(env_ptr, env.1);

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

    f_value(Ptr(Tag::Sym.elt(),f), Wide::widen(f)) <-- alloc(&Tag::Sym.elt(), value), let f = value.f();

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
    ptr_tag(ptr, Tag::Err.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_err();

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
    eval_input(expr, env) <-- input_ptr(expr, env);

    // expr is F: self-evaluating.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_f();

    // expr is Nil: self-evaluating. TODO: check value == 0.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_nil();

    ////////////////////////////////////////
    // expr is Sym

    relation lookup(Ptr, Ptr, Ptr, Ptr); // (input_expr, input_env, var, env)

    // If expr is not a built-in sym, look it up.
    ingress(env), lookup(expr, env, expr, env) <-- eval_input(expr, env), if expr.is_sym() && !Sym::is_built_in(expr);

    // Unbound variable: If env is nil during lookup, var is unbound. Return an an error.
    eval(input_expr, input_env, Ptr(Tag::Err.elt(), 0)) <-- lookup(input_expr, input_env, _, env), if env.is_nil();

    // If env is a cons, ingress the first binding.
    ingress(binding) <-- lookup(input_expr, input_env, _, env), cons_rel(binding, tail, env);

    // If var matches that bound in first binding, return the binding's value.
    eval(input_expr, input_env, value) <-- lookup(input_expr, input_env, var, env), cons_rel(binding, tail, env), cons_rel(var, value, binding);

    // If var does not match that bound in first binding, lookup var in next env.
    ingress(next_env), lookup(input_expr, input_env, var, next_env) <--
        lookup(input_expr, input_env, var, env), cons_rel(binding, next_env, env), cons_rel(bound_var, value, binding), if bound_var != var;

    ////////////////////////////////////////
    // expr is Cons
    ingress(expr) <-- eval_input(expr, env), if expr.is_cons();

    ////////////////////
    // let binding

    relation bind1(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)
    relation bind2(Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, this-env, bindings)

    ingress(tail), bind1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        let op = Memory::ptr_sym(*head, *head_value), if op.is_binding();

    // // Signal rule
    ingress(bindings), ingress(rest) <--
        bind1(expr, env, tail),
        cons_rel(bindings, rest, tail);

    bind2(expr, env, body, env, bindings) <--
        bind1(expr, env, tail),
        cons_rel(bindings, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: error otherwise

    eval_input(body, this_env) <--
        bind2(expr, env, body, this_env, bindings),
        if bindings.is_nil();

    eval(expr, env, result) <--
        bind2(expr, env, body, this_env, bindings),
        if bindings.is_nil(),
        eval(bod, this_env, result);

    // Signal rule
    ingress(binding), ingress(more_bindings) <--
        bind2(expr, env, body, this_env, bindings),
        cons_rel(binding, more_bindings, bindings);

    // Signal rule
    ingress(binding_tail) <--
        bind2(expr, env, body, this_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding);

    // Signal rule
     cons(var, val) <--
        bind2(expr, env, body, this_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(val, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // Signal rule
     cons(env_binding, this_env) <--
        bind2(expr, env, body, this_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(val, end, binding_tail), if end.is_nil(), // TODO: error otherwise
        cons_rel(var, val, env_binding);

    // This is the 'real rule'.
     bind2(expr, env, body, new_env, more_bindings) <--
        bind2(expr, env, body, this_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(val, end, binding_tail), if end.is_nil(), // TODO: error otherwise
        cons_rel(var, val, env_binding),
        cons_rel(env_binding, this_env, new_env);

    ////////////////////
    // fold -- default folding is fold_left
    relation fold(Ptr, Ptr, Sym, F, Ptr); // (expr, env, op, acc, tail)

    // If head is left-foldable op, reduce it with its neutral element.
    ingress(tail), fold(expr, env, op, op.neutral_element(), tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value), let op = Memory::ptr_sym(*head, *head_value), if op.is_left_foldable();

    // When left-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <--
        fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

    // When left-folding, if car has been evaled and is F, apply the op to it and the acc, then recursively
    // fold acc and new tail.
    ingress(cdr), fold(expr, env, op, op.apply_op(*acc, F(evaled_car.1)), cdr) <--
        fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car), if evaled_car.is_f();

    // left-folding operation with an empty (nil) tail
    eval(expr, env, Ptr(Tag::F.elt(), acc.0)) <-- fold(expr, env, _, acc, tail), if tail.is_nil();

    ////////////////////
    // fold_right

    relation fold_right(Ptr, Ptr, Sym, Ptr); // (expr, env, op, tail)

    // If head is right-foldable op, initiate fold_right.
    ingress(tail), fold_right(expr, env, op, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value), let op = Memory::ptr_sym(*head, *head_value), if op.is_right_foldable();

    // When right-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <-- fold_right(expr, env, op, tail), cons_rel(car, cdr, tail);

    // When right-folding an empty list, return the neutral element.
    eval(expr, env, Ptr(Tag::F.elt(), op.neutral_element().0)) <-- fold_right(expr, env, op, tail), if tail.is_nil();

    // When right-folding, if tail is a cons (not empty), revert to a (left) fold with evaled car as initial acc.
    ingress(cdr), fold(expr, env, op, F(evaled_car.1), cdr) <--
        fold_right(expr, env, op, tail),
        cons_rel(car, cdr, tail),
        eval(car, env, evaled_car), if evaled_car.is_f();

    // output
    output_ptr(output) <-- input_ptr(input, env), eval(input, env, output);

    ////////////////////////////////////////////////////////////////////////////////

}

#[cfg(test)]
mod test {
    use super::*;
    use crate::loam::Sexp as S;

    #[test]
    fn new_test_eval() {
        let empty_env = WidePtr::nil();

        let mut test = |input, expected_output: WidePtr, env: Option<WidePtr>| {
            let mut prog = EvaluationProgram::default();

            prog.toplevel_input = vec![(input, env.unwrap_or(empty_env))];
            prog.run();

            println!("{}", prog.relation_sizes_summary());

            assert_eq!(vec![(expected_output,)], prog.output_expr);
            prog
        };

        let err = WidePtr(Tag::Err.value(), Wide::widen(0));

        let prog = {
            allocator().init();

            // F is self-evaluating.
            let f = F(123);
            test(f.into(), f.into(), None);
        };

        let prog = {
            allocator().init();

            // Nil is self-evaluating.
            let nil = WidePtr::nil();

            test(nil.into(), nil.into(), None)
        };

        let prog = {
            allocator().init();

            // (+)
            let add = Cons::list(vec![S::sym('+')]);

            test(add.into(), F(0).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 1)
            let add = Cons::list(vec![S::sym('+'), S::f(1)]);

            test(add.into(), F(1).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 1 2)
            let add = Cons::list(vec![S::sym('+'), S::f(1), S::f(2)]);

            test(add.into(), F(3).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 1 2 3)
            let add = Cons::list(vec![S::sym('+'), S::f(1), S::f(2), S::f(3)]);

            test(add.into(), F(6).into(), None)
        };

        let prog = {
            allocator().init();

            // (*)
            let mul = Cons::list(vec![S::sym('*')]);

            test(mul.into(), F(1).into(), None)
        };

        let prog = {
            allocator().init();

            // (* 2)
            let mul = Cons::list(vec![S::sym('*'), S::f(2)]);

            test(mul.into(), F(2).into(), None)
        };

        let prog = {
            allocator().init();

            // (* 2 3)
            let mul = Cons::list(vec![S::sym('*'), S::f(2), S::f(3)]);

            test(mul.into(), F(6).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 2 3 4)
            let mul = Cons::list(vec![S::sym('*'), S::f(2), S::f(3), S::f(4)]);

            test(mul.into(), F(24).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 5 (* 3 4))
            let mul = Cons::list(vec![
                S::sym('+'),
                S::f(5),
                S::list(vec![S::sym('*'), S::f(3), S::f(4)]),
            ]);

            test(mul.into(), F(17).into(), None)
        };

        let prog = {
            allocator().init();

            // (/ 10 2 5)
            let x = Cons::list(vec![S::sym('/'), S::f(10), S::f(2), S::f(5)]);

            test(x.into(), F(1).into(), None)
        };

        let prog = {
            allocator().init();

            // (+ 5 (-) (*) (/) (+) (* 3 4 (- 7 2 1)) (/ 10 2 5))
            let x = Cons::list(vec![
                S::sym('+'),
                S::f(5),
                S::list(vec![S::sym('-')]),
                S::list(vec![S::sym('*')]),
                S::list(vec![S::sym('/')]),
                S::list(vec![S::sym('+')]),
                S::list(vec![
                    S::sym('*'),
                    S::f(3),
                    S::f(4),
                    S::list(vec![S::sym('-'), S::f(7), S::f(2), S::f(1)]),
                ]),
                S::list(vec![S::sym('/'), S::f(10), S::f(2), S::f(5)]),
            ]);

            test(x.into(), F(56).into(), None)
        };

        let prog = {
            allocator().init();

            let x: WidePtr = (&Sym::Char('x')).into();

            test(x, err, None)
        };

        let prog = {
            allocator().init();

            let x: WidePtr = (&Sym::Char('x')).into();
            let val: WidePtr = F(9).into();

            // ((x . 9))
            let env = Cons::bind(x, val, empty_env);

            test(x, val, Some(env))
        };

        let prog = {
            allocator().init();

            let x: WidePtr = (&Sym::Char('x')).into();
            let y: WidePtr = (&Sym::Char('y')).into();
            let z: WidePtr = (&Sym::Char('z')).into();
            let val: WidePtr = F(9).into();
            let val2: WidePtr = F(10).into();

            // ((y . 10) (x . 9))
            let env = Cons::bind(y, val2, Cons::bind(x, val, empty_env));

            test(x, val, Some(env));
            test(y, val2, Some(env));
            test(z, err, Some(env))
        };

        let prog = {
            allocator().init();

            let x = S::sym('x');
            let y = S::sym('y');
            let l = S::sym('l');
            let v = F(9);
            let v2 = F(10);

            //(x 9)
            let binding = S::list(vec![x.clone(), S::F(v)]);
            // ((x 9))
            let bindings = S::list(vec![binding]);
            // (l ((x 9)) x)
            let let_form: WidePtr = (&S::list(vec![l, bindings, x])).into();

            test(let_form.into(), v.into(), None);

            let binding2 = S::list(vec![y.clone(), S::F(v2)]);
            let bindings2 = S::list(vec![binding, binding2]);
            let let_form2: WidePtr = (&S::list(vec![l, bindings2, x])).into();
            let let_form3: WidePtr = (&S::list(vec![l, bindings2, y])).into();

            test(let_form2.into(), v.into(), None);
            test(let_form3.into(), v2.into(), None)
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
            toplevel_input,
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
            toplevel_input,
            input_ptr,
            eval_input,
            eval,
            hash4,
            hash4_rel,
            output_ptr,
            output_expr,
            ptr_value,
            cons_rel,
            cons_mem,
            cons_digest_mem,
            alloc,
            egress
        );

        // panic!("uiop");
    }
}
