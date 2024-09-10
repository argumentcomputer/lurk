// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]

use num_traits::FromPrimitive;
use p3_baby_bear::BabyBear;

use crate::loam::lurk_sym_index;
use crate::loam::memory::{initial_tag_relation, Memory};
use crate::loam::{LEWrap, LoamProgram, Num, Ptr, PtrEq, Wide, WidePtr, LE};
use crate::lurk::chipset::LurkChip;
use crate::lurk::state::BUILTIN_SYMBOLS;
use crate::lurk::tag::Tag;
use crate::lurk::zstore::{builtin_set, lurk_zstore, ZPtr};

use p3_field::{AbstractField, Field, PrimeField32};

use ascent::{ascent, Lattice};

use super::allocation::Allocator;

#[cfg(feature = "loam")]
ascent! {
    // #![trace]

    pub struct DistilledEvaluationProgram {
        pub allocator: Allocator,
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // NOTE: Relations are designated as either 'signal' or 'final'. Signal relations are not required for proving and
    // need not be present in the second-pass program.
    // Final relations must be present in the second pass..

    // Final: The standard tag mapping.
    relation tag(LE, Wide) = initial_tag_relation(); // (short-tag, wide-tag)

    // Final
    relation ptr_value(Ptr, Wide); // (ptr, value)

    // Final
    relation toplevel_input(WidePtr, WidePtr); // (expr, env)
    // Final
    relation output_expr(WidePtr); // (expr)
    // Final
    relation input_ptr(Ptr, Ptr); // (expr, env)
    // Final
    relation output_ptr(Ptr); // (wide-ptr)

    // Final
    relation hash4(Wide, Wide, Wide, Wide); // (a, b, c, d)
    // Signal
    relation unhash4(Wide); // (tag, digest)
    // Final
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, tag, digest)

    // Final
    relation hash6(Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f)
    // Signal
    relation unhash6(Wide); // (tag, digest)
    // Final
    relation hash6_rel(Wide, Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f, tag, digest)

    // Signal
    relation egress(Ptr); // (ptr)
    // Signal
    relation ingress(Ptr); // (ptr)

    // Signal
    relation alloc(LE, Wide); // (tag, value)
    // Signal
    relation cons(Ptr, Ptr); // (car, cdr)
    // Signal
    relation thunk(Ptr, Ptr); // (body, closed_env)
    // Signal
    relation fun(Ptr, Ptr, Ptr); // (args, body, closed_env)

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

    // Populate ptr_value if a cons_rel has been hashed in hash4_rel.
    ptr_value(cons, digest) <--
        cons_rel(car, cdr, cons),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        hash4_rel(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value, digest);
    // Other way around
    cons_rel(car, cdr, cons) <--
        ptr_value(cons, digest), if cons.tag() == Tag::Cons,
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        if car.wide_tag() == *car_tag && cdr.wide_tag() == *cdr_tag;

    ////////////////////////////////////////////////////////////////////////////////
    // Fun

    // TODO: this was copied directly from the cons memory, so we should be able to formalize with a macro.

    // Final
    relation fun_rel(Ptr, Ptr, Ptr, Ptr); // (args, body, closed-env, fun)
    // Final
    relation fun_digest_mem(Wide, LE); // (value, addr)
    // Final
    relation fun_mem(Ptr, Ptr, Ptr, LE); // (args, body, closed-env, addr)

    relation initial_fun_digest_mem(Wide, LE); // (value, addr)
    relation initial_fun_mem(Ptr, Ptr, Ptr, LE); // (args, body, closed-env, addr)
    fun_digest_mem(digest, addr) <-- initial_fun_digest_mem(digest, addr);
    fun_mem(args, body, closed_env, addr) <-- initial_fun_mem(args, body, closed_env, addr);

    // Register fun value.
    ptr_value(fun, value) <--
        alloc(tag, value), if *tag == Tag::Fun.elt(),
        fun_digest_mem(value, addr),
        let fun = Ptr(Tag::Fun.elt(), *addr);
    // Register fun relation.
    fun_rel(args, body, closed_env, fun) <--
        fun(args, body, closed_env),
        fun_mem(args, body, closed_env, addr),
        let fun = Ptr(Tag::Fun.elt(), *addr);

    // Populate ptr_value if a fun_rel has been hashed in hash6_rel.
    ptr_value(fun, digest) <--
        fun_rel(args, body, closed_env, fun),
        ptr_value(args, args_value), ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        hash6_rel(
            args.wide_tag(),
            args_value,
            body.wide_tag(),
            body_value,
            closed_env.wide_tag(),
            closed_env_value,
            digest,
        );
    // Other way around
    fun_rel(args, body, closed_env, fun) <--
        ptr_value(fun, digest), if fun.tag() == Tag::Fun,
        hash6_rel(
            args_tag,
            args_value,
            body_tag,
            body_value,
            closed_env_tag,
            closed_env_value,
            digest,
        ),
        ptr_value(args, args_value), ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        if args.wide_tag() == *args_tag && body.wide_tag() == *body_tag && closed_env.wide_tag() == *closed_env_tag;

    ////////////////////////////////////////////////////////////////////////////////
    // Thunk

    // TODO: this was copied directly from the fun memory, so we should be able to formalize with a macro.

    // Final
    relation thunk_rel(Ptr, Ptr, Ptr); // (body, closed-env, thunk)
    // Final
    relation thunk_digest_mem(Wide, LE); // (value, addr)
    // Final
    relation thunk_mem(Ptr, Ptr, LE); // (body, closed-env, addr)

    relation initial_thunk_digest_mem(Wide, LE); // (value, addr)
    relation initial_thunk_mem(Ptr, Ptr, LE); // (body, closed-env, addr)
    thunk_digest_mem(digest, addr) <-- initial_thunk_digest_mem(digest, addr);
    thunk_mem(body, closed_env, addr) <-- initial_thunk_mem(body, closed_env, addr);

    // Register thunk value.
    ptr_value(thunk, value) <--
        alloc(tag, value), if *tag == Tag::Thunk.elt(),
        thunk_digest_mem(value, addr),
        let thunk = Ptr(Tag::Thunk.elt(), *addr);
    // Register thunk relation.
    thunk_rel(body, closed_env, thunk) <--
        thunk(body, closed_env),
        thunk_mem(body, closed_env, addr),
        let thunk = Ptr(Tag::Thunk.elt(), *addr);

    // Populate ptr_value if a thunk_rel has been hashed in hash4_rel.
    ptr_value(thunk, digest) <--
        thunk_rel(body, closed_env, thunk),
        ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        hash4_rel(body.wide_tag(), body_value, closed_env.wide_tag(), closed_env_value, digest);
    // Other way around
    thunk_rel(body, closed_env, thunk) <--
        ptr_value(thunk, digest), if thunk.tag() == Tag::Thunk,
        hash4_rel(body_tag, body_value, closed_env_tag, closed_env_value, digest),
        ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        if body.wide_tag() == *body_tag && closed_env.wide_tag() == *closed_env_tag;

    ////////////////////////////////////////////////////////////////////////////////
    // Sym

    // Final
    relation sym_digest_mem(Wide, LE); // (digest, addr)

    ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), *addr);
    // todo: sym_value

    ////////////////////////////////////////////////////////////////////////////////
    // Builtin

    // Final
    relation builtin_digest_mem(Wide, LE); // (digest, addr)

    ptr_value(ptr, value) <-- builtin_digest_mem(value, addr), let ptr = Ptr(Tag::Builtin.elt(), *addr);
    // todo: builtin_value

    ////////////////////////////////////////////////////////////////////////////////
    // Nil

    // Final
    // Can this be combined with sym_digest_mem? Can it be eliminated? (probably eventually).
    relation nil_digest_mem(Wide, LE); // (digest, addr)

    ptr_value(ptr, value) <-- nil_digest_mem(value, addr), let ptr = Ptr(Tag::Nil.elt(), *addr);

    ////////////////////////////////////////////////////////////////////////////////
    // Num

    ptr_value(num, value) <-- alloc(tag, value), if *tag == Tag::Num.elt(), let num = Ptr(Tag::Num.elt(), value.f());

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    // Ingress 1: mark input expression for allocation.
    alloc(expr_tag, expr.1), alloc(env_tag, env.1) <--
        toplevel_input(expr, env), tag(expr_tag, expr.0), tag(env_tag, env.0);

    ingress(expr_ptr), input_ptr(expr_ptr, env_ptr) <--
        toplevel_input(expr, env),
        ptr_value(expr_ptr, expr.1),
        ptr_value(env_ptr, env.1),
        if expr_ptr.tag() == expr.tag() && env_ptr.tag() == env.tag();

    // mark ingress conses for unhashing.
    unhash4(digest) <-- ingress(ptr), if ptr.is_cons(), ptr_value(ptr, digest);
    unhash4(digest) <-- ingress(ptr), if ptr.is_thunk(), ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <--
        unhash4(digest), let [a, b, c, d] = _self.allocator.unhash4(digest);

    alloc(x_tag, x_value), alloc(y_tag, y_value) <--
        unhash4(digest),
        hash4_rel(wide_x_tag, x_value, wide_y_tag, y_value, digest),
        tag(x_tag, wide_x_tag),
        tag(y_tag, wide_y_tag);

    // mark ingress funs for unhashing
    unhash6(digest) <-- ingress(ptr), if ptr.is_fun(), ptr_value(ptr, digest);

    hash6_rel(a, b, c, d, e, f, digest) <--
        unhash6(digest), let [a, b, c, d, e, f] = _self.allocator.unhash6(digest);

    alloc(x_tag, x_value), alloc(y_tag, y_value), alloc(z_tag, z_value) <--
        unhash6(digest),
        hash6_rel(wide_x_tag, x_value, wide_y_tag, y_value, wide_z_tag, z_value, digest),
        tag(x_tag, wide_x_tag),
        tag(y_tag, wide_y_tag),
        tag(z_tag, wide_z_tag);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    // Cons
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // Fun
    egress(args), egress(body), egress(closed_env) <-- egress(fun), fun_rel(args, body, closed_env, fun);

    // Num
    ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    // Err
    ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_err();

    // Construct output_expr from output_ptr
    output_expr(WidePtr(ptr.wide_tag(), *value)) <-- output_ptr(ptr), ptr_value(ptr, value);

    // Cons
    hash4(car.wide_tag(), car_value, cdr.wide_tag(), cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    // Thunk
    hash4(body.wide_tag(), body_value, closed_env.wide_tag(), closed_env_value) <--
        egress(thunk),
        thunk_rel(body, closed_env, thunk),
        ptr_value(body, body_value), ptr_value(closed_env, closed_env_value);

    hash4_rel(a, b, c, d, digest) <--
        hash4(a, b, c, d), let digest = _self.allocator.hash4(*a, *b, *c, *d);

    // Fun
    hash6(args.wide_tag(), args_value, body.wide_tag(), body_value, closed_env.wide_tag(), closed_env_value) <--
        egress(fun),
        fun_rel(args, body, closed_env, fun),
        ptr_value(args, args_value),
        ptr_value(body, body_value),
        ptr_value(closed_env, closed_env_value);

    hash6_rel(a, b, c, d, e, f, digest) <--
        hash6(a, b, c, d, e, f), let digest = _self.allocator.hash6(*a, *b, *c, *d, *e, *f);

    ////////////////////////////////////////////////////////////////////////////////
    // eval

    // Signal
    relation eval_input(Ptr, Ptr); // (expr, env)
    // Final
    relation eval(Ptr, Ptr, Ptr); // (input-expr, env, output-expr)

    eval_input(expr, env) <-- input_ptr(expr, env);

    // expr is F: self-evaluating.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_num();

    // expr is Nil: self-evaluating. TODO: check value == nil value
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_nil();

    ////////////////////////////////////////
    // expr is Sym
    // Final
    relation lookup0(Ptr, Ptr, Ptr); // (outer-env, var, env)
    relation lookup(Ptr, Ptr, Ptr); // (var, outer-env, val)

    // If expr is a sym but not a built-in, look it up.
    ingress(env), lookup0(env, expr, env) <-- eval_input(expr, env), if expr.is_sym();

    // Unbound variable: If env is nil during lookup0, var is unbound. Return an an error.
    eval(var, outer_env, Ptr(Tag::Err.elt(), LE::zero())) <-- lookup0(outer_env, var, env), if env.is_nil();

    // If env is a cons, ingress the first binding.
    ingress(binding) <-- lookup0(outer_env, _, env), cons_rel(binding, tail, env);

    // If var matches that bound in first binding, return the binding's value.
    eval(var, outer_env, value) <--
        lookup0(outer_env, var, env),
        cons_rel(binding, tail, env),
        cons_rel(var, value, binding), if !value.is_thunk();

    // NOTE: to avoid negation, we may need a separate rule for every non-thunk tag in the rules above and below this comment.
    // This can be simplified with a not_thunk relation, as long as the set of valid tags is enumerable.
    // Then we can just have single rules matching against not_thunk: not_thunk(value).

    lookup(var, outer_env, value) <--
        lookup0(outer_env, var, env),
        cons_rel(binding, tail, env),
        cons_rel(var, value, binding);

    eval(var, outer_env, value) <-- lookup(var, outer_env, value), if !value.is_thunk();

    // If var does not match that bound in first binding, lookup0 var in next env.
    ingress(next_env), lookup0(outer_env, var, next_env) <--
        lookup0(outer_env, var, env),
        cons_rel(binding, next_env, env),
        cons_rel(bound_var, value, binding), if bound_var != var;

    ////////////////////
    // looked-up value is thunk

    cons(new_binding, closed_env) <--
        lookup(var, outer_env, value),
        thunk_rel(body, closed_env, thunk),
        cons_rel(var, thunk, new_binding);

    eval_input(body, extended_env) <--
        lookup(var, outer_env, value),
        thunk_rel(body, closed_env, thunk),
        cons_rel(var, thunk, new_binding),
        cons_rel(new_binding, closed_env, extended_env);

    eval(var, outer_env, result) <--
        lookup(var, outer_env, value),
        thunk_rel(body, closed_env, thunk),
        cons_rel(var, thunk, new_binding),
        cons_rel(new_binding, closed_env, extended_env),
        eval(body, extended_env, result);

    ////////////////////////////////////////
    // expr is Cons
    ingress(expr) <-- eval_input(expr, env), if expr.is_cons();

    ////////////////////
    // eq op

    // Signal: Query. Are these two pointers equal?
    relation eq(Ptr, Ptr, PtrEq);

    // Final: Transitive closure of all equal pointers. But we only lazily compute this,
    // and update when getting a query triggered from `eq(ptr, ptr, is_eq)` call. This also memoizes the computation.
    relation eq_rel(Ptr, Ptr, bool);

    // Signals for parsing
    relation eq_cont1(Ptr, Ptr, Ptr); // (expr, env, args)
    relation eq_cont2(Ptr, Ptr, Ptr, Ptr); // (expr, env, arg1, arg2)
    relation eq_cont3(Ptr, Ptr, Ptr, Ptr); // (expr, env, evaled-arg1, evaled-arg2)

    // Signal: Ingress 1st arg.
    ingress(tail), eq_cont1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_eq_op();

    // Signal: Ingress 2nd arg, evaluate 1st arg.
    ingress(rest), eval_input(arg1, env) <--
        eq_cont1(expr, env, tail),
        cons_rel(arg1, rest, tail);

    // Signal: Evaluate 2nd arg
    eval_input(arg2, env), eq_cont2(expr, env, arg1, arg2) <--
        eq_cont1(expr, env, tail),
        cons_rel(arg1, rest, tail),
        cons_rel(arg2, end, rest), if end.is_nil(); // TODO: otherwise error

    // Signal
    eq_cont3(expr, env, evaled_arg1, evaled_arg2) <--
        eq_cont2(expr, env, arg1, arg2),
        eval(arg1, env, evaled_arg1),
        eval(arg2, env, evaled_arg2);

    // Signal: Are these two pointers equal?
    eq(evaled_arg1, evaled_arg2, is_eq) <--
        eq_cont3(expr, env, evaled_arg1, evaled_arg2),
        let is_eq = evaled_arg1.is_eq(evaled_arg2);

    // Final: Return the result
    eval(expr, env, Ptr::lurk_bool(*is_eq)) <--
        eq_cont3(expr, env, evaled_arg1, evaled_arg2),
        eq_rel(evaled_arg1, evaled_arg2, is_eq);


    ////////////////////
    // eq coroutine

    // Signal
    relation eq_rel_cont1(Ptr, Ptr, LE); // (arg1, arg2, tag)

    // Signals: To implement the short-circuiting and lazy logic, we hold the subchildren in a continuation.
    relation eq_rel_tuple2_cont(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, PtrEq); // (arg1, arg2, x1, y1, x2, y2, is_eq)
    relation eq_rel_tuple3_cont(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, PtrEq); // (arg1, arg2, x1, y1, z1, x2, y2, z2, is_eq)

    // Signal: Base cases.
    eq_rel(arg1, arg2, true) <-- eq(arg1, arg2, PtrEq::Equal);
    eq_rel(arg1, arg2, false) <-- eq(arg1, arg2, PtrEq::NotEqual);

    // Signal: Prepare to match on the tag. I don't know if inlining the match would be more efficient.
    ingress(arg1), ingress(arg2), eq_rel_cont1(arg1, arg2, tag) <--
        eq(arg1, arg2, PtrEq::Unknown), let tag = arg1.0;

    // Signal: Match on the Cons tag and query the children
    eq_rel_tuple2_cont(arg1, arg2, car1, cdr1, car2, cdr2, is_eq) <--
        eq_rel_cont1(arg1, arg2, &Tag::Cons.elt()),
        // TODO: there is a bit of an issue here: what if not both cons_rels exist?
        cons_rel(car1, cdr1, arg1),
        cons_rel(car2, cdr2, arg2),
        let is_eq = Lattice::join(car1.is_eq(car2), cdr1.is_eq(cdr2));

    // Signal: Match on the Fun tag and query the children
    eq_rel_tuple3_cont(arg1, arg2, args1, args2, body1, body2, closed_env1, closed_env2, is_eq) <--
        eq_rel_cont1(arg1, arg2, &Tag::Fun.elt()),
        fun_rel(args1, body1, closed_env1, arg1),
        fun_rel(args2, body2, closed_env2, arg2),
        let is_eq = Lattice::join(Lattice::join(args1.is_eq(args2), body1.is_eq(body2)), closed_env1.is_eq(closed_env2));

    // Signal: Match on the Thunk tag and query the children
    eq_rel_tuple2_cont(arg1, arg2, body1, body2, closed_env1, closed_env2, is_eq) <--
        eq_rel_cont1(arg1, arg2, &Tag::Thunk.elt()),
        thunk_rel(body1, closed_env1, arg1),
        thunk_rel(body2, closed_env2, arg2),
        let is_eq = Lattice::join(body1.is_eq(body2), closed_env1.is_eq(closed_env2));

    // Signal: If both pairs are equal.
    eq_rel(arg1, arg2, true) <--
        eq_rel_tuple2_cont(arg1, arg2, x1, y1, x2, y2, PtrEq::Equal);

    // Signal: If at least one pair is not equal.
    eq_rel(arg1, arg2, false) <--
        eq_rel_tuple2_cont(arg1, arg2, x1, y1, x2, y2, PtrEq::NotEqual);

    // Signal: Recurse.
    eq(x1, x2, x_is_eq), eq(y1, y2, y_is_eq) <--
        eq_rel_tuple2_cont(arg1, arg2, x1, y1, x2, y2, PtrEq::Unknown),
        let x_is_eq = x1.is_eq(x2),
        let y_is_eq = y1.is_eq(y2);

    // Signal: Finish.
    eq_rel(arg1, arg2, is_eq) <--
        eq_rel_tuple2_cont(arg1, arg2, x1, y1, x2, y2, PtrEq::Unknown),
        eq_rel(x1, x2, x_is_eq),
        eq_rel(y1, y2, y_is_eq),
        let is_eq = *x_is_eq && *y_is_eq;

    // Signal: If all three pairs are equal.
    eq_rel(arg1, arg2, true) <--
        eq_rel_tuple3_cont(arg1, arg2, x1, y1, z1, x2, y2, z2, PtrEq::Equal);

    // Signal: If at least one pair is not equal.
    eq_rel(arg1, arg2, false) <--
        eq_rel_tuple3_cont(arg1, arg2, x1, y1, z1, x2, y2, z2, PtrEq::NotEqual);

    // Signal: Recurse.
    eq(x1, x2, x_is_eq), eq(y1, y2, y_is_eq), eq(z1, z2, z_is_eq) <--
        eq_rel_tuple3_cont(arg1, arg2, x1, y1, z1, x2, y2, z2, PtrEq::Unknown),
        let x_is_eq = x1.is_eq(x2),
        let y_is_eq = y1.is_eq(y2),
        let z_is_eq = z1.is_eq(z2);

    // Signal: Finish.
    eq_rel(arg1, arg2, is_eq) <--
        eq_rel_tuple3_cont(arg1, arg2, x1, y1, z1, x2, y2, z2, PtrEq::Unknown),
        eq_rel(x1, x2, x_is_eq),
        eq_rel(y1, y2, y_is_eq),
        eq_rel(z1, z2, z_is_eq),
        let is_eq = *x_is_eq && *y_is_eq && *z_is_eq;

    ////////////////////
    // cons op

    // Signals
    relation cons_cont1(Ptr, Ptr, Ptr); // (expr, env, unevaled-car-cdr)
    relation cons_cont2(Ptr, Ptr, Ptr, Ptr); // (expr, env, car, cdr)

    ingress(tail), cons_cont1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_cons_op();

    // Signal: eval car
    eval_input(car, env), ingress(rest) <--
        cons_cont1(expr, env, tail),
        cons_rel(car, rest, tail);

    // Signal: eval cdr
    eval_input(cdr, env), cons_cont2(expr, env, car, cdr) <--
        cons_cont1(expr, env, tail),
        cons_rel(car, rest, tail),
        cons_rel(cdr, end, rest), if end.is_nil(); // TODO: otherwise error

    // Signal:
    cons(evaled_car, evaled_cdr) <--
        cons_cont2(expr, env, car, cdr),
        eval(car, env, evaled_car),
        eval(cdr, env, evaled_cdr);

    // Register a cons created from a cons expression as its evaluation.
    eval(expr, env, evaled_cons) <--
        cons_cont2(expr, env, car, cdr),
        eval(car, env, evaled_car),
        eval(cdr, env, evaled_cdr),
        cons_rel(evaled_car, evaled_cdr, evaled_cons);

    ////////////////////
    // car and cdr op

    // Signals
    relation car_cdr_cont1(Ptr, Ptr, Ptr, bool); // (expr, env, tail)
    relation car_cdr_cont2(Ptr, Ptr, Ptr, bool); // (expr, env, body)

    ingress(tail), car_cdr_cont1(expr, env, tail, is_car) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_car_cdr(), let is_car = op.is_car();

    // Signal: eval body
    car_cdr_cont2(expr, env, body, is_car), eval_input(body, env) <--
        car_cdr_cont1(expr, env, tail, is_car),
        cons_rel(body, end, tail), if end.is_nil(); // TODO: otherwise error

    ingress(evaled) <--
        car_cdr_cont2(expr, env, body, is_car),
        eval(body, env, evaled);

    // Real rule matching car case
    eval(expr, env, car) <--
        car_cdr_cont2(expr, env, body, true),
        eval(body, env, evaled),
        cons_rel(car, _, evaled);

    // Real rule matching cdr case
    eval(expr, env, cdr) <--
        car_cdr_cont2(expr, env, body, false),
        eval(body, env, evaled),
        cons_rel(_, cdr, evaled);

    ////////////////////
    // atom op

    // Signals
    relation atom_cont1(Ptr, Ptr, Ptr); // (expr, env, tail)

    ingress(tail), atom_cont1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_atom_op();

    // Signal: eval body
    eval_input(body, env) <--
        atom_cont1(expr, env, tail),
        cons_rel(body, end, tail), if end.is_nil(); // TODO: otherwise error

    eval(expr, env, is_atom) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_atom_op(),
        cons_rel(body, end, tail), if end.is_nil(),
        eval(body, env, evaled),
        let is_atom = Ptr::lurk_bool(!evaled.is_cons()); // is this good?

    ////////////////////
    // quote op

    // Signals
    relation quote_cont1(Ptr, Ptr, Ptr); // (expr, env, tail)

    ingress(tail), quote_cont1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(op, tail, expr), if op.is_quote();

    // Signal: Don't eval body :P
    eval(expr, env, body) <--
        quote_cont1(expr, env, tail),
        cons_rel(body, end, tail), if end.is_nil(); // TODO: otherwise error

    ////////////////////
    // conditional

    ingress(rest) <--
        eval_input(expr, env), cons_rel(op, rest, expr),
        if op.is_if();

    // Signal: Evaluating if
    eval_input(cond, env), ingress(branches) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest);

    // Signal: Evaled condition is not nil: evaluate the a branch.
    eval_input(a, env) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if !evaled_cond.is_nil(); // FIXME: add not_nil relation to avoid negation.

    // Signal: Evaled condition is nil: ingress the remaining branch.
    ingress(more)  <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if evaled_cond.is_nil();

    // Evaled condition is not nil: return the evaled a branch.
    eval(expr, env, evaled_result) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if !evaled_cond.is_nil(),
        eval(a, env, evaled_result);

    // Signal: Evaled conditions is not nil: evaluate the b branch.
    eval_input(b, env) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if evaled_cond.is_nil(),
        cons_rel(b, end, more), if end.is_nil(); // otherwise syntax error
    // Evaled condition is nil: return the evaled b branch.
    eval(expr, env, evaled_result) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if evaled_cond.is_nil(),
        cons_rel(b, end, more), if end.is_nil(), // otherwise syntax error
        eval(b, env, evaled_result);

    ////////////////////
    // function call

    // TODO: Handle undersaturate function call (returning functions with fewer args than original).

    // Final
    relation fun_call(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, args, body, closed_env, rest)
    // Signal
    relation maybe_fun_call(Ptr, Ptr, Ptr, Ptr); // (expr, env, maybe_fun, rest)

    // If head is fun.
    ingress(args), ingress(rest),
    fun_call(expr, env, args, body, closed_env, rest) <--
        eval_input(expr, env),
        cons_rel(fun, rest, expr),
        fun_rel(args, body, closed_env, fun);

    // If head is not fun but might eval to one.
    eval_input(maybe_fun, env),
    maybe_fun_call(expr, env, maybe_fun, rest) <--
        eval_input(expr, env), cons_rel(maybe_fun, rest, expr), if !maybe_fun.is_fun() && !maybe_fun.is_built_in(); // the built_in exclusion may be redundant.

    // If head did eval to a fun.
    // TODO: factor out signal (maybe_fun_call)
    ingress(args), ingress(rest),
    fun_call(expr, env, args, body, closed_env, rest) <--
        maybe_fun_call(expr, env, maybe_fun, rest), eval(maybe_fun, env, fun), fun_rel(args, body, closed_env, fun);

    ingress(args), ingress(rest) <--
        fun_call(expr, env, args, body, closed_env, rest);


    // base case: args list is empty
    eval_input(body, closed_env) <--
        fun_call(expr, env, args, body, closed_env, rest),
        if args.is_nil() && rest.is_nil(); // TODO: error if arg is nil, but rest is not.

    // register base-case evaluation result
    eval(expr, env, result) <--
        fun_call(expr, env, args, body, closed_env, rest),
        if args.is_nil() && rest.is_nil(), // TODO: error if arg is nil, but rest is not.a
        eval(body, closed_env, result);

    eval_input(unevaled, env) <--
        fun_call(expr, env, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(unevaled, more_vals, rest);

    cons(arg, evaled) <--
        fun_call(expr, env, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(unevaled, more_vals, rest),
        eval(unevaled, env, evaled);

    cons(binding, closed_env) <--
        fun_call(expr, env, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(unevaled, more_vals, rest),
        eval(unevaled, env, evaled),
        cons_rel(arg, evaled, binding);

    fun_call(expr, env, more_args, body, new_closed_env, more_vals) <--
        fun_call(expr, env, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(unevaled, more_vals, rest),
        eval(unevaled, env, evaled),
        cons_rel(arg, evaled, binding),
        cons_rel(binding, closed_env, new_closed_env);

    ////////////////////
    // let binding

    // Signal
    relation bind_parse(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)
    // Signal
    relation rec_bind_parse(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)

    // Final
    relation bind(Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, bindings, is-rec)

    // These rules act, morally, as continuations and are all 'signal relations'.
    // Signal
    relation bind_cont1(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, binding, more-bindings, var, binding-tail, is-rec)
    // Signal
    relation bind_cont2(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, var, unevaled, more-bindings, is-rec)
    // Signal
    relation bind_cont3(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, var, evaled, more-bindings)

    ingress(tail), bind_parse(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_binding();

    ingress(tail), rec_bind_parse(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_recursive_binding();

    // // Signal rule
    ingress(bindings), ingress(rest) <--
        (bind_parse(expr, env, tail) || rec_bind_parse(expr, env, tail)),
        cons_rel(bindings, rest, tail);

    // let base case: bindings list is empty.
    bind(expr, env, body, env, bindings, false) <--
        bind_parse(expr, env, tail),
        cons_rel(bindings, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: error otherwise

    // letrec base case: bindings list is empty.
    bind(expr, env, body, env, bindings, true) <--
        // TODO: eliminate signal relation (rec_bind_parse) in primarily rule for second pass..
        rec_bind_parse(expr, env, tail),
        cons_rel(bindings, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: error otherwise

    // Evaluate body with extended environment.
    eval_input(body, extended_env) <--
        bind(expr, env, body, extended_env, bindings, _is_rec),
        if bindings.is_nil();

    eval(expr, env, result) <--
        bind(expr, env, body, extended_env, bindings, _is_rec),
        if bindings.is_nil(),
        eval(body, extended_env, result);

    // Signal rule
    ingress(binding), ingress(more_bindings) <--
        bind(expr, env, body, extended_env, bindings, _is_rec),
        cons_rel(binding, more_bindings, bindings);

    // Signal rule
    bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, is_rec),
    ingress(binding_tail) <--
        bind(expr, env, body, extended_env, bindings, is_rec),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding);

    // Signal rule (eval in let case)
    bind_cont2(expr, env, body, extended_env, var, unevaled, more_bindings, false),
    eval_input(unevaled, extended_env)
        <--
        bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, false),
        cons_rel(var, binding_tail, binding),
        cons_rel(unevaled, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // Signal rule (thunk in letrec case)
    bind_cont2(expr, env, body, extended_env, var, thunk_body, more_bindings, true),
    thunk(thunk_body, extended_env)
        <--
        bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, true),
        cons_rel(var, binding_tail, binding),
        cons_rel(thunk_body, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // let
    bind_cont3(expr, env, body, extended_env, var, evaled, more_bindings),
    cons(var, evaled) <--
        bind_cont2(expr, env, body, extended_env, var, unevaled, more_bindings, false),
        eval(unevaled, extended_env, evaled);

    // letrec
    // FIXME: evaluate thunk for effects before binding, in case it is never looked up.
    bind_cont3(expr, env, body, extended_env, var, thunk, more_bindings),
    cons(var, thunk) <--
        bind_cont2(expr, env, body, extended_env, var, thunk_body, more_bindings, true),
        thunk_rel(thunk_body, extended_env, thunk);

    // Signal rule
    cons(env_binding, extended_env) <--
        bind_cont3(expr, env, body, extended_env, var, val, more_bindings),
        cons_rel(var, val, env_binding);

    // This is the 'real rule'. Since the signal relations will be distilled out, the second-pass program should contain
    // all the required dependencies.
    bind(expr, env, body, new_env, more_bindings, false) <--
        bind(expr, env, body, extended_env, bindings, false),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(unevaled, end, binding_tail), if end.is_nil(), // TODO: error otherwise
        eval(unevaled, extended_env, evaled),
        cons_rel(var, evaled, env_binding),
        cons_rel(env_binding, extended_env, new_env);

    bind(expr, env, body, new_env, more_bindings, true) <--
        bind(expr, env, body, extended_env, bindings, true),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(thunk_body, end, binding_tail), if end.is_nil(), // TODO: error otherwise
        thunk_rel(thunk_body, extended_env, thunk),
        cons_rel(var, thunk, env_binding),
        cons_rel(env_binding, extended_env, new_env);


    // If a smart-enough compiler can arrange, it may be more efficient to use the version that depends on the signal
    // relations in the first pass, though.
    //
    //  relation bind_cont4(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, env_binding)
    //
    // // Signal rule
    //  bind_cont4(expr, env, body, extended_env, env_binding, more_bindings),
    //  cons(env_binding, extended_env) <--
    //     bind_cont2(expr, env, body, extended_env, var, val, more_bindings),
    //     cons_rel(var, val, env_binding);

    //  bind(expr, env, body, new_env, more_bindings) <--
    //     bind_cont4(expr, env, body, extended_env, env_binding, more_bindings),
    //     cons_rel(env_binding, extended_env, new_env);

    ////////////////////
    // first-element is not built-in

    ////////////////////
    // lambda

    // Signal
    relation lambda_cont1(Ptr, Ptr, Ptr); // (expr, env, args-and-body)
    relation lambda_cont2(Ptr, Ptr, Ptr, Ptr); // (expr, env, args, body)

    ingress(tail), lambda_cont1(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_lambda();

    // Signal
    ingress(rest) <--
        lambda_cont1(expr, env, tail),
        cons_rel(args, rest, tail);

    // Signal: create a fun from a parsed lambda evaluation
    fun(args, body, env), lambda_cont2(expr, env, args, body) <--
        lambda_cont1(expr, env, tail),
        cons_rel(args, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: otherwise error

    // register a fun created from a lambda expression as its evaluation
    eval(expr, env, fun) <--
        lambda_cont2(expr, env, args, body),
        fun_rel(args, body, env, fun);

    ////////////////////
    // fold -- default folding is fold_left

    // Real
    relation fold(Ptr, Ptr, Ptr, Num, Ptr); // (expr, env, op, acc, tail)

    // If head is left-foldable op, reduce it with its neutral element.
    // signal (?)
    ingress(tail), fold(expr, env, head, head.neutral_element(), tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_left_foldable();

    // When left-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car) <-- fold(expr, env, _, _, tail), cons_rel(car, cdr, tail);

    // When left-folding, if car has been evaled and is F, apply the op to it and the acc, then recursively
    // fold acc and new tail. TODO: error if car is not f.
    ingress(cdr), fold(expr, env, op, op.apply_op(*acc, Num(evaled_car.1)), cdr) <--
        fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car), if evaled_car.is_num();

    // left-folding operation with an empty (nil) tail
    eval(expr, env, Ptr(Tag::Num.elt(), acc.0)) <-- fold(expr, env, _, acc, tail), if tail.is_nil();

    ////////////////////
    // fold_right

    // Real
    relation fold_right(Ptr, Ptr, Ptr, Ptr); // (expr, env, op, tail)

    // If head is right-foldable op, initiate fold_right.
    ingress(tail), fold_right(expr, env, head, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_right_foldable();

    // When right-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car) <-- fold_right(expr, env, op, tail), cons_rel(car, cdr, tail);

    // When right-folding an empty list, return the neutral element.
    eval(expr, env, Ptr(Tag::Num.elt(), op.neutral_element().0)) <-- fold_right(expr, env, op, tail), if tail.is_nil();

    // When right-folding, if tail is a cons (not empty), revert to a (left) fold with evaled car as initial acc.
    ingress(cdr), fold(expr, env, op, Num(evaled_car.1), cdr) <--
        fold_right(expr, env, op, tail),
        cons_rel(car, cdr, tail),
        eval(car, env, evaled_car), if evaled_car.is_num();

    // output
    output_ptr(output) <-- input_ptr(input, env), eval(input, env, output);

    ////////////////////
    // bool_fold
    // TODO: error if args are not Num.

    // Signal
    relation bool_fold0(Ptr, Ptr, Ptr, Ptr); // (expr, env, op, tail)
    // Real
    relation bool_fold(Ptr, Ptr, Ptr, Num, Ptr); // (expr, env, op, acc, tail)

    // If head is relational op, reduce it with its neutral element.
    ingress(tail), bool_fold0(expr, env, head, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_relational();

    // bool0-folding operation with an empty (nil) tail (and no acc)
    // TODO: factor out signal relation (bool_fold0)
    eval(expr, env, Ptr::t()) <-- bool_fold0(expr, env, _op, tail), if tail.is_nil();

    // bool-folding operation with an empty (nil) tail
    eval(expr, env, Ptr::t()) <-- bool_fold(expr, env, _op, _acc, tail), if tail.is_nil();

    // When bool0-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <--
        bool_fold0(expr, env, _op, tail), cons_rel(car, cdr, tail);

    // TODO: inline signal relation (bool_fold0)
    ingress(tail), bool_fold(expr, env, op, Num(evaled_car.1), cdr) <--
        bool_fold0(expr, env, op, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car);

    eval_input(car, env), ingress(car), ingress(cdr) <-- bool_fold(expr, env, _, _, tail), cons_rel(car, cdr, tail);

    eval(expr, env, op.apply_relop(*acc,  Num(evaled_car.1))) <--
        bool_fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car),
        if cdr.is_nil();

    ingress(cdr), bool_fold(expr, env, op, Num(evaled_car.1), cdr) <--
        bool_fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car),
        if cdr.is_cons(),
        let x = op.apply_relop(*acc, Num(evaled_car.1)),
        if x.is_t();

    ////////////////////////////////////////////////////////////////////////////////

}

#[cfg(feature = "loam")]
impl DistilledEvaluationProgram {
    pub fn import_memory(&mut self, memory: Memory) {
        self.initial_cons_digest_mem = memory.cons_digest_mem;
        self.initial_cons_mem = memory.cons_mem;
        self.initial_fun_digest_mem = memory.fun_digest_mem;
        self.initial_fun_mem = memory.fun_mem;
        self.initial_thunk_digest_mem = memory.thunk_digest_mem;
        self.initial_thunk_mem = memory.thunk_mem;

        self.sym_digest_mem = memory.sym_digest_mem;
        self.builtin_digest_mem = memory.builtin_digest_mem;
        self.nil_digest_mem = memory.nil_digest_mem;
    }
}

#[cfg(test)]
#[cfg(feature = "loam")]
mod test {
    use hashbrown::raw;
    use p3_baby_bear::BabyBear;

    use crate::{
        loam::{
            evaluation::EvaluationProgram,
            memory::{generate_lisp_program, DistillationOptions},
            LoamProgram,
        },
        lurk::{
            chipset::LurkChip,
            zstore::{lurk_zstore, ZPtr, ZStore},
        },
    };

    use super::*;

    fn err() -> WidePtr {
        WidePtr(Tag::Err.value(), Wide::widen(LE::from_canonical_u32(0)))
    }

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
        env: Option<WidePtr>,
    ) -> EvaluationProgram {
        let mut prog = EvaluationProgram::default();

        prog.import_zstore(&zstore);
        prog.toplevel_input = vec![(input, env.unwrap_or(WidePtr::empty_env()))];
        prog.run();

        assert_eq!(vec![(expected_output,)], prog.output_expr);
        prog
    }

    fn test_second_phase(original_program: &EvaluationProgram) {
        let mut prog = DistilledEvaluationProgram::default();

        prog.allocator = original_program.allocator.clone();
        prog.toplevel_input = original_program.toplevel_input.clone();

        // Export the virtual memory and then distill it.
        let virtual_memory = original_program.export_memory();
        let options = DistillationOptions::new().with_summary(0.5);
        let memory = virtual_memory.distill(&options);

        // Import the distilled memory and run the second phase
        prog.import_memory(memory);
        prog.run();

        // println!("{}", prog.relation_sizes_summary());
        println!("cons_digest_mem size: {}", prog.cons_digest_mem.len());
        println!("cons_mem size: {}", prog.cons_mem.len());

        assert_eq!(prog.output_expr, original_program.output_expr);
    }

    fn test_aux(input: &str, expected_output: &str, env: Option<&str>) -> EvaluationProgram {
        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        let expected_output = read_wideptr(&mut zstore, expected_output);
        let env = env.map(|s| read_wideptr(&mut zstore, s));
        test_aux0(zstore, input, expected_output, env)
    }

    #[test]
    fn test_self_evaluating_f() {
        let prog = test_aux("123n", "123n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_self_evaluating_nil() {
        let prog = test_aux("nil", "nil", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_zero_arg_addition() {
        let prog = test_aux("(+)", "0n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_one_arg_addition() {
        let prog = test_aux("(+ 1n)", "1n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_two_arg_addition() {
        let prog = test_aux("(+ 1n 2n)", "3n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_three_arg_addition() {
        let prog = test_aux("(+ 1n 2n 3n)", "6n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_zerog_arg_multiplication() {
        let prog = test_aux("(*)", "1n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_one_arg_multiplication() {
        let prog = test_aux("(* 2n)", "2n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_two_arg_multiplication() {
        let prog = test_aux("(* 2n 3n)", "6n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_three_arg_multiplication() {
        let prog = test_aux("(* 2n 3n 4n)", "24n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_nested_arithmetic() {
        let prog = test_aux("(+ 5n (* 3n 4n))", "17n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_three_arg_division() {
        let prog = test_aux("(/ 10n 2n 5n)", "1n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_complicated_nested_arithmetic() {
        let prog = test_aux(
            "(+ 5n (-) (*) (/) (+) (* 3n 4n (- 7n 2n 1n)) (/ 10n 2n 5n))",
            "56n",
            None,
        );
        test_second_phase(&prog);
    }

    #[test]
    fn test_relational() {
        let prog = test_aux("(=)", "t", None);
        test_second_phase(&prog);

        let prog = test_aux("(= 1n)", "t", None);
        test_second_phase(&prog);

        let prog = test_aux("(= 1n 1n)", "t", None);
        test_second_phase(&prog);

        let prog = test_aux("(= 1n 1n 1n)", "t", None);
        test_second_phase(&prog);

        let prog = test_aux("(= 1n 2n)", "nil", None);
        test_second_phase(&prog);

        let prog = test_aux("(= 1n 1n 2n)", "nil", None);
        test_second_phase(&prog);

        // TODO: handle these type errors
        // test_aux1("(= nil)", err(), None);
        // test_aux1("(= 1 nil)", err(), None);
    }

    #[test]
    fn test_if() {
        test_aux("(if (= 1n 1n) 123n 456n)", "123n", None);
        test_aux("(if (= 1n 2n) 123n 456n)", "456n", None);
    }

    // #[test]
    // fn test_unbound_var() {
    //     test_aux1("x", err(), None);
    // }

    #[test]
    fn test_var_lookup() {
        test_aux("x", "9n", Some("((x . 9n))"));
    }

    #[test]
    fn test_deep_var_lookup() {
        let mut zstore = lurk_zstore();
        let env = read_wideptr(&mut zstore, "((y . 10n) (x . 9n))");
        let expr = read_wideptr(&mut zstore, "x");

        test_aux("x", "9n", Some("((y . 10n) (x . 9n))"));
        test_aux("y", "10n", Some("((y . 10n) (x . 9n))"));
        // test_aux1("z", err(), Some("((y . 10) (x . 9))"));
    }

    #[test]
    fn test_let_plain() {
        test_aux("(let ((x 9n)) x)", "9n", None);
        test_aux("(let ((x 9n)(y 10n)) x)", "9n", None);
        test_aux("(let ((x 9n)(y 10n)) y)", "10n", None);
        test_aux("(let ((x (+ 1n 1n))) x)", "2n", None);
        test_aux("(let ((y 9n) (x (+ 1n 1n))) x)", "2n", None);
    }

    #[test]
    fn test_letrec_plain() {
        test_aux("(letrec ((x 9n)) x)", "9n", None);
        test_aux("(letrec ((x (+ 1n 1n))) x)", "2n", None);

        test_aux("(letrec ((x 9n)(y 10n)) x)", "9n", None);
        test_aux("(letrec ((x 9n)(y 10n)) y)", "10n", None);
        test_aux("(letrec ((y 9n) (x (+ 1n 1n))) x)", "2n", None);
    }

    #[test]
    fn test_letrec_complex() {
        let fibonacci = |n| {
            format!(
                "
(letrec ((fibonacci (lambda (n) (if (< n 2n) 1n (+ (fibonacci (- n 2n)) (fibonacci (- n 1n)))))))
  (fibonacci {n}n))
"
            )
        };
        let prog = test_aux(&fibonacci(7), "21n", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_map_double_distilled() {
        let map_double = "
(letrec ((input (cons (cons 1n 2n) (cons 2n 4n)))
         (map-double (lambda (x) (if (atom x) (+ x x) (cons (map-double (car x))  (map-double (cdr x)))))))
    (map-double input))
        ";
        let prog = test_aux(map_double, "((2n . 4n) . (4n . 8n))", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_map_double_distilled_noncontiguous() {
        let map_double = "
(letrec ((input (quote ((1n . 2n) . (2n . 4n))))
         (map-double (lambda (x) (if (atom x) (+ x x) (cons (map-double (car x))  (map-double (cdr x)))))))
    (map-double input))
        ";
        let prog = test_aux(map_double, "((2n . 4n) . (4n . 8n))", None);
        test_second_phase(&prog);
    }

    #[test]
    fn test_eq_complex_distilled() {
        let n = std::env::var("LISP_N")
            .unwrap_or("4".to_owned())
            .parse::<usize>()
            .unwrap_or(4);
        let prog = test_aux(&generate_lisp_program(n, "eq"), "t", None);
        test_second_phase(&prog)
    }
}
