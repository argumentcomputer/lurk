// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]

use num_traits::FromPrimitive;
use p3_baby_bear::BabyBear;

use crate::loam::allocation::allocator;
use crate::loam::evaluation::Memory;
use crate::loam::lurk_sym_index;
use crate::loam::{LEWrap, Num, Ptr, Wide, WidePtr, LE};
use crate::lurk::chipset::LurkChip;
use crate::lurk::state::LURK_PACKAGE_SYMBOLS_NAMES;
use crate::lurk::tag::Tag;
use crate::lurk::zstore::{builtin_vec, lurk_zstore, ZPtr, ZStore};

use p3_field::{AbstractField, Field, PrimeField32};

use ascent::{ascent, Dual};

ascent! {
    #![trace]

    struct DistilledEvaluationProgram {
        zstore: ZStore<LE, LurkChip>,
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // NOTE: Relations are designated as either 'signal' or 'final'. Signal relations are not required for proving and
    // need not be present in the second-pass program.
    // Final relations must be present in the second pass..

    // Final: The standard tag mapping.
    relation tag(LE, Wide) = Memory::initial_tag_relation(); // (short-tag, wide-tag)

    // Final
    relation ptr_value(Ptr, Wide); // (ptr, value)

    // triggers memoized/deduplicated allocation of input conses by populating cons outside of testing, this indirection
    // is likely unnecessary.
    // relation input_cons(Ptr, Ptr); // (car, cdr)

    // Final
    relation toplevel_input(WidePtr, WidePtr); // (expr, env)
    // Final
    relation output_expr(WidePtr); // (expr)
    // Final
    relation input_ptr(Ptr, Ptr); // (expr, env)
    // Final
    relation output_ptr(Ptr); // (wide-ptr)

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

    // Register cons value.
    ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);
    // Register cons relation.
    cons_rel(car, cdr, cons) <-- cons_mem(car, cdr, addr), let cons = Ptr(Tag::Cons.elt(), addr.0.0);

    ////////////////////////////////////////////////////////////////////////////////
    // Fun

    // TODO: this was copied directly from the cons memory, so we should be able to formalize with a macro.

    // Final
    relation fun_rel(Ptr, Ptr, Ptr, Ptr); // (args, body, closed-env, fun)
    // Final
    lattice fun_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
    // Final
    lattice fun_mem(Ptr, Ptr, Ptr, Dual<LEWrap>); // (args, body, closed-env, addr)

    // Register fun value.
    ptr_value(ptr, value) <-- fun_digest_mem(value, addr), let ptr = Ptr(Tag::Fun.elt(), addr.0.0);
    // Register fun relation.
    fun_rel(args, body, closed_env, fun) <-- fun_mem(args, body, closed_env, addr), let fun = Ptr(Tag::Fun.elt(), addr.0.0);

    ////////////////////////////////////////////////////////////////////////////////
    // Thunk

    // TODO: this was copied directly from the fun memory, so we should be able to formalize with a macro.

    // Final
    relation thunk_rel(Ptr, Ptr, Ptr); // (body, closed-env, thunk)
    // Final
    lattice thunk_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
    // Final
    lattice thunk_mem(Ptr, Ptr, Dual<LEWrap>); // (body, closed-env, addr)

    // Register thunk value.
    ptr_value(ptr, value) <-- thunk_digest_mem(value, addr), let ptr = Ptr(Tag::Thunk.elt(), addr.0.0);
    // Register thunk relation.
    thunk_rel(body, closed_env, cons) <-- thunk_mem(body, closed_env, addr), let cons = Ptr(Tag::Thunk.elt(), addr.0.0);

    ////////////////////////////////////////////////////////////////////////////////
    // Sym

    // Final
    lattice sym_digest_mem(Wide, Dual<LEWrap>); // (digest, addr)

    // // Convert addr to ptr and register ptr relations.
    ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), addr.0.0);
    // todo: sym_value

    ////////////////////////////////////////////////////////////////////////////////
    // Builtin

    // Final
    lattice builtin_digest_mem(Wide, Dual<LEWrap>) = Memory::initial_builtin_relation(); // (digest, addr)

    // // Convert addr to ptr and register ptr relations.
    ptr_value(ptr, value) <-- builtin_digest_mem(value, addr), let ptr = Ptr(Tag::Builtin.elt(), addr.0.0);


    ////////////////////////////////////////////////////////////////////////////////
    // Nil

    // Final
    // Can this be combined with sym_digest_mem? Can it be eliminated? (probably eventually).
    lattice nil_digest_mem(Wide, Dual<LEWrap>) = Memory::initial_nil_relation(); // (digest, addr)

    ptr_value(ptr, value) <-- nil_digest_mem(value, addr), let ptr = Ptr(Tag::Nil.elt(), addr.0.0);

    ////////////////////////////////////////////////////////////////////////////////
    // Num

    // Final
    // not sure how this is supposed to work as Num is immediate... but hey it works
    relation num(Ptr);

    ptr_value(ptr, Wide::widen(ptr.1)) <-- num(ptr);

    ////////////////////////////////////////////////////////////////////////////////
    // Ingress path

    input_ptr(expr_ptr, env_ptr) <--
        toplevel_input(expr, env),
        ptr_value(expr_ptr, expr.1),
        ptr_value(env_ptr, env.1);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    // Construct output_expr from output_ptr
    output_expr(WidePtr(ptr.wide_tag(), *value)) <-- output_ptr(ptr), ptr_value(ptr, value);

    ////////////////////////////////////////////////////////////////////////////////
    // eval

    // Signal? -- I think it is final (winston)
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

    // initial lookup of symbol?
    lookup0(env, expr, env) <-- eval_input(expr, env), if expr.is_sym();

    // Unbound variable: If env is nil during lookup0, var is unbound. Return an an error.
    eval(var, outer_env, Ptr(Tag::Err.elt(), LE::zero())) <-- lookup0(outer_env, var, env), if env.is_nil();

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
    lookup0(outer_env, var, next_env) <--
        lookup0(outer_env, var, env),
        cons_rel(binding, next_env, env),
        cons_rel(bound_var, value, binding), if bound_var != var;

    ////////////////////
    // looked-up value is thunk

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


    ////////////////////
    // conditional

    // Signal: Evaluating if
    eval_input(cond, env) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest);

    // Signal: Evaled condition is not nil: evaluate the a branch.
    eval_input(a, env) <--
        eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if(),
        cons_rel(cond, branches, rest), eval(cond, env, evaled_cond),
        cons_rel(a, more, branches), if !evaled_cond.is_nil(); // FIXME: add not_nil relation to avoid negation.

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
    // Signal (for now)
    relation maybe_fun_call(Ptr, Ptr, Ptr, Ptr); // (expr, env, maybe_fun, rest)

    // If head is fun.
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
    fun_call(expr, env, args, body, closed_env, rest) <--
        maybe_fun_call(expr, env, maybe_fun, rest), eval(maybe_fun, env, fun), fun_rel(args, body, closed_env, fun);


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

    fun_call(expr, env, more_args, body, new_closed_env, more_vals) <--
        fun_call(expr, env, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(unevaled, more_vals, rest),
        eval(unevaled, env, evaled),
        cons_rel(arg, evaled, binding),
        cons_rel(binding, closed_env, new_closed_env);

    ////////////////////
    // let binding

    // // Signal
    // relation bind_parse(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)
    // // Signal
    // relation rec_bind_parse(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)

    // Final
    relation bind(Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, bindings, is-rec)

    // // These rules act, morally, as continuations and are all 'signal relations'.
    // // Signal
    // relation bind_cont1(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, binding, more-bindings, var, binding-tail, is-rec)
    // // Signal
    // relation bind_cont2(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, bool); // (expr, env, body, extended-env, var, unevaled, more-bindings, is-rec)
    // // Signal
    // relation bind_cont3(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, var, evaled, more-bindings)

    // bind_parse(expr, env, tail) <--
    //     eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
    //     if head.is_binding();

    // rec_bind_parse(expr, env, tail) <--
    //     eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
    //     if head.is_recursive_binding();

    // let base case: bindings list is empty.
    bind(expr, env, body, env, bindings, false) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_binding(),
        cons_rel(bindings, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: error otherwise

    // letrec base case: bindings list is empty.
    bind(expr, env, body, env, bindings, true) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_recursive_binding(),
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

    eval_input(unevaled, extended_env) <--
        bind(expr, env, body, extended_env, bindings, is_rec),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(unevaled, end, binding_tail), if end.is_nil();

    // // Signal rule
    // bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, is_rec) <--
    //     bind(expr, env, body, extended_env, bindings, is_rec),
    //     cons_rel(binding, more_bindings, bindings),
    //     cons_rel(var, binding_tail, binding),
    //     cons_rel(unevaled, end, binding_tail), if end.is_nil();

    // // Signal rule (eval in let case)
    // bind_cont2(expr, env, body, extended_env, var, unevaled, more_bindings, false),
    // eval_input(unevaled, extended_env)
    //     <--
    //     bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, false),
    //     cons_rel(var, binding_tail, binding),
    //     cons_rel(unevaled, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // // Signal rule (thunk in letrec case)
    // bind_cont2(expr, env, body, extended_env, var, thunk_body, more_bindings, true) <--
    //     bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail, true),
    //     cons_rel(var, binding_tail, binding),
    //     cons_rel(thunk_body, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // // let
    // bind_cont3(expr, env, body, extended_env, var, evaled, more_bindings) <--
    //     bind_cont2(expr, env, body, extended_env, var, unevaled, more_bindings, false),
    //     eval(unevaled, extended_env, evaled);

    // // letrec
    // // FIXME: evaluate thunk for effects before binding, in case it is never looked up.
    // bind_cont3(expr, env, body, extended_env, var, thunk, more_bindings) <--
    //     bind_cont2(expr, env, body, extended_env, var, thunk_body, more_bindings, true),
    //     thunk_rel(thunk_body, extended_env, thunk);

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

    // // Signal (for now)
    // relation lambda_parse(Ptr, Ptr, Ptr); // (expr, env, args-and-body)
    
    // lambda_parse(expr, env, tail) <--
    //     eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
    //     if head.is_lambda();

    // register a fun created from a lambda expression as its evaluation
    eval(expr, env, fun) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_lambda(),
        fun_rel(args, body, env, fun);

    ////////////////////
    // fold -- default folding is fold_left

    // Real
    relation fold(Ptr, Ptr, Ptr, Num, Ptr); // (expr, env, op, acc, tail)

    // If head is left-foldable op, reduce it with its neutral element.
    // signal (?)
    fold(expr, env, head, head.neutral_element(), tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_left_foldable();

    // When left-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    #[trace("is_left_foldable {} {:?} recurse", op.built_in_name(), op)]
    eval_input(car, env) <-- fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

    // When left-folding, if car has been evaled and is F, apply the op to it and the acc, then recursively
    // fold acc and new tail. TODO: error if car is not f.
    #[trace("is_left_foldable {} {:?} apply", op.built_in_name(), op)]
    fold(expr, env, op, op.apply_op(*acc, Num(evaled_car.1)), cdr) <--
        fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car), if evaled_car.is_num();

    // left-folding operation with an empty (nil) tail
    #[trace("is_left_foldable {} {:?} base", op.built_in_name(), op)]
    eval(expr, env, Ptr(Tag::Num.elt(), acc.0)) <-- fold(expr, env, op, acc, tail), if tail.is_nil();

    ////////////////////
    // fold_right

    // Real
    relation fold_right(Ptr, Ptr, Ptr, Ptr); // (expr, env, op, tail)

    // If head is right-foldable op, initiate fold_right.
    fold_right(expr, env, head, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_right_foldable();

    // When right-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env) <-- fold_right(expr, env, op, tail), cons_rel(car, cdr, tail);

    // When right-folding an empty list, return the neutral element.
    eval(expr, env, Ptr(Tag::Num.elt(), op.neutral_element().0)) <-- fold_right(expr, env, op, tail), if tail.is_nil();

    // When right-folding, if tail is a cons (not empty), revert to a (left) fold with evaled car as initial acc.
    fold(expr, env, op, Num(evaled_car.1), cdr) <--
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
    bool_fold0(expr, env, head, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), if head.is_relational();

    // bool0-folding operation with an empty (nil) tail (and no acc)
    // TODO: factor out signal relation (bool_fold0)
    eval(expr, env, Ptr::t()) <-- bool_fold0(expr, env, _op, tail), if tail.is_nil();

    // bool-folding operation with an empty (nil) tail
    eval(expr, env, Ptr::t()) <-- bool_fold(expr, env, _op, _acc, tail), if tail.is_nil();

    // When bool0-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env) <--
        bool_fold0(expr, env, _op, tail), cons_rel(car, cdr, tail);

    // TODO: inline signal relation (bool_fold0)
    bool_fold(expr, env, op, Num(evaled_car.1), cdr) <--
        bool_fold0(expr, env, op, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car);

    eval_input(car, env) <-- bool_fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

    eval(expr, env, op.apply_relop(*acc,  Num(evaled_car.1))) <--
        bool_fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car),
        if cdr.is_nil();

    bool_fold(expr, env, op, Num(evaled_car.1), cdr) <--
        bool_fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car),
        if cdr.is_cons(),
        let x = op.apply_relop(*acc, Num(evaled_car.1)),
        if x.is_t();

    ////////////////////////////////////////////////////////////////////////////////
}

#[cfg(test)]
mod test {
    use p3_baby_bear::BabyBear;

    use crate::{
        loam::evaluation::EvaluationProgram,
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

        allocator().import_hashes(zstore.tuple2_hashes());
        wide_ptr(tag.elt(), digest)
    }

    fn test_aux0(
        zstore: ZStore<BabyBear, LurkChip>,
        input: WidePtr,
        expected_output: WidePtr,
        env: Option<WidePtr>,
    ) -> EvaluationProgram {
        let mut prog = EvaluationProgram::default();

        prog.zstore = zstore;
        prog.toplevel_input = vec![(input, env.unwrap_or(WidePtr::empty_env()))];
        prog.run();

        println!("\n{}", prog.relation_sizes_summary());
        prog.print_memory_tables();

        assert_eq!(vec![(expected_output,)], prog.output_expr);
        assert!(prog.cons_mem_is_contiguous());
        prog
    }


    fn test_distilled(original_program: &EvaluationProgram) {
        let mut prog = DistilledEvaluationProgram::default();

        prog.zstore = original_program.zstore.clone();
        prog.toplevel_input = original_program.toplevel_input.clone();

        // transfer over the memory (assume it's been distilled)
        prog.cons_digest_mem = original_program.cons_digest_mem.clone();
        prog.cons_mem = original_program.cons_mem.clone();
        prog.fun_digest_mem = original_program.fun_digest_mem.clone();
        prog.fun_mem = original_program.fun_mem.clone();
        prog.thunk_digest_mem = original_program.thunk_digest_mem.clone();
        prog.thunk_mem = original_program.thunk_mem.clone();
        prog.sym_digest_mem = original_program.sym_digest_mem.clone();
        prog.builtin_digest_mem = original_program.builtin_digest_mem.clone();
        prog.nil_digest_mem = original_program.nil_digest_mem.clone();
        prog.num = original_program.num.clone();

        prog.run();

        println!("{}", prog.relation_sizes_summary());

        assert_eq!(prog.output_expr, original_program.output_expr);
    }

    fn test_aux(input: &str, expected_output: &str, env: Option<&str>) -> EvaluationProgram {
        allocator().init();

        let mut zstore = lurk_zstore();
        let input = read_wideptr(&mut zstore, input);
        let expected_output = read_wideptr(&mut zstore, expected_output);
        let env = env.map(|s| read_wideptr(&mut zstore, s));
        test_aux0(zstore, input, expected_output, env)
    }

    #[test]
    fn test_cons_mem_distilled() {
        let fibonacci_twice = |n| {
            format!(
                "
(letrec ((fibonacci (lambda (n) 
                        (if (< n 2) 
                            1 
                            (
                                let ((a (fibonacci (- n 1)))
                                     (b (fibonacci (- n 2))))
                                (+ a b)
                            )))))
  (+ (fibonacci {n}) (fibonacci {n})))
"
            )
        };
        let prog = test_aux(&fibonacci_twice(7), "42", None);
        test_distilled(&prog);
    }
}
