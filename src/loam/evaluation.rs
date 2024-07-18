// TODO: appease clippy for now
#![allow(clippy::all)]
#![allow(warnings)]

use num_traits::FromPrimitive;

use crate::loam::allocation::allocator;
use crate::loam::lurk_sym_index;
use crate::loam::{LEWrap, Num, Ptr, Wide, WidePtr, LE};
use crate::lurk::state::LURK_PACKAGE_SYMBOLS_NAMES;
use crate::lurk::tag::Tag;
use crate::lurk::zstore::{builtin_vec, lurk_zstore, ZPtr, ZStore};

use p3_field::{AbstractField, PrimeField32};

use ascent::{ascent, Dual};

pub struct Memory {}

impl Memory {
    fn initial_builtin_relation() -> Vec<(Wide, Dual<LEWrap>)> {
        let zstore = &mut lurk_zstore();
        builtin_vec()
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let ZPtr { tag: tag, digest } = zstore.intern_symbol(name);

                (Wide(digest), Dual(LEWrap(LE::from_canonical_u64(i as u64))))
            })
            .collect()
    }

    fn initial_builtin_addr() -> LE {
        LE::from_canonical_u64(LURK_PACKAGE_SYMBOLS_NAMES.len() as u64)
    }

    fn initial_nil_relation() -> Vec<(Wide, Dual<LEWrap>)> {
        let zstore = &mut lurk_zstore();
        let ZPtr { tag: _, digest } = zstore.intern_nil();
        vec![(Wide(digest), Dual(LEWrap(LE::from_canonical_u64(0u64))))]
    }

    fn initial_nil_addr() -> LE {
        LE::from_canonical_u64(1)
    }

    fn initial_tag_relation() -> Vec<(LE, Wide)> {
        Tag::wide_relation()
    }
}

impl Ptr {
    fn is_built_in_named(&self, name: &str) -> bool {
        if !self.is_builtin() {
            return false;
        }

        self.1.as_canonical_u32() as usize == lurk_sym_index(name).unwrap()
    }

    fn is_t(&self) -> bool {
        self.is_built_in_named("t")
    }

    fn is_binding(&self) -> bool {
        self.is_built_in_named("let")
    }

    fn is_recursive_binding(&self) -> bool {
        self.is_built_in_named("letrec")
    }

    fn is_lambda(&self) -> bool {
        self.is_built_in_named("lambda")
    }

    fn is_if(&self) -> bool {
        self.is_built_in_named("if")
    }

    fn is_left_foldable(&self) -> bool {
        self.is_built_in_named("+") || self.is_built_in_named("*")
    }

    fn is_right_foldable(&self) -> bool {
        self.is_built_in_named("/") || self.is_built_in_named("-")
    }

    fn is_built_in(&self) -> bool {
        if !self.is_builtin() {
            return false;
        }

        self.1 < Memory::initial_builtin_addr()
    }

    fn is_non_built_in(&self) -> bool {
        self.is_sym()
    }

    fn is_relational(&self) -> bool {
        self.is_built_in_named("=")
            || self.is_built_in_named("<")
            || self.is_built_in_named(">")
            || self.is_built_in_named("<=")
            || self.is_built_in_named(">=")
    }

    fn neutral_element(&self) -> Num {
        if self.is_built_in_named("+") || self.is_built_in_named("-") {
            return Num(LE::zero());
        }
        if self.is_built_in_named("*") || self.is_built_in_named("/") {
            return Num(LE::one());
        }
        unreachable!()
    }

    fn apply_op(&self, a: Num, b: Num) -> Num {
        // TODO: more efficient matching
        if self.is_built_in_named("+") {
            return Num(a.0 + b.0);
        }
        if self.is_built_in_named("-") {
            return Num(a.0 - b.0);
        }
        if self.is_built_in_named("*") {
            return Num(a.0 * b.0);
        }
        if self.is_built_in_named("/") {
            return Num(a.0 / b.0);
        }

        unreachable!()
    }

    fn apply_relop(&self, a: Num, b: Num) -> Self {
        // TODO: more efficient matching
        if self.is_built_in_named("=") {
            return Self::lurk_bool(a.0 == b.0);
        }
        if self.is_built_in_named("<") {
            return Self::lurk_bool(a.0 < b.0);
        }
        if self.is_built_in_named(">") {
            return Self::lurk_bool(a.0 > b.0);
        }
        if self.is_built_in_named("<=") {
            return Self::lurk_bool(a.0 <= b.0);
        }
        if self.is_built_in_named(">=") {
            return Self::lurk_bool(a.0 >= b.0);
        }

        unreachable!()
    }

    fn lurk_bool(b: bool) -> Self {
        if b {
            Self::t()
        } else {
            Self::nil()
        }
    }
}

impl Tag {
    pub fn elt(&self) -> LE {
        self.to_field::<LE>()
    }

    pub fn value(&self) -> Wide {
        Wide::widen(self.elt())
    }

    pub fn wide_relation() -> Vec<(LE, Wide)> {
        (0..Self::count())
            .map(|i| {
                let tag = Tag::from_u32(i.try_into().unwrap()).unwrap();
                (tag.elt(), tag.value())
            })
            .collect()
    }
}

// Because it's hard to share code between ascent programs, this is a copy of `AllocationProgram`, replacing the `map_double` function
// with evaluation.
ascent! {
    struct EvaluationProgram;

    ////////////////////////////////////////////////////////////////////////////////
    // Relations

    // NOTE: Relations are designated as either 'signal' or 'final'. Signal relations are not required for proving and
    // need not be present in the second-pass program.
    // Final relations must be present in the second pass..

    // Final: The standard tag mapping.
    relation tag(LE, Wide) = Memory::initial_tag_relation(); // (short-tag, wide-tag)

    // Final
    relation ptr_value(Ptr, Wide); // (ptr, value)}
    // Final (but could be optimized out).
    relation ptr_tag(Ptr, Wide); // (ptr, tag)

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

    // Signal: triggers allocation once per unique cons
    relation cons(Ptr, Ptr); // (car, cdr)
    // Final
    relation car(Ptr, Ptr); // (cons, car)
    // Final
    relation cdr(Ptr, Ptr); // (cons, cdr)
    // Final
    relation hash4(Ptr, Wide, Wide, Wide, Wide); // (a, b, c, d)
    // Signal
    relation unhash4(LE, Wide); // (tag, digest)
    // Final
    relation hash4_rel(Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, digest)

    // Signal
    relation fun(Ptr, Ptr, Ptr); // (args, body, closed_env)
    // Final
    relation hash6(Ptr, Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f)
    // Signal
    relation unhash6(LE, Wide); // (tag, digest)
    // Final
    relation hash6_rel(Wide, Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f, digest)

    // Signal
    relation thunk(Ptr, Ptr); // (body, closed_env)

    // Signal: inclusion triggers *_value relations.
    relation egress(Ptr); // (ptr)
    // Signal (is that right?)
    relation f_value(Ptr, Wide); // (ptr, immediate-wide-value)
    // Signal (is that right?)
    relation cons_value(Ptr, Wide); // (cons, value)

    // all known `Ptr`s should be added to ptr.
    // Signal
    relation ptr(Ptr); // (ptr)
    // Final
    relation ptr_tag(Ptr, Wide); // (ptr, tag)
    // Final
    relation ptr_value(Ptr, Wide); // (ptr, value)

    // supporting ingress
    // inclusion triggers *_value relations.
    // Signal
    relation ingress(Ptr); // (ptr)

    // Signal
    relation alloc(LE, Wide); // (tag, value)

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

    // Populating alloc(...) triggers allocation in cons_digest_mem.
    cons_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Cons.elt(), LE::zero())))) <-- alloc(tag, value), if *tag == Tag::Cons.elt();

    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Cons.value()), ptr_value(ptr, value) <-- cons_digest_mem(value, addr), let ptr = Ptr(Tag::Cons.elt(), addr.0.0);

    // Populating cons(...) triggers allocation in cons mem.
    cons_mem(car, cdr, Dual(LEWrap(allocator().alloc_addr(Tag::Cons.elt(), LE::zero())))) <-- cons(car, cdr);

    // Populate cons_digest_mem if a cons in cons_mem has been hashed in hash4_rel.
    cons_digest_mem(digest, addr) <--
        cons_mem(car, cdr, addr),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)) <-- cons_mem(car, cdr, addr);

    ptr(cons), ptr_tag(cons, Tag::Cons.value()) <-- cons_rel(_, _, cons);

    ////////////////////////////////////////////////////////////////////////////////
    // Fun

    // TODO: this was copied directly from the cons memory, so we should be able to formalize with a macro.

    // Final
    relation fun_rel(Ptr, Ptr, Ptr, Ptr); // (args, body, closed-env, fun)
    // Final
    lattice fun_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
    // Final
    lattice fun_mem(Ptr, Ptr, Ptr, Dual<LEWrap>); // (args, body, closed-env, addr)

    fun_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Fun.elt(), LE::zero())))) <-- alloc(tag, value), if *tag == Tag::Fun.elt();

    ptr(ptr), ptr_tag(ptr, Tag::Fun.value()), ptr_value(ptr, value) <-- fun_digest_mem(value, addr), let ptr = Ptr(Tag::Fun.elt(), addr.0.0);

    fun_mem(args, body, closed_env, Dual(LEWrap(allocator().alloc_addr(Tag::Fun.elt(), LE::zero())))) <-- fun(args, body, closed_env);

    fun_digest_mem(digest, addr) <--
        fun_mem(args, body, closed_env, addr),
        ptr_value(args, args_value), ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        ptr_tag(args, args_tag), ptr_tag(body, body_tag), ptr_tag(closed_env, closed_env_tag),
        hash6_rel(args_tag, args_value, body_tag, body_value, closed_env_tag, closed_env_value, digest);

    fun_rel(args, body, closed_env, Ptr(Tag::Fun.elt(), addr.0.0)) <-- fun_mem(args, body, closed_env, addr);

    ptr(fun), ptr_tag(fun, Tag::Fun.value()) <-- fun_rel(_, _, _, fun);

    ////////////////////////////////////////////////////////////////////////////////
    // Thunk

    // TODO: this was copied directly from the fun memory, so we should be able to formalize with a macro.

    // Final
    relation thunk_rel(Ptr, Ptr, Ptr); // (body, closed-env, thunk)
    // Final
    lattice thunk_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
    // Final
    lattice thunk_mem(Ptr, Ptr, Dual<LEWrap>); // (body, closed-env, addr)

    thunk_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Thunk.elt(), LE::zero())))) <-- alloc(tag, value), if *tag == Tag::Thunk.elt();

    ptr(ptr), ptr_tag(ptr, Tag::Thunk.value()), ptr_value(ptr, value) <-- thunk_digest_mem(value, addr), let ptr = Ptr(Tag::Thunk.elt(), addr.0.0);

    thunk_mem(body, closed_env, Dual(LEWrap(allocator().alloc_addr(Tag::Thunk.elt(), LE::zero())))) <-- thunk(body, closed_env);

    thunk_digest_mem(digest, addr) <--
        thunk_mem(body, closed_env, addr),
        ptr_value(body, body_value), ptr_value(closed_env, closed_env_value),
        ptr_tag(body, body_tag), ptr_tag(closed_env, closed_env_tag),
        hash4_rel(body_tag, body_value, closed_env_tag, closed_env_value, digest);

    thunk_rel(body, closed_env, Ptr(Tag::Thunk.elt(), addr.0.0)) <-- thunk_mem(body, closed_env, addr);

    ptr(thunk), ptr_tag(thunk, Tag::Thunk.value()) <-- thunk_rel(_, _, thunk);


    ////////////////////////////////////////////////////////////////////////////////
    // Sym

    // Final
    lattice sym_digest_mem(Wide, Dual<LEWrap>); // (digest, addr)

    // Populating alloc(...) triggers allocation in sym_digest_mem.
    sym_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Sym.elt(), LE::zero())))) <-- alloc(tag, value), if *tag == Tag::Sym.elt();

    // // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Sym.value()), ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), addr.0.0);
    // todo: sym_value

    ////////////////////////////////////////////////////////////////////////////////
    // Builtin

    // Final
    lattice builtin_digest_mem(Wide, Dual<LEWrap>) = Memory::initial_builtin_relation(); // (digest, addr)

    // Populating alloc(...) triggers allocation in sym_digest_mem.
    builtin_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Sym.elt(), Memory::initial_builtin_addr())))) <-- alloc(tag, value), if *tag == Tag::Builtin.elt();

    // // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Builtin.value()), ptr_value(ptr, value) <-- builtin_digest_mem(value, addr), let ptr = Ptr(Tag::Builtin.elt(), addr.0.0);
    // todo: builtin_value


    ////////////////////////////////////////////////////////////////////////////////
    // Nil

    // Final
    // Can this be combined with sym_digest_mem? Can it be eliminated? (probably eventually).
    lattice nil_digest_mem(Wide, Dual<LEWrap>) = Memory::initial_nil_relation(); // (digest, addr)

    nil_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Nil.elt(), Memory::initial_nil_addr())))) <-- alloc(tag, value), if *tag == Tag::Nil.elt();

    ptr(ptr), ptr_tag(ptr, Tag::Nil.value()), ptr_value(ptr, value) <-- nil_digest_mem(value, addr), let ptr = Ptr(Tag::Nil.elt(), addr.0.0);

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
    unhash4(Tag::Cons.elt(), digest) <-- ingress(ptr), if ptr.is_cons(), ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    // mark ingress funs for unhashing
    unhash6(Tag::Fun.elt(), digest) <-- ingress(ptr), if ptr.is_fun(), ptr_value(ptr, digest);

    hash6_rel(a, b, c, d, e, f, digest) <-- unhash6(_, digest), let [a, b, c, d, e, f] = allocator().unhash6(digest).unwrap();

    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(&Tag::Cons.elt(), digest),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    f_value(Ptr(Tag::Num.elt(), value.f()), value) <-- alloc(&Tag::Num.elt(), value);

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest),
        cons_digest_mem(digest, addr),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    ptr(cons), car(cons, car), cdr(cons, cdr) <-- cons_rel(car, cdr, cons);

    f_value(ptr, Wide::widen(ptr.1)) <-- ptr(ptr), if ptr.is_num();
    ptr(ptr) <-- f_value(ptr, _);

    // Provide cons_value when known.
    cons_value(ptr, digest)
        <-- hash4(ptr, car_tag, car_value, cdr_tag, cdr_value),
            hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest);

    ////////////////////////////////////////////////////////////////////////////////
    // Egress path

    // The output_ptr is marked for egress.
    egress(ptr) <-- output_ptr(ptr);

    // Cons
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // Fun
    egress(args), egress(body), egress(closed_env) <-- egress(fun), fun_rel(args, body, closed_env, fun);

    // Num: FIXME: change this when F becomes u32.
    ptr_tag(ptr, Tag::Num.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_num();

    // Err
    ptr_tag(ptr, Tag::Err.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_err();

    // Construct output_expr from output_ptr
    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), ptr_value(ptr, value), ptr_tag(ptr, wide_tag);

    // Cons
    hash4(cons, car_tag, car_value, cdr_tag, cdr_value) <--
        egress(cons),
        cons_rel(car, cdr, cons),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    // TODO: reorg src. This is not cons-specific.
    hash4_rel(a, b, c, d, allocator().hash4(*a, *b, *c, *d)) <-- hash4(ptr, a, b, c, d);

    // TODO: refactor names. This is shared with thunks (and other 2-ptr structures).
    // TODO: but also, is this actually necessary?
    ptr(car), ptr(cdr) <--
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, _),
        ptr_tag(car, wide_car_tag), ptr_tag(cdr, wide_cdr_tag),
        ptr_value(car, car_value), ptr_value(cdr, cdr_value);

    // Thunk
    hash4(thunk, body_tag, body_value, closed_env_tag, closed_env_value) <--
        egress(thunk),
        cons_rel(body, closed_env, thunk),
        ptr_tag(body, body_tag), ptr_tag(closed_env, closed_env_tag),
        ptr_value(body, body_value), ptr_value(closed_env, closed_env_value);

    // Fun
    hash6(fun, args_tag, args_value, body_tag, body_value, closed_env_tag, closed_env_value) <--
        egress(fun),
        fun_rel(args, body, closed_env, fun),
        ptr_tag(args, args_tag),
        ptr_value(args, args_value),
        ptr_tag(body, body_tag),
        ptr_value(body, body_value),
        ptr_tag(closed_env, closed_env_tag),
        ptr_value(closed_env, closed_env_value);

    hash6_rel(a, b, c, d, e, f, allocator().hash6(*a, *b, *c, *d, *e, *f)) <-- hash6(ptr, a, b, c, d, e, f);

    ptr(args), ptr(body), ptr(closed_env) <--
        hash6_rel(args_tag, args_value, body_tag, body_value, closed_env_tag, closed_env_value, _),
        ptr_tag(args, args_tag), ptr_tag(body, body_tag), ptr_tag(closed_env, closed_env_tag),
        ptr_value(args, args_value), ptr_value(body, body_value), ptr_value(closed_env, closed_env_value);

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
    // conditional

    ingress(rest) <-- eval_input(expr, env), cons_rel(op, rest, expr), if op.is_if();

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

    // If head is  fun.
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

    fun_call(expr, env, more_args, body, new_closed_env, more_vals)
        <--
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
    relation lambda_parse(Ptr, Ptr, Ptr); // (expr, env, args-and-body)

    ingress(tail), lambda_parse(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_lambda();

    // Signal
    ingress(rest) <--
        lambda_parse(expr, env, tail),
        cons_rel(args, rest, tail);

    // Signal: create a fun from a parsed lambda evaluation
    fun(args, body, env) <--
        lambda_parse(expr, env, tail),
        cons_rel(args, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: otherwise error

    // register a fun created from a lambda expression as its evaluation
    eval(expr, env, fun) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_lambda(),
        lambda_parse(expre, env, tail),
        fun(args, body, env),
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
    eval_input(car, env), ingress(car) <-- fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

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

    eval_input(car, env), ingress(car), ingress(cdr) <-- bool_fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::lurk::zstore::ZPtr;

    fn err() -> WidePtr {
        WidePtr(Tag::Err.value(), Wide::widen(LE::from_canonical_u32(0)))
    }

    fn wide_ptr(tag: LE, digest: [LE; 8]) -> WidePtr {
        WidePtr(Wide::widen(tag), Wide(digest))
    }

    fn read_wideptr(src: &str) -> WidePtr {
        let zstore = &mut lurk_zstore();
        let ZPtr { tag, digest } = zstore.read(src).unwrap();

        allocator().import_hashes(zstore.tuple2_hashes());
        wide_ptr(tag.elt(), digest)
    }

    fn test_aux0(
        input: WidePtr,
        expected_output: WidePtr,
        env: Option<WidePtr>,
    ) -> EvaluationProgram {
        let mut prog = EvaluationProgram::default();

        prog.toplevel_input = vec![(input, env.unwrap_or(WidePtr::empty_env()))];
        prog.run();

        println!("{}", prog.relation_sizes_summary());

        let expected = vec![(expected_output,)];

        let output_expr = prog.output_expr.clone();
        if &expected != &output_expr {
            let output_expr = prog.output_expr.clone();
            debug_prog(prog);
            dbg!(output_expr);
            panic!("mismatch");
        }

        assert_eq!(expected, output_expr);
        prog
    }

    fn test_aux(input: &str, expected_output: &str, env: Option<&str>) -> EvaluationProgram {
        allocator().init();

        test_aux0(
            read_wideptr(input),
            read_wideptr(expected_output),
            env.map(read_wideptr),
        )
    }

    fn test_aux1(input: &str, expected_output: WidePtr, env: Option<&str>) -> EvaluationProgram {
        allocator().init();

        test_aux0(read_wideptr(input), expected_output, env.map(read_wideptr))
    }

    #[test]
    fn test_self_evaluating_f() {
        test_aux("123", "123", None);
    }

    #[test]
    fn test_self_evaluating_nil() {
        let prog = test_aux("nil", "nil", None);
    }

    #[test]
    fn test_zero_arg_addition() {
        test_aux("(+)", "0", None);
    }

    #[test]
    fn test_one_arg_addition() {
        test_aux("(+ 1)", "1", None);
    }

    #[test]
    fn test_two_arg_addition() {
        test_aux("(+ 1 2)", "3", None);
    }

    #[test]
    fn test_three_arg_addition() {
        test_aux("(+ 1 2 3)", "6", None);
    }

    #[test]
    fn test_zerog_arg_multiplication() {
        test_aux("(*)", "1", None);
    }

    #[test]
    fn test_one_arg_multiplication() {
        test_aux("(* 2)", "2", None);
    }

    #[test]
    fn test_two_arg_multiplication() {
        test_aux("(* 2 3)", "6", None);
    }

    #[test]
    fn test_three_arg_multiplication() {
        test_aux("(* 2 3 4)", "24", None);
    }

    #[test]
    fn test_nested_arithmetic() {
        test_aux("(+ 5 (* 3 4))", "17", None);
    }

    #[test]
    fn test_three_arg_division() {
        test_aux("(/ 10 2 5)", "1", None);
    }

    #[test]
    fn test_complicated_nested_arithmetic() {
        test_aux(
            "(+ 5 (-) (*) (/) (+) (* 3 4 (- 7 2 1)) (/ 10 2 5))",
            "56",
            None,
        );
    }

    #[test]
    fn test_relational() {
        test_aux("(=)", "t", None);
        test_aux("(= 1)", "t", None);
        test_aux("(= 1 1)", "t", None);
        test_aux("(= 1 1 1)", "t", None);
        test_aux("(= 1 2)", "nil", None);
        test_aux("(= 1 1 2)", "nil", None);

        // TODO: handle these type errors
        // test_aux1("(= nil)", err(), None);
        // test_aux1("(= 1 nil)", err(), None);
    }

    #[test]
    fn test_if() {
        test_aux("(if (= 1 1) 123 456)", "123", None);
        test_aux("(if (= 1 2) 123 456)", "456", None);
    }

    #[test]
    fn test_unbound_var() {
        test_aux1("x", err(), None);
    }

    #[test]
    fn test_var_lookup() {
        test_aux("x", "9", Some("((x . 9))"));
    }

    #[test]
    fn test_deep_var_lookup() {
        let env = read_wideptr("((y . 10) (x . 9))");
        let expr = read_wideptr("x");

        test_aux("x", "9", Some("((y . 10) (x . 9))"));
        test_aux("y", "10", Some("((y . 10) (x . 9))"));
        test_aux1("z", err(), Some("((y . 10) (x . 9))"));
    }

    #[test]
    fn test_let_plain() {
        test_aux("(let ((x 9)) x)", "9", None);
        test_aux("(let ((x 9)(y 10)) x)", "9", None);
        test_aux("(let ((x 9)(y 10)) y)", "10", None);
        test_aux("(let ((x (+ 1 1))) x)", "2", None);
        test_aux("(let ((y 9) (x (+ 1 1))) x)", "2", None);
    }

    #[test]
    fn test_lambda() {
        let args_wide_ptr = read_wideptr("(x)");
        let body_wide_ptr = read_wideptr("(+ x 1)");
        let expected_fun_digest = allocator().hash6(
            args_wide_ptr.0,
            args_wide_ptr.1,
            body_wide_ptr.0,
            body_wide_ptr.1,
            WidePtr::empty_env().0,
            WidePtr::empty_env().1,
        );
        let expected_fun = WidePtr(Tag::Fun.value(), expected_fun_digest);

        test_aux1("(lambda (x) (+ x 1))", expected_fun, None);

        test_aux("((lambda (x) (+ x 1)) 7)", "8", None);

        test_aux("(let ((f (lambda () 123))) (f))", "123", None);
        test_aux("(let ((f (lambda (x) (+ 1 x)))) (f 2))", "3", None);

        // evaled args
        test_aux("(let ((f (lambda (x) (+ 1 x)))) (f (* 2 3)))", "7", None);

        // multiple args
        test_aux("(let ((f (lambda (a b) (* a b)))) (f 2 3))", "6", None);

        // closure
        test_aux(
            "(let ((k 123)(foo (lambda (x) (+ x k)))) (foo 1))",
            "124",
            None,
        );

        test_aux(
            "(let ((foo (lambda (x) (* x 2)))(bar 123)) (foo 3))",
            "6",
            None,
        );
        test_aux(
            "(let ((foo (lambda (x) (* x 2)))(bar (lambda () 123))) (foo 3))",
            "6",
            None,
        );
        test_aux(
            "(let ((foo (lambda (x) (* x 2)))(bar (lambda (x) 123))) (foo 3))",
            "6",
            None,
        );

        // nested calls
        test_aux(
            "(let ((foo (lambda (x) (* x 2))) (bar (lambda (x) (+ 1 (foo x))))) (bar 3))",
            "7",
            None,
        );

        ////////////////////////////////////////
        // with letrec

        test_aux("(letrec ((f (lambda () 123))) (f))", "123", None);
        test_aux("(letrec ((f (lambda (x) (+ 1 x)))) (f 2))", "3", None);

        // evaled args
        test_aux("(letrec ((f (lambda (x) (+ 1 x)))) (f (* 2 3)))", "7", None);

        // multiple args
        test_aux("(letrec ((f (lambda (a b) (* a b)))) (f 2 3))", "6", None);

        // closure
        test_aux(
            "(letrec ((k 123)(foo (lambda (x) (+ x k)))) (foo 1))",
            "124",
            None,
        );

        test_aux(
            "(letrec ((foo (lambda (x) (* x 2)))(bar 123)) (foo 3))",
            "6",
            None,
        );
        test_aux(
            "(letrec ((foo (lambda (x) (* x 2)))(bar (lambda () 123))) (foo 3))",
            "6",
            None,
        );
        test_aux(
            "(letrec ((foo (lambda (x) (* x 2)))(bar (lambda (x) 123))) (foo 3))",
            "6",
            None,
        );

        // nested calls
        test_aux(
            "(letrec ((foo (lambda (x) (* x 2))) (bar (lambda (x) (+ 1 (foo x))))) (bar 3))",
            "7",
            None,
        );
    }

    #[test]
    fn test_letrec_binding() {
        let thunk = "(letrec ((f 123)) f)";

        let expr_ptr = read_wideptr("123");
        let env_ptr = WidePtr::empty_env();

        let expected_thunk_digest = allocator().hash4(expr_ptr.0, expr_ptr.1, env_ptr.0, env_ptr.1);

        let expected_thunk = WidePtr(Tag::Thunk.value(), expected_thunk_digest);
        let prog = test_aux1(thunk, expr_ptr, None);
    }

    #[test]
    fn test_letrec_plain() {
        test_aux("(letrec ((x 9)) x)", "9", None);
        test_aux("(letrec ((x (+ 1 1))) x)", "2", None);

        test_aux("(letrec ((x 9)(y 10)) x)", "9", None);
        test_aux("(letrec ((x 9)(y 10)) y)", "10", None);
        test_aux("(letrec ((y 9) (x (+ 1 1))) x)", "2", None);
    }

    #[test]
    fn test_letrec() {
        let factorial = |n| {
            format!(
                "
(letrec ((factorial (lambda (n) (if (= n 0) 1 (* n (factorial (- n 1)))))))
   (factorial {n}))"
            )
        };

        let fibonacci = |n| {
            format!(
                "
(letrec ((fibonacci (lambda (n) (if (< n 2) 1 (+ (fibonacci (- n 2)) (fibonacci (- n 1)))))))
  (fibonacci {n}))
"
            )
        };

        test_aux(&factorial(0), "1", None);
        test_aux(&factorial(1), "1", None);
        test_aux(&factorial(4), "24", None);

        // // 1, 1, 2, 3, 5, 8, 13, 21
        test_aux(&fibonacci(0), "1", None);
        test_aux(&fibonacci(1), "1", None);
        test_aux(&fibonacci(5), "8", None);
        test_aux(&fibonacci(7), "21", None);
    }

    #[test]
    fn test_show_summary() {
        println!("{}", EvaluationProgram::summary());
    }

    fn debug_prog(prog: EvaluationProgram) {
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
            fun_rel,
            fun_mem,
            fun,
            sym_digest_mem,
            fun_call,
            thunk_rel,
            thunk_mem,
            thunk_digest_mem,
            lookup,
            bool_fold,
            bool_fold0,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            toplevel_input,
            input_ptr,
            eval_input,
            eval,
            // hash4,
            // unhash4,
            // hash4_rel,
            output_ptr,
            output_expr,
            //ptr_value,
            // cons,
            cons_rel,
            cons_mem,
            // cons_digest_mem,
            // alloc,
            // ingress,
            // egress,
            // fun_rel,
            // fun_mem,
            // fun,
            // sym_digest_mem,
            fun_call,
            // hash4_rel,
            thunk_rel,
            thunk_mem,
            thunk_digest_mem,
            lookup,
            alloc,
            bool_fold,
            bool_fold0
        );
    }
}
