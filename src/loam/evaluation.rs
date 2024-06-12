use crate::loam::allocation::allocator;
use crate::loam::{LEWrap, Num, Ptr, Wide, WidePtr, LE};
use crate::lurk::reader::{read, ReadData};
use crate::lurk::state::{State, LURK_PACKAGE_SYMBOLS_NAMES};
use crate::lurk::zstore::Tag;

use p3_field::{AbstractField, PrimeField32};

use ascent::{ascent, Dual};

pub struct Memory {}

fn simple_read(src: &str) -> ReadData {
    read(State::init_lurk_state().rccell(), src).unwrap()
}

impl Memory {
    fn initial_sym_relation() -> Vec<(Wide, Dual<LEWrap>)> {
        LURK_PACKAGE_SYMBOLS_NAMES
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let ReadData { digest, .. } = simple_read(name);
                (Wide(digest), Dual(LEWrap(LE::from_canonical_u64(i as u64))))
            })
            .collect()
    }
    fn initial_sym_addr() -> LE {
        LE::from_canonical_u64(LURK_PACKAGE_SYMBOLS_NAMES.len() as u64)
    }

    fn initial_tag_relation() -> Vec<(LE, Wide)> {
        Tag::wide_relation()
    }
}

// TODO: This can use a hashtable lookup, or could even be known at compile-time (but how to make that non-brittle since iter() is not const?).
fn lurk_sym_index(name: &str) -> Option<usize> {
    LURK_PACKAGE_SYMBOLS_NAMES.iter().position(|s| *s == name)
}

impl Ptr {
    fn is_built_in_named(&self, name: &str) -> bool {
        self.1.as_canonical_u32() as usize == lurk_sym_index(name).unwrap()
    }

    fn is_binding(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.is_built_in_named("let")
    }

    fn is_lambda(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.is_built_in_named("lambda")
    }

    fn is_left_foldable(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.is_built_in_named("+") || self.is_built_in_named("*")
    }

    fn is_right_foldable(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.is_built_in_named("/") || self.is_built_in_named("-")
    }

    fn is_built_in(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.1 < Memory::initial_sym_addr()
    }

    fn is_non_built_in(&self) -> bool {
        if !self.is_sym() {
            return false;
        }
        self.1 >= Memory::initial_sym_addr()
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
                let tag = Tag::from(i);
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

    relation fun(Ptr, Ptr, Ptr); // (args, body, closed_env)
    relation hash6(Ptr, Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f)
    relation unhash6(LE, Wide, Ptr); // (tag, digest, ptr)
    relation hash6_rel(Wide, Wide, Wide, Wide, Wide, Wide, Wide); // (a, b, c, d, e, f, digest)

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
    lattice cons_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
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

    relation fun_rel(Ptr, Ptr, Ptr, Ptr); // (args, body, closed-env, fun)

    lattice fun_digest_mem(Wide, Dual<LEWrap>); // (value, addr)
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
    // Sym

    lattice sym_digest_mem(Wide, Dual<LEWrap>) = Memory::initial_sym_relation(); // (digest, addr)
    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Sym.value()), ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), addr.0.0);
    // todo: sym_value

    // Populating alloc(...) triggers allocation in sym_digest_mem.
    sym_digest_mem(value, Dual(LEWrap(allocator().alloc_addr(Tag::Sym.elt(), Memory::initial_sym_addr())))) <-- alloc(tag, value), if *tag == Tag::Sym.elt();

    // Convert addr to ptr and register ptr relations.
    ptr(ptr), ptr_tag(ptr, Tag::Sym.value()), ptr_value(ptr, value) <-- sym_digest_mem(value, addr), let ptr = Ptr(Tag::Sym.elt(), addr.0.0);


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
    unhash4(Tag::Cons.elt(), digest, ptr) <-- ingress(ptr), if ptr.is_cons(), ptr_value(ptr, digest);

    // unhash to acquire preimage pointers from digest.
    hash4_rel(a, b, c, d, digest) <-- unhash4(_, digest, ptr), let [a, b, c, d] = allocator().unhash4(digest).unwrap();

    // mark ingress funs for unhashing
    unhash6(Tag::Fun.elt(), digest, ptr) <-- ingress(ptr), if ptr.is_fun(), ptr_value(ptr, digest);

    hash6_rel(a, b, c, d, e, f, digest) <-- unhash6(_, digest, ptr), let [a, b, c, d, e, f] = allocator().unhash6(digest).unwrap();

    alloc(car_tag, car_value),
    alloc(cdr_tag, cdr_value) <--
        unhash4(&Tag::Cons.elt(), digest, _),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag),
        tag(cdr_tag, wide_cdr_tag);

    // ptr(ptr), ptr_value(ptr, Wide::widen(f)) <-- alloc(&Tag::Nil.elt(), value), let f = value.f(), let ptr = Ptr(Tag::Nil.elt(), f);
    f_value(Ptr(Tag::Num.elt(), value.f()), value) <-- alloc(&Tag::Num.elt(), value); // let f = value.f();

    ptr(ptr), ptr_value(ptr, value) <-- alloc(&Tag::Nil.elt(), value), let ptr = Ptr(Tag::Nil.elt(), value.f());

    cons_rel(car, cdr, Ptr(Tag::Cons.elt(), addr.0.0)),
    cons_mem(car, cdr, addr) <--
        hash4_rel(car_tag, car_value, cdr_tag, cdr_value, digest),
        cons_digest_mem(digest, addr),
        ptr_tag(car, car_tag), ptr_tag(cdr, cdr_tag),
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

    // Cons
    egress(car), egress(cdr) <-- egress(cons), cons_rel(car, cdr, cons);

    // Fun
    egress(args), egress(body), egress(closed_env) <-- egress(fun), fun_rel(args, body, closed_env, fun);

    // F: FIXME: change this when F becomes u32.
    ptr_tag(ptr, Tag::Num.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_f();

    // Err
    ptr_tag(ptr, Tag::Err.value()), ptr_value(ptr, Wide::widen(ptr.1)) <-- egress(ptr), if ptr.is_err();

    // Construct output_expr from output_ptr
    output_expr(WidePtr(*wide_tag, *value)) <-- output_ptr(ptr), ptr_value(ptr, value), ptr_tag(ptr, wide_tag);

    // Cons
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

    alloc(car_tag, car_value), alloc(cdr_tag, cdr_value) <--
        cons_digest_mem(digest, addr),
        hash4_rel(wide_car_tag, car_value, wide_cdr_tag, cdr_value, digest),
        tag(car_tag, wide_car_tag), tag(cdr_tag, wide_cdr_tag);

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

    alloc(args_tag, args_value), alloc(body_tag, body_value), alloc(closed_env_tag, closed_env_value) <--
        fun_digest_mem(digest, addr),
        hash6_rel(wide_args_tag, args_value, wide_body_tag, body_value, wide_closed_env_tag, closed_env_value, digest),
        tag(args_tag, wide_args_tag), tag(body_tag, wide_body_tag), tag(closed_env_tag, wide_closed_env_tag);

    ////////////////////////////////////////////////////////////////////////////////
    // eval

    relation eval_input(Ptr, Ptr); // (expr, env)
    relation eval(Ptr, Ptr, Ptr); // (input-expr, env, output-expr)

    // FIXME: We need to actually allocate, or otherwise define this Nil Ptr.
    // It's fine for now, while env is unused.
    eval_input(expr, env) <-- input_ptr(expr, env);

    // expr is F: self-evaluating.
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_f();

    // expr is Nil: self-evaluating. TODO: check value == nil value
    eval(expr, env, expr) <-- eval_input(expr, env), if expr.is_nil();

    ////////////////////////////////////////
    // expr is Sym

    relation lookup(Ptr, Ptr, Ptr, Ptr); // (input_expr, input_env, var, env)

    // If expr is not a built-in sym, look it up.
    ingress(env), lookup(expr, env, expr, env) <-- eval_input(expr, env), if expr.is_non_built_in();

    // Unbound variable: If env is nil during lookup, var is unbound. Return an an error.
    eval(input_expr, input_env, Ptr(Tag::Err.elt(), LE::zero())) <-- lookup(input_expr, input_env, _, env), if env.is_nil();

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

    relation eval_head_parse(Ptr, Ptr, Ptr, Ptr); // (expr, env, head, rest)

    // if head is a cons [or eventually other non-built-in]
    ingress(head),
    eval_head_parse(expr, env, head, rest),
    eval_input(head, env) <--
        eval_input(expr, env), cons_rel(head, rest, expr), if head.is_cons();

    // construct new expression to evaluate, using evaled head
    cons(evaled_head, rest) <--
        eval_head_parse(expr, env, head, rest),
        eval(head, env, evaled_head);

    // mark the new expression for evaluation
    // Signal rule
    ingress(rest),
    eval_input(new_expr, env) <--
        eval_head_parse(expr, env, head, rest),
        eval(head, env, evaled_head),
        cons_rel(evaled_head, rest, new_expr);

    // register evaluation result
    eval(expr, env, result) <--
        eval_head_parse(expr, env, head, rest),
        eval(head, env, evaled_head),
        cons_rel(evaled_head, rest, new_expr),
        eval(new_expr, env, result);

    ////////////////////

    // TODO: parse_fun relation?

    relation parse_fun_call(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, fun, args, body, closed_env, rest)

    ingress(args), ingress(rest),
    parse_fun_call(expr, env, fun, args, body, closed_env, rest) <--
        eval_input(expr, env),
        cons_rel(fun, rest, expr),
        fun_rel(args, body, closed_env, fun);

    // base case: args list is empty
    eval_input(body, closed_env) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        if args.is_nil() && rest.is_nil(); // TODO: error if arg is nil, but rest is not.

    // register base-case evaluation result
    eval(expr, env, result) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        if args.is_nil(),
        eval(body, closed_env, result);

    cons(arg, val) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(val, more_vals, rest);

    cons(binding, closed_env) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(val, more_vals, rest),
        cons_rel(arg, val, binding);

    eval_input(body, new_closed_env) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(val, more_vals, rest),
        cons_rel(arg, val, binding),
        cons_rel(binding, closed_env, new_closed_env);

    eval(expr, env, result) <--
        parse_fun_call(expr, env, fun, args, body, closed_env, rest),
        cons_rel(arg, more_args, args),
        cons_rel(val, more_vals, rest),
        cons_rel(arg, val, binding),
        cons_rel(binding, closed_env, new_closed_env),
        eval(body, new_closed_env, result);

    ////////////////////
    // let binding

    relation bind_parse(Ptr, Ptr, Ptr); // (expr, env, bindings-and-body)
    relation bind(Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, bindings)

    // These rules act, morally, as continuations and are all 'signal relations'.
    relation bind_cont1(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, binding, more-bindings, var, binding_tail)
    relation bind_cont2(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, var, val, more-bindings)

    ingress(tail), bind_parse(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
       if head.is_binding();

    // // Signal rule
    ingress(bindings), ingress(rest) <--
        bind_parse(expr, env, tail),
        cons_rel(bindings, rest, tail);

    // Base case: bindings list is empty.
    bind(expr, env, body, env, bindings) <--
        bind_parse(expr, env, tail),
        cons_rel(bindings, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: error otherwise

    // Evaluate body with extended environment.
    eval_input(body, extended_env) <--
        bind(expr, env, body, extended_env, bindings),
        if bindings.is_nil();

    eval(expr, env, result) <--
        bind(expr, env, body, extended_env, bindings),
        if bindings.is_nil(),
        eval(bod, extended_env, result);

    // Signal rule
    ingress(binding), ingress(more_bindings) <--
        bind(expr, env, body, extended_env, bindings),
        cons_rel(binding, more_bindings, bindings);

    // Signal rule
    bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail),
    ingress(binding_tail) <--
        bind(expr, env, body, extended_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding);

    // Signal rule
    bind_cont2(expr, env, body, extended_env, var, val, more_bindings),
    cons(var, val) <--
        bind_cont1(expr, env, body, extended_env, binding, more_bindings, var, binding_tail),
        cons_rel(var, binding_tail, binding),
        cons_rel(val, end, binding_tail), if end.is_nil(); // TODO: error otherwise

    // Signal rule
     cons(env_binding, extended_env) <--
        bind_cont2(expr, env, body, extended_env, var, val, more_bindings),
        cons_rel(var, val, env_binding);

    // This is the 'real rule'. Since the signal relations will be distilled out, the second-pass program should contain
    // all the required dependencies.
     bind(expr, env, body, new_env, more_bindings) <--
        bind(expr, env, body, extended_env, bindings),
        cons_rel(binding, more_bindings, bindings),
        cons_rel(var, binding_tail, binding),
        cons_rel(val, end, binding_tail), if end.is_nil(), // TODO: error otherwise
        cons_rel(var, val, env_binding),
        cons_rel(env_binding, extended_env, new_env);

    // If a smart-enough compiler can arrange, it may be more efficient to use the version that depends on the signal
    // relations in the first pass, though.
    //
    //  relation bind_cont3(Ptr, Ptr, Ptr, Ptr, Ptr, Ptr); // (expr, env, body, extended-env, env_binding)
    //
    // // Signal rule
    //  bind_cont3(expr, env, body, extended_env, env_binding, more_bindings),
    //  cons(env_binding, extended_env) <--
    //     bind_cont2(expr, env, body, extended_env, var, val, more_bindings),
    //     cons_rel(var, val, env_binding);

    //  bind(expr, env, body, new_env, more_bindings) <--
    //     bind_cont3(expr, env, body, extended_env, env_binding, more_bindings),
    //     cons_rel(env_binding, extended_env, new_env);

    ////////////////////
    // first-element is not built-in

    ////////////////////
    // lambda

    relation lambda_parse(Ptr, Ptr, Ptr); // (expr, env, args-and-body)

    ingress(tail), lambda_parse(expr, env, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_lambda();

    // // Signal rule
    ingress(rest) <--
        lambda_parse(expr, env, tail),
        cons_rel(args, rest, tail);

    // create a fun from a parsed lambda evaluation
    fun(args, body, env) <--
        lambda_parse(expr, env, tail),
        cons_rel(args, rest, tail),
        cons_rel(body, end, rest), if end.is_nil(); // TODO: otherwise error

    // register a fun created from a lambda expression as its evaluation
    eval(expr, env, fun) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_lambda(),
        //let op = Memory::ptr_sym(*head, *head_value), if op.is_some() && op.unwrap().is_lambda(),
        lambda_parse(expre, env, tail),
        fun(args, body, env),
        fun_rel(args, body, env, fun);

    ////////////////////
    // fold -- default folding is fold_left
    relation fold(Ptr, Ptr, Ptr, Num, Ptr); // (expr, env, op, acc, tail)

    // If head is left-foldable op, reduce it with its neutral element.
    ingress(tail), fold(expr, env, head, head.neutral_element(), tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_left_foldable();
        // let op = Memory::ptr_sym(*head, *head_value), if op.is_some() && op.unwrap().is_left_foldable();

    // When left-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <--
        fold(expr, env, op, _, tail), cons_rel(car, cdr, tail);

    // When left-folding, if car has been evaled and is F, apply the op to it and the acc, then recursively
    // fold acc and new tail.
    ingress(cdr), fold(expr, env, op, op.apply_op(*acc, Num(evaled_car.1)), cdr) <--
        fold(expr, env, op, acc, tail), cons_rel(car, cdr, tail), eval(car, env, evaled_car), if evaled_car.is_f();

    // left-folding operation with an empty (nil) tail
    eval(expr, env, Ptr(Tag::Num.elt(), acc.0)) <-- fold(expr, env, _, acc, tail), if tail.is_nil();

    ////////////////////
    // fold_right

    relation fold_right(Ptr, Ptr, Ptr, Ptr); // (expr, env, op, tail)

    // If head is right-foldable op, initiate fold_right.
    ingress(tail), fold_right(expr, env, head, tail) <--
        eval_input(expr, env), cons_rel(head, tail, expr), ptr_value(head, head_value),
        if head.is_right_foldable();
        //let op = Memory::ptr_sym(*head, *head_value), if op.is_some() && op.unwrap().is_right_foldable();

    // When right-folding with tail that is a cons, ingress its car and cdr, and eval the car.
    eval_input(car, env), ingress(car), ingress(cdr) <-- fold_right(expr, env, op, tail), cons_rel(car, cdr, tail);

    // When right-folding an empty list, return the neutral element.
    eval(expr, env, Ptr(Tag::Num.elt(), op.neutral_element().0)) <-- fold_right(expr, env, op, tail), if tail.is_nil();

    // When right-folding, if tail is a cons (not empty), revert to a (left) fold with evaled car as initial acc.
    ingress(cdr), fold(expr, env, op, Num(evaled_car.1), cdr) <--
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
    use crate::lurk::state::State;

    fn err() -> WidePtr {
        WidePtr(Tag::Err.value(), Wide::widen(LE::from_canonical_u32(0)))
    }

    fn wide_ptr(tag: LE, digest: [LE; 8]) -> WidePtr {
        WidePtr(Wide::widen(tag), Wide(digest))
    }

    fn read_wideptr(src: &str) -> WidePtr {
        let ReadData {
            tag,
            digest,
            hashes,
        } = simple_read(src);

        allocator().import_hashes(hashes);
        wide_ptr(tag, digest)
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

        assert_eq!(vec![(expected_output,)], prog.output_expr);
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
        test_aux("nil", "nil", None);
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
    fn test_let() {
        test_aux("(let ((x 9)) x)", "9", None);
        test_aux("(let ((x 9)(y 10)) x)", "9", None);
        test_aux("(let ((x 9)(y 10)) y)", "10", None);
    }

    #[test]
    fn test_lambda() {
        let args_wide_ptr: WidePtr = read_wideptr("(x)");
        let body_wide_ptr: WidePtr = read_wideptr("(+ x 1)");
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
            parse_fun_call,
            ..
        } = prog;

        ptr_value.sort_by_key(|(key, _)| *key);

        dbg!(
            toplevel_input,
            input_ptr,
            eval_input,
            eval,
            hash4,
            unhash4,
            hash4_rel,
            output_ptr,
            output_expr,
            ptr_value,
            cons,
            cons_rel,
            cons_mem,
            cons_digest_mem,
            alloc,
            ingress,
            egress,
            fun_rel,
            fun_mem,
            fun,
            sym_digest_mem,
            parse_fun_call,
        );
    }
}
