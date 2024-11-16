use p3_field::AbstractField;

use crate::{func, lair::expr::FuncE};

// This coroutine is used specifically to create commitments. If we ever need
// the `hasher3` gadget to ingress/egress data, we should define a new `hash3`
// coroutine so the data doesn't get mixed up. We need this separation so API
// consumers (such as the REPL) can have precise information about what's been
// committed to so far.
pub fn commit<F>() -> FuncE<F> {
    func!(
        invertible fn commit(preimg: [24]): [8] {
            let img: [8] = extern_call(hasher3, preimg);
            return img
        }
    )
}

pub fn hash4<F>() -> FuncE<F> {
    func!(
        invertible fn hash4(preimg: [32]): [8] {
            let img: [8] = extern_call(hasher4, preimg);
            return img
        }
    )
}

pub fn hash5<F>() -> FuncE<F> {
    func!(
        invertible fn hash5(preimg: [40]): [8] {
            let img: [8] = extern_call(hasher5, preimg);
            return img
        }
    )
}

pub fn u64_add<F>() -> FuncE<F> {
    func!(
        fn u64_add(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_add, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_sub<F>() -> FuncE<F> {
    func!(
        fn u64_sub(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_sub, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_mul<F>() -> FuncE<F> {
    func!(
        fn u64_mul(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(u64_mul, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn u64_divrem<F>() -> FuncE<F> {
    func!(
        fn u64_divrem(a, b): [2] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (q: [8], r: [8]) = extern_call(u64_divrem, a, b);
            let q = store(q);
            let r = store(r);
            return (q, r)
        }
    )
}

pub fn u64_lessthan<F>() -> FuncE<F> {
    func!(
        fn u64_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c = extern_call(u64_lessthan, a, b);
            return c
        }
    )
}

pub fn u64_iszero<F>() -> FuncE<F> {
    func!(
        fn u64_iszero(a): [1] {
            let a: [8] = load(a);
            // this is slightly cheaper than doing it in Lair itself
            let b = extern_call(u64_iszero, a);
            return b
        }
    )
}

pub fn digest_equal<F: AbstractField>() -> FuncE<F> {
    func!(
        fn digest_equal(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let diff = sub(a, b);
            if diff {
                let zero = 0;
                return zero
            }
            let one = 1;
            return one
        }
    )
}

pub fn big_num_lessthan<F>() -> FuncE<F> {
    func!(
        fn big_num_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c = extern_call(big_num_lessthan, a, b);
            return c
        }
    )
}
