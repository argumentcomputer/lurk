use p3_field::AbstractField;

use crate::{func, lair::expr::FuncE};

// hash functions

pub fn hash3<F>() -> FuncE<F> {
    func!(
        invertible fn hash3(preimg: [24]): [8] {
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

// u64 functions

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

// i64 functions

pub fn i64_divrem<F: AbstractField>() -> FuncE<F> {
    func!(
        fn i64_divrem(a, b): [2] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (a_is_neg, a_abs: [8]) = extern_call(i64_into_sign_abs, a);
            let (b_is_neg, b_abs: [8]) = extern_call(i64_into_sign_abs, b);
            let (q: [8], r: [8]) = extern_call(u64_divrem, a_abs, b_abs);
            let different_signs = sub(a_is_neg, b_is_neg);
            if different_signs {
                let q_is_neg = 1;
                let q: [8] = extern_call(i64_from_sign_abs, q_is_neg, q);
                let q = store(q);
                let r = store(r);
                return (q, r)
            }
            let q_is_neg = 0;
            let q: [8] = extern_call(i64_from_sign_abs, q_is_neg, q);
            let q = store(q);
            let r = store(r);
            return (q, r)
        }
    )
}

pub fn i64_lessthan<F>() -> FuncE<F> {
    func!(
        fn i64_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (a_is_neg, a_abs: [8]) = extern_call(i64_into_sign_abs, a);
            let (b_is_neg, b_abs: [8]) = extern_call(i64_into_sign_abs, b);
            if a_is_neg {
                if b_is_neg {
                    // both negative
                    let c = extern_call(u64_lessthan, b_abs, a_abs);
                    return c
                }
                return a_is_neg // return true
            }
            if b_is_neg {
                return a_is_neg // return false
            }
            // both positive
            let c = extern_call(u64_lessthan, a_abs, b_abs);
            return c
        }
    )
}

// i63 functions

pub fn i63_add<F>() -> FuncE<F> {
    func!(
        fn i63_add(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(i63_add, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn i63_sub<F>() -> FuncE<F> {
    func!(
        fn i63_sub(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(i63_sub, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn i63_mul<F>() -> FuncE<F> {
    func!(
        fn i63_mul(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let c: [8] = extern_call(i63_mul, a, b);
            let c = store(c);
            return c
        }
    )
}

pub fn i63_divrem<F: AbstractField>() -> FuncE<F> {
    func!(
        fn i63_divrem(a, b): [2] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (a_is_neg, a_abs: [8]) = extern_call(i63_into_sign_abs, a);
            let (b_is_neg, b_abs: [8]) = extern_call(i63_into_sign_abs, b);
            let (q: [8], r: [8]) = extern_call(u64_divrem, a_abs, b_abs);
            let different_signs = sub(a_is_neg, b_is_neg);
            if different_signs {
                let q_is_neg = 1;
                let q: [8] = extern_call(i63_from_sign_abs, q_is_neg, q);
                let q = store(q);
                let r = store(r);
                return (q, r)
            }
            let q_is_neg = 0;
            let q: [8] = extern_call(i63_from_sign_abs, q_is_neg, q);
            let q = store(q);
            let r = store(r);
            return (q, r)
        }
    )
}

pub fn i63_lessthan<F>() -> FuncE<F> {
    func!(
        fn i63_lessthan(a, b): [1] {
            let a: [8] = load(a);
            let b: [8] = load(b);
            let (a_is_neg, a_abs: [8]) = extern_call(i63_into_sign_abs, a);
            let (b_is_neg, b_abs: [8]) = extern_call(i63_into_sign_abs, b);
            if a_is_neg {
                if b_is_neg {
                    // both negative
                    let c = extern_call(u64_lessthan, b_abs, a_abs);
                    return c
                }
                return a_is_neg // return true
            }
            if b_is_neg {
                return a_is_neg // return false
            }
            // both positive
            let c = extern_call(u64_lessthan, a_abs, b_abs);
            return c
        }
    )
}

// other

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
