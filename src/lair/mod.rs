use p3_field::Field;

use crate::func;

use self::toplevel::Toplevel;

pub mod air;
pub mod bytecode;
pub mod chip;
pub mod execute;
pub mod expr;
mod macros;
pub mod map;
pub mod memory;
mod pointer;
pub mod toplevel;
pub mod trace;

#[derive(Copy, Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct Name(pub &'static str);

impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[inline]
#[allow(dead_code)]
pub(crate) fn field_from_u32<F: p3_field::AbstractField>(i: u32) -> F {
    F::from_canonical_u32(i)
}

#[inline]
#[allow(dead_code)]
pub(crate) fn field_from_i32<F: p3_field::AbstractField>(i: i32) -> F {
    if i < 0 {
        -F::from_canonical_u32((-i).try_into().unwrap())
    } else {
        F::from_canonical_u32(i.try_into().unwrap())
    }
}

pub type List<T> = Box<[T]>;

#[allow(dead_code)]
pub(crate) fn demo_toplevel<F: Field + Ord>() -> Toplevel<F> {
    let factorial_e = func!(
    fn factorial(n): 1 {
        let one = num(1);
        if n {
            let pred = sub(n, one);
            let m = call(factorial, pred);
            let res = mul(n, m);
            return res
        }
        return one
    });
    let fib_e = func!(
    fn fib(n): 1 {
        let one = num(1);
        match n {
            0 => {
                return one
            }
            1 => {
                return one
            }
        };
        let n_1 = sub(n, one);
        let a = call(fib, n_1);
        let n_2 = sub(n_1, one);
        let b = call(fib, n_2);
        let res = add(a, b);
        return res
    });
    let even_e = func!(
    fn even(n): 1 {
        let one = num(1);
        match n {
            0 => {
                return one
            }
        };
        let pred = sub(n, one);
        let res = call(odd, pred);
        return res
    });

    let odd_e = func!(
    fn odd(n): 1 {
        let one = num(1);
        match n {
            0 => {
                let zero = num(0);
                return zero
            }
        };
        let pred = sub(n, one);
        let res = call(even, pred);
        return res
    });

    Toplevel::<F>::new(&[factorial_e, fib_e, even_e, odd_e])
}
