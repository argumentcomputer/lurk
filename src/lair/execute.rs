use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
};

use p3_field::Field;

impl<F: Field + Ord> Func<F> {
    pub fn execute(&self, args: &mut Vec<F>, toplevel: &Toplevel<F>) -> Vec<F> {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(args, toplevel)
    }
}

impl<F: Field + Ord> Block<F> {
    fn execute(&self, stack: &mut Vec<F>, toplevel: &Toplevel<F>) -> Vec<F> {
        self.ops.iter().for_each(|op| op.execute(stack, toplevel));
        self.ctrl.execute(stack, toplevel)
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn execute(&self, stack: &mut Vec<F>, toplevel: &Toplevel<F>) -> Vec<F> {
        match self {
            Ctrl::Return(vars) => vars.iter().map(|var| stack[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = stack[*b];
                if b.is_zero() {
                    f.execute(stack, toplevel)
                } else {
                    t.execute(stack, toplevel)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = stack[*v];
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute(stack, toplevel)
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn execute(&self, stack: &mut Vec<F>, toplevel: &Toplevel<F>) {
        match self {
            Op::Const(c) => {
                stack.push(*c);
            }
            Op::Add(a, b) => {
                let a = stack[*a];
                let b = stack[*b];
                stack.push(a + b);
            }
            Op::Sub(a, b) => {
                let a = stack[*a];
                let b = stack[*b];
                stack.push(a - b);
            }
            Op::Mul(a, b) => {
                let a = stack[*a];
                let b = stack[*b];
                stack.push(a * b);
            }
            Op::Div(a, b) => {
                let a = stack[*a];
                let b = stack[*b];
                stack.push(a / b);
            }
            Op::Call(idx, inp) => {
                let (_, func) = toplevel.map().get_index(*idx as usize).unwrap();
                let args = &mut inp.iter().map(|a| stack[*a]).collect();
                let out = func.execute(args, toplevel);
                stack.extend(out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{func, lair::toplevel::Toplevel};

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lair_execute_test() {
        let factorial_e = func!(
        fn factorial(n): 1 {
            let one = num(1);
            match n {
                0 => {
                    return one
                }
            };
            let pred = sub(n, one);
            let m = call(factorial, pred);
            let res = mul(n, m);
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

        let toplevel = Toplevel::new(&[even_e, factorial_e, odd_e]);

        let factorial = toplevel.get_func("factorial").unwrap();
        let mut args = vec![F::from_canonical_u32(5)];
        let out = factorial.execute(&mut args, &toplevel);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(120));

        let even = toplevel.get_func("even").unwrap();
        let mut args = vec![F::from_canonical_u32(7)];
        let out = even.execute(&mut args, &toplevel);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));

        let odd = toplevel.get_func("odd").unwrap();
        let mut args = vec![F::from_canonical_u32(7)];
        let out = odd.execute(&mut args, &toplevel);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(1));
    }
}
