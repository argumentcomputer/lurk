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
                let (_, func) = toplevel.map().get_index(*idx).unwrap();
                let args = &mut inp.iter().map(|a| stack[*a]).collect();
                let out = func.execute(args, toplevel);
                stack.extend(out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lair::{expr::*, toplevel::Toplevel, Name};

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lair_execute_test() {
        let ops = vec![
            OpE::Add(Var("d"), Var("a"), Var("b")),
            OpE::Mul(Var("x"), Var("c"), Var("d")),
        ];
        let ctrl = CtrlE::Return(vec![Var("x")]);
        let body = BlockE { ops, ctrl };
        let name = Name("test");
        let func = FuncE::<F> {
            name,
            body,
            input_params: vec![Var("a"), Var("b"), Var("c")],
            output_size: 1,
        };
        let mut args = (2..=4).map(F::from_canonical_u32).collect();
        let toplevel = Toplevel::new(&[func]);
        let func = toplevel.map().get(&name).unwrap();
        let out = func.execute(&mut args, &toplevel);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(20));
    }
}
