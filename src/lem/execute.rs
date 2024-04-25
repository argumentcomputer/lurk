use std::collections::BTreeMap;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
    List,
};

use p3_field::Field;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult<F> {
    output: List<F>,
    multiplicity: usize,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct QueryMap<F>(BTreeMap<List<F>, QueryResult<F>>);

impl<F: Clone + Ord> QueryMap<F> {
    pub fn new() -> Self {
        QueryMap(BTreeMap::new())
    }

    pub fn get(&self, input: &[F]) -> Option<&QueryResult<F>> {
        self.0.get(input)
    }

    pub fn get_mut(&mut self, input: &[F]) -> Option<&mut QueryResult<F>> {
        self.0.get_mut(input)
    }

    #[inline]
    pub fn increase_count(&mut self, input: &[F]) -> bool {
        if let Some(event) = self.get_mut(input) {
            event.multiplicity += 1;
            true
        } else {
            false
        }
    }

    pub fn insert_new(&mut self, input: &[F], output: List<F>) {
        let result = QueryResult {
            output,
            multiplicity: 1,
        };
        assert!(self.0.insert(input.into(), result).is_none());
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F> {
    record: Vec<QueryMap<F>>,
}

impl<F: Field + Ord> QueryRecord<F> {
    pub fn new(toplevel: &Toplevel<F>) -> Self {
        let record = (0..toplevel.size()).map(|_| QueryMap::new()).collect();
        Self { record }
    }

    pub fn record(&self) -> &Vec<QueryMap<F>> {
        &self.record
    }

    pub fn record_event(&mut self, toplevel: &Toplevel<F>, func_idx: usize, args: &mut Vec<F>) {
        let (_, func) = toplevel.map().get_index(func_idx).unwrap();
        if !self.record[func_idx].increase_count(args) {
            let out = func.execute(args, toplevel, self);
            self.record[func_idx].insert_new(args, out.into());
        }
    }
}

impl<F: Field + Ord> Func<F> {
    pub fn execute(
        &self,
        args: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> Vec<F> {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(args, toplevel, record)
    }
}

impl<F: Field + Ord> Block<F> {
    fn execute(
        &self,
        stack: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> Vec<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(stack, toplevel, record));
        self.ctrl.execute(stack, toplevel, record)
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn execute(
        &self,
        stack: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> Vec<F> {
        match self {
            Ctrl::Return(vars) => vars.iter().map(|var| stack[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = stack[*b];
                if b.is_zero() {
                    f.execute(stack, toplevel, record)
                } else {
                    t.execute(stack, toplevel, record)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = stack[*v];
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute(stack, toplevel, record)
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn execute(&self, stack: &mut Vec<F>, toplevel: &Toplevel<F>, record: &mut QueryRecord<F>) {
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
                let out = func.execute(args, toplevel, record);
                stack.extend(out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lem::{execute::QueryRecord, toplevel::Toplevel, Name},
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lem_execute_test() {
        let factorial = func!(
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
        let even = func!(
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
        let odd = func!(
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
        let toplevel = Toplevel::new(&[even, factorial, odd]);

        let factorial = toplevel.map().get(&Name("factorial")).unwrap();
        let mut args = vec![F::from_canonical_u32(5)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = factorial.execute(&mut args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(120));

        let even = toplevel.map().get(&Name("even")).unwrap();
        let mut args = vec![F::from_canonical_u32(7)];
        let out = even.execute(&mut args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));

        let odd = toplevel.map().get(&Name("odd")).unwrap();
        let mut args = vec![F::from_canonical_u32(7)];
        let out = odd.execute(&mut args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(1));
    }
}
