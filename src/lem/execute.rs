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

impl<F> QueryMap<F> {
    #[inline]
    pub fn new() -> Self {
        QueryMap(BTreeMap::new())
    }
}

impl<F: Clone + Ord> QueryMap<F> {
    #[inline]
    pub fn query(&mut self, input: &[F]) -> Option<List<F>> {
        if let Some(event) = self.0.get_mut(input) {
            event.multiplicity += 1;
            Some(event.output.clone())
        } else {
            None
        }
    }

    pub fn insert_result(&mut self, input: List<F>, output: List<F>) {
        let result = QueryResult {
            output,
            multiplicity: 1,
        };
        assert!(self.0.insert(input, result).is_none());
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F> {
    record: Vec<QueryMap<F>>,
}

impl<F: Clone> QueryRecord<F> {
    #[inline]
    pub fn new(toplevel: &Toplevel<F>) -> Self {
        Self {
            record: vec![QueryMap::new(); toplevel.size()],
        }
    }
}

impl<F> QueryRecord<F> {
    #[inline]
    pub fn record(&self) -> &Vec<QueryMap<F>> {
        &self.record
    }
}

impl<F: Field + Ord> QueryRecord<F> {
    pub fn record_event(
        &mut self,
        toplevel: &Toplevel<F>,
        func_idx: usize,
        args: List<F>,
    ) -> List<F> {
        let (_, func) = toplevel.map().get_index(func_idx).unwrap();
        if let Some(out) = self.record[func_idx].query(&args) {
            out
        } else {
            let out = func.execute(&args, toplevel, self);
            self.record[func_idx].insert_result(args, out.clone());
            out
        }
    }
}

impl<F: Field + Ord> Func<F> {
    pub fn execute(
        &self,
        args: &[F],
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        let stack_frame = &mut args.into();
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(stack_frame, toplevel, record)
    }
}

impl<F: Field + Ord> Block<F> {
    fn execute(
        &self,
        stack_frame: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(stack_frame, toplevel, record));
        self.ctrl.execute(stack_frame, toplevel, record)
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn execute(
        &self,
        stack_frame: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        match self {
            Ctrl::Return(vars) => vars.iter().map(|var| stack_frame[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = stack_frame[*b];
                if b.is_zero() {
                    f.execute(stack_frame, toplevel, record)
                } else {
                    t.execute(stack_frame, toplevel, record)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = stack_frame[*v];
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute(stack_frame, toplevel, record)
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn execute(
        &self,
        stack_frame: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) {
        match self {
            Op::Const(c) => {
                stack_frame.push(*c);
            }
            Op::Add(a, b) => {
                let a = stack_frame[*a];
                let b = stack_frame[*b];
                stack_frame.push(a + b);
            }
            Op::Sub(a, b) => {
                let a = stack_frame[*a];
                let b = stack_frame[*b];
                stack_frame.push(a - b);
            }
            Op::Mul(a, b) => {
                let a = stack_frame[*a];
                let b = stack_frame[*b];
                stack_frame.push(a * b);
            }
            Op::Div(a, b) => {
                let a = stack_frame[*a];
                let b = stack_frame[*b];
                stack_frame.push(a / b);
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| stack_frame[*a]).collect();
                let out = record.record_event(toplevel, *idx as usize, args);
                stack_frame.extend(out.iter());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lem::{execute::QueryRecord, toplevel::Toplevel},
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lem_execute_test() {
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
        let args = &[F::from_canonical_u32(5)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = factorial.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(120));

        let even = toplevel.get_func("even").unwrap();
        let args = &[F::from_canonical_u32(7)];
        let out = even.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));

        let odd = toplevel.get_func("odd").unwrap();
        let args = &[F::from_canonical_u32(4)];
        let out = odd.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));
    }
}
