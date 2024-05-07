use std::collections::{btree_map::Iter, BTreeMap};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chip::FuncChip,
    toplevel::Toplevel,
    List,
};

use p3_field::Field;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult<F> {
    pub(crate) output: List<F>,
    pub(crate) mult: u32,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct QueryMap<F>(pub(crate) BTreeMap<List<F>, QueryResult<F>>);

impl<F> QueryMap<F> {
    #[inline]
    pub fn new() -> Self {
        QueryMap(BTreeMap::new())
    }

    #[inline]
    pub fn size(&self) -> usize {
        self.0.len()
    }
}

impl<F: Clone + Ord> QueryMap<F> {
    #[inline]
    pub fn query(&mut self, input: &[F]) -> Option<List<F>> {
        if let Some(event) = self.0.get_mut(input) {
            event.mult += 1;
            Some(event.output.clone())
        } else {
            None
        }
    }

    pub fn insert_result(&mut self, input: List<F>, output: List<F>) {
        let result = QueryResult { output, mult: 1 };
        assert!(self.0.insert(input, result).is_none());
    }

    pub fn iter(&self) -> Iter<'_, List<F>, QueryResult<F>> {
        self.0.iter()
    }

    pub fn get(&self, args: &List<F>) -> Option<&QueryResult<F>> {
        self.0.get(args)
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

impl<'a, F: Field + Ord> FuncChip<'a, F> {
    pub fn execute(&self, args: List<F>, queries: &mut QueryRecord<F>) {
        let index = self.func.index;
        let toplevel = self.toplevel;
        if queries.record[index].query(&args).is_none() {
            let out = self.func.execute(&args, toplevel, queries);
            queries.record[index].insert_result(args, out);
        }
    }
}

impl<F: Field + Ord> QueryRecord<F> {
    fn record_event_and_return(
        &mut self,
        toplevel: &Toplevel<F>,
        func_idx: usize,
        args: List<F>,
    ) -> List<F> {
        let func = toplevel.get_by_index(func_idx).unwrap();
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
    fn execute(&self, args: &[F], toplevel: &Toplevel<F>, record: &mut QueryRecord<F>) -> List<F> {
        let frame = &mut args.into();
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(frame, toplevel, record)
    }
}

impl<F: Field + Ord> Block<F> {
    fn execute(
        &self,
        frame: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(frame, toplevel, record));
        self.ctrl.execute(frame, toplevel, record)
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn execute(
        &self,
        frame: &mut Vec<F>,
        toplevel: &Toplevel<F>,
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        match self {
            Ctrl::Return(_, vars) => vars.iter().map(|var| frame[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = frame.get(*b).unwrap();
                if b.is_zero() {
                    f.execute(frame, toplevel, record)
                } else {
                    t.execute(frame, toplevel, record)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = frame.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute(frame, toplevel, record)
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn execute(&self, frame: &mut Vec<F>, toplevel: &Toplevel<F>, record: &mut QueryRecord<F>) {
        match self {
            Op::Const(c) => {
                frame.push(*c);
            }
            Op::Add(a, b) => {
                let a = frame[*a];
                let b = frame[*b];
                frame.push(a + b);
            }
            Op::Sub(a, b) => {
                let a = frame[*a];
                let b = frame[*b];
                frame.push(a - b);
            }
            Op::Mul(a, b) => {
                let a = frame[*a];
                let b = frame[*b];
                frame.push(a * b);
            }
            Op::Inv(a) => {
                let a = frame.get(*a).unwrap();
                frame.push(a.inverse());
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| frame[*a]).collect();
                let out = record.record_event_and_return(toplevel, *idx as usize, args);
                frame.extend(out.iter());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lair::{demo_toplevel, execute::QueryRecord, toplevel::Toplevel},
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lair_execute_test() {
        let toplevel = demo_toplevel::<_>();

        let factorial = toplevel.get_by_name("factorial").unwrap();
        let args = &[F::from_canonical_u32(5)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = factorial.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(120));

        let even = toplevel.get_by_name("even").unwrap();
        let args = &[F::from_canonical_u32(7)];
        let out = even.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));

        let odd = toplevel.get_by_name("odd").unwrap();
        let args = &[F::from_canonical_u32(4)];
        let out = odd.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));
    }

    #[test]
    fn lair_div_test() {
        let test_e = func!(
            fn test(a, b): 1 {
                let n = div(a, b);
                return n
            }
        );
        let toplevel = Toplevel::new(&[test_e]);
        let test = toplevel.get_by_name("test").unwrap();
        let args = &[F::from_canonical_u32(20), F::from_canonical_u32(4)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(5));
    }

    #[test]
    fn lair_shadow_test() {
        let test_e = func!(
            fn test(x): 1 {
                let x = add(x, x);
                let x = add(x, x);
                let x = add(x, x);
                return x
            }
        );
        let toplevel = Toplevel::new(&[test_e]);
        let test = toplevel.get_by_name("test").unwrap();
        let args = &[F::from_canonical_u32(10)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(80));
    }
}
