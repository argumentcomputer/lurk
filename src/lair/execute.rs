use std::collections::BTreeMap;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chip::FuncChip,
    toplevel::Toplevel,
    List,
};

use indexmap::IndexMap;
use p3_field::PrimeField;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult<T> {
    pub(crate) output: T,
    pub(crate) mult: u32,
}

pub(crate) type QueryMap<F> = BTreeMap<List<F>, QueryResult<List<F>>>;
pub(crate) type MemMap<F> = IndexMap<List<F>, u32>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F: PrimeField> {
    pub(crate) func_queries: Vec<QueryMap<F>>,
    pub(crate) mem_queries: Vec<MemMap<F>>,
}

const NUM_MEM_TABLES: usize = 4;
const MEM_TABLE_SIZES: [usize; NUM_MEM_TABLES] = [3, 4, 6, 8];

pub fn mem_index_from_len(len: usize) -> Option<usize> {
    MEM_TABLE_SIZES.iter().position(|&i| len == i)
}

impl<F: PrimeField + Ord> QueryRecord<F> {
    #[inline]
    pub fn new(toplevel: &Toplevel<F>) -> Self {
        Self {
            func_queries: vec![BTreeMap::new(); toplevel.size()],
            mem_queries: vec![IndexMap::new(); NUM_MEM_TABLES],
        }
    }

    #[inline]
    pub fn func_queries(&self) -> &Vec<QueryMap<F>> {
        &self.func_queries
    }

    pub fn query(&mut self, index: usize, input: &[F]) -> Option<List<F>> {
        if let Some(event) = self.func_queries[index].get_mut(input) {
            event.mult += 1;
            Some(event.output.clone())
        } else {
            None
        }
    }

    pub fn insert_result(&mut self, index: usize, input: List<F>, output: List<F>) {
        let result = QueryResult { output, mult: 1 };
        assert!(self.func_queries[index].insert(input, result).is_none());
    }

    fn record_event_and_return(
        &mut self,
        toplevel: &Toplevel<F>,
        func_idx: usize,
        args: List<F>,
    ) -> List<F> {
        let func = toplevel.get_by_index(func_idx).unwrap();
        if let Some(out) = self.query(func_idx, &args) {
            out
        } else {
            let out = func.execute(&args, toplevel, self);
            self.insert_result(func_idx, args, out.clone());
            out
        }
    }

    fn store(&mut self, args: List<F>) -> F {
        let len = args.len();
        let idx = mem_index_from_len(len)
            .unwrap_or_else(|| panic!("There are no mem tables of size {}", len));
        if let Some((ptr, _, mult)) = self.mem_queries[idx].get_full_mut(&args) {
            *mult += 1;
            F::from_canonical_usize(ptr)
        } else {
            let (ptr, _) = self.mem_queries[idx].insert_full(args, 1);
            F::from_canonical_usize(ptr)
        }
    }

    fn load(&mut self, len: usize, ptr: F) -> &[F] {
        let ptr_f: usize = ptr
            .as_canonical_biguint()
            .try_into()
            .expect("Field element is too big for a pointer");
        let idx = mem_index_from_len(len)
            .unwrap_or_else(|| panic!("There are no mem tables of size {}", len));
        let (args, mult) = self.mem_queries[idx]
            .get_index_mut(ptr_f)
            .expect("Unbound pointer");
        *mult += 1;
        args
    }
}

impl<'a, F: PrimeField + Ord> FuncChip<'a, F> {
    pub fn execute(&self, args: List<F>, queries: &mut QueryRecord<F>) {
        let index = self.func.index;
        let toplevel = self.toplevel;
        if queries.query(index, &args).is_none() {
            let out = self.func.execute(&args, toplevel, queries);
            queries.insert_result(index, args, out);
        }
    }
}

impl<F: PrimeField + Ord> Func<F> {
    fn execute(&self, args: &[F], toplevel: &Toplevel<F>, record: &mut QueryRecord<F>) -> List<F> {
        let frame = &mut args.into();
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(frame, toplevel, record)
    }
}

impl<F: PrimeField + Ord> Block<F> {
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

impl<F: PrimeField + Ord> Ctrl<F> {
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

impl<F: PrimeField + Ord> Op<F> {
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
                let out = record.record_event_and_return(toplevel, *idx, args);
                frame.extend(out.iter());
            }
            Op::Store(inp) => {
                let args = inp.iter().map(|a| frame[*a]).collect();
                let ptr = record.store(args);
                frame.push(ptr);
            }
            Op::Load(len, ptr) => {
                let ptr = frame.get(*ptr).unwrap();
                let args = record.load(*len, *ptr);
                frame.extend(args);
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
