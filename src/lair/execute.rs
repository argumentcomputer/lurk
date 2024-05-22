use std::{collections::BTreeMap, slice::Iter};

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

pub fn mem_index_to_len(idx: usize) -> Option<usize> {
    MEM_TABLE_SIZES.get(idx).copied()
}

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

    pub fn execute_iter(&self, args: List<F>, queries: &mut QueryRecord<F>) {
        let index = self.func.index;
        let toplevel = self.toplevel;
        if queries.query(index, &args).is_none() {
            let out = self.func.execute_iter(&args, toplevel, queries);
            queries.insert_result(index, args, out);
        }
    }
}

type VarMap<F> = Vec<F>;
struct Frame<'a, F> {
    index: usize,
    args: List<F>,
    ops: Iter<'a, Op<F>>,
    ctrl: &'a Ctrl<F>,
    map: VarMap<F>,
}
type Stack<'a, F> = Vec<Frame<'a, F>>;
enum Continuation<F> {
    Return(Vec<F>),
    Apply(usize, Vec<F>),
}

impl<F: PrimeField + Ord> Func<F> {
    fn execute(&self, args: &[F], toplevel: &Toplevel<F>, queries: &mut QueryRecord<F>) -> List<F> {
        let frame = &mut args.into();
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(frame, toplevel, queries)
    }

    pub fn execute_iter(
        &self,
        args: &[F],
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> List<F> {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        let mut map = args.to_vec();
        let mut ops = self.body.ops.iter();
        let mut ctrl = &self.body.ctrl;
        let mut stack = vec![];
        loop {
            let cont = Op::execute_step(ops, ctrl, map, &mut stack, toplevel, queries);
            match cont {
                Continuation::Return(out) => {
                    if let Some(frame) = stack.pop() {
                        ctrl = frame.ctrl;
                        ops = frame.ops;
                        map = frame.map;
                        map.extend(out.iter());
                        queries.insert_result(frame.index, frame.args, out.into());
                    } else {
                        map = out;
                        break;
                    }
                }
                Continuation::Apply(idx, args) => {
                    let func = toplevel.get_by_index(idx).unwrap();
                    map = args;
                    ctrl = &func.body.ctrl;
                    ops = func.body.ops.iter();
                }
            }
        }
        map.into()
    }
}

impl<F: PrimeField + Ord> Block<F> {
    fn execute(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> List<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(map, toplevel, queries));
        self.ctrl.execute(map, toplevel, queries)
    }

    fn execute_step<'a>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> Continuation<F> {
        let ops = self.ops.iter();
        let ctrl = &self.ctrl;
        Op::execute_step(ops, ctrl, map, stack, toplevel, queries)
    }
}

impl<F: PrimeField + Ord> Ctrl<F> {
    fn execute(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> List<F> {
        match self {
            Ctrl::Return(_, vars) => vars.iter().map(|var| map[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = map.get(*b).unwrap();
                if b.is_zero() {
                    f.execute(map, toplevel, queries)
                } else {
                    t.execute(map, toplevel, queries)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute(map, toplevel, queries)
            }
        }
    }

    fn execute_step<'a>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> Continuation<F> {
        match self {
            Ctrl::Return(_, vars) => {
                let out = vars.iter().map(|var| map[*var]).collect();
                Continuation::Return(out)
            }
            Ctrl::If(b, t, f) => {
                let b = map.get(*b).unwrap();
                if b.is_zero() {
                    f.execute_step(map, stack, toplevel, queries)
                } else {
                    t.execute_step(map, stack, toplevel, queries)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute_step(map, stack, toplevel, queries)
            }
        }
    }
}

impl<F: PrimeField + Ord> Op<F> {
    fn execute(&self, map: &mut VarMap<F>, toplevel: &Toplevel<F>, queries: &mut QueryRecord<F>) {
        match self {
            Op::Const(c) => {
                map.push(*c);
            }
            Op::Add(a, b) => {
                let a = map[*a];
                let b = map[*b];
                map.push(a + b);
            }
            Op::Sub(a, b) => {
                let a = map[*a];
                let b = map[*b];
                map.push(a - b);
            }
            Op::Mul(a, b) => {
                let a = map[*a];
                let b = map[*b];
                map.push(a * b);
            }
            Op::Inv(a) => {
                let a = map.get(*a).unwrap();
                map.push(a.inverse());
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| map[*a]).collect();
                let out = queries.record_event_and_return(toplevel, *idx, args);
                map.extend(out.iter());
            }
            Op::Store(inp) => {
                let args = inp.iter().map(|a| map[*a]).collect();
                let ptr = queries.store(args);
                map.push(ptr);
            }
            Op::Load(len, ptr) => {
                let ptr = map.get(*ptr).unwrap();
                let args = queries.load(*len, *ptr);
                map.extend(args);
            }
        }
    }

    fn execute_step<'a>(
        mut ops: Iter<'a, Self>,
        ctrl: &'a Ctrl<F>,
        mut map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F>,
        queries: &mut QueryRecord<F>,
    ) -> Continuation<F> {
        while let Some(op) = ops.next() {
            match op {
                Op::Const(c) => {
                    map.push(*c);
                }
                Op::Add(a, b) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a + b);
                }
                Op::Sub(a, b) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a - b);
                }
                Op::Mul(a, b) => {
                    let a = map[*a];
                    let b = map[*b];
                    map.push(a * b);
                }
                Op::Inv(a) => {
                    let a = map.get(*a).unwrap();
                    map.push(a.inverse());
                }
                Op::Store(inp) => {
                    let args = inp.iter().map(|a| map[*a]).collect();
                    let ptr = queries.store(args);
                    map.push(ptr);
                }
                Op::Load(len, ptr) => {
                    let ptr = map.get(*ptr).unwrap();
                    let args = queries.load(*len, *ptr);
                    map.extend(args);
                }
                Op::Call(index, inp) => {
                    let args = inp.iter().map(|a| map[*a]).collect::<Vec<_>>();
                    if let Some(out) = queries.query(*index, &args) {
                        map.extend(out.iter())
                    } else {
                        stack.push(Frame {
                            index: *index,
                            args: args.clone().into(),
                            ops,
                            ctrl,
                            map,
                        });
                        return Continuation::Apply(*index, args);
                    }
                }
            }
        }
        ctrl.execute_step(map, stack, toplevel, queries)
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
    fn lair_execute_iter_test() {
        let toplevel = demo_toplevel::<_>();

        let fib = toplevel.get_by_name("fib").unwrap();
        let args = &[F::from_canonical_u32(100000)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = fib.execute_iter(args, &toplevel, record);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(309996207));
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
