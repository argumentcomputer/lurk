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
pub(crate) type InvQueryMap<F> = BTreeMap<List<F>, List<F>>;
pub(crate) type MemMap<F> = IndexMap<List<F>, u32>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F: PrimeField> {
    pub(crate) func_queries: Vec<QueryMap<F>>,
    pub(crate) inv_func_queries: Vec<Option<InvQueryMap<F>>>,
    pub(crate) mem_queries: Vec<MemMap<F>>,
}

const NUM_MEM_TABLES: usize = 5;
const MEM_TABLE_SIZES: [usize; NUM_MEM_TABLES] = [3, 4, 5, 6, 8];

pub fn mem_index_to_len(idx: usize) -> Option<usize> {
    MEM_TABLE_SIZES.get(idx).copied()
}

pub fn mem_index_from_len(len: usize) -> Option<usize> {
    MEM_TABLE_SIZES.iter().position(|&i| len == i)
}

pub fn mem_init<F: Clone>() -> Vec<MemMap<F>> {
    vec![IndexMap::new(); NUM_MEM_TABLES]
}

pub fn mem_store<F: PrimeField + Ord>(mem: &mut [MemMap<F>], args: List<F>) -> F {
    let len = args.len();
    let idx = mem_index_from_len(len)
        .unwrap_or_else(|| panic!("There are no mem tables of size {}", len));
    if let Some((i, _, mult)) = mem[idx].get_full_mut(&args) {
        *mult += 1;
        F::from_canonical_usize(i + 1)
    } else {
        let (i, _) = mem[idx].insert_full(args, 1);
        F::from_canonical_usize(i + 1)
    }
}

pub fn mem_load<F: PrimeField + Ord>(mem: &mut [MemMap<F>], len: usize, ptr: F) -> &[F] {
    let ptr_f: usize = ptr
        .as_canonical_biguint()
        .try_into()
        .expect("Field element is too big for a pointer");
    let idx = mem_index_from_len(len)
        .unwrap_or_else(|| panic!("There are no mem tables of size {}", len));
    let (args, mult) = mem[idx].get_index_mut(ptr_f - 1).expect("Unbound pointer");
    *mult += 1;
    args
}

impl<F: PrimeField + Ord> QueryRecord<F> {
    #[inline]
    pub fn new(toplevel: &Toplevel<F>) -> Self {
        Self::new_with_init_mem(toplevel, mem_init())
    }

    #[inline]
    pub fn new_with_init_mem(toplevel: &Toplevel<F>, mem_queries: Vec<MemMap<F>>) -> Self {
        let func_queries = vec![BTreeMap::new(); toplevel.size()];
        let inv_func_queries = toplevel
            .map
            .iter()
            .map(|(_, func)| {
                if func.invertible {
                    Some(BTreeMap::new())
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(mem_queries.len(), NUM_MEM_TABLES);
        Self {
            func_queries,
            inv_func_queries,
            mem_queries,
        }
    }
    #[inline]
    pub fn func_queries(&self) -> &Vec<QueryMap<F>> {
        &self.func_queries
    }

    pub fn query(&mut self, index: usize, input: &[F]) -> Option<&List<F>> {
        if let Some(event) = self.func_queries[index].get_mut(input) {
            event.mult += 1;
            Some(&event.output)
        } else {
            None
        }
    }

    pub fn query_preimage(&mut self, index: usize, input: &[F]) -> Option<&List<F>> {
        let output = self.inv_func_queries[index].as_ref()?.get(input)?;
        let event = self.func_queries[index].get_mut(output)?;
        event.mult += 1;
        Some(output)
    }

    pub fn insert_result(&mut self, index: usize, input: List<F>, output: List<F>) {
        if let Some(queries) = &mut self.inv_func_queries[index] {
            queries.insert(output.clone(), input.clone());
        }
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
            out.clone()
        } else {
            let out = func.execute(&args, toplevel, self);
            self.insert_result(func_idx, args, out.clone());
            out
        }
    }

    pub fn store(&mut self, args: List<F>) -> F {
        mem_store(&mut self.mem_queries, args)
    }

    pub fn load(&mut self, len: usize, ptr: F) -> &[F] {
        mem_load(&mut self.mem_queries, len, ptr)
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
            Op::Not(a) => {
                let a = map.get(*a).unwrap();
                let b = if a.is_zero() { F::one() } else { F::zero() };
                map.push(b);
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| map[*a]).collect();
                let out = queries.record_event_and_return(toplevel, *idx, args);
                map.extend(out.iter());
            }
            Op::PreImg(idx, inp) => {
                let args = inp.iter().map(|a| map[*a]).collect::<List<_>>();
                let out = queries
                    .query_preimage(*idx, &args)
                    .expect("Cannot find preimg");
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
            Op::Debug(s) => println!("{}", s),
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
                Op::Not(a) => {
                    let a = map.get(*a).unwrap();
                    let b = if a.is_zero() { F::one() } else { F::zero() };
                    map.push(b);
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
                Op::Debug(s) => println!("{}", s),
                Op::PreImg(idx, inp) => {
                    let args = inp.iter().map(|a| map[*a]).collect::<List<_>>();
                    let out = queries
                        .query_preimage(*idx, &args)
                        .expect("Cannot find preimg");
                    map.extend(out.iter());
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
        lair::{demo_toplevel, execute::QueryRecord, field_from_u32, toplevel::Toplevel, List},
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

    #[test]
    fn lair_preimg_test() {
        let polynomial_e = func!(
            invertible fn polynomial(a0, a1, a2, a3, x): 1 {
                // a2 + a3*x
                let coef = mul(a3, x);
                let res = add(a2, coef);
                // a1 + a2*x + a3*x^2
                let coef = mul(res, x);
                let res = add(a1, coef);
                // a0 + a1*x + a2*x^2 + a3*x^3
                let coef = mul(res, x);
                let res = add(a0, coef);
                return res
            }
        );
        let inverse_e = func!(
            fn inverse(y): 5 {
                let (a0, a1, a2, a3, x) = preimg(polynomial, y);
                return (a0, a1, a2, a3, x)
            }
        );
        let toplevel = Toplevel::<F>::new(&[polynomial_e, inverse_e]);
        let polynomial = toplevel.get_by_name("polynomial").unwrap();
        let inverse = toplevel.get_by_name("inverse").unwrap();
        let args = [1, 3, 5, 7, 20]
            .into_iter()
            .map(field_from_u32)
            .collect::<List<_>>();
        let record = &mut QueryRecord::new(&toplevel);
        let out = record.record_event_and_return(&toplevel, polynomial.index, args.clone());
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(58061));
        let inp = inverse.execute(&out, &toplevel, record);
        assert_eq!(inp.len(), 5);
        let expect_inp = args;
        assert_eq!(inp, expect_inp);
    }
}
