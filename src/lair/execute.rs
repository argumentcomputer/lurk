use fxhash::FxBuildHasher;
use indexmap::IndexMap;
use p3_field::{AbstractField, Field, PrimeField};
use sphinx_core::air::MachineProgram;
use sphinx_core::stark::MachineRecord;
use std::collections::HashMap;
use std::slice::Iter;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chip::FuncChip,
    hasher::Hasher,
    toplevel::Toplevel,
    List,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult<T> {
    pub(crate) output: T,
    pub(crate) mult: u32,
}

impl<T> QueryResult<T> {
    fn init(output: T) -> Self {
        Self { output, mult: 0 }
    }
}

pub(crate) type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub(crate) type QueryMap<F> = FxIndexMap<List<F>, QueryResult<List<F>>>;
pub(crate) type InvQueryMap<F> = FxIndexMap<List<F>, List<F>>;
pub(crate) type MemMap<F> = FxIndexMap<List<F>, u32>;

#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F: Field> {
    pub(crate) func_queries: Vec<QueryMap<F>>,
    pub(crate) inv_func_queries: Vec<Option<InvQueryMap<F>>>,
    pub mem_queries: Vec<MemMap<F>>,
}

impl<F: Field> MachineProgram<F> for QueryRecord<F> {
    fn pc_start(&self) -> F {
        F::zero()
    }
}

impl<F: Field> MachineRecord for QueryRecord<F> {
    type Config = ();

    fn index(&self) -> u32 {
        0
    }

    fn set_index(&mut self, _index: u32) {}

    fn stats(&self) -> HashMap<String, usize> {
        Default::default()
    }

    fn append(&mut self, _other: &mut Self) {}

    fn shard(self, _config: &Self::Config) -> Vec<Self> {
        vec![]
    }

    fn public_values<F2: AbstractField>(&self) -> Vec<F2> {
        vec![]
    }
}

const NUM_MEM_TABLES: usize = 5;
const MEM_TABLE_SIZES: [usize; NUM_MEM_TABLES] = [3, 4, 5, 6, 8];

#[inline]
pub fn mem_index_to_len(idx: usize) -> usize {
    MEM_TABLE_SIZES[idx]
}

#[inline]
pub fn mem_index_from_len(len: usize) -> usize {
    MEM_TABLE_SIZES
        .iter()
        .position(|&i| len == i)
        .unwrap_or_else(|| panic!("There are no mem tables of size {}", len))
}

#[inline]
pub fn mem_init<F: Clone>() -> Vec<MemMap<F>> {
    vec![FxIndexMap::default(); NUM_MEM_TABLES]
}

pub fn mem_store<F: Field>(mem: &mut [MemMap<F>], args: List<F>) -> F {
    let len = args.len();
    let mem_idx = mem_index_from_len(len);
    let mem_map_idx = if let Some((i, _, mult)) = mem[mem_idx].get_full_mut(&args) {
        *mult += 1;
        i
    } else {
        mem[mem_idx].insert_full(args, 1).0
    };
    F::from_canonical_usize(mem_map_idx + 1)
}

pub fn mem_load<F: PrimeField>(mem: &mut [MemMap<F>], len: usize, ptr: F) -> &[F] {
    let ptr_f: usize = ptr
        .as_canonical_biguint()
        .try_into()
        .expect("Field element is too big for a pointer");
    let mem_idx = mem_index_from_len(len);
    let (args, mult) = mem[mem_idx]
        .get_index_mut(ptr_f - 1)
        .expect("Unbound pointer");
    *mult += 1;
    args
}

impl<F: Field> QueryRecord<F> {
    #[inline]
    pub fn new<H: Hasher<F>>(toplevel: &Toplevel<F, H>) -> Self {
        Self::new_with_init_mem(toplevel, mem_init())
    }

    #[inline]
    pub fn new_with_init_mem<H: Hasher<F>>(
        toplevel: &Toplevel<F, H>,
        mem_queries: Vec<MemMap<F>>,
    ) -> Self {
        let func_queries = vec![FxIndexMap::default(); toplevel.size()];
        let inv_func_queries = toplevel
            .map
            .iter()
            .map(|(_, func)| {
                if func.invertible {
                    Some(FxIndexMap::default())
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

    /// Injects new queries for a function referenced by name. If a query is already present, do nothing.
    /// Otherwise, add it with multiplicity zero. Further, if the function is invertible, add the query
    /// to its `inv_func_queries` as well.
    pub fn inject_queries<
        I: Into<List<F>>,
        O: Into<List<F>>,
        T: IntoIterator<Item = (I, O)>,
        H: Hasher<F>,
    >(
        &mut self,
        name: &'static str,
        toplevel: &Toplevel<F, H>,
        new_queries_data: T,
    ) {
        let func = toplevel.get_by_name(name).expect("Unknown Func");
        for (inp, out) in new_queries_data {
            let (inp, out) = (inp.into(), out.into());
            let queries = &mut self.func_queries[func.index];
            if !queries.contains_key(&inp) {
                if func.invertible {
                    self.inv_func_queries[func.index]
                        .as_mut()
                        .expect("Inverse query map not found")
                        .insert(out.clone(), inp.clone());
                }
                queries.insert(inp, QueryResult::init(out));
            }
        }
    }

    /// Resets all multiplicities to zero
    pub fn reset_multiplicities(&mut self) {
        self.func_queries.iter_mut().for_each(|query_map| {
            query_map.iter_mut().for_each(|(_, r)| r.mult = 0);
        });
        self.mem_queries.iter_mut().for_each(|mem_map| {
            mem_map.iter_mut().for_each(|(_, mult)| *mult = 0);
        });
    }
}

impl<F: Field + Ord> QueryRecord<F> {
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

    pub fn store(&mut self, args: List<F>) -> F {
        mem_store(&mut self.mem_queries, args)
    }
}

impl<F: PrimeField> QueryRecord<F> {
    fn record_event_and_return<H: Hasher<F>>(
        &mut self,
        toplevel: &Toplevel<F, H>,
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

    pub fn load(&mut self, len: usize, ptr: F) -> &[F] {
        mem_load(&mut self.mem_queries, len, ptr)
    }
}

impl<'a, F: PrimeField, H: Hasher<F>> FuncChip<'a, F, H> {
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

impl<F: PrimeField> Func<F> {
    fn execute<H: Hasher<F>>(
        &self,
        args: &[F],
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
    ) -> List<F> {
        let frame = &mut args.into();
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        self.body().execute(frame, toplevel, queries)
    }

    pub fn execute_iter<H: Hasher<F>>(
        &self,
        args: &[F],
        toplevel: &Toplevel<F, H>,
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

impl<F: PrimeField> Block<F> {
    fn execute<H: Hasher<F>>(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
    ) -> List<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(map, toplevel, queries));
        self.ctrl.execute(map, toplevel, queries)
    }

    fn execute_step<'a, H: Hasher<F>>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
    ) -> Continuation<F> {
        let ops = self.ops.iter();
        let ctrl = &self.ctrl;
        Op::execute_step(ops, ctrl, map, stack, toplevel, queries)
    }
}

impl<F: PrimeField> Ctrl<F> {
    fn execute<H: Hasher<F>>(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F, H>,
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
            Ctrl::IfMany(vars, t, f) => {
                if vars.iter().any(|&var| {
                    let b = map[var];
                    b != F::zero()
                }) {
                    t.execute(map, toplevel, queries)
                } else {
                    f.execute(map, toplevel, queries)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute(map, toplevel, queries)
            }
            Ctrl::MatchMany(v, cases) => {
                let v = v.iter().map(|&v| map[v]).collect();
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute(map, toplevel, queries)
            }
        }
    }

    fn execute_step<'a, H: Hasher<F>>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
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
            Ctrl::IfMany(vars, t, f) => {
                if vars.iter().any(|&var| {
                    let b = map[var];
                    b != F::zero()
                }) {
                    t.execute_step(map, stack, toplevel, queries)
                } else {
                    f.execute_step(map, stack, toplevel, queries)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute_step(map, stack, toplevel, queries)
            }
            Ctrl::MatchMany(v, cases) => {
                let v = v.iter().map(|&v| map[v]).collect();
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute_step(map, stack, toplevel, queries)
            }
        }
    }
}

impl<F: PrimeField> Op<F> {
    fn execute<H: Hasher<F>>(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
    ) {
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
            Op::Hash(inp) => {
                let args: List<_> = inp.iter().map(|a| map[*a]).collect();
                let hasher = &toplevel.hasher;
                map.extend(hasher.hash(&args).iter());
            }
            Op::Debug(s) => println!("{}", s),
        }
    }

    fn execute_step<'a, H: Hasher<F>>(
        mut ops: Iter<'a, Self>,
        ctrl: &'a Ctrl<F>,
        mut map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
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
                Op::Hash(inp) => {
                    let args: List<_> = inp.iter().map(|a| map[*a]).collect();
                    let hasher = &toplevel.hasher;
                    map.extend(hasher.hash(&args).iter());
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
        lair::{
            demo_toplevel, execute::QueryRecord, field_from_u32, hasher::LurkHasher,
            toplevel::Toplevel, List,
        },
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    #[test]
    fn lair_execute_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();

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
        let toplevel = demo_toplevel::<_, LurkHasher>();

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
            fn test(a, b): [1] {
                let n = div(a, b);
                return n
            }
        );
        let toplevel = Toplevel::<_, LurkHasher>::new(&[test_e]);
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
            fn test(x): [1] {
                let x = add(x, x);
                let x = add(x, x);
                let x = add(x, x);
                return x
            }
        );
        let toplevel = Toplevel::<_, LurkHasher>::new(&[test_e]);
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
            invertible fn polynomial(a0, a1, a2, a3, x): [1] {
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
            fn inverse(y): [5] {
                let (a0, a1, a2, a3, x) = preimg(polynomial, y);
                return (a0, a1, a2, a3, x)
            }
        );
        let toplevel = Toplevel::<F, LurkHasher>::new(&[polynomial_e, inverse_e]);
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

    #[test]
    fn lair_array_test() {
        let test1_e = func!(
            fn test1(x: [4], y: [3]): [3] {
                let (_foo, a: [2], b: [2], _foo: [2]) = (x, y);
                let (sums1: [2], sum2: [1]) = call(test2, a, b);
                return (sums1, sum2)
            }
        );
        let test2_e = func!(
            fn test2(z: [4]): [3] {
                let (a, b, c, d) = z;
                let a_b = add(a, b);
                let b_c = add(b, c);
                let c_d = add(c, d);
                return (a_b, b_c, c_d)
            }
        );
        let toplevel = Toplevel::<_, LurkHasher>::new(&[test1_e, test2_e]);
        let test = toplevel.get_by_name("test1").unwrap();
        let f = F::from_canonical_u32;
        let args = &[f(1), f(2), f(3), f(4), f(5), f(6), f(7)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record);
        let expected_len = 3;
        assert_eq!(out.len(), expected_len);
        assert_eq!(out[0..expected_len], [f(5), f(7), f(9)]);
    }
}
