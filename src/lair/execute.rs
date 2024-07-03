use hashbrown::HashMap;
use indexmap::IndexMap;
use p3_field::{AbstractField, Field, PrimeField};
use rustc_hash::FxBuildHasher;
use sphinx_core::stark::{Indexed, MachineRecord};
use std::slice::Iter;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    func_chip::FuncChip,
    hasher::Hasher,
    toplevel::Toplevel,
    List,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QueryResult<F> {
    pub(crate) output: List<F>,
    pub(crate) mult: u32,
}

impl<F> QueryResult<F> {
    fn once(output: List<F>) -> Self {
        Self { output, mult: 1 }
    }
}

type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
type QueryMap<F> = FxIndexMap<List<F>, QueryResult<F>>;
type InvQueryMap<F> = FxIndexMap<List<F>, List<F>>;
pub(crate) type MemMap<F> = FxIndexMap<List<F>, u32>;

#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F: Field> {
    index: u32,
    pub(crate) func_queries: Vec<QueryMap<F>>,
    pub(crate) inv_func_queries: Vec<Option<InvQueryMap<F>>>,
    pub mem_queries: Vec<MemMap<F>>,
}

impl<F: Field> Indexed for QueryRecord<F> {
    fn index(&self) -> u32 {
        self.index
    }
}

pub struct ShardingConfig {
    max_shard_size: usize,
}

impl Default for ShardingConfig {
    fn default() -> Self {
        Self {
            max_shard_size: 1 << 20,
        }
    }
}

impl<F: Field> MachineRecord for QueryRecord<F> {
    type Config = ShardingConfig;

    fn set_index(&mut self, index: u32) {
        self.index = index
    }

    fn stats(&self) -> HashMap<String, usize> {
        // TODO: use `IndexMap` instead so the original insertion order is kept
        let mut map = HashMap::default();

        map.insert("num_funcs".to_string(), self.func_queries.len());
        map.insert(
            "num_func_queries".to_string(),
            self.func_queries.iter().map(|im| im.iter().count()).sum(),
        );
        map.insert(
            "sum_func_queries_mults".to_string(),
            self.func_queries
                .iter()
                .map(|im| im.values().map(|r| r.mult as usize).sum::<usize>())
                .sum(),
        );

        map.insert("num_mem_tables".to_string(), self.mem_queries.len());
        map.insert(
            "num_mem_queries".to_string(),
            self.mem_queries.iter().map(|im| im.iter().count()).sum(),
        );
        map.insert(
            "sum_mem_queries_mults".to_string(),
            self.mem_queries
                .iter()
                .map(|im| im.values().map(|mult| *mult as usize).sum::<usize>())
                .sum(),
        );
        map
    }

    fn append(&mut self, other: &mut Self) {
        // draining func queries from `other` to `self`, starting from the end
        let mut func_idx = self.func_queries.len() - 1;
        while let Some(func_queries) = other.func_queries.pop() {
            let self_func_queries = &mut self.func_queries[func_idx];
            for (inp, other_res) in func_queries {
                if other_res.mult == 0 {
                    continue;
                }
                if let Some(self_res) = self_func_queries.get_mut(&inp) {
                    assert_eq!(&self_res.output, &other_res.output);
                    self_res.mult += other_res.mult;
                } else {
                    self_func_queries.insert(inp, other_res);
                }
            }
            func_idx -= 1;
        }

        // dropping to save up memory because this is just auxiliary data for execution
        self.inv_func_queries = vec![];

        // draining mem queries from `other` to `self`, starting from the end
        let mut mem_idx = self.mem_queries.len() - 1;
        while let Some(other_mem_map) = other.mem_queries.pop() {
            let self_mem_map = &mut self.mem_queries[mem_idx];
            for (args, other_mult) in other_mem_map {
                if other_mult == 0 {
                    continue;
                }
                if let Some(self_mult) = self_mem_map.get_mut(&args) {
                    *self_mult += other_mult;
                } else {
                    self_mem_map.insert(args, other_mult);
                }
            }
            mem_idx -= 1;
        }
    }

    fn shard(self, config: &Self::Config) -> Vec<Self> {
        let Self {
            index: _,
            mut func_queries,
            inv_func_queries: _,
            mut mem_queries,
        } = self;

        let num_funcs = func_queries.len();
        let num_mem_tables = mem_queries.len();

        let max_shard_size = config.max_shard_size;

        if max_shard_size == 0 {
            return vec![Self {
                index: 0,
                func_queries,
                inv_func_queries: vec![],
                mem_queries,
            }];
        }

        let max_num_func_queries = func_queries.iter().map(IndexMap::len).max().unwrap_or(0);
        let max_num_mem_queries = mem_queries.iter().map(IndexMap::len).max().unwrap_or(0);

        let div_ceil = |numer, denom| (numer + denom - 1) / denom;
        let num_shards_needed_for_func_queries = div_ceil(max_num_func_queries, max_shard_size);
        let num_shards_needed_for_mem_queries = div_ceil(max_num_mem_queries, max_shard_size);
        let num_shards_needed =
            num_shards_needed_for_func_queries.max(num_shards_needed_for_mem_queries);

        if num_shards_needed < 2 {
            vec![Self {
                index: 0,
                func_queries,
                inv_func_queries: vec![],
                mem_queries,
            }]
        } else {
            let empty_func_queries = vec![FxIndexMap::default(); num_funcs];
            let empty_mem_queries = vec![FxIndexMap::default(); num_mem_tables];
            let mut shards = Vec::with_capacity(num_shards_needed);
            let num_shards_needed_u32: u32 = num_shards_needed
                .try_into()
                .expect("Number of shards needed is too big");
            for index in 0..num_shards_needed_u32 {
                let mut sharded_func_queries = empty_func_queries.clone();
                for func_idx in 0..num_funcs {
                    let queries = &mut func_queries[func_idx];
                    sharded_func_queries[func_idx]
                        .extend(queries.drain(0..max_shard_size.min(queries.len())));
                }
                let mut sharded_mem_queries = empty_mem_queries.clone();
                for mem_idx in 0..num_mem_tables {
                    let queries = &mut mem_queries[mem_idx];
                    sharded_mem_queries[mem_idx]
                        .extend(queries.drain(0..max_shard_size.min(queries.len())));
                }
                shards.push(QueryRecord {
                    index,
                    func_queries: sharded_func_queries,
                    inv_func_queries: vec![],
                    mem_queries: sharded_mem_queries,
                });
            }
            shards
        }
    }

    fn public_values<F2: AbstractField>(&self) -> Vec<F2> {
        vec![]
    }
}

const NUM_MEM_TABLES: usize = 5;
pub(crate) const MEM_TABLE_SIZES: [usize; NUM_MEM_TABLES] = [3, 4, 5, 6, 8];

#[inline]
pub fn mem_index_to_len(idx: usize) -> usize {
    MEM_TABLE_SIZES[idx]
}

#[inline]
pub fn mem_index_from_len(len: usize) -> usize {
    MEM_TABLE_SIZES
        .iter()
        .position(|&i| len == i)
        .unwrap_or_else(|| panic!("There are no mem tables of size {len}"))
}

impl<F: PrimeField> QueryRecord<F> {
    #[inline]
    pub fn new<H: Hasher<F>>(toplevel: &Toplevel<F, H>) -> Self {
        let mem_queries = vec![FxIndexMap::default(); NUM_MEM_TABLES];
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
        Self {
            index: 0,
            func_queries,
            inv_func_queries,
            mem_queries,
        }
    }

    #[inline]
    pub fn get_output(&self, func: &Func<F>, inp: &[F]) -> &[F] {
        &self.func_queries[func.index]
            .get(inp)
            .expect("No output registered for the provided input")
            .output
    }

    #[inline]
    pub fn func_queries(&self) -> &Vec<QueryMap<F>> {
        &self.func_queries
    }

    /// Injects queries for invertible functions, allowing `Op::PreImg` to work smoothly
    /// without needing a first execution pass.
    pub fn inject_inv_queries<
        'a,
        I: Clone + Into<List<F>> + 'a,
        O: Clone + Into<List<F>> + 'a,
        T: IntoIterator<Item = (&'a I, &'a O)>,
        H: Hasher<F>,
    >(
        &mut self,
        name: &'static str,
        toplevel: &Toplevel<F, H>,
        new_queries_data: T,
    ) {
        let func = toplevel.get_by_name(name).expect("Unknown Func");
        let inv_func_queries = self.inv_func_queries[func.index]
            .as_mut()
            .expect("Inverse query map not found");
        for (inp, out) in new_queries_data {
            inv_func_queries.insert(out.clone().into(), inp.clone().into());
        }
    }

    /// Erases the records of func and memory queries, but leaves the history of
    /// invertible queries untouched
    pub fn clean(&mut self) {
        self.func_queries.iter_mut().for_each(|func_query| {
            *func_query = FxIndexMap::default();
        });
        self.mem_queries.iter_mut().for_each(|mem_map| {
            *mem_map = FxIndexMap::default();
        });
    }

    pub fn query(&mut self, index: usize, input: &[F]) -> Option<&List<F>> {
        if let Some(event) = self.func_queries[index].get_mut(input) {
            event.mult += 1;
            Some(&event.output)
        } else {
            None
        }
    }

    pub fn query_preimage(&mut self, index: usize, out: &[F]) -> &List<F> {
        let inp = self.inv_func_queries[index]
            .as_ref()
            .expect("Missing inverse map")
            .get(out)
            .expect("Preimg not found");
        let func_queries = &mut self.func_queries[index];
        if let Some(result) = func_queries.get_mut(inp) {
            assert_eq!(out, result.output.as_ref());
            result.mult += 1;
        } else {
            func_queries.insert(inp.clone(), QueryResult::once(out.into()));
        }
        inp
    }

    pub fn insert_result(&mut self, index: usize, input: List<F>, output: List<F>) {
        if let Some(queries) = &mut self.inv_func_queries[index] {
            queries.insert(output.clone(), input.clone());
        }
        assert!(self.func_queries[index]
            .insert(input, QueryResult::once(output))
            .is_none());
    }

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

    pub fn store(&mut self, args: List<F>) -> F {
        let mem_idx = mem_index_from_len(args.len());
        let mem_map = &mut self.mem_queries[mem_idx];
        let mem_map_idx = if let Some((i, _, mult)) = mem_map.get_full_mut(&args) {
            *mult += 1;
            i
        } else {
            mem_map.insert_full(args, 1).0
        };
        F::from_canonical_usize(mem_map_idx + 1)
    }

    pub fn load(&mut self, len: usize, ptr: F) -> &[F] {
        let ptr_f: usize = ptr
            .as_canonical_biguint()
            .try_into()
            .expect("Field element is too big for a pointer");
        let mem_idx = mem_index_from_len(len);
        let (args, mult) = self.mem_queries[mem_idx]
            .get_index_mut(ptr_f - 1)
            .expect("Unbound pointer");
        *mult += 1;
        args
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
                let out = queries.query_preimage(*idx, &args);
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
                    let out = queries.query_preimage(*idx, &args);
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
            demo_toplevel, execute::QueryRecord, field_from_u32, func_chip::FuncChip,
            hasher::LurkHasher, toplevel::Toplevel, List,
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
        let test3_e = func!(
            fn test3(a: [4]): [4] {
                let b = [2, 3, 7, 5];
                let c = [-1, -1, 0, 2];
                let tmp = div(a, b);
                let res = add(tmp, c);
                return res
            }
        );
        let toplevel = Toplevel::<_, LurkHasher>::new(&[test1_e, test2_e, test3_e]);
        let test = toplevel.get_by_name("test1").unwrap();
        let f = F::from_canonical_u32;
        let args = &[f(1), f(2), f(3), f(4), f(5), f(6), f(7)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record);
        let expected_len = 3;
        assert_eq!(out.len(), expected_len);
        assert_eq!(out[0..expected_len], [f(5), f(7), f(9)]);

        let test = toplevel.get_by_name("test3").unwrap();
        let f = F::from_canonical_u32;
        let args = &[f(4), f(9), f(21), f(10)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record);
        let expected_len = 4;
        assert_eq!(out.len(), expected_len);
        assert_eq!(out[0..expected_len], [f(1), f(2), f(3), f(4)]);
    }

    #[test]
    fn consistent_clean() {
        let half_e = func!(
            fn half(x): [1] {
                let pre = preimg(double, x);
                return pre
            }
        );
        let double_e = func!(
            invertible fn double(x): [1] {
                let two_x = add(x, x);
                return two_x
            }
        );

        let toplevel = Toplevel::<F, LurkHasher>::new(&[half_e, double_e]);
        let half = FuncChip::from_name("half", &toplevel);
        let double = FuncChip::from_name("double", &toplevel);

        let queries = &mut QueryRecord::new(&toplevel);
        let f = F::from_canonical_u32;
        queries.inject_inv_queries("double", &toplevel, [(&[f(1)], &[f(2)])]);
        let args = [f(2)];

        half.execute_iter(args.into(), queries);
        let res1 = queries.get_output(half.func, &args).to_vec();
        let traces1 = (
            half.generate_trace_sequential(queries),
            double.generate_trace_sequential(queries),
        );

        // even after `clean`, the preimg of `double(1)` can still be recovered
        queries.clean();
        half.execute_iter(args.into(), queries);
        let res2 = queries.get_output(half.func, &args).to_vec();
        let traces2 = (
            half.generate_trace_sequential(queries),
            double.generate_trace_sequential(queries),
        );
        assert_eq!(res1, res2);
        assert_eq!(traces1, traces2);

        queries.clean();
        half.execute(args.into(), queries);
        let res3 = queries.get_output(half.func, &args);
        let traces3 = (
            half.generate_trace_sequential(queries),
            double.generate_trace_sequential(queries),
        );
        assert_eq!(res2, res3);
        assert_eq!(traces2, traces3);
    }
}
