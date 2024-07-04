use hashbrown::HashMap;
use indexmap::{IndexMap, IndexSet};
use p3_field::{AbstractField, Field, PrimeField};
use rustc_hash::FxBuildHasher;
use sphinx_core::stark::{Indexed, MachineRecord};
use std::slice::Iter;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    hasher::Hasher,
    toplevel::Toplevel,
    List,
};

#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct QueryResult<F> {
    pub(crate) output: Option<List<F>>,
    /// (func_idx, caller_nonce, call_ident)
    pub(crate) callers_nonces: IndexSet<(usize, usize, usize)>,
}

impl<F> QueryResult<F> {
    #[inline]
    pub(crate) fn expect_output(&self) -> &[F] {
        self.output.as_ref().expect("Result not computed").as_ref()
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
    pub(crate) mem_queries: Vec<MemMap<F>>,
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
                .map(|im| im.values().map(|r| r.callers_nonces.len()).sum::<usize>())
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

    fn append(&mut self, _: &mut Self) {
        // just a no-op because `generate_dependencies` is a no-op
    }

    fn shard(self, config: &Self::Config) -> Vec<Self> {
        let Self {
            index: _,
            mut func_queries,
            inv_func_queries,
            mut mem_queries,
        } = self;

        let num_funcs = func_queries.len();
        let num_mem_tables = mem_queries.len();

        let max_shard_size = config.max_shard_size;

        if max_shard_size == 0 {
            return vec![Self {
                index: 0,
                func_queries,
                inv_func_queries,
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
                inv_func_queries,
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
                    inv_func_queries: inv_func_queries.clone(), // We can use the same inverse map for all shards
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
        self.func_queries[func.index]
            .get(inp)
            .expect("No output registered for the provided input")
            .expect_output()
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

    pub fn query(
        &mut self,
        index: usize,
        input: &[F],
        caller_index: usize,
        caller_nonce: usize,
        call_ident: usize,
    ) -> Option<&List<F>> {
        if let Some(event) = self.func_queries[index].get_mut(input) {
            let output = event.output.as_ref().expect("Loop detected");
            event
                .callers_nonces
                .insert((caller_index, caller_nonce, call_ident));
            Some(output)
        } else {
            None
        }
    }

    pub fn query_preimage(
        &mut self,
        index: usize,
        out: &[F],
        caller_index: usize,
        caller_nonce: usize,
        call_ident: usize,
    ) -> &List<F> {
        let inp = self.inv_func_queries[index]
            .as_ref()
            .expect("Missing inverse map")
            .get(out)
            .expect("Preimg not found");
        let func_queries = &mut self.func_queries[index];
        if let Some(event) = func_queries.get_mut(inp) {
            assert_eq!(out, event.expect_output());
            event
                .callers_nonces
                .insert((caller_index, caller_nonce, call_ident));
        } else {
            let mut callers_nonces = IndexSet::new();
            callers_nonces.insert((caller_index, caller_nonce, call_ident));
            let result = QueryResult {
                output: Some(out.into()),
                callers_nonces,
            };
            func_queries.insert(inp.clone(), result);
        }
        inp
    }

    fn record_event_and_return<H: Hasher<F>>(
        &mut self,
        toplevel: &Toplevel<F, H>,
        func_idx: usize,
        args: &[F],
        caller_index: usize,
        caller_nonce: usize,
        call_ident: usize,
    ) -> List<F> {
        if let Some(out) = self.query(func_idx, args, caller_index, caller_nonce, call_ident) {
            out.clone()
        } else {
            let func = toplevel.get_by_index(func_idx).unwrap();
            let (nonce, _) =
                self.func_queries[func_idx].insert_full(args.into(), QueryResult::default());
            let out = func.execute(args, toplevel, self, nonce);
            let QueryResult {
                output,
                callers_nonces,
            } = self.func_queries[func_idx].get_mut(args).unwrap();
            assert_eq!(*output, None);
            *output = Some(out.clone());
            callers_nonces.insert((caller_index, caller_nonce, call_ident));
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

impl<F: PrimeField, H: Hasher<F>> Toplevel<F, H> {
    pub fn execute(&self, func: &Func<F>, args: &[F], record: &mut QueryRecord<F>) {
        let index = func.index;
        let (nonce, _) =
            record.func_queries[index].insert_full(args.into(), QueryResult::default());
        let out = func.execute(args, self, record, nonce);
        let QueryResult {
            output,
            callers_nonces,
        } = record.func_queries[index].get_mut(args).unwrap();
        *output = Some(out);
        callers_nonces.insert((0, 0, 0)); // This corresponds to the builder.receive done in the Entrypoint chip
    }

    #[inline]
    pub fn execute_iter_by_name(
        &self,
        name: &'static str,
        args: &[F],
        record: &mut QueryRecord<F>,
    ) {
        let func = self
            .get_by_name(name)
            .expect("Entrypoint function not found");
        self.execute_iter(func, args, record)
    }

    pub fn execute_iter(&self, func: &Func<F>, args: &[F], record: &mut QueryRecord<F>) {
        let index = func.index;
        let (nonce, _) =
            record.func_queries[index].insert_full(args.into(), QueryResult::default());
        let out = func.execute_iter(args, self, record, nonce);
        let QueryResult {
            output,
            callers_nonces,
        } = record.func_queries[index].get_mut(args).unwrap();
        *output = Some(out);
        callers_nonces.insert((0, 0, 0));
    }

    #[inline]
    pub fn execute_by_name(&self, name: &'static str, args: &[F], record: &mut QueryRecord<F>) {
        let func = self
            .get_by_name(name)
            .expect("Entrypoint function not found");
        self.execute(func, args, record)
    }
}

type VarMap<F> = Vec<F>;
struct Frame<'a, F> {
    index: usize,
    args: List<F>,
    ops: Iter<'a, Op<F>>,
    ctrl: &'a Ctrl<F>,
    map: VarMap<F>,
    caller_index: usize,
    caller_nonce: usize,
    call_ident: usize,
}
type Stack<'a, F> = Vec<Frame<'a, F>>;
enum Continuation<F> {
    Return(Vec<F>),
    Apply(usize, usize, Vec<F>),
}

impl<F: PrimeField> Func<F> {
    pub(crate) fn execute<H: Hasher<F>>(
        &self,
        args: &[F],
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        nonce: usize,
    ) -> List<F> {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        let frame = &mut args.into();
        let func_index = self.index;
        self.body()
            .execute(frame, toplevel, queries, func_index, nonce)
    }

    pub fn execute_iter<H: Hasher<F>>(
        &self,
        args: &[F],
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        mut nonce: usize,
    ) -> List<F> {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        let mut map = args.to_vec();
        let mut ops = self.body.ops.iter();
        let mut ctrl = &self.body.ctrl;
        let mut stack = vec![];
        let mut func_index = self.index;
        loop {
            let cont = Op::execute_step(
                ops, ctrl, map, &mut stack, toplevel, queries, func_index, nonce,
            );
            match cont {
                Continuation::Return(out) => {
                    if let Some(frame) = stack.pop() {
                        ctrl = frame.ctrl;
                        ops = frame.ops;
                        map = frame.map;
                        func_index = frame.caller_index;
                        nonce = frame.caller_nonce;
                        map.extend(out.iter());
                        let QueryResult {
                            output,
                            callers_nonces,
                        } = queries.func_queries[frame.index]
                            .get_mut(&frame.args)
                            .unwrap();
                        assert_eq!(*output, None);
                        *output = Some(out.into());
                        callers_nonces.insert((
                            frame.caller_index,
                            frame.caller_nonce,
                            frame.call_ident,
                        ));
                    } else {
                        map = out;
                        break;
                    }
                }
                Continuation::Apply(idx, callee_nonce, args) => {
                    let func = toplevel.get_by_index(idx).unwrap();
                    map = args;
                    ctrl = &func.body.ctrl;
                    ops = func.body.ops.iter();
                    func_index = idx;
                    nonce = callee_nonce;
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
        func_index: usize,
        nonce: usize,
    ) -> List<F> {
        self.ops
            .iter()
            .for_each(|op| op.execute(map, toplevel, queries, func_index, nonce));
        self.ctrl.execute(map, toplevel, queries, func_index, nonce)
    }

    fn execute_step<'a, H: Hasher<F>>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        func_index: usize,
        nonce: usize,
    ) -> Continuation<F> {
        let ops = self.ops.iter();
        let ctrl = &self.ctrl;
        Op::execute_step(ops, ctrl, map, stack, toplevel, queries, func_index, nonce)
    }
}

impl<F: PrimeField> Ctrl<F> {
    fn execute<H: Hasher<F>>(
        &self,
        map: &mut VarMap<F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        func_index: usize,
        nonce: usize,
    ) -> List<F> {
        match self {
            Ctrl::Return(_, vars) => vars.iter().map(|var| map[*var]).collect(),
            Ctrl::If(b, t, f) => {
                let b = map.get(*b).unwrap();
                if b.is_zero() {
                    f.execute(map, toplevel, queries, func_index, nonce)
                } else {
                    t.execute(map, toplevel, queries, func_index, nonce)
                }
            }
            Ctrl::IfMany(vars, t, f) => {
                if vars.iter().any(|&var| {
                    let b = map[var];
                    b != F::zero()
                }) {
                    t.execute(map, toplevel, queries, func_index, nonce)
                } else {
                    f.execute(map, toplevel, queries, func_index, nonce)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute(map, toplevel, queries, func_index, nonce)
            }
            Ctrl::MatchMany(v, cases) => {
                let v = v.iter().map(|&v| map[v]).collect();
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute(map, toplevel, queries, func_index, nonce)
            }
        }
    }

    fn execute_step<'a, H: Hasher<F>>(
        &'a self,
        map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        func_index: usize,
        nonce: usize,
    ) -> Continuation<F> {
        match self {
            Ctrl::Return(_, vars) => {
                let out = vars.iter().map(|var| map[*var]).collect();
                Continuation::Return(out)
            }
            Ctrl::If(b, t, f) => {
                let b = map.get(*b).unwrap();
                if b.is_zero() {
                    f.execute_step(map, stack, toplevel, queries, func_index, nonce)
                } else {
                    t.execute_step(map, stack, toplevel, queries, func_index, nonce)
                }
            }
            Ctrl::IfMany(vars, t, f) => {
                if vars.iter().any(|&var| {
                    let b = map[var];
                    b != F::zero()
                }) {
                    t.execute_step(map, stack, toplevel, queries, func_index, nonce)
                } else {
                    f.execute_step(map, stack, toplevel, queries, func_index, nonce)
                }
            }
            Ctrl::Match(v, cases) => {
                let v = map.get(*v).unwrap();
                cases
                    .match_case(v)
                    .expect("No match")
                    .execute_step(map, stack, toplevel, queries, func_index, nonce)
            }
            Ctrl::MatchMany(v, cases) => {
                let v = v.iter().map(|&v| map[v]).collect();
                cases
                    .match_case(&v)
                    .expect("No match")
                    .execute_step(map, stack, toplevel, queries, func_index, nonce)
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
        func_index: usize,
        nonce: usize,
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
            Op::Call(idx, inp, call_ident) => {
                let args = inp.iter().map(|a| map[*a]).collect::<List<_>>();
                let out = queries.record_event_and_return(
                    toplevel,
                    *idx,
                    &args,
                    func_index,
                    nonce,
                    *call_ident,
                );
                map.extend(out.iter());
            }
            Op::PreImg(idx, out, call_ident) => {
                let out = out.iter().map(|a| map[*a]).collect::<List<_>>();
                let inp = queries.query_preimage(*idx, &out, func_index, nonce, *call_ident);
                map.extend(inp.iter());
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

    #[allow(clippy::too_many_arguments)]
    fn execute_step<'a, H: Hasher<F>>(
        mut ops: Iter<'a, Self>,
        ctrl: &'a Ctrl<F>,
        mut map: VarMap<F>,
        stack: &mut Stack<'a, F>,
        toplevel: &Toplevel<F, H>,
        queries: &mut QueryRecord<F>,
        func_index: usize,
        nonce: usize,
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
                Op::PreImg(idx, inp, ident) => {
                    let args = inp.iter().map(|a| map[*a]).collect::<List<_>>();
                    let out = queries.query_preimage(*idx, &args, func_index, nonce, *ident);
                    map.extend(out.iter());
                }
                Op::Call(index, inp, ident) => {
                    let args = inp.iter().map(|a| map[*a]).collect::<Vec<_>>();
                    if let Some(out) = queries.query(*index, &args, func_index, nonce, *ident) {
                        map.extend(out.iter())
                    } else {
                        let (callee_nonce, _) = queries.func_queries[*index]
                            .insert_full(args.clone().into(), QueryResult::default());
                        stack.push(Frame {
                            index: *index,
                            args: args.clone().into(),
                            ops,
                            ctrl,
                            map,
                            caller_index: func_index,
                            caller_nonce: nonce,
                            call_ident: *ident,
                        });
                        return Continuation::Apply(*index, callee_nonce, args);
                    }
                }
                Op::Hash(inp) => {
                    let args: List<_> = inp.iter().map(|a| map[*a]).collect();
                    let hasher = &toplevel.hasher;
                    map.extend(hasher.hash(&args).iter());
                }
            }
        }
        ctrl.execute_step(map, stack, toplevel, queries, func_index, nonce)
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
        let out = factorial.execute(args, &toplevel, record, 0);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(120));

        let even = toplevel.get_by_name("even").unwrap();
        let args = &[F::from_canonical_u32(7)];
        let out = even.execute(args, &toplevel, record, 0);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));

        let odd = toplevel.get_by_name("odd").unwrap();
        let args = &[F::from_canonical_u32(4)];
        let out = odd.execute(args, &toplevel, record, 0);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(0));
    }

    #[test]
    fn lair_execute_iter_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();

        let fib = toplevel.get_by_name("fib").unwrap();
        let args = &[F::from_canonical_u32(100000)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = fib.execute_iter(args, &toplevel, record, 0);
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
        let out = test.execute(args, &toplevel, record, 0);
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
        let out = test.execute(args, &toplevel, record, 0);
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
        let out = record.record_event_and_return(&toplevel, polynomial.index, &args, 0, 0, 0);
        assert_eq!(out.len(), 1);
        assert_eq!(out[0], F::from_canonical_u32(58061));
        let inp = inverse.execute(&out, &toplevel, record, 0);
        assert_eq!(inp, args);
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
        let out = test.execute(args, &toplevel, record, 0);
        let expected_len = 3;
        assert_eq!(out.len(), expected_len);
        assert_eq!(out[0..expected_len], [f(5), f(7), f(9)]);

        let test = toplevel.get_by_name("test3").unwrap();
        let f = F::from_canonical_u32;
        let args = &[f(4), f(9), f(21), f(10)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = test.execute(args, &toplevel, record, 0);
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
        let half = toplevel.get_by_name("half").unwrap();
        let half_chip = FuncChip::from_name("half", &toplevel);
        let double_chip = FuncChip::from_name("double", &toplevel);

        let queries = &mut QueryRecord::new(&toplevel);
        let f = F::from_canonical_u32;
        queries.inject_inv_queries("double", &toplevel, [(&[f(1)], &[f(2)])]);
        let args = &[f(2)];

        toplevel.execute_iter(half, args, queries);
        let res1 = queries.get_output(half, args).to_vec();
        let traces1 = (
            half_chip.generate_trace_sequential(queries),
            double_chip.generate_trace_sequential(queries),
        );

        // even after `clean`, the preimg of `double(1)` can still be recovered
        queries.clean();
        toplevel.execute_iter(half, args, queries);
        let res2 = queries.get_output(half, args).to_vec();
        let traces2 = (
            half_chip.generate_trace_sequential(queries),
            double_chip.generate_trace_sequential(queries),
        );
        assert_eq!(res1, res2);
        assert_eq!(traces1, traces2);

        queries.clean();
        toplevel.execute(half, args, queries);
        let res3 = queries.get_output(half, args);
        let traces3 = (
            half_chip.generate_trace_sequential(queries),
            double_chip.generate_trace_sequential(queries),
        );
        assert_eq!(res2, res3);
        assert_eq!(traces2, traces3);
    }
}
