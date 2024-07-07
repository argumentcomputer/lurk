use hashbrown::HashMap;
use indexmap::{IndexMap, IndexSet};
use p3_field::{AbstractField, Field, PrimeField32};
use rustc_hash::{FxBuildHasher, FxHashMap};
use sphinx_core::stark::{Indexed, MachineRecord};

use super::{
    bytecode::{Ctrl, Func, Op},
    hasher::Hasher,
    toplevel::Toplevel,
    List,
};

type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;

type QueryMap<F> = FxIndexMap<List<F>, QueryResult<F>>;
type InvQueryMap<F> = FxHashMap<List<F>, List<F>>;
pub(crate) type MemMap<F> = FxIndexMap<List<F>, FxIndexSet<(usize, usize, usize)>>;

#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct QueryResult<F> {
    pub(crate) output: Option<List<F>>,
    /// (func_index, caller_shard, caller_nonce, call_ident)
    pub(crate) callers_nonces: FxIndexSet<(usize, usize, usize, usize)>,
}

impl<F> QueryResult<F> {
    #[inline]
    pub(crate) fn expect_output(&self) -> &[F] {
        self.output.as_ref().expect("Result not computed").as_ref()
    }
}

#[derive(Default, Clone, Debug, Eq, PartialEq)]
pub struct QueryRecord<F: Field> {
    index: u32,
    pub(crate) func_queries: Vec<QueryMap<F>>,
    pub(crate) inv_func_queries: Vec<Option<InvQueryMap<F>>>,
    pub(crate) mem_queries: Vec<MemMap<F>>,
    pub(crate) shard_config: ShardingConfig,
}

impl<F: Field> Indexed for QueryRecord<F> {
    fn index(&self) -> u32 {
        self.index
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ShardingConfig {
    max_shard_size: usize,
}

impl ShardingConfig {
    #[inline]
    fn index_to_shard_nonce(&self, query_index: usize) -> (usize, usize) {
        let size = self.max_shard_size;
        let shard = query_index / size;
        let nonce = query_index % size;
        (shard, nonce)
    }
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
                .map(|im| im.values().map(|set| set.len()).sum::<usize>())
                .sum(),
        );
        map
    }

    fn append(&mut self, _: &mut Self) {
        // just a no-op because `generate_dependencies` is a no-op
    }

    fn shard(self, _config: &Self::Config) -> Vec<Self> {
        // let Self {
        //     index: _,
        //     mut func_queries,
        //     inv_func_queries,
        //     mut mem_queries,
        // } = self;

        // let num_funcs = func_queries.len();
        // let num_mem_tables = mem_queries.len();

        // let max_shard_size = config.max_shard_size;

        // if max_shard_size == 0 {
        //     return vec![Self {
        //         index: 0,
        //         func_queries,
        //         inv_func_queries,
        //         mem_queries,
        //     }];
        // }

        // let max_num_func_queries = func_queries.iter().map(IndexMap::len).max().unwrap_or(0);
        // let max_num_mem_queries = mem_queries.iter().map(IndexMap::len).max().unwrap_or(0);

        // let div_ceil = |numer, denom| (numer + denom - 1) / denom;
        // let num_shards_needed_for_func_queries = div_ceil(max_num_func_queries, max_shard_size);
        // let num_shards_needed_for_mem_queries = div_ceil(max_num_mem_queries, max_shard_size);
        // let num_shards_needed =
        //     num_shards_needed_for_func_queries.max(num_shards_needed_for_mem_queries);

        // if num_shards_needed < 2 {
        //     vec![Self {
        //         index: 0,
        //         func_queries,
        //         inv_func_queries,
        //         mem_queries,
        //     }]
        // } else {
        //     let empty_func_queries = vec![FxIndexMap::default(); num_funcs];
        //     let empty_mem_queries = vec![FxIndexMap::default(); num_mem_tables];
        //     let mut shards = Vec::with_capacity(num_shards_needed);
        //     let num_shards_needed_u32: u32 = num_shards_needed
        //         .try_into()
        //         .expect("Number of shards needed is too big");
        //     for index in 0..num_shards_needed_u32 {
        //         let mut sharded_func_queries = empty_func_queries.clone();
        //         for func_idx in 0..num_funcs {
        //             let queries = &mut func_queries[func_idx];
        //             sharded_func_queries[func_idx]
        //                 .extend(queries.drain(0..max_shard_size.min(queries.len())));
        //         }
        //         let mut sharded_mem_queries = empty_mem_queries.clone();
        //         for mem_idx in 0..num_mem_tables {
        //             let queries = &mut mem_queries[mem_idx];
        //             sharded_mem_queries[mem_idx]
        //                 .extend(queries.drain(0..max_shard_size.min(queries.len())));
        //         }
        //         shards.push(QueryRecord {
        //             index,
        //             func_queries: sharded_func_queries,
        //             inv_func_queries: inv_func_queries.clone(), // We can use the same inverse map for all shards
        //             mem_queries: sharded_mem_queries,
        //         });
        //     }
        //     shards
        // }
        todo!()
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

impl<F: PrimeField32> QueryRecord<F> {
    #[inline]
    pub fn new<H: Hasher<F>>(toplevel: &Toplevel<F, H>) -> Self {
        Self::new_with_shard_config(toplevel, ShardingConfig::default())
    }

    #[inline]
    pub fn new_with_shard_config<H: Hasher<F>>(
        toplevel: &Toplevel<F, H>,
        shard_config: ShardingConfig,
    ) -> Self {
        let mem_queries = vec![FxIndexMap::default(); NUM_MEM_TABLES];
        let func_queries = vec![FxIndexMap::default(); toplevel.size()];
        let inv_func_queries = toplevel
            .map
            .iter()
            .map(|(_, func)| {
                if func.invertible {
                    Some(FxHashMap::default())
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
            shard_config,
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
        let func = toplevel.get_by_name(name);
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

    fn query(
        &mut self,
        index: usize,
        input: &[F],
        caller_func_index: usize,
        caller_query_index: usize,
        call_ident: usize,
    ) -> Option<&List<F>> {
        let (caller_shard, caller_nonce) =
            self.shard_config.index_to_shard_nonce(caller_query_index);
        if let Some(event) = self.func_queries[index].get_mut(input) {
            let output = event.output.as_ref().expect("Loop detected");
            event.callers_nonces.insert((
                caller_func_index,
                caller_shard,
                caller_nonce,
                call_ident,
            ));
            Some(output)
        } else {
            None
        }
    }

    pub fn query_preimage(
        &mut self,
        index: usize,
        out: &[F],
        caller_func_index: usize,
        caller_query_index: usize,
        call_ident: usize,
    ) -> &List<F> {
        let inp = self.inv_func_queries[index]
            .as_ref()
            .expect("Missing inverse map")
            .get(out)
            .expect("Preimg not found");
        let (caller_shard, caller_nonce) =
            self.shard_config.index_to_shard_nonce(caller_query_index);
        let func_queries = &mut self.func_queries[index];
        if let Some(event) = func_queries.get_mut(inp) {
            assert_eq!(out, event.expect_output());
            event.callers_nonces.insert((
                caller_func_index,
                caller_shard,
                caller_nonce,
                call_ident,
            ));
        } else {
            let mut callers_nonces = IndexSet::default();
            callers_nonces.insert((caller_func_index, caller_shard, caller_nonce, call_ident));
            let result = QueryResult {
                output: Some(out.into()),
                callers_nonces,
            };
            func_queries.insert(inp.clone(), result);
        }
        inp
    }

    fn store(
        &mut self,
        args: List<F>,
        caller_index: usize,
        caller_nonce: usize,
        store_ident: usize,
    ) -> F {
        let mem_idx = mem_index_from_len(args.len());
        let mem_map = &mut self.mem_queries[mem_idx];
        let mem_map_idx = if let Some((i, _, callers_nonces)) = mem_map.get_full_mut(&args) {
            callers_nonces.insert((caller_index, caller_nonce, store_ident));
            i
        } else {
            let mut callers_nonces = IndexSet::default();
            callers_nonces.insert((caller_index, caller_nonce, store_ident));
            mem_map.insert_full(args, callers_nonces).0
        };
        F::from_canonical_usize(mem_map_idx + 1)
    }

    fn load(
        &mut self,
        len: usize,
        ptr: F,
        caller_index: usize,
        caller_nonce: usize,
        load_ident: usize,
    ) -> &[F] {
        let ptr_f = ptr.as_canonical_u32() as usize;
        let mem_idx = mem_index_from_len(len);
        let (args, callers_nonces) = self.mem_queries[mem_idx]
            .get_index_mut(ptr_f - 1)
            .expect("Unbound pointer");
        callers_nonces.insert((caller_index, caller_nonce, load_ident));
        args
    }
}

impl<F: PrimeField32, H: Hasher<F>> Toplevel<F, H> {
    pub fn execute(&self, func: &Func<F>, args: &[F], record: &mut QueryRecord<F>) -> List<F> {
        let func_index = func.index;
        let (query_index, _) =
            record.func_queries[func_index].insert_full(args.into(), QueryResult::default());
        let out = func.execute(args, self, record, query_index);
        if let Some(inv_map) = &mut record.inv_func_queries[func_index] {
            inv_map.insert(out.clone(), args.into());
        }
        let query_result = record.func_queries[func_index]
            .get_index_mut(query_index)
            .unwrap()
            .1;
        // the following entry corresponds to the builder.receive done in LairChip::Entrypoint
        query_result.callers_nonces.insert((0, 0, 0, 0));
        out
    }

    #[inline]
    pub fn execute_by_name(
        &self,
        name: &'static str,
        args: &[F],
        record: &mut QueryRecord<F>,
    ) -> List<F> {
        let func = self.get_by_name(name);
        self.execute(func, args, record)
    }
}

enum ExecEntry<'a, F> {
    Op(&'a Op<F>),
    Ctrl(&'a Ctrl<F>),
}

struct CallerState<F> {
    func_index: usize,
    query_index: usize,
    call_ident: usize,
    map: Vec<F>,
}

impl<F: PrimeField32> Func<F> {
    fn execute<H: Hasher<F>>(
        &self,
        args: &[F],
        toplevel: &Toplevel<F, H>,
        record: &mut QueryRecord<F>,
        mut query_index: usize,
    ) -> List<F> {
        assert!(
            record.func_queries[self.index]
                .get_index(query_index)
                .is_some(),
            "Query map entry not preallocated"
        );
        let mut exec_entries_stack = vec![];
        let mut callers_states_stack = vec![];
        macro_rules! push_block_exec_entries {
            ($block:expr) => {
                exec_entries_stack.push(ExecEntry::Ctrl(&$block.ctrl));
                exec_entries_stack.extend($block.ops.iter().rev().map(ExecEntry::Op));
            };
        }
        push_block_exec_entries!(&self.body);
        let mut map = args.to_vec();
        let mut func_index = self.index;
        while let Some(exec_entry) = exec_entries_stack.pop() {
            match exec_entry {
                ExecEntry::Op(Op::Call(callee_index, inp, ident)) => {
                    // `map_buffer` will become the map for the called function
                    let mut map_buffer = inp.iter().map(|v| map[*v]).collect::<Vec<_>>();
                    if let Some(out) =
                        record.query(*callee_index, &map_buffer, func_index, query_index, *ident)
                    {
                        map.extend(out.iter())
                    } else {
                        // insert dummy entry
                        let (callee_query_index, _) = record.func_queries[*callee_index]
                            .insert_full(map_buffer.clone().into(), QueryResult::default());
                        // swap so we can save the old map in `map_buffer` and move on
                        // with `map` already set
                        std::mem::swap(&mut map_buffer, &mut map);
                        // save the current caller state
                        callers_states_stack.push(CallerState {
                            func_index,
                            query_index,
                            call_ident: *ident,
                            map: map_buffer,
                        });
                        // prepare outer variables to go into the new func scope
                        func_index = *callee_index;
                        query_index = callee_query_index;
                        push_block_exec_entries!(&toplevel.get_by_index(func_index).body);
                    }
                }
                ExecEntry::Op(Op::PreImg(callee_index, out, ident)) => {
                    let out = out.iter().map(|v| map[*v]).collect::<List<_>>();
                    let inp =
                        record.query_preimage(*callee_index, &out, func_index, query_index, *ident);
                    map.extend(inp.iter());
                }
                ExecEntry::Op(Op::Const(c)) => map.push(*c),
                ExecEntry::Op(Op::Add(a, b)) => map.push(map[*a] + map[*b]),
                ExecEntry::Op(Op::Sub(a, b)) => map.push(map[*a] - map[*b]),
                ExecEntry::Op(Op::Mul(a, b)) => map.push(map[*a] * map[*b]),
                ExecEntry::Op(Op::Inv(a)) => map.push(map[*a].inverse()),
                ExecEntry::Op(Op::Not(a)) => map.push(if map[*a].is_zero() {
                    F::one()
                } else {
                    F::zero()
                }),
                ExecEntry::Op(Op::Store(args, ident)) => {
                    let args = args.iter().map(|a| map[*a]).collect();
                    let ptr = record.store(args, func_index, query_index, *ident);
                    map.push(ptr);
                }
                ExecEntry::Op(Op::Load(len, ptr, ident)) => {
                    let ptr = map[*ptr];
                    let args = record.load(*len, ptr, func_index, query_index, *ident);
                    map.extend(args);
                }
                ExecEntry::Op(Op::Debug(s)) => println!("{}", s),
                ExecEntry::Op(Op::Hash(preimg)) => {
                    let preimg: List<_> = preimg.iter().map(|a| map[*a]).collect();
                    map.extend(toplevel.hasher.hash(&preimg));
                }
                ExecEntry::Ctrl(Ctrl::Return(_, out)) => {
                    let out = out.iter().map(|v| map[*v]).collect::<Vec<_>>();
                    let (inp, query_result) = record.func_queries[func_index]
                        .get_index_mut(query_index)
                        .unwrap();
                    assert!(query_result.output.is_none());
                    let out_list: List<_> = out.clone().into();
                    if let Some(inv_map) = &mut record.inv_func_queries[func_index] {
                        inv_map.insert(out_list.clone(), inp.clone());
                    }
                    query_result.output = Some(out_list);
                    if let Some(CallerState {
                        func_index: caller_func_idx,
                        query_index: caller_query_index,
                        map: caller_map,
                        call_ident,
                    }) = callers_states_stack.pop()
                    {
                        // recover the state of the caller
                        func_index = caller_func_idx;
                        query_index = caller_query_index;
                        map = caller_map;
                        // insert caller nonce data
                        let (caller_shard, caller_nonce) =
                            record.shard_config.index_to_shard_nonce(caller_query_index);
                        query_result.callers_nonces.insert((
                            func_index,
                            caller_shard,
                            caller_nonce,
                            call_ident,
                        ));
                        // extend the map with the call output
                        map.extend(out);
                    } else {
                        // no outer caller... about to exit
                        map = out;
                    }
                }
                ExecEntry::Ctrl(Ctrl::If(b, t, f)) => {
                    if map[*b].is_zero() {
                        push_block_exec_entries!(f);
                    } else {
                        push_block_exec_entries!(t);
                    }
                }
                ExecEntry::Ctrl(Ctrl::IfMany(bs, t, f)) => {
                    if bs.iter().any(|b| !map[*b].is_zero()) {
                        push_block_exec_entries!(t);
                    } else {
                        push_block_exec_entries!(f);
                    }
                }
                ExecEntry::Ctrl(Ctrl::Match(v, cases)) => {
                    let block = cases.match_case(&map[*v]).expect("No match");
                    push_block_exec_entries!(block);
                }
                ExecEntry::Ctrl(Ctrl::MatchMany(vs, cases)) => {
                    let vs = vs.iter().map(|v| map[*v]).collect();
                    let block = cases.match_case(&vs).expect("No match");
                    push_block_exec_entries!(block);
                }
            }
        }
        map.into()
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

        let factorial = toplevel.get_by_name("factorial");
        let args = &[F::from_canonical_u32(5)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(factorial, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(120)]);

        let even = toplevel.get_by_name("even");
        let args = &[F::from_canonical_u32(7)];
        let out = toplevel.execute(even, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(0)]);

        let odd = toplevel.get_by_name("odd");
        let args = &[F::from_canonical_u32(4)];
        let out = toplevel.execute(odd, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(0)]);
    }

    #[test]
    fn lair_execute_iter_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();

        let fib = toplevel.get_by_name("fib");
        let args = &[F::from_canonical_u32(100000)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(fib, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(309996207)]);
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
        let test = toplevel.get_by_name("test");
        let args = &[F::from_canonical_u32(20), F::from_canonical_u32(4)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(test, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(5)]);
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
        let test = toplevel.get_by_name("test");
        let args = &[F::from_canonical_u32(10)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(test, args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(80)]);
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
        let polynomial = toplevel.get_by_name("polynomial");
        let inverse = toplevel.get_by_name("inverse");
        let args = [1, 3, 5, 7, 20]
            .into_iter()
            .map(field_from_u32)
            .collect::<List<_>>();
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(polynomial, &args, record);
        assert_eq!(out.as_ref(), [F::from_canonical_u32(58061)]);
        let inp = toplevel.execute(inverse, &out, record);
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
        let test = toplevel.get_by_name("test1");
        let f = F::from_canonical_u32;
        let args = &[f(1), f(2), f(3), f(4), f(5), f(6), f(7)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(test, args, record);
        assert_eq!(out.as_ref(), [f(5), f(7), f(9)]);

        let test = toplevel.get_by_name("test3");
        let f = F::from_canonical_u32;
        let args = &[f(4), f(9), f(21), f(10)];
        let record = &mut QueryRecord::new(&toplevel);
        let out = toplevel.execute(test, args, record);
        assert_eq!(out.as_ref(), [f(1), f(2), f(3), f(4)]);
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
        let half = toplevel.get_by_name("half");
        let half_chip = FuncChip::from_name("half", &toplevel);
        let double_chip = FuncChip::from_name("double", &toplevel);

        let queries = &mut QueryRecord::new(&toplevel);
        let f = F::from_canonical_u32;
        queries.inject_inv_queries("double", &toplevel, [(&[f(1)], &[f(2)])]);
        let args = &[f(2)];

        toplevel.execute(half, args, queries);
        let res1 = queries.get_output(half, args).to_vec();
        let traces1 = (
            half_chip.generate_trace_sequential(queries),
            double_chip.generate_trace_sequential(queries),
        );

        // even after `clean`, the preimg of `double(1)` can still be recovered
        queries.clean();
        toplevel.execute(half, args, queries);
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
