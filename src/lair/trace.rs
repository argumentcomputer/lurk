use std::slice::Iter;

use p3_field::{PrimeField, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use crate::{air::builder::Record, lair::execute::mem_index_from_len};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    execute::{QueryRecord, Shard},
    func_chip::{ColumnLayout, Degree, FuncChip, LayoutSizes},
    hasher::Hasher,
    List,
};

#[derive(Default)]
pub struct NA;

pub type ColumnIndex = ColumnLayout<NA, usize>;
pub type ColumnMutSlice<'a, T> = ColumnLayout<&'a mut T, &'a mut [T]>;

impl<'a, T> ColumnMutSlice<'a, T> {
    pub fn from_slice(slice: &'a mut [T], layout_sizes: LayoutSizes) -> Self {
        let (nonce, slice) = slice.split_at_mut(1);
        let (input, slice) = slice.split_at_mut(layout_sizes.input);
        let (aux, slice) = slice.split_at_mut(layout_sizes.aux);
        let (sel, slice) = slice.split_at_mut(layout_sizes.sel);
        assert!(slice.is_empty());
        let nonce = &mut nonce[0];
        Self {
            nonce,
            input,
            aux,
            sel,
        }
    }

    pub fn push_input(&mut self, index: &mut ColumnIndex, t: T) {
        self.input[index.input] = t;
        index.input += 1;
    }

    pub fn push_aux(&mut self, index: &mut ColumnIndex, t: T) {
        self.aux[index.aux] = t;
        index.aux += 1;
    }
}

impl<'a, F: PrimeField32, H: Hasher<F>> FuncChip<'a, F, H> {
    /// Per-row parallel trace generation
    pub fn generate_trace(&self, shard: &Shard<'_, F>) -> RowMajorMatrix<F> {
        let func_queries = &shard.record().func_queries()[self.func.index];
        let range = shard.get_func_range(self.func.index);
        let width = self.width();
        let non_dummy_height = range.len();
        let height = non_dummy_height.next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        // initializing nonces
        rows.chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| row[0] = F::from_canonical_usize(range.start + i));
        let non_dummies = &mut rows[0..non_dummy_height * width];
        non_dummies
            .par_chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| {
                let (args, result) = func_queries.get_index(range.start + i).unwrap();
                let index = &mut ColumnIndex::default();
                let slice = &mut ColumnMutSlice::from_slice(row, self.layout_sizes);
                let requires = result.requires.iter();
                let queries = shard.record();
                let hasher = &self.toplevel.hasher;
                self.func
                    .populate_row(args, index, slice, queries, requires, hasher);
            });
        RowMajorMatrix::new(rows, width)
    }
}

#[derive(Clone)]
struct TraceCtx<'a, F: PrimeField32, H> {
    queries: &'a QueryRecord<F>,
    hasher: &'a H,
    func_idx: usize,
    call_inp: List<F>,
    requires: Iter<'a, Record>,
}

impl<F: PrimeField32> Func<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        args: &[F],
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        requires: Iter<'_, Record>,
        hasher: &H,
    ) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.iter().map(|arg| (*arg, 1)).collect();
        // Context of which function this is
        let ctx = &mut TraceCtx {
            func_idx: self.index,
            call_inp: args.into(),
            queries,
            hasher,
            requires,
        };
        // One column per input
        args.iter().for_each(|arg| slice.push_input(index, *arg));
        self.body.populate_row(ctx, map, index, slice);
    }
}

impl<F: PrimeField32> Block<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, H>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(ctx, map, index, slice));
        self.ctrl.populate_row(ctx, map, index, slice);
    }
}

impl<F: PrimeField32> Ctrl<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, H>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
    ) {
        match self {
            Ctrl::Return(ident, _) => {
                assert!(ctx.requires.next().is_none());
                slice.sel[*ident] = F::one();
                let query_map = &ctx.queries.func_queries()[ctx.func_idx];
                let lookup = query_map
                    .get(&ctx.call_inp)
                    .expect("Cannot find query result")
                    .provide;
                let provide = lookup.into_provide();
                slice.push_aux(index, provide.last_nonce);
                slice.push_aux(index, provide.last_count);
            }
            Ctrl::Match(t, cases) => {
                let (t, _) = map[*t];
                if let Some(branch) = cases.branches.get(&t) {
                    branch.populate_row(ctx, map, index, slice);
                } else {
                    for (f, _) in cases.branches.iter() {
                        slice.push_aux(index, (t - *f).inverse());
                    }
                    let branch = cases.default.as_ref().expect("No match");
                    branch.populate_row(ctx, map, index, slice);
                }
            }
            Ctrl::MatchMany(vars, cases) => {
                let vals = vars.iter().map(|&var| map[var].0).collect();
                if let Some(branch) = cases.branches.get(&vals) {
                    branch.populate_row(ctx, map, index, slice);
                } else {
                    for (fs, _) in cases.branches.iter() {
                        let diffs = vals.iter().zip(fs.iter()).map(|(val, f)| *val - *f);
                        push_inequality_witness(index, slice, diffs);
                    }
                    let branch = cases.default.as_ref().expect("No match");
                    branch.populate_row(ctx, map, index, slice);
                }
            }
            Ctrl::If(b, t, f) => {
                let (b, _) = map[*b];
                if b != F::zero() {
                    slice.push_aux(index, b.inverse());
                    t.populate_row(ctx, map, index, slice);
                } else {
                    f.populate_row(ctx, map, index, slice);
                }
            }
            Ctrl::IfMany(vars, t, f) => {
                let vals = vars.iter().map(|&var| map[var].0);
                if vals.clone().any(|b| b != F::zero()) {
                    push_inequality_witness(index, slice, vals);
                    t.populate_row(ctx, map, index, slice);
                } else {
                    f.populate_row(ctx, map, index, slice);
                }
            }
        }
    }
}

fn push_inequality_witness<F: PrimeField, I: Iterator<Item = F>>(
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_, F>,
    iter: I,
) {
    let mut found = false;
    for f in iter {
        if !found && f != F::zero() {
            slice.push_aux(index, f.inverse());
            found = true;
        } else {
            slice.push_aux(index, F::zero());
        }
    }
    assert!(found);
}

impl<F: PrimeField32> Op<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, H>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
    ) {
        match self {
            Op::Const(f) => map.push((*f, 0)),
            Op::Add(a, b) => {
                let (a, a_deg) = map[*a];
                let (b, b_deg) = map[*b];
                let deg = a_deg.max(b_deg);
                map.push((a + b, deg));
            }
            Op::Sub(a, b) => {
                let (a, a_deg) = map[*a];
                let (b, b_deg) = map[*b];
                let deg = a_deg.max(b_deg);
                map.push((a - b, deg));
            }
            Op::Mul(a, b) => {
                let (a, a_deg) = map[*a];
                let (b, b_deg) = map[*b];
                let deg = a_deg + b_deg;
                let f = a * b;
                if deg < 2 {
                    map.push((f, deg));
                } else {
                    map.push((f, 1));
                    slice.push_aux(index, f);
                }
            }
            Op::Inv(a) => {
                let (a, a_deg) = map[*a];
                let f = a.inverse();
                if a_deg == 0 {
                    map.push((f, 0));
                } else {
                    map.push((f, 1));
                    slice.push_aux(index, f);
                }
            }
            Op::Not(a) => {
                let (a, a_deg) = map[*a];
                let d = if a.is_zero() { F::zero() } else { a.inverse() };
                let f = if a.is_zero() { F::one() } else { F::zero() };
                if a_deg == 0 {
                    map.push((f, 0));
                } else {
                    map.push((f, 1));
                    slice.push_aux(index, d);
                    slice.push_aux(index, f);
                }
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| map[*a].0).collect::<List<_>>();
                let query_map = &ctx.queries.func_queries()[*idx];
                let result = query_map.get(&args).expect("Cannot find query result");
                for f in result.expect_output().iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                let lookup = ctx.requires.next().expect("Not enough require hints");
                let require = lookup.into_require();
                slice.push_aux(index, require.prev_nonce);
                slice.push_aux(index, require.prev_count);
                slice.push_aux(index, require.count_inv);
            }
            Op::PreImg(idx, out) => {
                let out = out.iter().map(|a| map[*a].0).collect::<List<_>>();
                let inv_map = ctx.queries.inv_func_queries[*idx]
                    .as_ref()
                    .expect("Function not invertible");
                let inp = inv_map.get(&out).expect("Cannot find preimage");
                for f in inp.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                let lookup = ctx.requires.next().expect("Not enough require hints");
                let require = lookup.into_require();
                slice.push_aux(index, require.prev_nonce);
                slice.push_aux(index, require.prev_count);
                slice.push_aux(index, require.count_inv);
            }
            Op::Store(args) => {
                let mem_idx = mem_index_from_len(args.len());
                let query_map = &ctx.queries.mem_queries[mem_idx];
                let args = args.iter().map(|a| map[*a].0).collect::<List<_>>();
                let i = query_map
                    .get_index_of(&args)
                    .expect("Cannot find query result");
                let f = F::from_canonical_usize(i + 1);
                map.push((f, 1));
                slice.push_aux(index, f);
                let lookup = ctx.requires.next().expect("Not enough require hints");
                let require = lookup.into_require();
                slice.push_aux(index, require.prev_nonce);
                slice.push_aux(index, require.prev_count);
                slice.push_aux(index, require.count_inv);
            }
            Op::Load(len, ptr) => {
                let mem_idx = mem_index_from_len(*len);
                let query_map = &ctx.queries.mem_queries[mem_idx];
                let ptr = map[*ptr].0.as_canonical_u32() as usize;
                let (args, _) = query_map
                    .get_index(ptr - 1)
                    .expect("Cannot find query result");
                for f in args.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                let lookup = ctx.requires.next().expect("Not enough require hints");
                let require = lookup.into_require();
                slice.push_aux(index, require.prev_nonce);
                slice.push_aux(index, require.prev_count);
                slice.push_aux(index, require.count_inv);
            }
            Op::Hash(preimg) => {
                let preimg = preimg.iter().map(|a| map[*a].0).collect::<List<_>>();
                let witness_size = ctx.hasher.witness_size(preimg.len());
                let mut witness = vec![F::zero(); witness_size];
                let img = ctx.hasher.populate_witness(&preimg, &mut witness);
                for f in img {
                    map.push((f, 1));
                    slice.push_aux(index, f);
                }
                for f in witness {
                    slice.push_aux(index, f);
                }
            }
            Op::Debug(..) => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        air::debug::{debug_constraints_collecting_queries, TraceQueries},
        func,
        lair::{
            demo_toplevel,
            execute::{QueryRecord, Shard, ShardingConfig},
            field_from_u32,
            hasher::LurkHasher,
            lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
            toplevel::Toplevel,
            trace::LayoutSizes,
        },
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use sphinx_core::{
        air::MachineAir,
        stark::{MachineRecord, StarkMachine},
        utils::BabyBearPoseidon2,
    };

    use super::FuncChip;

    #[test]
    fn lair_layout_sizes_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();

        let factorial = toplevel.get_by_name("factorial");
        let out = factorial.compute_layout_sizes(&toplevel);
        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 1,
            aux: 8,
            sel: 2,
        };
        assert_eq!(out, expected_layout_sizes);
    }

    #[test]
    fn lair_trace_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let args = &[F::from_canonical_u32(5)];
        toplevel.execute_by_name("factorial", args, &mut queries);
        let trace = factorial_chip.generate_trace(&Shard::new(&queries));
        #[rustfmt::skip]
        let expected_trace = [
            // in order: nonce, n, 1/n, fact(n-1), prev_nonce, prev_count, count_inv, n*fact(n-1), last_nonce, last_count and selectors
            0, 5, 1610612737, 24, 0, 0, 1, 120, 0, 1, 1, 0,
            1, 4, 1509949441,  6, 0, 0, 1,  24, 0, 1, 1, 0,
            2, 3, 1342177281,  2, 0, 0, 1,   6, 1, 1, 1, 0,
            3, 2, 1006632961,  1, 0, 0, 1,   2, 2, 1, 1, 0,
            4, 1,          1,  1, 0, 0, 1,   1, 3, 1, 1, 0,
            5, 0,          4,  1, 0, 0, 0,   0, 0, 0, 0, 1,
            // dummy
            6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[F::from_canonical_u32(7)];
        toplevel.execute_by_name("fib", args, &mut queries);
        let trace = fib_chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = [
            // in order: nonce, n, 1/n, 1/(n-1), fib(n-1), prev_nonce, prev_count, count_inv, fib(n-2), prev_nonce, prev_count, count_inv, last_nonce, last_count and selectors
            0, 7,  862828252, 1677721601, 8, 0, 0, 1, 5, 1, 1, 1006632961, 0, 1, 0, 0, 1,
            1, 6, 1677721601, 1610612737, 5, 0, 0, 1, 3, 2, 1, 1006632961, 0, 1, 0, 0, 1,
            2, 5, 1610612737, 1509949441, 3, 0, 0, 1, 2, 3, 1, 1006632961, 0, 2, 0, 0, 1,
            3, 4, 1509949441, 1342177281, 2, 0, 0, 1, 1, 4, 1, 1006632961, 1, 2, 0, 0, 1,
            4, 3, 1342177281, 1006632961, 1, 0, 0, 1, 1, 5, 1, 1006632961, 2, 2, 0, 0, 1,
            5, 2, 1006632961,          1, 1, 0, 0, 1, 0, 0, 0,          1, 3, 2, 0, 0, 1,
            6, 1,          4,          2, 0, 0, 0, 0, 0, 0, 0,          0, 0, 0, 0, 1, 0,
            7, 0,          5,          1, 0, 0, 0, 0, 0, 0, 0,          0, 0, 0, 1, 0, 0,
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[test]
    fn lair_match_trace_test() {
        let func_e = func!(
        fn test(n, m): [1] {
            let one = 1;
            match n {
                0 => {
                    return one
                }
                1 => {
                    return m
                }
                2 => {
                    let res = mul(m, m);
                    return res
                }
                3 => {
                    let res = mul(m, m);
                    let res = mul(res, res);
                    return res
                }
            };
            let pred = sub(n, one);
            let res = call(test, pred, m);
            return res
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 2,
            aux: 10,
            sel: 5,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let args = &[F::from_canonical_u32(5), F::from_canonical_u32(2)];
        let mut queries = QueryRecord::new(&toplevel);
        toplevel.execute_by_name("test", args, &mut queries);
        let trace = test_chip.generate_trace(&Shard::new(&queries));
        #[rustfmt::skip]
        let expected_trace = [
            // The big numbers in the trace are the inverted elements, the witnesses of
            // the inequalities that appear on the default case. Note that the branch
            // that does not follow the default will reuse the slots for the inverted
            // elements to minimize the number of columns
            0, 5, 2, 1610612737, 1509949441, 1342177281, 1006632961, 16, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1,
            1, 4, 2, 1509949441, 1342177281, 1006632961,          1, 16, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1,
            2, 3, 2,          4,         16,          1,          1,  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0,
            // dummy
            3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[test]
    fn lair_inner_match_trace_test() {
        let func_e = func!(
        fn test(n, m): [1] {
            let zero = 0;
            let one = 1;
            let two = 2;
            let three = 3;
            match n {
                0 => {
                    match m {
                        0 => {
                            return zero
                        }
                        1 => {
                            return one
                        }
                    }
                }
                1 => {
                    match m {
                        0 => {
                            return two
                        }
                        1 => {
                            return three
                        }
                    }
                }
            }
        });
        let toplevel = Toplevel::<F, LurkHasher>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 2,
            aux: 2,
            sel: 4,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let zero = &[F::from_canonical_u32(0), F::from_canonical_u32(0)];
        let one = &[F::from_canonical_u32(0), F::from_canonical_u32(1)];
        let two = &[F::from_canonical_u32(1), F::from_canonical_u32(0)];
        let three = &[F::from_canonical_u32(1), F::from_canonical_u32(1)];
        let mut queries = QueryRecord::new(&toplevel);
        let test_func = toplevel.get_by_name("test");
        toplevel.execute(test_func, zero, &mut queries);
        toplevel.execute(test_func, one, &mut queries);
        toplevel.execute(test_func, two, &mut queries);
        toplevel.execute(test_func, three, &mut queries);
        let trace = test_chip.generate_trace(&Shard::new(&queries));

        let expected_trace = [
            // nonce, two inputs, last_nonce, last_count, selectors
            0, 0, 0, 0, 1, 1, 0, 0, 0, //
            1, 0, 1, 0, 1, 0, 1, 0, 0, //
            2, 1, 0, 0, 1, 0, 0, 1, 0, //
            3, 1, 1, 0, 1, 0, 0, 0, 1, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[ignore]
    #[test]
    fn lair_shard_test() {
        type H = LurkHasher;
        let func_ack = func!(
        fn ackermann(m, n): [1] {
            let one = 1;
            match m {
                0 => {
                    let ret = add(n, one);
                    return ret
                }
            };
            let m_minus_one = sub(m, one);
            match n {
                0 => {
                    let ret = call(ackermann, m_minus_one, one);
                    return ret
                }
            };
            let n_minus_one = sub(n, one);
            let inner = call(ackermann, m, n_minus_one);
            let ret = call(ackermann, m_minus_one, inner);
            return ret
        });
        let toplevel = Toplevel::<F, H>::new(&[func_ack]);
        let ack_chip = FuncChip::from_name("ackermann", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let f = F::from_canonical_usize;
        // These inputs should perform enough recursive calls (5242889) to
        // generate 2 shards with the default shard size of 1 << 22
        let inp = &[f(3), f(18)];
        let out = toplevel.execute_by_name("ackermann", inp, &mut queries);
        // For constant m = 3, A(3, n) = 2^(n + 3) - 3
        assert_eq!(out[0], f(2097149));

        let lair_chips = build_lair_chip_vector(&ack_chip);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(config, build_chip_vector(&ack_chip), 0);

        let (pk, _vk) = machine.setup(&LairMachineProgram);
        let shard = Shard::new(&queries);
        let shards = shard.clone().shard(&ShardingConfig::default());
        assert!(
            shards.len() > 1,
            "lair_shard_test must have more than one shard"
        );

        let mut lookup_queries = Vec::new();
        for shard in shards.iter() {
            let queries: Vec<_> = lair_chips
                .iter()
                .map(|chip| {
                    if chip.included(shard) {
                        let trace = chip.generate_trace(shard, &mut Shard::default());
                        debug_constraints_collecting_queries(chip, &[], None, &trace)
                    } else {
                        Default::default()
                    }
                })
                .collect();
            lookup_queries.extend(queries.into_iter());
        }
        TraceQueries::verify_many(lookup_queries);

        machine.debug_constraints(&pk, shard.clone());
    }
}
