use std::{borrow::BorrowMut, slice::Iter};

use p3_field::{PrimeField, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use crate::{
    air::builder::Record, gadgets::bytes::record::DummyBytesRecord,
    lair::execute::mem_index_from_len,
};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chipset::Chipset,
    execute::{QueryRecord, Shard},
    func_chip::{ColumnLayout, Degree, FuncChip, LayoutSizes},
    provenance::{DepthLessThan, DEPTH_LESS_THAN_SIZE, DEPTH_W},
    toplevel::Toplevel,
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
        let (output, slice) = slice.split_at_mut(layout_sizes.output);
        let (aux, slice) = slice.split_at_mut(layout_sizes.aux);
        let (sel, slice) = slice.split_at_mut(layout_sizes.sel);
        assert!(slice.is_empty());
        let nonce = &mut nonce[0];
        Self {
            nonce,
            input,
            aux,
            sel,
            output,
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

    pub fn push_output(&mut self, index: &mut ColumnIndex, t: T) {
        self.output[index.output] = t;
        index.output += 1;
    }
}

impl<F: PrimeField32> ColumnMutSlice<'_, F> {
    pub fn push_provide(&mut self, index: &mut ColumnIndex, lookup: Record) {
        let provide = lookup.into_provide();
        self.push_aux(index, provide.last_nonce);
        self.push_aux(index, provide.last_count);
    }

    pub fn push_require(&mut self, index: &mut ColumnIndex, lookup: Record) {
        let require = lookup.into_require();
        self.push_aux(index, require.prev_nonce);
        self.push_aux(index, require.prev_count);
        self.push_aux(index, require.count_inv);
    }
}

impl<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> FuncChip<'_, F, C1, C2> {
    /// Per-row parallel trace generation
    pub fn generate_trace(&self, shard: &Shard<'_, F>) -> RowMajorMatrix<F> {
        let func_queries = &shard.queries().func_queries()[self.func.index];
        let range = shard.get_func_range(func_queries.len());
        let width = self.width();
        let non_dummy_height = range.len();
        let height = non_dummy_height.next_power_of_two();
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
                let mut depth_requires = result.depth_requires.iter();
                let provide = result.provide;
                let queries = shard.queries();
                result
                    .output
                    .as_ref()
                    .unwrap()
                    .iter()
                    .for_each(|&o| slice.push_output(index, o));
                slice.push_provide(index, provide);
                // provenance and range check
                if self.func.partial {
                    let num_requires = (DEPTH_W / 2) + (DEPTH_W % 2);
                    let depth: [u8; DEPTH_W] = result.depth.to_le_bytes();
                    for b in depth {
                        slice.push_aux(index, F::from_canonical_u8(b));
                    }
                    for _ in 0..num_requires {
                        let lookup = *depth_requires.next().expect("Not enough require hints");
                        slice.push_require(index, lookup);
                    }
                }
                self.func.populate_row(
                    args,
                    index,
                    slice,
                    queries,
                    requires,
                    self.toplevel,
                    result.depth,
                    depth_requires,
                );
            });
        RowMajorMatrix::new(rows, width)
    }
}

struct TraceCtx<'a, F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>> {
    queries: &'a QueryRecord<F>,
    toplevel: &'a Toplevel<F, C1, C2>,
    requires: Iter<'a, Record>,
    depth: u32,
    depth_requires: Iter<'a, Record>,
}

impl<F: PrimeField32> Func<F> {
    #[allow(clippy::too_many_arguments)]
    fn populate_row<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        args: &[F],
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        requires: Iter<'_, Record>,
        toplevel: &Toplevel<F, C1, C2>,
        depth: u32,
        depth_requires: Iter<'_, Record>,
    ) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.iter().map(|arg| (*arg, 1)).collect();
        // Context of which function this is
        let ctx = &mut TraceCtx {
            queries,
            requires,
            toplevel,
            depth,
            depth_requires,
        };
        // One column per input
        args.iter().for_each(|arg| slice.push_input(index, *arg));
        self.body.populate_row(ctx, map, index, slice);
    }
}

impl<F: PrimeField32> Block<F> {
    fn populate_row<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, C1, C2>,
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
    fn populate_row<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, C1, C2>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
    ) {
        match self {
            Ctrl::Return(ident, _) => {
                assert!(ctx.requires.next().is_none());
                assert!(ctx.depth_requires.next().is_none());
                slice.sel[*ident] = F::one();
            }
            Ctrl::Choose(var, cases, branches) => {
                let val = map[*var].0;
                let i = cases.match_case(&val).expect("No match");
                let branch = &branches[*i];
                branch.populate_row(ctx, map, index, slice);
            }
            Ctrl::ChooseMany(vars, cases) => {
                let vals = vars.iter().map(|&var| map[var].0).collect();
                let branch = cases.match_case(&vals).expect("No match");
                branch.populate_row(ctx, map, index, slice);
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

fn push_depth<F: PrimeField32, C1: Chipset<F>, C2: Chipset<F>>(
    index: &mut ColumnIndex,
    slice: &mut ColumnMutSlice<'_, F>,
    ctx: &mut TraceCtx<'_, F, C1, C2>,
    depth: u32,
) {
    let depth_bytes: [u8; DEPTH_W] = depth.to_le_bytes();
    for b in depth_bytes {
        slice.push_aux(index, F::from_canonical_u8(b));
    }
    let bytes = &mut DummyBytesRecord;
    let witness: &mut [F] = &mut [F::zero(); DEPTH_LESS_THAN_SIZE];
    let less_than: &mut DepthLessThan<F> = witness.borrow_mut();
    less_than.populate(&depth, &ctx.depth, bytes);
    witness.iter().for_each(|w| slice.push_aux(index, *w));
    for _ in 0..DepthLessThan::<F>::num_requires() {
        let lookup = *ctx.depth_requires.next().expect("Not enough require hints");
        slice.push_require(index, lookup);
    }
}

impl<F: PrimeField32> Op<F> {
    fn populate_row<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        ctx: &mut TraceCtx<'_, F, C1, C2>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
    ) {
        match self {
            Op::AssertEq(..) => {}
            Op::AssertNe(a, b) => {
                let diffs = a.iter().zip(b.iter()).map(|(a, b)| map[*a].0 - map[*b].0);
                push_inequality_witness(index, slice, diffs);
            }
            Op::Contains(a, b) => {
                let (b, _) = map[*b];
                a.iter().map(|a| map[*a].0 - b).reduce(|acc, diff| {
                    let acc = acc * diff;
                    slice.push_aux(index, acc);
                    acc
                });
            }
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
                let func = ctx.toplevel.func_by_index(*idx);
                let args = inp.iter().map(|a| map[*a].0).collect::<List<_>>();
                let query_map = &ctx.queries.func_queries()[*idx];
                let result = query_map.get(&args).expect("Cannot find query result");
                for f in result.expect_output().iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                let lookup = *ctx.requires.next().expect("Not enough require hints");
                slice.push_require(index, lookup);
                // dependency provenance and constraints
                if func.partial {
                    push_depth(index, slice, ctx, result.depth);
                }
            }
            Op::PreImg(idx, out, _) => {
                let func = ctx.toplevel.func_by_index(*idx);
                let out = out.iter().map(|a| map[*a].0).collect::<List<_>>();
                let inv_map = ctx.queries.inv_func_queries[*idx]
                    .as_ref()
                    .expect("Function not invertible");
                let inp = inv_map.get(&out).expect("Cannot find preimage");
                // dependency provenance and constraints
                for f in inp.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                let lookup = *ctx.requires.next().expect("Not enough require hints");
                slice.push_require(index, lookup);
                if func.partial {
                    let query_map = &ctx.queries.func_queries()[*idx];
                    let result = query_map.get(inp).expect("Cannot find query result");
                    push_depth(index, slice, ctx, result.depth);
                };
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
                let lookup = *ctx.requires.next().expect("Not enough require hints");
                slice.push_require(index, lookup);
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
                let lookup = *ctx.requires.next().expect("Not enough require hints");
                slice.push_require(index, lookup);
            }
            Op::ExternCall(chip_idx, input) => {
                let chip = ctx.toplevel.chip_by_index(*chip_idx);

                let input = input.iter().map(|a| map[*a].0).collect::<List<_>>();
                let mut witness = vec![F::zero(); chip.witness_size()];

                let out = chip.populate_witness(&input, &mut witness);
                for f in out {
                    map.push((f, 1));
                }

                // order: witness, requires
                for f in witness {
                    slice.push_aux(index, f);
                }
                for _ in 0..chip.require_size() {
                    let lookup = *ctx.requires.next().expect("Not enough require hints");
                    slice.push_require(index, lookup);
                }
            }
            Op::RangeU8(xs) => {
                let num_requires = (xs.len() / 2) + (xs.len() % 2);
                for _ in 0..num_requires {
                    let lookup = *ctx.requires.next().expect("Not enough require hints");
                    slice.push_require(index, lookup);
                }
            }
            Op::Emit(_) | Op::Breakpoint | Op::Debug(_) => (),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        air::debug::debug_chip_constraints_and_queries_with_sharding,
        func,
        lair::{
            chipset::NoChip,
            demo_toplevel,
            execute::{QueryRecord, Shard, ShardingConfig},
            field_from_u32,
            lair_chip::{build_chip_vector, build_lair_chip_vector, LairMachineProgram},
            toplevel::Toplevel,
            trace::LayoutSizes,
        },
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;
    use sphinx_core::{
        stark::{LocalProver, MachineRecord, StarkGenericConfig, StarkMachine},
        utils::{BabyBearPoseidon2, SphinxCoreOpts},
    };

    use super::FuncChip;

    #[test]
    fn lair_layout_sizes_test() {
        let toplevel = demo_toplevel::<F>();

        let factorial = toplevel.func_by_name("factorial");
        let out = factorial.compute_layout_sizes(&toplevel);
        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 1,
            aux: 8,
            sel: 2,
            output: 1,
        };
        assert_eq!(out, expected_layout_sizes);
    }

    #[test]
    fn lair_trace_test() {
        let toplevel = demo_toplevel::<F>();
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let args = &[F::from_canonical_u32(5)];
        toplevel
            .execute_by_name("factorial", args, &mut queries, None)
            .unwrap();
        let trace = factorial_chip.generate_trace(&Shard::new(&queries));
        #[rustfmt::skip]
        let expected_trace = [
            // in order: nonce, n, 1/n, fact(n-1), prev_nonce, prev_count, count_inv, n*fact(n-1), last_nonce, last_count and selectors
            0, 5, 120, 0, 1, 1610612737, 24, 0, 0, 1, 120, 0, 1,
            1, 4,  24, 0, 1, 1509949441,  6, 0, 0, 1,  24, 0, 1,
            2, 3,   6, 1, 1, 1342177281,  2, 0, 0, 1,   6, 0, 1,
            3, 2,   2, 2, 1, 1006632961,  1, 0, 0, 1,   2, 0, 1,
            4, 1,   1, 3, 1,          1,  1, 0, 0, 1,   1, 0, 1,
            5, 0,   1, 4, 1,          0,  0, 0, 0, 0,   0, 1, 0,
            // dummy
            6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);

        let mut queries = QueryRecord::new(&toplevel);
        let args = &[F::from_canonical_u32(7)];
        toplevel
            .execute_by_name("fib", args, &mut queries, None)
            .unwrap();
        let trace = fib_chip.generate_trace(&Shard::new(&queries));

        #[rustfmt::skip]
        let expected_trace = [
            // in order: nonce, n, fib(n), last_nonce, last_count, 1/n, 1/(n-1), fib(n-1), prev_nonce, prev_count, count_inv, fib(n-2), prev_nonce, prev_count, count_inv and selectors
            0, 7, 13, 0, 1, 862828252, 1677721601, 8, 0, 0, 1, 5, 1, 1, 1006632961, 0, 0, 1,
            1, 6, 8, 0, 1, 1677721601, 1610612737, 5, 0, 0, 1, 3, 2, 1, 1006632961, 0, 0, 1,
            2, 5, 5, 0, 2, 1610612737, 1509949441, 3, 0, 0, 1, 2, 3, 1, 1006632961, 0, 0, 1,
            3, 4, 3, 1, 2, 1509949441, 1342177281, 2, 0, 0, 1, 1, 4, 1, 1006632961, 0, 0, 1,
            4, 3, 2, 2, 2, 1342177281, 1006632961, 1, 0, 0, 1, 1, 5, 1, 1006632961, 0, 0, 1,
            5, 2, 1, 3, 2, 1006632961,          1, 1, 0, 0, 1, 0, 0, 0,          1, 0, 0, 1,
            6, 1, 1, 4, 2,          0,          0, 0, 0, 0, 0, 0, 0, 0,          0, 0, 1, 0,
            7, 0, 0, 5, 1,          0,          0, 0, 0, 0, 0, 0, 0, 0,          0, 1, 0, 0,
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 2,
            aux: 10,
            sel: 5,
            output: 1,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let args = &[F::from_canonical_u32(5), F::from_canonical_u32(2)];
        let mut queries = QueryRecord::new(&toplevel);
        toplevel
            .execute_by_name("test", args, &mut queries, None)
            .unwrap();
        let trace = test_chip.generate_trace(&Shard::new(&queries));
        #[rustfmt::skip]
        let expected_trace = [
            // The big numbers in the trace are the inverted elements, the witnesses of
            // the inequalities that appear on the default case. Note that the branch
            // that does not follow the default will reuse the slots for the inverted
            // elements to minimize the number of columns
            0, 5, 2, 16, 0, 1, 1610612737, 1509949441, 1342177281, 1006632961, 16, 0, 0, 1, 0, 0, 0, 0, 1,
            1, 4, 2, 16, 0, 1, 1509949441, 1342177281, 1006632961,          1, 16, 0, 0, 1, 0, 0, 0, 0, 1,
            2, 3, 2, 16, 1, 1,          4,         16,          0,          0,  0, 0, 0, 0, 0, 0, 0, 1, 0,
            // dummy
            3, 0, 0,  0, 0, 0,          0,          0,          0,          0,  0, 0, 0, 0, 0, 0, 0, 0, 0,
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
        let toplevel = Toplevel::<F, NoChip, NoChip>::new_pure(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            nonce: 1,
            input: 2,
            aux: 2,
            sel: 4,
            output: 1,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let zero = &[F::from_canonical_u32(0), F::from_canonical_u32(0)];
        let one = &[F::from_canonical_u32(0), F::from_canonical_u32(1)];
        let two = &[F::from_canonical_u32(1), F::from_canonical_u32(0)];
        let three = &[F::from_canonical_u32(1), F::from_canonical_u32(1)];
        let mut queries = QueryRecord::new(&toplevel);
        let test_func = toplevel.func_by_name("test");
        toplevel
            .execute(test_func, zero, &mut queries, None)
            .unwrap();
        toplevel
            .execute(test_func, one, &mut queries, None)
            .unwrap();
        toplevel
            .execute(test_func, two, &mut queries, None)
            .unwrap();
        toplevel
            .execute(test_func, three, &mut queries, None)
            .unwrap();
        let trace = test_chip.generate_trace(&Shard::new(&queries));

        let expected_trace = [
            // nonce, two inputs, output, last_nonce, last_count, selectors
            0, 0, 0, 0, 0, 1, 1, 0, 0, 0, //
            1, 0, 1, 1, 0, 1, 0, 1, 0, 0, //
            2, 1, 0, 2, 0, 1, 0, 0, 1, 0, //
            3, 1, 1, 3, 0, 1, 0, 0, 0, 1, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[ignore]
    #[test]
    fn lair_shard_test() {
        sphinx_core::utils::setup_logger();
        type C = NoChip;
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
        let toplevel = Toplevel::<F, C, C>::new_pure(&[func_ack]);
        let ack_chip = FuncChip::from_name("ackermann", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let f = F::from_canonical_usize;
        // These inputs should perform enough recursive calls (5242889) to
        // generate 2 shards with the default shard size of 1 << 22
        let inp = &[f(3), f(18)];
        let out = toplevel
            .execute_by_name("ackermann", inp, &mut queries, None)
            .unwrap();
        // For constant m = 3, A(3, n) = 2^(n + 3) - 3
        assert_eq!(out[0], f(2097149));

        let lair_chips = build_lair_chip_vector(&ack_chip);

        let shard = Shard::new(&queries);
        let shards = shard.clone().shard(&ShardingConfig::default());
        assert!(
            shards.len() > 1,
            "lair_shard_test must have more than one shard"
        );

        debug_chip_constraints_and_queries_with_sharding(
            &queries,
            &lair_chips,
            Some(ShardingConfig::default()),
        );

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&ack_chip),
            queries.expect_public_values().len(),
        );

        let (pk, vk) = machine.setup(&LairMachineProgram);
        let mut challenger_p = machine.config().challenger();
        let mut challenger_v = machine.config().challenger();
        let shard = Shard::new(&queries);

        machine.debug_constraints(&pk, shard.clone());
        let opts = SphinxCoreOpts::default();
        let proof = machine.prove::<LocalProver<_, _>>(&pk, shard, &mut challenger_p, opts);
        machine
            .verify(&vk, &proof, &mut challenger_v)
            .expect("proof verifies");
    }
}
