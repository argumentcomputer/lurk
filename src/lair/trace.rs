use p3_field::PrimeField;
use p3_matrix::dense::RowMajorMatrix;
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use crate::lair::execute::mem_index_from_len;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    execute::QueryRecord,
    func_chip::{ColumnLayout, Degree, FuncChip, LayoutSizes},
    hasher::Hasher,
    List,
};

// TODO: Should we reuse the existing CallCtx instead and remove this? (probably yes if we can)
#[derive(Clone)]
struct FuncCtx<F> {
    func_idx: usize,
    call_inp: List<F>,
}

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

impl<'a, F: PrimeField, H: Hasher<F>> FuncChip<'a, F, H> {
    /// Generates the trace containing only queries with non-zero multiplicities
    pub fn generate_trace_sequential(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let func_queries = &queries.func_queries()[self.func.index];
        let width = self.width();
        let non_dummy_height = func_queries.len();
        let height = non_dummy_height.next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        // initializing nonces
        rows.chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| row[0] = F::from_canonical_usize(i));
        for (i, (args, _)) in func_queries.iter().enumerate() {
            let start = i * width;
            let index = &mut ColumnIndex::default();
            let row = &mut rows[start..start + width];
            let slice = &mut ColumnMutSlice::from_slice(row, self.layout_sizes);
            self.func
                .populate_row(args, index, slice, queries, &self.toplevel.hasher);
        }
        RowMajorMatrix::new(rows, width)
    }

    /// Per-row parallel version of `generate_trace_sequential`
    pub fn generate_trace_parallel(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let func_queries = &queries.func_queries()[self.func.index];
        let width = self.width();
        let non_dummy_height = func_queries.len();
        let height = non_dummy_height.next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        // initializing nonces
        rows.chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| row[0] = F::from_canonical_usize(i));
        let non_dummies = &mut rows[0..func_queries.len() * width];
        non_dummies
            .par_chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| {
                let (args, _) = func_queries.get_index(i).unwrap();
                let index = &mut ColumnIndex::default();
                let slice = &mut ColumnMutSlice::from_slice(row, self.layout_sizes);
                self.func
                    .populate_row(args, index, slice, queries, &self.toplevel.hasher);
            });
        RowMajorMatrix::new(rows, width)
    }
}

impl<F: PrimeField> Func<F> {
    pub fn populate_row<H: Hasher<F>>(
        &self,
        args: &[F],
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        hasher: &H,
    ) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.iter().map(|arg| (*arg, 1)).collect();
        // Context of which function this is
        let func_ctx = FuncCtx {
            func_idx: self.index,
            call_inp: args.into(),
        };
        // One column per input
        args.iter().for_each(|arg| slice.push_input(index, *arg));
        self.body
            .populate_row(&func_ctx, map, index, slice, queries, hasher);
    }
}

impl<F: PrimeField> Block<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        func_ctx: &FuncCtx<F>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        hasher: &H,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(func_ctx, map, index, slice, queries, hasher));
        self.ctrl
            .populate_row(func_ctx, map, index, slice, queries, hasher);
    }
}

impl<F: PrimeField> Ctrl<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        func_ctx: &FuncCtx<F>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        hasher: &H,
    ) {
        match self {
            Ctrl::Return(ident, _) => {
                slice.sel[*ident] = F::one();
                // Fixme: last_nonce, last_count
                let query_map = &queries.func_queries()[func_ctx.func_idx];
                let result = query_map
                    .get(&func_ctx.call_inp)
                    .expect("Cannot find query result");
                let last_count = result.callers_nonces.len();
                let (_, last_nonce, _) = result
                    .callers_nonces
                    .last()
                    .expect("Must have at least one caller");
                slice.push_aux(index, F::from_canonical_usize(*last_nonce));
                slice.push_aux(index, F::from_canonical_usize(last_count));
            }
            Ctrl::Match(t, cases) => {
                let (t, _) = map[*t];
                if let Some(branch) = cases.branches.get(&t) {
                    branch.populate_row(func_ctx, map, index, slice, queries, hasher);
                } else {
                    for (f, _) in cases.branches.iter() {
                        slice.push_aux(index, (t - *f).inverse());
                    }
                    let branch = cases.default.as_ref().expect("No match");
                    branch.populate_row(func_ctx, map, index, slice, queries, hasher);
                }
            }
            Ctrl::MatchMany(vars, cases) => {
                let vals = vars.iter().map(|&var| map[var].0).collect();
                if let Some(branch) = cases.branches.get(&vals) {
                    branch.populate_row(func_ctx, map, index, slice, queries, hasher);
                } else {
                    for (fs, _) in cases.branches.iter() {
                        let diffs = vals.iter().zip(fs.iter()).map(|(val, f)| *val - *f);
                        push_inequality_witness(index, slice, diffs);
                    }
                    let branch = cases.default.as_ref().expect("No match");
                    branch.populate_row(func_ctx, map, index, slice, queries, hasher);
                }
            }
            Ctrl::If(b, t, f) => {
                let (b, _) = map[*b];
                if b != F::zero() {
                    slice.push_aux(index, b.inverse());
                    t.populate_row(func_ctx, map, index, slice, queries, hasher);
                } else {
                    f.populate_row(func_ctx, map, index, slice, queries, hasher);
                }
            }
            Ctrl::IfMany(vars, t, f) => {
                let vals = vars.iter().map(|&var| map[var].0);
                if vals.clone().any(|b| b != F::zero()) {
                    push_inequality_witness(index, slice, vals);
                    t.populate_row(func_ctx, map, index, slice, queries, hasher);
                } else {
                    f.populate_row(func_ctx, map, index, slice, queries, hasher);
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

impl<F: PrimeField> Op<F> {
    fn populate_row<H: Hasher<F>>(
        &self,
        func_ctx: &FuncCtx<F>,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
        hasher: &H,
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
            Op::Call(idx, inp, call_ident) => {
                let args = inp.iter().map(|a| map[*a].0).collect::<List<_>>();
                let query_map = &queries.func_queries()[*idx];
                let result = query_map.get(&args).expect("Cannot find query result");
                for f in result.expect_output().iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                // Fixme: prev_nonce, prev_count, count_inv
                let nonce: usize = slice
                    .nonce
                    .as_canonical_biguint()
                    .try_into()
                    .expect("Nonce is larger than usize");
                let prev_count = result
                    .callers_nonces
                    .get_index_of(&(func_ctx.func_idx, nonce, *call_ident))
                    .expect("Cannot find caller nonce entry");
                if prev_count == 0 {
                    // we are the first require, fill in hardcoded provide values
                    slice.push_aux(index, F::from_canonical_usize(0)); // prev_nonce
                    slice.push_aux(index, F::from_canonical_usize(0)); // prev_count
                    slice.push_aux(index, F::from_canonical_usize(1).inverse());
                // count_inv
                } else {
                    // we are somewhere in the middle of the list, get the predecessor
                    let (_, prev_nonce, _) =
                        result.callers_nonces.get_index(prev_count - 1).unwrap();
                    slice.push_aux(index, F::from_canonical_usize(*prev_nonce));
                    slice.push_aux(index, F::from_canonical_usize(prev_count));
                    slice.push_aux(index, F::from_canonical_usize(prev_count + 1).inverse());
                }
            }
            Op::PreImg(idx, out, call_ident) => {
                let out = out.iter().map(|a| map[*a].0).collect::<List<_>>();
                let inv_map = queries.inv_func_queries[*idx]
                    .as_ref()
                    .expect("Function not invertible");
                let inp = inv_map.get(&out).expect("Cannot find preimage");
                for f in inp.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
                // Fixme: prev_nonce, prev_count, count_inv
                let query_map = &queries.func_queries()[*idx];
                let query_result = query_map.get(inp).expect("Cannot find query result");
                let nonce: usize = slice
                    .nonce
                    .as_canonical_biguint()
                    .try_into()
                    .expect("Nonce is larger than usize");
                let prev_count = query_result
                    .callers_nonces
                    .get_index_of(&(func_ctx.func_idx, nonce, *call_ident))
                    .expect("Cannot find caller nonce entry");
                if prev_count == 0 {
                    // we are the first require, fill in hardcoded provide values
                    slice.push_aux(index, F::from_canonical_usize(0)); // prev_nonce
                    slice.push_aux(index, F::from_canonical_usize(0)); // prev_count
                    slice.push_aux(index, F::from_canonical_usize(1).inverse());
                // count_inv
                } else {
                    // we are somewhere in the middle of the list, get the predecessor
                    let (_, prev_nonce, _) = query_result
                        .callers_nonces
                        .get_index(prev_count - 1)
                        .unwrap();
                    slice.push_aux(index, F::from_canonical_usize(*prev_nonce));
                    slice.push_aux(index, F::from_canonical_usize(prev_count));
                    slice.push_aux(index, F::from_canonical_usize(prev_count + 1).inverse());
                }
            }
            Op::Store(args) => {
                let mem_idx = mem_index_from_len(args.len());
                let query_map = &queries.mem_queries[mem_idx];
                let args = args.iter().map(|a| map[*a].0).collect::<List<_>>();
                let i = query_map
                    .get_index_of(&args)
                    .expect("Cannot find query result");
                let f = F::from_canonical_usize(i + 1);
                map.push((f, 1));
                slice.push_aux(index, f);
            }
            Op::Load(len, ptr) => {
                let mem_idx = mem_index_from_len(*len);
                let query_map = &queries.mem_queries[mem_idx];
                let ptr: usize = map[*ptr].0.as_canonical_biguint().try_into().unwrap();
                let (args, _) = query_map
                    .get_index(ptr - 1)
                    .expect("Cannot find query result");
                for f in args.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
            }
            Op::Hash(preimg) => {
                let preimg = preimg.iter().map(|a| map[*a].0).collect::<List<_>>();
                let witness_size = hasher.witness_size(preimg.len());
                let mut witness = vec![F::zero(); witness_size];
                let img = hasher.populate_witness(&preimg, &mut witness);
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
        func,
        lair::{
            demo_toplevel, execute::QueryRecord, field_from_u32, hasher::LurkHasher,
            toplevel::Toplevel, trace::LayoutSizes,
        },
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    use super::FuncChip;

    #[test]
    fn lair_layout_sizes_test() {
        let toplevel = demo_toplevel::<_, LurkHasher>();

        let factorial = toplevel.get_by_name("factorial").unwrap();
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
        let queries = &mut QueryRecord::new(&toplevel);

        let args = &[F::from_canonical_u32(5)];
        toplevel.execute_by_name("factorial", args, queries);
        let trace = factorial_chip.generate_trace_parallel(queries);
        let expected_trace = [
            // in order: nonce, n, 1/n, fact(n-1), prev_nonce, prev_count, count_inv, n*fact(n-1), last_nonce, last_count and selectors
            0, 5, 1610612737, 24, 0, 0, 1, 120, 0, 1, 1, 0, //
            1, 4, 1509949441, 6, 0, 0, 1, 24, 0, 1, 1, 0, //
            2, 3, 1342177281, 2, 0, 0, 1, 6, 1, 1, 1, 0, //
            3, 2, 1006632961, 1, 0, 0, 1, 2, 2, 1, 1, 0, //
            4, 1, 1, 1, 0, 0, 1, 1, 3, 1, 1, 0, //
            5, 0, 4, 1, 0, 0, 0, 0, 0, 0, 0, 1, //
            // dummy
            6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
            7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);

        let args = &[F::from_canonical_u32(7)];
        toplevel.execute_by_name("fib", args, queries);
        let trace = fib_chip.generate_trace_parallel(queries);

        let expected_trace = [
            // in order: nonce, n, 1/n, 1/(n-1), fib(n-1), prev_nonce, prev_count, count_inv, fib(n-2), prev_nonce, prev_count, count_inv, last_nonce, last_count and selectors
            0, 7, 862828252, 1677721601, 13, 0, 0, 1, 8, 1, 1, 1006632961, 0, 1, 0, 0, 1, //
            1, 6, 1677721601, 1610612737, 8, 0, 0, 1, 5, 2, 1, 1006632961, 0, 1, 0, 0, 1, //
            2, 5, 1610612737, 1509949441, 5, 0, 0, 1, 3, 3, 1, 1006632961, 0, 2, 0, 0, 1, //
            3, 4, 1509949441, 1342177281, 3, 0, 0, 1, 2, 4, 1, 1006632961, 1, 2, 0, 0, 1, //
            4, 3, 1342177281, 1006632961, 2, 0, 0, 1, 1, 5, 1, 1006632961, 2, 2, 0, 0, 1, //
            5, 2, 1006632961, 1, 1, 0, 0, 1, 1, 0, 0, 1, 3, 2, 0, 0, 1, //
            6, 1, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, //
            7, 0, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, //
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
        let queries = &mut QueryRecord::new(&toplevel);
        toplevel.execute_by_name("test", args, queries);
        let trace = test_chip.generate_trace_parallel(queries);
        let expected_trace = [
            // The big numbers in the trace are the inverted elements, the witnesses of
            // the inequalities that appear on the default case. Note that the branch
            // that does not follow the default will reuse the slots for the inverted
            // elements to minimize the number of columns
            0, 5, 2, 1610612737, 1509949441, 1342177281, 1006632961, 16, 0, 0, 1, 0, 1, 0, 0, 0,
            0, //
            1, 1, 4, 2, 1509949441, 1342177281, 1006632961, 1, 16, 0, 0, 1, 0, 1, 0, 0, 0, 0,
            1, //
            2, 3, 2, 4, 16, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, //
            // dummy
            3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
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
        let queries = &mut QueryRecord::new(&toplevel);
        let test_func = toplevel.get_by_name("test").unwrap();
        toplevel.execute(test_func, zero, queries);
        toplevel.execute(test_func, one, queries);
        toplevel.execute(test_func, two, queries);
        toplevel.execute(test_func, three, queries);
        let trace = test_chip.generate_trace_parallel(queries);

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
}
