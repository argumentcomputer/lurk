use p3_field::PrimeField;
use p3_matrix::dense::RowMajorMatrix;
use rayon::{
    iter::{IndexedParallelIterator, ParallelIterator},
    slice::ParallelSliceMut,
};

use crate::lair::execute::mem_index_from_len;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chip::{ColumnLayout, Degree, FuncChip, LayoutSizes},
    execute::QueryRecord,
    List,
};

pub type ColumnIndex = ColumnLayout<usize>;
pub type ColumnMutSlice<'a, T> = ColumnLayout<&'a mut [T]>;

impl<'a, T> ColumnMutSlice<'a, T> {
    pub fn from_slice(slice: &'a mut [T], layout_sizes: LayoutSizes) -> Self {
        let (input, slice) = slice.split_at_mut(layout_sizes.input);
        let (output, slice) = slice.split_at_mut(layout_sizes.output);
        let (aux, slice) = slice.split_at_mut(layout_sizes.aux);
        let (sel, slice) = slice.split_at_mut(layout_sizes.sel);
        assert!(slice.is_empty());
        Self {
            input,
            output,
            aux,
            sel,
        }
    }

    pub fn push_input(&mut self, index: &mut ColumnIndex, t: T) {
        self.input[index.input] = t;
        index.input += 1;
    }

    pub fn push_output(&mut self, index: &mut ColumnIndex, t: T) {
        self.output[index.output] = t;
        index.output += 1;
    }

    pub fn push_aux(&mut self, index: &mut ColumnIndex, t: T) {
        self.aux[index.aux] = t;
        index.aux += 1;
    }
}

impl<'a, F: PrimeField> FuncChip<'a, F> {
    pub fn generate_trace(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let query_map = &queries.func_queries()[self.func.index];
        let width = self.width();
        let height = query_map.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        for (i, (args, res)) in query_map.iter().enumerate() {
            let start = i * width;
            let index = &mut ColumnIndex::default();
            let row = &mut rows[start..start + width];
            let slice = &mut ColumnMutSlice::from_slice(row, self.layout_sizes);
            slice.push_aux(index, F::from_canonical_u32(res.mult));
            self.func.populate_row(args, index, slice, queries);
        }
        RowMajorMatrix::new(rows, width)
    }

    pub fn generate_trace_parallel(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let func_queries = Vec::from_iter(&queries.func_queries()[self.func.index]);
        let width = self.width();
        let height = func_queries.len().next_power_of_two().max(4);
        let mut rows = vec![F::zero(); height * width];
        let non_dummies = &mut rows[0..func_queries.len() * width];
        non_dummies
            .par_chunks_mut(width)
            .enumerate()
            .for_each(|(i, row)| {
                let (args, res) = func_queries[i];
                let index = &mut ColumnIndex::default();
                let slice = &mut ColumnMutSlice::from_slice(row, self.layout_sizes);
                slice.push_aux(index, F::from_canonical_u32(res.mult));
                self.func.populate_row(args, index, slice, queries);
            });
        RowMajorMatrix::new(rows, width)
    }
}

impl<F: PrimeField> Func<F> {
    pub fn populate_row(
        &self,
        args: &[F],
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
    ) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.iter().map(|arg| (*arg, 1)).collect();
        // One column per input
        args.iter().for_each(|arg| slice.push_input(index, *arg));
        self.body.populate_row(map, index, slice, queries);
    }
}

impl<F: PrimeField> Block<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, index, slice, queries));
        self.ctrl.populate_row(map, index, slice, queries);
    }
}

impl<F: PrimeField> Ctrl<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
    ) {
        match self {
            Ctrl::Return(ident, out) => {
                slice.sel[*ident] = F::one();
                out.iter().for_each(|i| slice.push_output(index, map[*i].0))
            }
            Ctrl::Match(t, cases) => {
                let (t, _) = map[*t];
                if let Some(branch) = cases.branches.get(&t) {
                    branch.populate_row(map, index, slice, queries);
                } else {
                    let branch = cases.default.as_ref().expect("No match");
                    branch.populate_row(map, index, slice, queries);
                    for (f, _) in cases.branches.iter() {
                        slice.push_aux(index, (t - *f).inverse());
                    }
                }
            }
            Ctrl::If(b, t, f) => {
                let (b, _) = map[*b];
                if b != F::zero() {
                    t.populate_row(map, index, slice, queries);
                    slice.push_aux(index, b.inverse());
                } else {
                    f.populate_row(map, index, slice, queries);
                }
            }
        }
    }
}

impl<F: PrimeField> Op<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        index: &mut ColumnIndex,
        slice: &mut ColumnMutSlice<'_, F>,
        queries: &QueryRecord<F>,
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
                let query_map = &queries.func_queries()[*idx];
                let result = query_map.get(&args).expect("Cannot find query result");
                for f in result.output.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
            }
            Op::PreImg(idx, inp) => {
                let args = inp.iter().map(|a| map[*a].0).collect::<List<_>>();
                let inv_map = queries.inv_func_queries[*idx]
                    .as_ref()
                    .expect("Function not invertible");
                let result = inv_map.get(&args).expect("Cannot find preimage");
                for f in result.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
                }
            }
            Op::Store(args) => {
                let idx = mem_index_from_len(args.len());
                let query_map = &queries.mem_queries[idx];
                let args = args.iter().map(|a| map[*a].0).collect::<List<_>>();
                let i = query_map
                    .get_index_of(&args)
                    .expect("Cannot find query result");
                let f = F::from_canonical_usize(i + 1);
                map.push((f, 1));
                slice.push_aux(index, f);
            }
            Op::Load(len, ptr) => {
                let idx = mem_index_from_len(*len);
                let query_map = &queries.mem_queries[idx];
                let ptr: usize = map[*ptr].0.as_canonical_biguint().try_into().unwrap();
                let (args, _) = query_map
                    .get_index(ptr - 1)
                    .expect("Cannot find query result");
                for f in args.iter() {
                    map.push((*f, 1));
                    slice.push_aux(index, *f);
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
            demo_toplevel, execute::QueryRecord, field_from_u32, toplevel::Toplevel,
            trace::LayoutSizes,
        },
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    use super::FuncChip;

    #[test]
    fn lair_layout_sizes_test() {
        let toplevel = demo_toplevel::<F>();

        let factorial = toplevel.get_by_name("factorial").unwrap();
        let out = factorial.compute_layout_sizes(&toplevel);
        let expected_layout_sizes = LayoutSizes {
            input: 1,
            output: 1,
            aux: 4,
            sel: 2,
        };
        assert_eq!(out, expected_layout_sizes);
    }

    #[test]
    fn lair_trace_test() {
        let toplevel = demo_toplevel::<F>();
        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let fib_chip = FuncChip::from_name("fib", &toplevel);
        let queries = &mut QueryRecord::new(&toplevel);

        let args = [F::from_canonical_u32(5)].into();
        factorial_chip.execute(args, queries);
        let trace = factorial_chip.generate_trace_parallel(queries);
        let expected_trace = [
            // in order: n, output, mult, fact(n-1), n*fact(n-1), 1/n, and selectors
            0, 1, 1, 0, 0, 0, 0, 1, //
            1, 1, 1, 1, 1, 1, 1, 0, //
            2, 2, 1, 1, 2, 1006632961, 1, 0, //
            3, 6, 1, 2, 6, 1342177281, 1, 0, //
            4, 24, 1, 6, 24, 1509949441, 1, 0, //
            5, 120, 1, 24, 120, 1610612737, 1, 0, //
            // dummy
            0, 0, 0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);

        let args = [F::from_canonical_u32(7)].into();
        fib_chip.execute(args, queries);
        let trace = fib_chip.generate_trace_parallel(queries);

        let expected_trace = [
            // in order: n, output, mult, fib(n-1), fib(n-2), 1/n, 1/(n-1), and selectors
            0, 1, 1, 0, 0, 0, 0, 1, 0, 0, //
            1, 1, 2, 0, 0, 0, 0, 0, 1, 0, //
            2, 2, 2, 1, 1, 1006632961, 1, 0, 0, 1, //
            3, 3, 2, 2, 1, 1342177281, 1006632961, 0, 0, 1, //
            4, 5, 2, 3, 2, 1509949441, 1342177281, 0, 0, 1, //
            5, 8, 2, 5, 3, 1610612737, 1509949441, 0, 0, 1, //
            6, 13, 1, 8, 5, 1677721601, 1610612737, 0, 0, 1, //
            7, 21, 1, 13, 8, 862828252, 1677721601, 0, 0, 1, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[test]
    fn lair_match_trace_test() {
        let func_e = func!(
        fn test(n, m): 1 {
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
        let toplevel = Toplevel::<F>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            input: 2,
            output: 1,
            aux: 6,
            sel: 5,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let args = [F::from_canonical_u32(5), F::from_canonical_u32(2)].into();
        let queries = &mut QueryRecord::new(&toplevel);
        test_chip.execute(args, queries);
        let trace = test_chip.generate_trace_parallel(queries);
        let expected_trace = [
            // The big numbers in the trace are the inverted elements, the witnesses of
            // the inequalities that appear on the default case. Note that the branch
            // that does not follow the default will reuse the slots for the inverted
            // elements to minimize the number of columns
            3, 2, 16, 1, 4, 16, 0, 0, 0, 0, 0, 0, 1, 0, //
            4, 2, 16, 1, 16, 1509949441, 1342177281, 1006632961, 1, 0, 0, 0, 0, 1, //
            5, 2, 16, 1, 16, 1610612737, 1509949441, 1342177281, 1006632961, 0, 0, 0, 0, 1, //
            // dummy
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }

    #[test]
    fn lair_inner_match_trace_test() {
        let func_e = func!(
        fn test(n, m): 1 {
            let zero = 0;
            let one = 1;
            let two = 2;
            let three = 3;
            match n {
                0 => {
                    match m {
                        0 => {
                            return zero;
                        }
                        1 => {
                            return one;
                        }
                    }
                }
                1 => {
                    match m {
                        0 => {
                            return two;
                        }
                        1 => {
                            return three;
                        }
                    }
                }
            }
        });
        let toplevel = Toplevel::<F>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);

        let expected_layout_sizes = LayoutSizes {
            input: 2,
            output: 1,
            aux: 1,
            sel: 4,
        };
        assert_eq!(test_chip.layout_sizes, expected_layout_sizes);

        let zero = [F::from_canonical_u32(0), F::from_canonical_u32(0)].into();
        let one = [F::from_canonical_u32(0), F::from_canonical_u32(1)].into();
        let two = [F::from_canonical_u32(1), F::from_canonical_u32(0)].into();
        let three = [F::from_canonical_u32(1), F::from_canonical_u32(1)].into();
        let queries = &mut QueryRecord::new(&toplevel);
        test_chip.execute(zero, queries);
        test_chip.execute(one, queries);
        test_chip.execute(two, queries);
        test_chip.execute(three, queries);
        let trace = test_chip.generate_trace_parallel(queries);

        let expected_trace = [
            // two inputs, one output, multiplicity, selectors
            0, 0, 0, 1, 1, 0, 0, 0, //
            0, 1, 1, 1, 0, 1, 0, 0, //
            1, 0, 2, 1, 0, 0, 1, 0, //
            1, 1, 3, 1, 0, 0, 0, 1, //
        ]
        .into_iter()
        .map(field_from_u32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }
}
