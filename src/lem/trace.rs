use p3_air::BaseAir;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    execute::QueryRecord,
    toplevel::Toplevel,
    List,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct ColumnLayout<T> {
    input: T,
    output: T,
    aux: T,
    sel: T,
}
pub type Columns<T> = ColumnLayout<Vec<T>>;
pub type ColumnSlice<'a, T> = ColumnLayout<&'a [T]>;
pub type Width = ColumnLayout<usize>;

impl<T: Clone> Columns<T> {
    pub fn new_with_capacity(width: &Width) -> Self {
        let input = Vec::with_capacity(width.input);
        let output = Vec::with_capacity(width.output);
        let aux = Vec::with_capacity(width.aux);
        let sel = Vec::with_capacity(width.sel);
        Self {
            input,
            output,
            aux,
            sel,
        }
    }

    pub fn fill_with_dummy(&mut self, dummy: T) {
        self.input.resize(self.input.capacity(), dummy.clone());
        self.output.resize(self.output.capacity(), dummy.clone());
        self.aux.resize(self.aux.capacity(), dummy.clone());
        self.sel.resize(self.sel.capacity(), dummy);
    }

    pub fn push_input(&mut self, t: T) {
        self.input.push(t)
    }

    pub fn push_output(&mut self, t: T) {
        self.output.push(t)
    }

    pub fn push_aux(&mut self, t: T) {
        self.aux.push(t)
    }

    pub fn push_sel(&mut self, t: T) {
        self.sel.push(t)
    }

    pub fn extend_vec(self, vec: &mut Vec<T>) {
        vec.extend(self.input);
        vec.extend(self.output);
        vec.extend(self.aux);
        vec.extend(self.sel);
    }
}

impl<'a, T> ColumnSlice<'a, T> {
    pub fn from_slice(slice: &'a [T], width: Width) -> Self {
        assert_eq!(
            slice.len(),
            width.input + width.output + width.aux + width.sel
        );
        let mut from = 0;
        let mut to = width.input;
        let input = &slice[from..to];
        from += width.input;
        to += width.output;
        let output = &slice[from..to];
        from += width.output;
        to += width.aux;
        let aux = &slice[from..to];
        from += width.aux;
        to += width.sel;
        let sel = &slice[from..to];
        Self {
            input,
            output,
            aux,
            sel,
        }
    }
}

pub struct FuncChip<'a, F> {
    func: &'a Func<F>,
    toplevel: &'a Toplevel<F>,
    width: Width,
}

impl<'a, F> FuncChip<'a, F> {
    pub fn from_name(name: &'static str, toplevel: &'a Toplevel<F>) -> Self {
        let func = toplevel.get_by_name(name).unwrap();
        let width = func.compute_width(toplevel);
        Self {
            func,
            toplevel,
            width,
        }
    }

    pub fn from_index(idx: usize, toplevel: &'a Toplevel<F>) -> Self {
        let func = toplevel.get_by_index(idx).unwrap();
        let width = func.compute_width(toplevel);
        Self {
            func,
            toplevel,
            width,
        }
    }

    pub fn width(&self) -> usize {
        self.width.input + self.width.output + self.width.aux + self.width.sel
    }

    pub fn func(&self) -> &Func<F> {
        self.func
    }

    pub fn toplevel(&self) -> &Toplevel<F> {
        self.toplevel
    }
}

impl<'a, F: Sync> BaseAir<F> for FuncChip<'a, F> {
    fn width(&self) -> usize {
        self.width.input + self.width.output + self.width.aux + self.width.sel
    }
}

impl<'a, F: Field + Ord> FuncChip<'a, F> {
    pub fn generate_trace(&self, queries: &QueryRecord<F>) -> RowMajorMatrix<F> {
        let index = self.func.index;
        let query_map = &queries.record()[index];
        let mut rows_vec = vec![];
        for (args, res) in query_map.iter() {
            let mult = F::from_canonical_u32(res.mult);
            let row = self.compute_row(mult, args, queries);
            row.extend_vec(&mut rows_vec);
        }

        // padding
        let width = self.width();
        let height = query_map.size();
        let next_pow = height.next_power_of_two().max(4);
        let dummy = vec![F::zero(); (next_pow - height) * width];
        rows_vec.extend(dummy);

        RowMajorMatrix::new(rows_vec, self.width())
    }

    pub fn compute_row(&self, mult: F, args: &[F], queries: &QueryRecord<F>) -> Columns<F> {
        let mut row = Columns::new_with_capacity(&self.width);
        if mult != F::zero() {
            let not_dummy = F::one();
            row.push_aux(mult);
            row.push_sel(not_dummy);
            self.func.populate_row(args, &mut row, queries);
        }
        row.fill_with_dummy(F::zero());
        row
    }
}

type Degree = u8;

impl<F> Func<F> {
    pub fn compute_width(&self, toplevel: &Toplevel<F>) -> Width {
        let input = self.input_size;
        let output = self.output_size;
        // multiplicity and initial selector
        let mut aux = 1;
        let mut sel = 1;
        let degrees = &mut vec![1; input];
        self.body
            .compute_width(degrees, toplevel, &mut aux, &mut sel);
        Width {
            input,
            output,
            aux,
            sel,
        }
    }
}

impl<F> Block<F> {
    fn compute_width(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.compute_width(degrees, toplevel, aux));
        self.ctrl.compute_width(degrees, toplevel, aux, sel);
    }
}

impl<F> Ctrl<F> {
    fn compute_width(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        match self {
            Ctrl::Return(..) => (),
            Ctrl::Match(_, cases) => {
                *sel += cases.size();
                let degrees_len = degrees.len();
                let mut max_aux = *aux;
                for (_, block) in cases.branches.iter() {
                    let block_aux = &mut aux.clone();
                    block.compute_width(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                }
                if let Some(block) = &cases.default {
                    let block_aux = &mut aux.clone();
                    block.compute_width(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                }
                *aux = max_aux;
            }
            Ctrl::If(_, t, f) => {
                *sel += 2;
                let degrees_len = degrees.len();
                let t_aux = &mut aux.clone();
                t.compute_width(degrees, toplevel, t_aux, sel);
                degrees.truncate(degrees_len);
                let f_aux = &mut aux.clone();
                f.compute_width(degrees, toplevel, f_aux, sel);
                degrees.truncate(degrees_len);
                *aux = (*t_aux).max(*f_aux);
            }
        }
    }
}

impl<F> Op<F> {
    fn compute_width(&self, degrees: &mut Vec<Degree>, toplevel: &Toplevel<F>, aux: &mut usize) {
        match self {
            Op::Const(..) => {
                degrees.push(0);
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                let deg = degrees[*a].max(degrees[*b]);
                degrees.push(deg);
            }
            Op::Mul(a, b) => {
                let deg = degrees[*a] + degrees[*b];
                // degree less than 2 does not need allocation
                if deg < 2 {
                    degrees.push(deg);
                } else {
                    degrees.push(1);
                    *aux += 1;
                }
            }
            Op::Inv(a) => {
                let a_deg = degrees[*a];
                if a_deg == 0 {
                    degrees.push(0);
                } else {
                    degrees.push(1);
                    *aux += 1;
                }
            }
            Op::Call(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx as usize).unwrap();
                let out_size = func.output_size;
                *aux += out_size;
                degrees.extend(vec![1; out_size]);
            }
            Op::Pol(..) => {
                todo!()
            }
        }
    }
}

impl<F: Field + Ord> Func<F> {
    pub fn populate_row(&self, args: &[F], row: &mut Columns<F>, queries: &QueryRecord<F>) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.iter().map(|arg| (*arg, 1)).collect();
        // One column per input
        row.input.extend(args);
        self.body.populate_row(map, row, queries);
    }
}

impl<F: Field + Ord> Block<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        row: &mut Columns<F>,
        queries: &QueryRecord<F>,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, row, queries));
        self.ctrl.populate_row(map, row, queries);
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        row: &mut Columns<F>,
        queries: &QueryRecord<F>,
    ) {
        match self {
            Ctrl::Return(out) => out.iter().for_each(|i| row.push_output(map[*i].0)),
            Ctrl::Match(t, cases) => {
                let (t, _) = map[*t];
                let mut sels = vec![F::zero(); cases.size()];
                let match_idx = cases
                    .get_index_of(&t)
                    .unwrap_or_else(|| panic!("No match for value {:?}", t));
                sels[match_idx] = F::one();
                row.sel.extend(&sels);
                let branch = cases.get_index(match_idx).unwrap();
                branch.populate_row(map, row, queries);
            }
            Ctrl::If(b, t, f) => {
                let (b, _) = map[*b];
                if b != F::zero() {
                    row.push_sel(F::one());
                    row.push_sel(F::zero());
                    t.populate_row(map, row, queries);
                } else {
                    row.push_sel(F::zero());
                    row.push_sel(F::one());
                    f.populate_row(map, row, queries);
                }
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn populate_row(
        &self,
        map: &mut Vec<(F, Degree)>,
        row: &mut Columns<F>,
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
                    row.push_aux(f);
                }
            }
            Op::Inv(a) => {
                let (a, a_deg) = map[*a];
                let f = a.inverse();
                if a_deg == 0 {
                    map.push((f, 0));
                } else {
                    map.push((f, 1));
                    row.push_aux(f);
                }
            }
            Op::Pol(..) => {
                todo!()
            }
            Op::Call(idx, inp) => {
                let args = inp.iter().map(|a| map[*a].0).collect::<List<_>>();
                let query_map = &queries.record()[*idx as usize];
                let result = query_map.get(&args).expect("Cannot find query result");
                for f in result.output.iter() {
                    map.push((*f, 1));
                    row.push_aux(*f);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lem::{execute::QueryRecord, field_from_i32, toplevel::Toplevel, trace::Width},
    };

    use p3_baby_bear::BabyBear as F;
    use p3_field::AbstractField;

    use super::FuncChip;

    #[test]
    fn lem_width_test() {
        let func_e = func!(
        fn factorial(n): 1 {
            let one = num(1);
            if n {
                let pred = sub(n, one);
                let m = call(factorial, pred);
                let res = mul(n, m);
                return res
            }
            return one
        });
        let toplevel = Toplevel::<F>::new(&[func_e]);

        let factorial = toplevel.get_by_name("factorial").unwrap();
        let out = factorial.compute_width(&toplevel);
        let expected_width = Width {
            input: 1,
            output: 1,
            aux: 3,
            sel: 3,
        };
        assert_eq!(out, expected_width);
    }

    #[test]
    fn lem_trace_test() {
        let func_e = func!(
        fn factorial(n): 1 {
            let one = num(1);
            if n {
                let pred = sub(n, one);
                let m = call(factorial, pred);
                let res = mul(n, m);
                return res
            }
            return one
        });
        let toplevel = Toplevel::<F>::new(&[func_e]);

        let factorial_chip = FuncChip::from_name("factorial", &toplevel);
        let args = [F::from_canonical_u32(5)].into();
        let queries = &mut QueryRecord::new(&toplevel);
        queries.record_event(&toplevel, factorial_chip.func.index, args);
        let trace = factorial_chip.generate_trace(queries);
        let expected_trace = [
            // in order: input, output, mult, m, res, and selectors
            0, 1, 1, 0, 0, 1, 0, 1, //
            1, 1, 1, 1, 1, 1, 1, 0, //
            2, 2, 1, 1, 2, 1, 1, 0, //
            3, 6, 1, 2, 6, 1, 1, 0, //
            4, 24, 1, 6, 24, 1, 1, 0, //
            5, 120, 1, 24, 120, 1, 1, 0, //
            // dummy
            0, 0, 0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, 0, 0, //
        ]
        .into_iter()
        .map(field_from_i32)
        .collect::<Vec<_>>();
        assert_eq!(trace.values, expected_trace);
    }
}
