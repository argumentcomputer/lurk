use p3_air::BaseAir;
use p3_field::Field;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
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

impl<T> Columns<T> {
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
    pub fn compute_row(&self, args: &[F]) -> Columns<F> {
        let mut row = Columns::new_with_capacity(&self.width);
        self.func.populate_row(args, &mut row, self.toplevel);
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
            Op::Pol(limbs) => {
                todo!()
            }
            Op::Call(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx as usize).unwrap();
                let out_size = func.output_size;
                println!("Hey {}", out_size);
                *aux += out_size;
                degrees.extend(vec![1; out_size]);
            }
        }
    }
}

impl<F: Field + Ord> Func<F> {
    pub fn populate_row(&self, args: &[F], row: &mut Columns<F>, toplevel: &Toplevel<F>) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        // Variable to value map
        let map = &mut args.to_vec();
        // One column per input
        row.input.extend(args);
        self.body.populate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Block<F> {
    fn populate_row(&self, map: &mut Vec<F>, row: &mut Columns<F>, toplevel: &Toplevel<F>) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, row, toplevel));
        self.ctrl.populate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn populate_row(&self, map: &mut Vec<F>, row: &mut Columns<F>, toplevel: &Toplevel<F>) {
        match self {
            Ctrl::Return(..) => {
                todo!()
            }
            Ctrl::Match(..) => {
                todo!()
            }
            Ctrl::If(..) => {
                todo!()
            }
        }
    }
}

impl<F: Field + Ord> Op<F> {
    fn populate_row(&self, map: &mut Vec<F>, row: &mut Columns<F>, toplevel: &Toplevel<F>) {
        match self {
            Op::Const(..) => {
                todo!()
            }
            Op::Add(..) => {
                todo!()
            }
            Op::Sub(..) => {
                todo!()
            }
            Op::Mul(..) => {
                todo!()
            }
            Op::Inv(..) => {
                todo!()
            }
            Op::Pol(..) => {
                todo!()
            }
            Op::Call(..) => {
                todo!()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lem::{toplevel::Toplevel, trace::Width},
    };

    use p3_baby_bear::BabyBear as F;

    #[test]
    fn lem_width_test() {
        let func_e = func!(
        fn test(n): 1 {
            let one = num(1);
            match n {
                0 => {
                    return one
                }
            };
            let pred = sub(n, one);
            let m = call(test, pred);
            let res = mul(n, m);
            return res
        });
        let toplevel = Toplevel::<F>::new(&[func_e]);

        let test = toplevel.get_by_name("test").unwrap();
        let out = test.compute_width(&toplevel);
        let expected_width = Width {
            input: 1,
            output: 1,
            aux: 3,
            sel: 3,
        };
        assert_eq!(out, expected_width);
    }
}
