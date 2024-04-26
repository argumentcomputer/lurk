use p3_air::BaseAir;
use p3_field::Field;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
};

#[derive(Clone, Debug, Default)]
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

impl<'a, F: Field + Ord> FuncChip<'a, F> {
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

type Degree = u8;

impl<F: Field + Ord> Func<F> {
    pub fn compute_width(&self, toplevel: &Toplevel<F>) -> Width {
        let input = self.input_size;
        let output = self.output_size;
        let mut aux = 0;
        let mut sel = 0;
        let degrees = &mut vec![1; input + output];
        self.body
            .compute_width(degrees, toplevel, &mut aux, &mut sel);
        Width {
            input,
            output,
            aux,
            sel,
        }
    }

    pub fn populate_row(&self, args: &[F], row: &mut Vec<F>, toplevel: &Toplevel<F>) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        let map = &mut args.to_vec();
        // One column per input
        row.extend(args);
        self.body.populate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Block<F> {
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

    fn populate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, row, toplevel));
        self.ctrl.populate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Ctrl<F> {
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
                    let previous_aux = &mut aux.clone();
                    block.compute_width(degrees, toplevel, previous_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*aux);
                }
                if let Some(block) = &cases.default {
                    let previous_aux = &mut aux.clone();
                    block.compute_width(degrees, toplevel, previous_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*aux);
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

    fn populate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
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
                degrees.extend(vec![1; out_size]);
            }
        }
    }

    fn populate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
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
            Op::Call(..) => {
                todo!()
            }
        }
    }
}
