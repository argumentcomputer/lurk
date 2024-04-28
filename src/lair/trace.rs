use p3_field::Field;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
};

pub(crate) struct Columns<T>(Vec<T>);

type Degree = u8;

impl<F: Field + Ord> Func<F> {
    pub fn compute_width(&self, toplevel: &Toplevel<F>) -> usize {
        let num_args = self.input_size;
        let degrees = &mut vec![1; num_args];
        num_args + self.body.compute_width(degrees, toplevel)
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
    fn compute_width(&self, degrees: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
        let ctrl_width = self.ctrl.compute_width(degrees, toplevel);
        self.ops.iter().fold(ctrl_width, |acc, op| {
            acc + op.compute_width(degrees, toplevel)
        })
    }

    fn populate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
        self.ops
            .iter()
            .for_each(|op| op.populate_row(map, row, toplevel));
        self.ctrl.populate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn compute_width(&self, degrees: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
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
    fn compute_width(&self, degrees: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
        match self {
            Op::Const(..) => {
                degrees.push(0);
                0
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                let deg = degrees[*a].max(degrees[*b]);
                degrees.push(deg);
                0
            }
            Op::Mul(a, b) => {
                let deg = degrees[*a] + degrees[*b];
                // degree less than 2 does not need allocation
                if deg < 2 {
                    degrees.push(deg);
                    0
                } else {
                    degrees.push(1);
                    1
                }
            }
            Op::Inv(a) => {
                let a_deg = degrees[*a];
                if a_deg == 0 {
                    degrees.push(0);
                    0
                } else {
                    degrees.push(1);
                    1
                }
            }
            Op::Call(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx as usize).unwrap();
                let out_size = func.output_size;
                degrees.extend(vec![1; out_size]);
                0
            }
            Op::Pol(..) => {
                todo!()
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
            Op::Pol(..) => {
                todo!()
            }
            Op::Call(..) => {
                todo!()
            }
        }
    }
}
