use p3_field::Field;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
};

pub(crate) struct Columns<T>(Vec<T>);

type Degree = u8;

impl<F: Field + Ord> Func<F> {
    pub fn compute_width(&self, toplevel: &Toplevel<F>) -> usize {
        let args = self.input_size;
        let map = &mut vec![1; args];
        args + self.body.compute_width(map, toplevel)
    }

    pub fn generate_row(&self, args: &[F], row: &mut Vec<F>, toplevel: &Toplevel<F>) {
        assert_eq!(self.input_size(), args.len(), "Argument mismatch");
        let map = &mut args.to_vec();
        // One column per input
        row.extend(args);
        self.body.generate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Block<F> {
    fn compute_width(&self, map: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
        let num = self.ctrl.compute_width(map, toplevel);
        self.ops
            .iter()
            .fold(num, |acc, op| acc + op.compute_width(map, toplevel))
    }

    fn generate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
        self.ops
            .iter()
            .for_each(|op| op.generate_row(map, row, toplevel));
        self.ctrl.generate_row(map, row, toplevel);
    }
}

impl<F: Field + Ord> Ctrl<F> {
    fn compute_width(&self, map: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
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

    fn generate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
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
    fn compute_width(&self, map: &mut Vec<Degree>, toplevel: &Toplevel<F>) -> usize {
        match self {
            Op::Const(..) => {
                map.push(0);
                0
            }
            Op::Add(a, b) | Op::Sub(a, b) => {
                let deg = map[*a].max(map[*b]);
                map.push(deg);
                0
            }
            Op::Mul(a, b) => {
                let deg = map[*a] + map[*b];
                // degree less than 2 does not need allocation
                if deg < 2 {
                    map.push(deg);
                    0
                } else {
                    map.push(1);
                    1
                }
            }
            Op::Inv(a) => {
                let a_deg = map[*a];
                if a_deg == 0 {
                    map.push(0);
                    0
                } else {
                    map.push(1);
                    1
                }
            }
            Op::Call(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx as usize).unwrap();
                let out_size = func.output_size;
                map.extend(vec![1; out_size]);
                0
            }
        }
    }

    fn generate_row(&self, map: &mut Vec<F>, row: &mut Vec<F>, toplevel: &Toplevel<F>) {
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
