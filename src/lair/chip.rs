use p3_air::BaseAir;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    toplevel::Toplevel,
    List,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct ColumnLayout<T> {
    pub(crate) input: T,
    pub(crate) output: T,
    pub(crate) aux: T,
    pub(crate) sel: T,
}

pub type LayoutSizes = ColumnLayout<usize>;

impl LayoutSizes {
    #[inline]
    fn total(&self) -> usize {
        self.input + self.output + self.aux + self.sel
    }
}

pub struct FuncChip<'a, F> {
    pub(crate) func: &'a Func<F>,
    pub(crate) toplevel: &'a Toplevel<F>,
    pub(crate) layout_sizes: LayoutSizes,
}

impl<'a, F> FuncChip<'a, F> {
    #[inline]
    pub fn from_name(name: &'static str, toplevel: &'a Toplevel<F>) -> Self {
        let func = toplevel.get_by_name(name).expect("Func not found");
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_index(idx: usize, toplevel: &'a Toplevel<F>) -> Self {
        let func = toplevel.get_by_index(idx).expect("Index out of bounds");
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_func(func: &'a Func<F>, toplevel: &'a Toplevel<F>) -> Self {
        let layout_sizes = func.compute_layout_sizes(toplevel);
        Self {
            func,
            toplevel,
            layout_sizes,
        }
    }

    #[inline]
    pub fn from_toplevel(toplevel: &'a Toplevel<F>) -> List<Self> {
        toplevel
            .map
            .get_pairs()
            .iter()
            .map(|(_, func)| FuncChip::from_func(func, toplevel))
            .collect()
    }

    #[inline]
    pub fn width(&self) -> usize {
        self.layout_sizes.total()
    }

    #[inline]
    pub fn func(&self) -> &Func<F> {
        self.func
    }

    #[inline]
    pub fn toplevel(&self) -> &Toplevel<F> {
        self.toplevel
    }
}

impl<'a, F: Sync> BaseAir<F> for FuncChip<'a, F> {
    fn width(&self) -> usize {
        self.width()
    }
}

pub type Degree = u8;

impl<F> Func<F> {
    pub fn compute_layout_sizes(&self, toplevel: &Toplevel<F>) -> LayoutSizes {
        let input = self.input_size;
        let output = self.output_size;
        // first auxiliary is multiplicity
        let mut aux = 1;
        let mut sel = 0;
        let degrees = &mut vec![1; input];
        self.body
            .compute_layout_sizes(degrees, toplevel, &mut aux, &mut sel);
        LayoutSizes {
            input,
            output,
            aux,
            sel,
        }
    }
}

impl<F> Block<F> {
    fn compute_layout_sizes(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        self.ops
            .iter()
            .for_each(|op| op.compute_layout_sizes(degrees, toplevel, aux));
        self.ctrl.compute_layout_sizes(degrees, toplevel, aux, sel);
    }
}

impl<F> Ctrl<F> {
    fn compute_layout_sizes(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        match self {
            Ctrl::Return(..) => *sel += 1,
            Ctrl::Match(_, cases) => {
                let degrees_len = degrees.len();
                let mut max_aux = *aux;
                for (_, block) in cases.branches.iter() {
                    let block_aux = &mut aux.clone();
                    block.compute_layout_sizes(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                }
                if let Some(block) = &cases.default {
                    let block_aux = &mut aux.clone();
                    *block_aux += cases.branches.size();
                    block.compute_layout_sizes(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                }
                *aux = max_aux;
            }
            Ctrl::If(_, t, f) => {
                let degrees_len = degrees.len();
                let t_aux = &mut aux.clone();
                // for proof of inequality we need inversion
                *t_aux += 1;
                t.compute_layout_sizes(degrees, toplevel, t_aux, sel);
                degrees.truncate(degrees_len);
                let f_aux = &mut aux.clone();
                f.compute_layout_sizes(degrees, toplevel, f_aux, sel);
                degrees.truncate(degrees_len);
                *aux = (*t_aux).max(*f_aux);
            }
        }
    }
}

impl<F> Op<F> {
    fn compute_layout_sizes(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F>,
        aux: &mut usize,
    ) {
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
            Op::Not(a) => {
                let a_deg = degrees[*a];
                if a_deg == 0 {
                    degrees.push(0);
                } else {
                    degrees.push(1);
                    *aux += 2;
                }
            }
            Op::Call(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx).unwrap();
                let out_size = func.output_size;
                *aux += out_size;
                degrees.extend(vec![1; out_size]);
            }
            Op::PreImg(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx).unwrap();
                let out_size = func.input_size;
                *aux += out_size;
                degrees.extend(vec![1; out_size]);
            }
            Op::Store(..) => {
                *aux += 1;
                degrees.push(1);
            }
            Op::Load(ptr_size, ..) => {
                *aux += *ptr_size;
                degrees.extend(vec![1; *ptr_size]);
            }
            Op::Debug(..) => (),
        }
    }
}
