use p3_air::BaseAir;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chipset::Chipset,
    toplevel::Toplevel,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct ColumnLayout<Value, Slice> {
    pub(crate) nonce: Value,
    pub(crate) input: Slice,
    pub(crate) aux: Slice,
    pub(crate) sel: Slice,
}

pub type LayoutSizes = ColumnLayout<usize, usize>;

impl LayoutSizes {
    #[inline]
    fn total(&self) -> usize {
        self.nonce + self.input + self.aux + self.sel
    }
}

pub struct FuncChip<'a, F, H: Chipset<F>> {
    pub(crate) func: &'a Func<F>,
    pub(crate) toplevel: &'a Toplevel<F, H>,
    pub(crate) layout_sizes: LayoutSizes,
}

impl<'a, F, H: Chipset<F>> FuncChip<'a, F, H> {
    #[inline]
    pub fn from_name(name: &'static str, toplevel: &'a Toplevel<F, H>) -> Self {
        let func = toplevel.get_by_name(name);
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_index(idx: usize, toplevel: &'a Toplevel<F, H>) -> Self {
        let func = toplevel.get_by_index(idx);
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_func(func: &'a Func<F>, toplevel: &'a Toplevel<F, H>) -> Self {
        let layout_sizes = func.compute_layout_sizes(toplevel);
        Self {
            func,
            toplevel,
            layout_sizes,
        }
    }

    #[inline]
    pub fn from_toplevel(toplevel: &'a Toplevel<F, H>) -> Vec<Self> {
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
    pub fn toplevel(&self) -> &Toplevel<F, H> {
        self.toplevel
    }
}

impl<'a, F: Sync, H: Chipset<F>> BaseAir<F> for FuncChip<'a, F, H> {
    fn width(&self) -> usize {
        self.width()
    }
}

pub type Degree = u8;

impl<F> Func<F> {
    pub fn compute_layout_sizes<H: Chipset<F>>(&self, toplevel: &Toplevel<F, H>) -> LayoutSizes {
        let input = self.input_size;
        let mut aux = 0;
        let mut sel = 0;
        let degrees = &mut vec![1; input];
        self.body
            .compute_layout_sizes(degrees, toplevel, &mut aux, &mut sel);
        LayoutSizes {
            nonce: 1,
            input,
            aux,
            sel,
        }
    }
}

impl<F> Block<F> {
    fn compute_layout_sizes<H: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, H>,
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
    fn compute_layout_sizes<H: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, H>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        match self {
            Ctrl::Return(..) => {
                // exactly one selector per return
                *sel += 1;
                // last nonce, last count
                *aux += 2;
            }
            Ctrl::Choose(_, cases, branches) => {
                let degrees_len = degrees.len();
                let mut max_aux = *aux;
                let mut process = |block: &Block<_>| {
                    let block_aux = &mut aux.clone();
                    block.compute_layout_sizes(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                };
                branches.iter().for_each(&mut process);
                if let Some(block) = cases.default.as_ref() {
                    process(block)
                };
                *aux = max_aux;
            }
            Ctrl::ChooseMany(_, cases) => {
                let degrees_len = degrees.len();
                let mut max_aux = *aux;
                let mut process = |block: &Block<_>| {
                    let block_aux = &mut aux.clone();
                    block.compute_layout_sizes(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                };
                cases.branches.iter().for_each(|(_, block)| process(block));
                if let Some(block) = cases.default.as_ref() {
                    process(block)
                };
                *aux = max_aux;
            }
        }
    }
}

impl<F> Op<F> {
    fn compute_layout_sizes<H: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, H>,
        aux: &mut usize,
    ) {
        match self {
            Op::AssertEq(..) => {}
            Op::AssertNe(a, _) => {
                *aux += a.len();
            }
            Op::Contains(a, _) => {
                *aux += a.len() - 1;
            }
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
                let func = toplevel.get_by_index(*f_idx);
                let out_size = func.output_size;
                // output of function, prev_nonce, prev_count, count_inv
                *aux += out_size + 3;
                degrees.extend(vec![1; out_size]);
            }
            Op::PreImg(f_idx, ..) => {
                let func = toplevel.get_by_index(*f_idx);
                let inp_size = func.input_size;
                // input of function, prev_nonce, prev_count, count_inv
                *aux += inp_size + 3;
                degrees.extend(vec![1; inp_size]);
            }
            Op::Store(..) => {
                *aux += 4;
                degrees.push(1);
            }
            Op::Load(ptr_size, ..) => {
                *aux += *ptr_size + 3;
                degrees.extend(vec![1; *ptr_size]);
            }
            Op::ExternCall(chip_idx, _) => {
                let chip = toplevel.get_chip_by_index(*chip_idx);
                let require_size = chip.require_size();
                let witness_size = chip.witness_size();
                let aux_size = witness_size + require_size * 3;
                *aux += aux_size;
                degrees.extend(vec![1; aux_size]);
            }
            Op::Debug(..) => (),
            Op::RangeU8(_) => {
                *aux += 3;
            }
        }
    }
}
