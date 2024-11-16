use p3_air::BaseAir;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chipset::Chipset,
    provenance::{DepthLessThan, DEPTH_LESS_THAN_SIZE, DEPTH_W},
    toplevel::Toplevel,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct ColumnLayout<Value, Slice> {
    pub(crate) nonce: Value,
    pub(crate) input: Slice,
    pub(crate) output: Slice,
    pub(crate) aux: Slice,
    pub(crate) sel: Slice,
}

pub type LayoutSizes = ColumnLayout<usize, usize>;

impl LayoutSizes {
    #[inline]
    fn total(&self) -> usize {
        self.nonce + self.input + self.aux + self.sel + self.output
    }
}

pub struct FuncChip<'a, F, C1: Chipset<F>, C2: Chipset<F>> {
    pub(crate) func: &'a Func<F>,
    pub(crate) toplevel: &'a Toplevel<F, C1, C2>,
    pub(crate) layout_sizes: LayoutSizes,
}

impl<'a, F, C1: Chipset<F>, C2: Chipset<F>> FuncChip<'a, F, C1, C2> {
    #[inline]
    pub fn from_name(name: &'static str, toplevel: &'a Toplevel<F, C1, C2>) -> Self {
        let func = toplevel.func_by_name(name);
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_index(idx: usize, toplevel: &'a Toplevel<F, C1, C2>) -> Self {
        let func = toplevel.func_by_index(idx);
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_func(func: &'a Func<F>, toplevel: &'a Toplevel<F, C1, C2>) -> Self {
        let layout_sizes = func.compute_layout_sizes(toplevel);
        Self {
            func,
            toplevel,
            layout_sizes,
        }
    }

    #[inline]
    pub fn from_toplevel(toplevel: &'a Toplevel<F, C1, C2>) -> Vec<Self> {
        toplevel
            .func_map
            .values()
            .map(|func| FuncChip::from_func(func, toplevel))
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
    pub fn toplevel(&self) -> &Toplevel<F, C1, C2> {
        self.toplevel
    }
}

impl<F: Sync, C1: Chipset<F>, C2: Chipset<F>> BaseAir<F> for FuncChip<'_, F, C1, C2> {
    fn width(&self) -> usize {
        self.width()
    }
}

pub type Degree = u8;

impl<F> Func<F> {
    pub fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        toplevel: &Toplevel<F, C1, C2>,
    ) -> LayoutSizes {
        let input = self.input_size;
        // last nonce, last count
        let mut aux = 2;
        // provenance and range check
        if self.partial {
            let num_requires = (DEPTH_W / 2) + (DEPTH_W % 2);
            aux += DEPTH_W + 3 * num_requires;
        }
        let mut sel = 0;
        let output = self.output_size;
        let degrees = &mut vec![1; input];
        self.body
            .compute_layout_sizes(degrees, toplevel, &mut aux, &mut sel);
        LayoutSizes {
            nonce: 1,
            input,
            aux,
            sel,
            output,
        }
    }
}

impl<F> Block<F> {
    fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, C1, C2>,
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
    fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, C1, C2>,
        aux: &mut usize,
        sel: &mut usize,
    ) {
        match self {
            Ctrl::Return(..) => {
                // exactly one selector per return
                *sel += 1;
            }
            Ctrl::Choose(_, _, branches) => {
                let degrees_len = degrees.len();
                let mut max_aux = *aux;
                branches.iter().for_each(|block| {
                    let block_aux = &mut aux.clone();
                    block.compute_layout_sizes(degrees, toplevel, block_aux, sel);
                    degrees.truncate(degrees_len);
                    max_aux = max_aux.max(*block_aux);
                });
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
    fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, C1, C2>,
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
                let func = toplevel.func_by_index(*f_idx);
                let out_size = func.output_size;
                // output of function, prev_nonce, prev_count, count_inv
                *aux += out_size + 3;
                // dependency provenance and witness
                if func.partial {
                    let require_size = DepthLessThan::<F>::num_requires();
                    *aux += DEPTH_W + DEPTH_LESS_THAN_SIZE + 3 * require_size;
                }
                degrees.extend(vec![1; out_size]);
            }
            Op::PreImg(f_idx, ..) => {
                let func = toplevel.func_by_index(*f_idx);
                let inp_size = func.input_size;
                // input of function, prev_nonce, prev_count, count_inv
                *aux += inp_size + 3;
                // dependency provenance and witness
                if func.partial {
                    let require_size = DepthLessThan::<F>::num_requires();
                    *aux += DEPTH_W + DEPTH_LESS_THAN_SIZE + 3 * require_size;
                }
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
                let chip = toplevel.chip_by_index(*chip_idx);
                let require_size = chip.require_size();
                let witness_size = chip.witness_size();
                let aux_size = witness_size + require_size * 3;
                *aux += aux_size;
                degrees.extend(vec![1; aux_size]);
            }
            Op::RangeU8(xs) => {
                let num_requires = (xs.len() / 2) + (xs.len() % 2);
                *aux += 3 * num_requires;
            }
            Op::Emit(_) | Op::Breakpoint | Op::Debug(_) => (),
        }
    }
}
