use p3_air::BaseAir;

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    chipset::Chipset,
    expr::ReturnGroup,
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
    pub(crate) return_group: ReturnGroup,
}

impl<'a, F, C1: Chipset<F>, C2: Chipset<F>> FuncChip<'a, F, C1, C2> {
    #[inline]
    pub fn from_name_main(name: &'static str, toplevel: &'a Toplevel<F, C1, C2>) -> Self {
        let func = toplevel.func_by_name(name);
        Self::from_func(func, 0, toplevel)
    }

    #[inline]
    pub fn from_index(idx: usize, group: ReturnGroup, toplevel: &'a Toplevel<F, C1, C2>) -> Self {
        let func = toplevel.func_by_index(idx);
        Self::from_func(func, group, toplevel)
    }

    #[inline]
    pub fn from_func(
        func: &'a Func<F>,
        return_group: ReturnGroup,
        toplevel: &'a Toplevel<F, C1, C2>,
    ) -> Self {
        let layout_sizes = func.compute_layout_sizes(return_group, toplevel);
        Self {
            func,
            toplevel,
            layout_sizes,
            return_group,
        }
    }

    #[inline]
    pub fn from_toplevel(toplevel: &'a Toplevel<F, C1, C2>) -> Vec<Self> {
        toplevel
            .func_map
            .values()
            .flat_map(|func| {
                func.return_groups
                    .iter()
                    .map(|g| FuncChip::from_func(func, *g, toplevel))
            })
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
        group: ReturnGroup,
        toplevel: &Toplevel<F, C1, C2>,
    ) -> LayoutSizes {
        let degrees = &mut vec![1; self.input_size];
        let mut layout = self
            .body
            .compute_layout_sizes(group, degrees, toplevel)
            .expect("Group {group} doesn't exist");
        layout.nonce = 1;
        layout.input = self.input_size;
        layout.output = self.output_size;
        // last nonce, last count
        layout.aux += 2;
        // provenance and range check
        if self.partial {
            let num_requires = (DEPTH_W / 2) + (DEPTH_W % 2);
            layout.aux += DEPTH_W + 3 * num_requires;
        }
        layout
    }
}

impl<F> Block<F> {
    fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        group: ReturnGroup,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, C1, C2>,
    ) -> Option<LayoutSizes> {
        let mut aux = 0;
        self.ops
            .iter()
            .for_each(|op| op.compute_layout_sizes(degrees, toplevel, &mut aux));
        let mut layout = self.ctrl.compute_layout_sizes(group, degrees, toplevel)?;
        layout.aux += aux;
        Some(layout)
    }
}

impl<F> Ctrl<F> {
    fn compute_layout_sizes<C1: Chipset<F>, C2: Chipset<F>>(
        &self,
        group: ReturnGroup,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, C1, C2>,
    ) -> Option<LayoutSizes> {
        let mut layout = LayoutSizes::default();
        match self {
            Ctrl::Return(_, _, return_group) => {
                // exactly one selector per return
                if group != *return_group {
                    return None;
                }
                layout.sel += 1;
            }
            Ctrl::Choose(_, cases, branches) => {
                let degrees_len = degrees.len();
                let mut process = |block: &Block<_>| {
                    if let Some(block_layout) = block.compute_layout_sizes(group, degrees, toplevel)
                    {
                        degrees.truncate(degrees_len);
                        layout.sel += block_layout.sel;
                        layout.aux = layout.aux.max(block_layout.aux);
                    }
                };
                branches.iter().for_each(&mut process);
                if let Some(block) = cases.default.as_ref() {
                    process(block);
                };
            }
            Ctrl::ChooseMany(_, cases) => {
                let degrees_len = degrees.len();
                let mut process = |block: &Block<_>| {
                    if let Some(block_layout) = block.compute_layout_sizes(group, degrees, toplevel)
                    {
                        degrees.truncate(degrees_len);
                        layout.sel += block_layout.sel;
                        layout.aux = layout.aux.max(block_layout.aux);
                    }
                };
                cases.branches.iter().for_each(|(_, block)| process(block));
                if let Some(block) = cases.default.as_ref() {
                    process(block);
                };
            }
        };
        Some(layout)
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
