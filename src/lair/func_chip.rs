use p3_air::BaseAir;
use p3_field::{Field, PrimeField};
use p3_matrix::dense::RowMajorMatrix;
use sphinx_core::air::{EventLens, MachineAir, WithEvents};

use super::{
    bytecode::{Block, Ctrl, Func, Op},
    execute::QueryRecord,
    hasher::Hasher,
    lair_chip::LairMachineProgram,
    toplevel::Toplevel,
};

#[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
pub struct ColumnLayout<T> {
    pub(crate) input: T,
    pub(crate) aux: T,
    pub(crate) sel: T,
}

pub type LayoutSizes = ColumnLayout<usize>;

impl LayoutSizes {
    #[inline]
    fn total(&self) -> usize {
        self.input + self.aux + self.sel
    }
}

pub struct FuncChip<'a, F, H: Hasher<F>> {
    pub(crate) func: &'a Func<F>,
    pub(crate) toplevel: &'a Toplevel<F, H>,
    pub(crate) layout_sizes: LayoutSizes,
}

impl<'a, F, H: Hasher<F>> FuncChip<'a, F, H> {
    #[inline]
    pub fn from_name(name: &'static str, toplevel: &'a Toplevel<F, H>) -> Self {
        let func = toplevel.get_by_name(name).expect("Func not found");
        Self::from_func(func, toplevel)
    }

    #[inline]
    pub fn from_index(idx: usize, toplevel: &'a Toplevel<F, H>) -> Self {
        let func = toplevel.get_by_index(idx).expect("Index out of bounds");
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

impl<'a, F: Sync, H: Hasher<F>> BaseAir<F> for FuncChip<'a, F, H> {
    fn width(&self) -> usize {
        self.width()
    }
}

pub type Degree = u8;

impl<F> Func<F> {
    pub fn compute_layout_sizes<H: Hasher<F>>(&self, toplevel: &Toplevel<F, H>) -> LayoutSizes {
        let input = self.input_size;
        // first auxiliary is multiplicity
        let mut aux = 1;
        let mut sel = 0;
        let degrees = &mut vec![1; input];
        self.body
            .compute_layout_sizes(degrees, toplevel, &mut aux, &mut sel);
        LayoutSizes { input, aux, sel }
    }
}

impl<F> Block<F> {
    fn compute_layout_sizes<H: Hasher<F>>(
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
    fn compute_layout_sizes<H: Hasher<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, H>,
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
            Ctrl::MatchMany(vars, cases) => {
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
                    // It is assumed that all arrays have the same length and matches
                    // the number of variables in the match statement
                    let arr_size = vars.len();
                    *block_aux += cases.branches.size() * arr_size;
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
            Ctrl::IfMany(vars, t, f) => {
                let degrees_len = degrees.len();
                let t_aux = &mut aux.clone();
                *t_aux += vars.len();
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
    fn compute_layout_sizes<H: Hasher<F>>(
        &self,
        degrees: &mut Vec<Degree>,
        toplevel: &Toplevel<F, H>,
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
            Op::Hash(preimg) => {
                let hasher = &toplevel.hasher;
                let img_size = hasher.img_size();
                let witness_size = hasher.witness_size(preimg.len());
                let aux_size = img_size + witness_size;
                *aux += aux_size;
                degrees.extend(vec![1; aux_size]);
            }
            Op::Debug(..) => (),
        }
    }
}

impl<'a, 'b, F: Field, H: Hasher<F>> WithEvents<'a> for FuncChip<'b, F, H> {
    type Events = &'a QueryRecord<F>;
}

impl<'a, F: Field, H: Hasher<F>> EventLens<FuncChip<'a, F, H>> for QueryRecord<F> {
    fn events(&self) -> <FuncChip<'a, F, H> as WithEvents<'_>>::Events {
        self
    }
}

impl<'a, F: PrimeField, H: Hasher<F>> MachineAir<F> for FuncChip<'a, F, H> {
    type Record = QueryRecord<F>;
    type Program = LairMachineProgram;

    #[inline]
    fn name(&self) -> String {
        self.func.name.to_string()
    }

    #[inline]
    fn generate_trace<EL: EventLens<Self>>(
        &self,
        input: &EL,
        _: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        self.generate_trace_parallel(input.events())
    }

    #[inline]
    fn included(&self, queries: &Self::Record) -> bool {
        !queries.func_queries[self.func.index].is_empty()
    }

    #[inline]
    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}
}
