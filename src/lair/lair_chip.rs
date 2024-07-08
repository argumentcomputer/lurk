use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field, PrimeField, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use sphinx_core::{
    air::{EventLens, MachineAir, MachineProgram, WithEvents},
    stark::Chip,
};

use crate::air::builder::{LookupBuilder, RequireRecord};

use super::{
    execute::{mem_index_from_len, Shard, MEM_TABLE_SIZES},
    func_chip::FuncChip,
    hasher::Hasher,
    memory::MemChip,
    relations::CallRelation,
};

pub enum LairChip<'a, F, H: Hasher<F>> {
    Func(FuncChip<'a, F, H>),
    Mem(MemChip<F>),
    Entrypoint {
        func_idx: F,
        inp: Vec<F>, // TODO: remove this!
        out: Vec<F>, // TODO: remove this!
    },
}

impl<'a, F, H: Hasher<F>> LairChip<'a, F, H> {
    #[inline]
    pub fn entrypoint(func_idx: F, inp: Vec<F>, out: Vec<F>) -> Self {
        Self::Entrypoint { func_idx, inp, out }
    }
}

impl<'a, F: Field, H: Hasher<F>> WithEvents<'a> for LairChip<'_, F, H> {
    type Events = &'a Shard<F>;
}

impl<'a, F: Field, H: Hasher<F>> EventLens<LairChip<'a, F, H>> for Shard<F> {
    fn events(&self) -> <LairChip<'a, F, H> as WithEvents<'_>>::Events {
        self
    }
}

impl<'a, F: Sync, H: Hasher<F>> BaseAir<F> for LairChip<'a, F, H> {
    fn width(&self) -> usize {
        match self {
            Self::Func(func_chip) => func_chip.width(),
            Self::Mem(mem_chip) => mem_chip.width(),
            Self::Entrypoint { .. } => 1,
        }
    }
}

pub struct LairMachineProgram;

impl<F: AbstractField> MachineProgram<F> for LairMachineProgram {
    fn pc_start(&self) -> F {
        F::zero()
    }
}

impl<'a, F: PrimeField32, H: Hasher<F>> MachineAir<F> for LairChip<'a, F, H> {
    type Record = Shard<F>;
    type Program = LairMachineProgram;

    fn name(&self) -> String {
        match self {
            Self::Func(func_chip) => format!("Func[{}]", func_chip.func.name),
            Self::Mem(mem_chip) => format!("{}-wide", mem_chip.len),
            // the following is required by sphinx
            // TODO: engineer our way out of such upstream check
            Self::Entrypoint { .. } => "CPU".to_string(),
        }
    }

    fn generate_trace<EL: EventLens<Self>>(
        &self,
        shard: &EL,
        _: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        match self {
            Self::Func(func_chip) => func_chip.generate_trace_parallel(shard.events()),
            Self::Mem(mem_chip) => mem_chip.generate_trace(shard.events()),
            Self::Entrypoint { .. } => RowMajorMatrix::new(vec![F::zero(); 1], 1),
        }
    }

    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}

    fn included(&self, queries: &Self::Record) -> bool {
        match self {
            Self::Func(func_chip) => {
                let range = queries.get_func_range(func_chip.func.index);
                !range.is_empty()
            }
            Self::Mem(mem_chip) => {
                queries.index == 0
                // let range = queries.get_mem_range(mem_index_from_len(mem_chip.len));
                // !range.is_empty()
            }
            Self::Entrypoint { .. } => queries.index == 0,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Entrypoint { .. } => 1,
            _ => 0,
        }
    }

    fn generate_preprocessed_trace(&self, _program: &Self::Program) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Entrypoint { .. } => Some(RowMajorMatrix::new(vec![F::zero(); 1], 1)),
            _ => None,
        }
    }
}

impl<'a, AB, H: Hasher<AB::F>> Air<AB> for LairChip<'a, AB::F, H>
where
    AB: AirBuilder + LookupBuilder,
    <AB as AirBuilder>::Var: std::fmt::Debug,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Func(func_chip) => func_chip.eval(builder),
            Self::Mem(mem_chip) => mem_chip.eval(builder),
            Self::Entrypoint { func_idx, inp, out } => {
                builder.require(
                    CallRelation(*func_idx, inp.clone(), out.clone()),
                    AB::F::zero(),
                    RequireRecord {
                        prev_nonce: AB::F::zero(),
                        prev_count: AB::F::zero(),
                        count_inv: AB::F::one(),
                    },
                    AB::F::one(),
                );
                // Dummy constraint of degree 3
                let tmp = builder.main().get(0, 0).into();
                builder.assert_zero(tmp.cube());
            }
        }
    }
}

pub fn build_lair_chip_vector<'a, F: PrimeField32, H: Hasher<F>>(
    entry_func_chip: &FuncChip<'a, F, H>,
    inp: Vec<F>,
    out: Vec<F>,
) -> Vec<LairChip<'a, F, H>> {
    let toplevel = &entry_func_chip.toplevel;
    let func = &entry_func_chip.func;
    assert_eq!(func.input_size, inp.len());
    assert_eq!(func.output_size, out.len());
    let mut chip_vector = Vec::with_capacity(1 + toplevel.map.size() + MEM_TABLE_SIZES.len());
    chip_vector.push(LairChip::entrypoint(
        F::from_canonical_usize(func.index),
        inp,
        out,
    ));
    for func_chip in FuncChip::from_toplevel(toplevel) {
        chip_vector.push(LairChip::Func(func_chip));
    }
    for mem_len in MEM_TABLE_SIZES {
        chip_vector.push(LairChip::Mem(MemChip::new(mem_len)));
    }
    chip_vector
}

pub fn build_chip_vector<'a, F: PrimeField32, H: Hasher<F>>(
    entry_func_chip: &FuncChip<'a, F, H>,
    inp: Vec<F>,
    out: Vec<F>,
) -> Vec<Chip<F, LairChip<'a, F, H>>> {
    build_lair_chip_vector(entry_func_chip, inp, out)
        .into_iter()
        .map(Chip::new)
        .collect()
}

pub fn set_chip_vector_io<F: PrimeField32, H: Hasher<F>>(
    chip_vector: &mut [Chip<F, LairChip<'_, F, H>>],
    new_inp: Vec<F>,
    new_out: Vec<F>,
) {
    let LairChip::Entrypoint { func_idx, inp, out } = chip_vector[0].as_ref() else {
        panic!("Invalid chip vector");
    };
    assert_eq!(inp.len(), new_inp.len());
    assert_eq!(out.len(), new_out.len());
    chip_vector[0] = Chip::new(LairChip::Entrypoint {
        func_idx: *func_idx,
        inp: new_inp,
        out: new_out,
    })
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lair::{execute::QueryRecord, func_chip::FuncChip, hasher::LurkHasher, toplevel::Toplevel},
    };

    use super::*;

    use p3_baby_bear::BabyBear;
    use sphinx_core::utils::BabyBearPoseidon2;
    use sphinx_core::{
        stark::{LocalProver, StarkGenericConfig, StarkMachine},
        utils::SphinxCoreOpts,
    };

    #[test]
    fn test_prove_and_verify() {
        sphinx_core::utils::setup_logger();

        type F = BabyBear;
        type H = LurkHasher;
        let func_f = func!(
            fn test2(n): [1] {
                let x = add(n, n);
                return x
            }
        );
        let func_e = func!(
        fn test(): [2] {
            let one = 1;
            let two = 2;
            let _three = 3;
            let x = call(test2, one);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            let x = call(test2, x);
            return (two, x)
        });
        // let ptr1 = store(one, two, three);
        // let ptr2 = store(one, one, one);
        // let _ptr3 = store(two, two, three);
        // let _ptr4 = store(one, one, three);
        // let _ptr5 = store(one, three, three);
        // let _ptr6 = store(one, two, one);
        // let _ptr7 = store(three, two, three);
        // let _ptr8 = store(one, three, two);
        // let (_x, _y, _z) = load(ptr1);
        let toplevel = Toplevel::<F, H>::new(&[func_e, func_f]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let mut queries = QueryRecord::new(&toplevel);

        let inp = &[];
        toplevel.execute_by_name("test", inp, &mut queries);
        let out = queries.get_output(test_chip.func, inp).to_vec();

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(config, build_chip_vector(&test_chip, vec![], out), 0);

        let (pk, vk) = machine.setup(&LairMachineProgram);
        let mut challenger_p = machine.config().challenger();
        let mut challenger_v = machine.config().challenger();
        let shard = Shard::new(queries);
        use sphinx_core::stark::MachineRecord;
        let shards = shard
            .clone()
            .shard(&crate::lair::execute::ShardingConfig { max_shard_size: 4 });
        // panic!("num_shards: {}", shards.len());

        machine.debug_constraints(&pk, shard.clone(), &mut challenger_p.clone());
        let opts = SphinxCoreOpts::default();
        let proof = machine.prove::<LocalProver<_, _>>(&pk, shard, &mut challenger_p, opts);
        machine
            .verify(&vk, &proof, &mut challenger_v)
            .expect("proof verifies");
    }
}
