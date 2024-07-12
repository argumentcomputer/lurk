use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir};
use p3_field::{AbstractField, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use sphinx_core::{
    air::{EventLens, MachineAir, MachineProgram, WithEvents},
    stark::Chip,
};

use crate::air::builder::{LookupBuilder, RequireRecord};

use super::{
    bytecode::Func,
    execute::{Shard, MEM_TABLE_SIZES},
    func_chip::FuncChip,
    hasher::Hasher,
    memory::MemChip,
    relations::OuterCallRelation,
};

pub enum LairChip<'a, F, H: Hasher<F>> {
    Func(FuncChip<'a, F, H>),
    Mem(MemChip<F>),
    Entrypoint {
        func_idx: usize,
        num_public_values: usize,
    },
    Preprocessed,
}

impl<'a, F, H: Hasher<F>> LairChip<'a, F, H> {
    #[inline]
    pub fn entrypoint(func: &Func<F>) -> Self {
        Self::Entrypoint {
            func_idx: func.index,
            num_public_values: func.input_size + func.output_size,
        }
    }
}

impl<'a, F: PrimeField32, H: Hasher<F>> WithEvents<'a> for LairChip<'_, F, H> {
    type Events = &'a Shard<'a, F>;
}

impl<'a, F: PrimeField32, H: Hasher<F>> EventLens<LairChip<'a, F, H>> for Shard<'a, F> {
    fn events(&self) -> <LairChip<'a, F, H> as WithEvents<'_>>::Events {
        self
    }
}

impl<'a, F: Sync, H: Hasher<F>> BaseAir<F> for LairChip<'a, F, H> {
    fn width(&self) -> usize {
        match self {
            Self::Func(func_chip) => func_chip.width(),
            Self::Mem(mem_chip) => mem_chip.width(),
            Self::Entrypoint {
                num_public_values, ..
            } => *num_public_values,
            Self::Preprocessed => 1,
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
    type Record = Shard<'a, F>;
    type Program = LairMachineProgram;

    fn name(&self) -> String {
        match self {
            Self::Func(func_chip) => format!("Func[{}]", func_chip.func.name),
            Self::Mem(mem_chip) => format!("Mem[{}-wide]", mem_chip.len),
            Self::Entrypoint { func_idx, .. } => format!("Entrypoint[{func_idx}]"),
            // the following is required by sphinx
            // TODO: engineer our way out of such upstream check
            Self::Preprocessed => "CPU".to_string(),
        }
    }

    fn generate_trace<EL: EventLens<Self>>(
        &self,
        shard: &EL,
        _: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        match self {
            Self::Func(func_chip) => func_chip.generate_trace(shard.events()),
            Self::Mem(mem_chip) => mem_chip.generate_trace(shard.events()),
            Self::Entrypoint {
                num_public_values, ..
            } => {
                let public_values = shard.events().expect_public_values();
                assert_eq!(*num_public_values, public_values.len());
                RowMajorMatrix::new(public_values.to_vec(), *num_public_values)
            }
            Self::Preprocessed => RowMajorMatrix::new(vec![F::zero(); 1], 1),
        }
    }

    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}

    fn included(&self, shard: &Self::Record) -> bool {
        match self {
            Self::Func(func_chip) => {
                let range = shard.get_func_range(func_chip.func.index);
                !range.is_empty()
            }
            Self::Mem(_mem_chip) => {
                shard.index == 0
                // TODO: This snippet or equivalent is needed for memory sharding
                // let range = shard.get_mem_range(mem_index_from_len(mem_chip.len));
                // !range.is_empty()
            }
            Self::Entrypoint { .. } => shard.index == 0,
            Self::Preprocessed => true,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Preprocessed => 1,
            _ => 0,
        }
    }

    fn generate_preprocessed_trace(&self, _program: &Self::Program) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::Preprocessed => Some(RowMajorMatrix::new(vec![F::zero(); 1], 1)),
            _ => None,
        }
    }
}

impl<'a, AB, H: Hasher<AB::F>> Air<AB> for LairChip<'a, AB::F, H>
where
    AB: AirBuilderWithPublicValues + LookupBuilder,
    <AB as AirBuilder>::Var: std::fmt::Debug,
{
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Func(func_chip) => func_chip.eval(builder),
            Self::Mem(mem_chip) => mem_chip.eval(builder),
            Self::Entrypoint {
                func_idx,
                num_public_values,
            } => {
                let func_idx = AB::F::from_canonical_usize(*func_idx);
                let public_values = builder.main().first_row().collect::<Vec<_>>();
                assert_eq!(public_values.len(), *num_public_values);

                // these values aren't correct for all builders!
                let public_values_from_builder = builder.public_values().to_vec();
                for (&a, b) in public_values.iter().zip(public_values_from_builder) {
                    // this is only accounted for by the builder used to collect constraints
                    builder.assert_eq(a, b);
                }

                builder.require(
                    OuterCallRelation(func_idx, public_values),
                    AB::F::zero(),
                    RequireRecord {
                        prev_nonce: AB::F::zero(),
                        prev_count: AB::F::zero(),
                        count_inv: AB::F::one(),
                    },
                    AB::F::one(),
                );
            }
            Self::Preprocessed => {
                // Dummy constraint of degree 3
                let tmp = builder.main().get(0, 0).into();
                builder.assert_zero(tmp.cube());
            }
        }
    }
}

pub fn build_lair_chip_vector<'a, F: PrimeField32, H: Hasher<F>>(
    entry_func_chip: &FuncChip<'a, F, H>,
) -> Vec<LairChip<'a, F, H>> {
    let toplevel = &entry_func_chip.toplevel;
    let func = &entry_func_chip.func;
    let mut chip_vector = Vec::with_capacity(2 + toplevel.map.size() + MEM_TABLE_SIZES.len());
    chip_vector.push(LairChip::entrypoint(func));
    chip_vector.push(LairChip::Preprocessed);
    for func_chip in FuncChip::from_toplevel(toplevel) {
        chip_vector.push(LairChip::Func(func_chip));
    }
    for mem_len in MEM_TABLE_SIZES {
        chip_vector.push(LairChip::Mem(MemChip::new(mem_len)));
    }
    chip_vector
}

#[inline]
pub fn build_chip_vector_from_lair_chips<
    'a,
    F: PrimeField32,
    H: Hasher<F>,
    I: IntoIterator<Item = LairChip<'a, F, H>>,
>(
    lair_chips: I,
) -> Vec<Chip<F, LairChip<'a, F, H>>> {
    lair_chips.into_iter().map(Chip::new).collect()
}

#[inline]
pub fn build_chip_vector<'a, F: PrimeField32, H: Hasher<F>>(
    entry_func_chip: &FuncChip<'a, F, H>,
) -> Vec<Chip<F, LairChip<'a, F, H>>> {
    build_chip_vector_from_lair_chips(build_lair_chip_vector(entry_func_chip))
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
        type F = BabyBear;
        type H = LurkHasher;
        let func_e = func!(
        fn test(): [2] {
            let one = 1;
            let two = 2;
            let three = 3;
            let ptr1 = store(one, two, three);
            let ptr2 = store(one, one, one);
            let (_x, y, _z) = load(ptr1);
            return (ptr2, y)
        });
        let toplevel = Toplevel::<F, H>::new(&[func_e]);
        let test_chip = FuncChip::from_name("test", &toplevel);
        let mut record = QueryRecord::new(&toplevel);

        toplevel.execute_by_name("test", &[], &mut record);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(
            config,
            build_chip_vector(&test_chip),
            record.expect_public_values().len(),
        );

        let (pk, vk) = machine.setup(&LairMachineProgram);
        let mut challenger_p = machine.config().challenger();
        let mut challenger_v = machine.config().challenger();
        let shard = Shard::new(&record);

        machine.debug_constraints(&pk, shard.clone());
        let opts = SphinxCoreOpts::default();
        let proof = machine.prove::<LocalProver<_, _>>(&pk, shard, &mut challenger_p, opts);
        machine
            .verify(&vk, &proof, &mut challenger_v)
            .expect("proof verifies");
    }
}
