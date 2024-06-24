use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field, PrimeField};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use sphinx_core::{
    air::{EventLens, MachineAir, MachineProgram, WithEvents},
    stark::Chip,
};

use crate::air::builder::LookupBuilder;

use super::{
    execute::{QueryRecord, MEM_TABLE_SIZES},
    func_chip::FuncChip,
    hasher::Hasher,
    memory::MemChip,
    toplevel::Toplevel,
};

pub enum LairChip<'a, F, H: Hasher<F>> {
    Func(FuncChip<'a, F, H>),
    Mem(MemChip<F>),
    DummyPreprocessed,
}

impl<'a, 'b, F: Field, H: Hasher<F>> WithEvents<'a> for LairChip<'b, F, H> {
    type Events = &'a QueryRecord<F>;
}

impl<'a, F: Field, H: Hasher<F>> EventLens<LairChip<'a, F, H>> for QueryRecord<F> {
    fn events(&self) -> <LairChip<'a, F, H> as WithEvents<'_>>::Events {
        self
    }
}

impl<'a, F: Sync, H: Hasher<F>> BaseAir<F> for LairChip<'a, F, H> {
    fn width(&self) -> usize {
        match self {
            Self::Func(func_chip) => func_chip.width(),
            Self::Mem(mem_chip) => mem_chip.width(),
            Self::DummyPreprocessed => 1,
        }
    }
}

pub struct LairMachineProgram;

impl<F: AbstractField> MachineProgram<F> for LairMachineProgram {
    fn pc_start(&self) -> F {
        F::zero()
    }
}

impl<'a, F: PrimeField, H: Hasher<F>> MachineAir<F> for LairChip<'a, F, H> {
    type Record = QueryRecord<F>;
    type Program = LairMachineProgram;

    fn name(&self) -> String {
        match self {
            Self::Func(func_chip) => format!("Func[{}]", func_chip.name()),
            Self::Mem(mem_chip) => format!("Mem[{}]", mem_chip.name()),
            Self::DummyPreprocessed => "Dummy".to_string(),
        }
    }

    fn generate_trace<EL: EventLens<Self>>(
        &self,
        input: &EL,
        output: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        match self {
            Self::Func(func_chip) => func_chip.generate_trace(input.events(), output),
            Self::Mem(mem_chip) => mem_chip.generate_trace(input.events(), output),
            Self::DummyPreprocessed => RowMajorMatrix::new(vec![F::zero(); 1], 1),
        }
    }

    fn generate_dependencies<EL: EventLens<Self>>(&self, _: &EL, _: &mut Self::Record) {}

    fn included(&self, queries: &Self::Record) -> bool {
        match self {
            Self::Func(func_chip) => func_chip.included(queries),
            Self::Mem(mem_chip) => mem_chip.included(queries),
            Self::DummyPreprocessed => true,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::DummyPreprocessed => 1,
            _ => 0,
        }
    }

    fn generate_preprocessed_trace(&self, _program: &Self::Program) -> Option<RowMajorMatrix<F>> {
        match self {
            Self::DummyPreprocessed => Some(RowMajorMatrix::new(vec![F::zero(); 1], 1)),
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
            Self::DummyPreprocessed => {
                // Dummy constraint of degree 3
                let tmp = builder.main().get(0, 0).into();
                builder.assert_zero(tmp.cube());
            }
        }
    }
}

pub fn build_chip_vector<F: PrimeField, H: Hasher<F>>(
    toplevel: &Toplevel<F, H>,
) -> Vec<Chip<F, LairChip<'_, F, H>>> {
    let mut chip_vector = Vec::with_capacity(1 + toplevel.map.size() + MEM_TABLE_SIZES.len());
    chip_vector.push(Chip::new(LairChip::DummyPreprocessed));
    for func_chip in FuncChip::from_toplevel(toplevel) {
        chip_vector.push(Chip::new(LairChip::Func(func_chip)));
    }
    for mem_len in MEM_TABLE_SIZES {
        chip_vector.push(Chip::new(LairChip::Mem(MemChip::new(mem_len))));
    }
    chip_vector
}

#[cfg(test)]
mod tests {
    use crate::{
        func,
        lair::{func_chip::FuncChip, hasher::LurkHasher, toplevel::Toplevel},
    };

    use super::*;

    use crate::lair::execute::QueryRecord;
    use p3_baby_bear::BabyBear;
    use sphinx_core::{stark::{LocalProver, StarkGenericConfig, StarkMachine}, utils::SphinxCoreOpts};
    use sphinx_core::utils::BabyBearPoseidon2;

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
        let mut queries = QueryRecord::new(&toplevel);
        test_chip.execute([].into(), &mut queries);

        let config = BabyBearPoseidon2::new();
        let machine = StarkMachine::new(config, build_chip_vector(&toplevel), 0);

        let (pk, vk) = machine.setup(&LairMachineProgram);
        let mut challenger_p = machine.config().challenger();
        let mut challenger_v = machine.config().challenger();
        machine.debug_constraints(&pk, queries.clone(), &mut challenger_p.clone());
        let opts = SphinxCoreOpts::default();
        let proof = machine.prove::<LocalProver<_, _>>(&pk, queries, &mut challenger_p, opts);
        machine
            .verify(&vk, &proof, &mut challenger_v)
            .expect("proof verifies");
    }
}
