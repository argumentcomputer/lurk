use std::marker::PhantomData;

use self::config::PoseidonConfig;

mod air;
mod columns;
mod config;
mod constants;
mod eval;
mod trace;
mod util;

/// A chip that implements addition for the opcode ADD.
pub struct Poseidon2Chip<C>
where
    C: PoseidonConfig,
{
    _p: PhantomData<C>,
}

// TODO: Add tests
#[cfg(test)]
mod tests {
    // use crate::air::DebugConstraintBuilder;

    // use super::*;

    // use self::config::{BabyBearConfig16, BabyBearConfig4};

    // use hybrid_array::{typenum::*, ArraySize};
    // use itertools::Itertools;
    // use std::{borrow::Borrow, time::Instant};
    // use wp1_core::runtime::ExecutionRecord;

    // use p3_baby_bear::BabyBear;
    // use p3_field::AbstractField;
    // use p3_matrix::{
    //     dense::{DenseMatrix, RowMajorMatrix},
    //     stack::VerticalPair,
    //     Matrix,
    // };
    // use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
    // use p3_symmetric::Permutation;

    // fn generate_trace_with<Config: PoseidonConfig>() {
    //     let chip = Poseidon2Chip::<Config> { _p: PhantomData };

    //     let first_values = [0; 52].map(BabyBear::from_canonical_u32);
    //     let second_values = [0; 7].map(BabyBear::from_canonical_u32);

    //     let first: DenseMatrix<BabyBear, &[_]> = DenseMatrix::new(first_values.as_slice(), 52);
    //     let second: DenseMatrix<_, &[_]> = DenseMatrix::new(second_values.as_slice(), 7);

    //     let main = VerticalPair::new(first, second);

    //     let mut builder = DebugConstraintBuilder::new(main, 3, 3);

    //     // dbg!(BaseAir::<BabyBear>::width(&chip));

    //     chip.eval(&mut builder);

    //     // let test_inputs = vec![];

    //     // let gt: Poseidon2<
    //     //     BabyBear,
    //     //     Poseidon2ExternalMatrixGeneral,
    //     //     DiffusionMatrixBabybear,
    //     //     WIDTH,
    //     //     7,
    //     // > = inner_perm();

    //     // let expected_outputs = test_inputs
    //     //     .iter()
    //     //     .map(|input| gt.permute(*input))
    //     //     .collect::<Vec<_>>();
    // }

    // #[test]
    // fn generate_trace() {
    //     generate_trace_with::<BabyBearConfig4>();
    //     generate_trace_with::<BabyBearConfig16>();
    // }

    // fn prove_babybear_with() {
    //     todo!()
    // }

    // #[test]
    // fn prove_babybear() {
    //     prove_babybear_with()
    // }

    // #[test]
    // fn prove_babybear() {
    //     let config = BabyBearPoseidon2::new();
    //     let mut challenger = config.challenger();

    //     let chip = Poseidon2Chip;

    //     let test_inputs = (0..16)
    //         .map(|i| [BabyBear::from_canonical_u32(i); WIDTH])
    //         .collect_vec();

    //     let mut input_exec = ExecutionRecord::<BabyBear>::default();
    //     for input in test_inputs.iter().cloned() {
    //         input_exec.poseidon2_events.push(Poseidon2Event { input });
    //     }
    //     let trace: RowMajorMatrix<BabyBear> =
    //         chip.generate_trace(&input_exec, &mut ExecutionRecord::<BabyBear>::default());
    //     println!(
    //         "trace dims is width: {:?}, height: {:?}",
    //         trace.width(),
    //         trace.height()
    //     );

    //     let start = Instant::now();
    //     let proof = uni_stark_prove(&config, &chip, &mut challenger, trace);
    //     let duration = start.elapsed().as_secs_f64();
    //     println!("proof duration = {:?}", duration);

    //     let mut challenger: p3_challenger::DuplexChallenger<
    //         BabyBear,
    //         Poseidon2<BabyBear, Poseidon2ExternalMatrixGeneral, DiffusionMatrixBabybear, 16, 7>,
    //         16,
    //     > = config.challenger();
    //     let start = Instant::now();
    //     uni_stark_verify(&config, &chip, &mut challenger, &proof)
    //         .expect("expected proof to be valid");

    //     let duration = start.elapsed().as_secs_f64();
    //     println!("verify duration = {:?}", duration);
    // }
}
