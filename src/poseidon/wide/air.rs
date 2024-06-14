use std::iter::zip;

use super::{columns::Poseidon2WideCols, Poseidon2WideChip};
use crate::poseidon::config::PoseidonConfig;

use hybrid_array::{typenum::*, ArraySize};
use itertools::{chain, izip};

use p3_air::{AirBuilder, BaseAir};
use p3_field::AbstractField;
use p3_symmetric::Permutation;

// impl<F: PrimeField32, const DEGREE: usize> MachineAir<F> for Poseidon2WideChip<DEGREE> {
//     type Record = ExecutionRecord<F>;
//
//     type Program = RecursionProgram<F>;
//
//     fn name(&self) -> String {
//         format!("Poseidon2Wide {}", DEGREE)
//     }
//
//     fn generate_dependencies(&self, _: &Self::Record, _: &mut Self::Record) {
//         // This is a no-op.
//     }
//
//     #[instrument(name = "generate poseidon2 wide trace", level = "debug", skip_all, fields(rows = input.poseidon2_events.len()))]
//     fn generate_trace(
//         &self,
//         input: &ExecutionRecord<F>,
//         _: &mut ExecutionRecord<F>,
//     ) -> RowMajorMatrix<F> {
//         let mut rows = Vec::new();
//
//         assert!(DEGREE >= 3, "Minimum supported constraint degree is 3");
//         let use_sbox_3 = DEGREE < 7;
//         let num_columns = <Self as BaseAir<F>>::width(self);
//
//         for event in &input.poseidon2_events {
//             let mut row = Vec::new();
//             row.resize(num_columns, F::zero());
//
//             let mut cols = if use_sbox_3 {
//                 let cols: &mut Poseidon2SBoxCols<F> = row.as_mut_slice().borrow_mut();
//                 Poseidon2ColTypeMut::Wide(cols)
//             } else {
//                 let cols: &mut Poseidon2Cols<F> = row.as_mut_slice().borrow_mut();
//                 Poseidon2ColTypeMut::Narrow(cols)
//             };
//
//             let (poseidon2_cols, mut external_sbox, mut internal_sbox) = cols.get_cols_mut();
//
//             let memory = &mut poseidon2_cols.memory;
//             memory.timestamp = event.clk;
//             memory.dst = event.dst;
//             memory.left = event.left;
//             memory.right = event.right;
//             memory.is_real = F::one();
//
//             // Apply the initial round.
//             for i in 0..WIDTH {
//                 memory.input[i].populate(&event.input_records[i]);
//             }
//
//             for i in 0..WIDTH {
//                 memory.output[i].populate(&event.result_records[i]);
//             }
//
//             poseidon2_cols.external_rounds_state[0] = event.input;
//             external_linear_layer(&mut poseidon2_cols.external_rounds_state[0]);
//
//             // Apply the first half of external rounds.
//             for r in 0..NUM_EXTERNAL_ROUNDS / 2 {
//                 let next_state = populate_external_round(poseidon2_cols, &mut external_sbox, r);
//
//                 if r == NUM_EXTERNAL_ROUNDS / 2 - 1 {
//                     poseidon2_cols.internal_rounds_state = next_state;
//                 } else {
//                     poseidon2_cols.external_rounds_state[r + 1] = next_state;
//                 }
//             }
//
//             // Apply the internal rounds.
//             poseidon2_cols.external_rounds_state[NUM_EXTERNAL_ROUNDS / 2] =
//                 populate_internal_rounds(poseidon2_cols, &mut internal_sbox);
//
//             // Apply the second half of external rounds.
//             for r in NUM_EXTERNAL_ROUNDS / 2..NUM_EXTERNAL_ROUNDS {
//                 let next_state = populate_external_round(poseidon2_cols, &mut external_sbox, r);
//                 if r == NUM_EXTERNAL_ROUNDS - 1 {
//                     // Do nothing, since we set the cols.output by populating the output records
//                     // after this loop.
//                     for i in 0..WIDTH {
//                         assert_eq!(event.result_records[i].value[0], next_state[i]);
//                     }
//                 } else {
//                     poseidon2_cols.external_rounds_state[r + 1] = next_state;
//                 }
//             }
//
//             rows.push(row);
//         }
//
//         // Pad the trace to a power of two.
//         pad_rows_fixed(
//             &mut rows,
//             || vec![F::zero(); num_columns],
//             self.fixed_log2_rows,
//         );
//
//         // Convert the trace to a row major matrix.
//         let trace =
//             RowMajorMatrix::new(rows.into_iter().flatten().collect::<Vec<_>>(), num_columns);
//
//         #[cfg(debug_assertions)]
//         println!(
//             "poseidon2 wide trace dims is width: {:?}, height: {:?}",
//             trace.width(),
//             trace.height()
//         );
//
//         trace
//     }
//
//     fn included(&self, record: &Self::Record) -> bool {
//         !record.poseidon2_events.is_empty()
//     }
// }

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> BaseAir<C::F> for Poseidon2WideChip<C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    fn width(&self) -> usize {
        Poseidon2WideCols::<C::F, C, WIDTH>::num_cols()
    }
}

// fn eval_mem<AB: SP1RecursionAirBuilder>(builder: &mut AB, local: &Poseidon2MemCols<AB::Var>) {
//     // Evaluate all of the memory.
//     for i in 0..WIDTH {
//         let input_addr = if i < WIDTH / 2 {
//             local.left + AB::F::from_canonical_usize(i)
//         } else {
//             local.right + AB::F::from_canonical_usize(i - WIDTH / 2)
//         };
//
//         builder.recursion_eval_memory_access_single(
//             local.timestamp,
//             input_addr,
//             &local.input[i],
//             local.is_real,
//         );
//
//         let output_addr = local.dst + AB::F::from_canonical_usize(i);
//         builder.recursion_eval_memory_access_single(
//             local.timestamp + AB::F::from_canonical_usize(1),
//             output_addr,
//             &local.output[i],
//             local.is_real,
//         );
//     }
//
//     // Constraint that the operands are sent from the CPU table.
//     let operands: [AB::Expr; 4] = [
//         local.timestamp.into(),
//         local.dst.into(),
//         local.left.into(),
//         local.right.into(),
//     ];
//     builder.receive_table(
//         Opcode::Poseidon2Compress.as_field::<AB::F>(),
//         &operands,
//         local.is_real,
//     );
// }

impl<T: Copy, C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2WideCols<T, C, WIDTH> where
    Sub1<C::R_P>: ArraySize
{
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2WideChip<C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    pub fn eval<AB: AirBuilder<F = C::F>>(
        builder: &mut AB,
        input: [AB::Expr; WIDTH],
        output: [AB::Expr; WIDTH],
        cols: &Poseidon2WideCols<AB::Var, C, WIDTH>,
        is_real: impl Into<AB::Expr>,
    ) {
        let is_real = is_real.into();

        // When is_real = 0, set all constants to 0
        let external_constants = C::external_constants()
            .iter()
            .map(|constants| constants.map(|constant| is_real.clone() * constant));
        let internal_constants = C::internal_constants()
            .iter()
            .map(|&constant| is_real.clone() * constant);

        let mut external_rounds = izip!(
            &cols.external_rounds_state,
            external_constants,
            &cols.external_rounds_sbox
        );

        let internal_state_init = &cols.internal_rounds_state_init;
        let internal_rounds_state0 = chain([&internal_state_init[0]], &cols.internal_rounds_state0);
        let internal_rounds = izip!(
            internal_rounds_state0,
            internal_constants,
            &cols.internal_rounds_sbox,
        );

        // When is_real = 0, the constraints apply the identity to [0; WIDTH]
        let mut state: [AB::Expr; WIDTH] = input.map(|x| is_real.clone() * x);

        // Apply the initial round.
        C::external_linear_layer().permute_mut(&mut state);

        // Apply the first half of external rounds.
        for (state_expected, constants, sbox_3) in external_rounds.by_ref().take(C::r_f() / 2) {
            Self::eval_external_round(builder, &mut state, state_expected, sbox_3, constants);
        }

        // Before applying the internal rounds, ensure the state matches the expected state and replace the expressions
        // with linear ones.
        // Note: we skip the first state component since it is checked by `eval_internal_rounds`
        for (state, &state_expected) in zip(state.iter_mut(), internal_state_init).skip(1) {
            builder.assert_eq(state.clone(), state_expected);
            *state = state_expected.into();
        }

        // Apply the internal rounds.
        for (&state0_expected, constant, &sbox_3) in internal_rounds {
            Self::eval_internal_round(builder, &mut state, state0_expected, constant, sbox_3);
        }

        // Apply the second half of external rounds.
        debug_assert_eq!(external_rounds.len(), C::r_f() / 2);
        for (state_expected, constants, sbox_3) in external_rounds {
            Self::eval_external_round(builder, &mut state, state_expected, sbox_3, constants);
        }

        for (state, output) in zip(state, output) {
            builder.assert_eq(state, output * is_real.clone());
        }
    }

    fn eval_external_round<AB: AirBuilder<F = C::F>>(
        builder: &mut AB,
        state: &mut [AB::Expr; WIDTH],
        state_expected: &[AB::Var; WIDTH],
        sbox_3: &[AB::Var; WIDTH],
        constants: [AB::Expr; WIDTH],
    ) {
        // Check that the input state matches the expected round state, and replace it to ensure `state` is linear
        for (state, &state_expected) in zip(state.iter_mut(), state_expected) {
            builder.assert_eq(state.clone(), state_expected);
            *state = state_expected.into();
        }

        // add round constants
        for (state, constant) in zip(state.iter_mut(), constants) {
            *state += constant;
        }

        // apply sbox
        for (state, &sbox_3) in zip(state.iter_mut(), sbox_3) {
            let state_pow3 = state.cube();
            builder.assert_eq(state_pow3, sbox_3);

            *state *= sbox_3.into().square();
        }

        // apply external linear layer
        C::external_linear_layer().permute_mut(state)
    }

    fn eval_internal_round<AB: AirBuilder<F = C::F>>(
        builder: &mut AB,
        state: &mut [AB::Expr; WIDTH],
        state0_expected: AB::Var,
        constant: AB::Expr,
        sbox_3: AB::Var,
    ) {
        // Check that the first state value matches the expected state, and replace it to ensure `state` is linear
        // before applying the sbox
        builder.assert_eq(state[0].clone(), state0_expected);
        state[0] = state0_expected.into();

        // add round constant
        state[0] += constant;

        // apply sbox
        builder.assert_eq(state[0].cube(), sbox_3);
        state[0] *= sbox_3.into().square();

        // apply internal linear layer
        C::internal_linear_layer().permute_mut(state);
    }
}
