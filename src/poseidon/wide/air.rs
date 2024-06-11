use crate::poseidon::config::PoseidonConfig;
use crate::poseidon::wide::columns::Poseidon2WideCols;
use crate::poseidon::wide::Poseidon2WideChip;
use hybrid_array::typenum::*;
use hybrid_array::ArraySize;
use p3_air::BaseAir;
use p3_air::{Air, AirBuilder};
use p3_field::AbstractField;
use p3_symmetric::Permutation;
use std::iter::zip;
use std::ops::Sub;

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
    C::R_P: Sub<B1>,
    <<C as PoseidonConfig<WIDTH>>::R_P as Sub<B1>>::Output: ArraySize,
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

impl<const WIDTH: usize, C: PoseidonConfig<WIDTH>> Poseidon2WideCols<C::F, C, WIDTH>
where
    C::R_P: Sub<B1>,
    <<C as PoseidonConfig<WIDTH>>::R_P as Sub<B1>>::Output: ArraySize,
{
    pub fn eval<AB: AirBuilder<F = C::F>>(
        &self,
        builder: &mut AB,
        input: [AB::Expr; WIDTH],
        is_real: impl Into<AB::Expr>,
    ) -> [AB::Expr; WIDTH] {
        let is_real = is_real.into();
        // let is_a: AB::Var = cols.is_a;
        // let is_b: AB::Var = cols.is_b;
        //         builder.assert_bool(is_a); builder.assert_bool(is_b);
        //        let is_real = is_a + is_b;
        //        builder.assert_bool(is_real.clone()) ;

        // let poseidon2_cols = cols.get_poseidon2_cols();
        // let memory = poseidon2_cols.memory;
        // eval_mem(builder, &memory);

        // Apply the initial round.
        let mut state = C::external_linear_layer().permute(input);

        // Apply the first half of external rounds.
        for r in 0..C::r_f() / 2 {
            state = self.eval_external_round(builder, state, r, is_real.clone());
        }

        // Apply the internal rounds.
        state = self.eval_internal_rounds(builder, state, is_real.clone());

        // Apply the second half of external rounds.
        for r in C::r_f() / 2..C::r_f() {
            state = self.eval_external_round(builder, state, r, is_real.clone());
        }

        state
    }

    fn eval_external_round<AB: AirBuilder<F = C::F>>(
        &self,
        builder: &mut AB,
        state: [AB::Expr; WIDTH],
        r: usize,
        is_real: AB::Expr,
    ) -> [AB::Expr; WIDTH] {
        let current_state = &self.external_rounds_state[r];

        for (state, &state_expected) in zip(state, current_state) {
            builder
                .when(is_real.clone())
                .assert_eq(state, state_expected);
        }

        let constants = &C::external_constants()[r];

        let add_rc: [AB::Expr; WIDTH] =
            core::array::from_fn(|i| current_state[i].into() + is_real.clone() * constants[i]);

        let sbox_deg_3 = self.external_rounds_sbox[r];
        let sbox_deg_3_expected: [AB::Expr; WIDTH] = core::array::from_fn(|i| add_rc[i].cube());
        for (&sbox, sbox_expected) in zip(sbox_deg_3, sbox_deg_3_expected) {
            builder.assert_eq(sbox, sbox_expected.clone());
        }

        let sbox_deg_7: [AB::Expr; WIDTH] =
            core::array::from_fn(|i| sbox_deg_3[i].into().square() * add_rc[i].clone());

        let state = C::external_linear_layer().permute(sbox_deg_7);

        state
        // // Apply the sboxes.
        // // See `populate_external_round` for why we don't have columns for the sbox output here.
        // let mut sbox_deg_7: [AB::Expr; WIDTH] = core::array::from_fn(|_| AB::Expr::zero());
        // let mut sbox_deg_3: [AB::Expr; WIDTH] = core::array::from_fn(|_| AB::Expr::zero());
        // let expected_sbox_deg_3 = cols.get_external_sbox(r);
        // for i in 0..WIDTH {
        //     sbox_deg_3[i] = add_rc[i].clone() * add_rc[i].clone() * add_rc[i].clone();
        //
        //     if let Some(expected) = expected_sbox_deg_3 {
        //         builder.assert_eq(expected[i], sbox_deg_3[i].clone());
        //         sbox_deg_3[i] = expected[i].into();
        //     }
        //
        //     sbox_deg_7[i] = sbox_deg_3[i].clone() * sbox_deg_3[i].clone() * add_rc[i].clone();
        // }
        //
        // // Apply the linear layer.
        // let mut state = sbox_deg_7;
        // external_linear_layer(&mut state);
        //
        // let next_state_cols = if r == NUM_EXTERNAL_ROUNDS / 2 - 1 {
        //     poseidon2_cols.internal_rounds_state
        // } else if r == NUM_EXTERNAL_ROUNDS - 1 {
        //     core::array::from_fn(|i| *poseidon2_cols.memory.output[i].value())
        // } else {
        //     poseidon2_cols.external_rounds_state[r + 1]
        // };
        // for i in 0..WIDTH {
        //     builder.assert_eq(next_state_cols[i], state[i].clone());
        // }
    }

    fn eval_internal_rounds<AB: AirBuilder<F = C::F>>(
        &self,
        builder: &mut AB,
        input: [AB::Expr; WIDTH],
        is_real: AB::Expr,
    ) -> [AB::Expr; WIDTH] {
        for (input, &input_expected) in zip(input, &self.internal_rounds_state) {
            builder.assert_eq(input, input_expected);
        }

        let mut state = self.internal_rounds_state.clone().map(Into::into);

        let s0 = &self.internal_rounds_s0;

        for r in 0..C::r_p() {
            // Add the round constant
            let add_rc: AB::Expr = state[0].into() + is_real.clone() * C::internal_constants()[r];

            let sbox_deg_3 = self.internal_rounds_sbox[r];
            let sbox_deg_3_expected = add_rc.cube();
            builder.assert_eq(sbox_deg_3.clone(), sbox_deg_3_expected);

            let sbox_deg_7 = sbox_deg_3.into().square() * add_rc;

            // Apply the linear layer.
            // See `populate_internal_rounds` for why we don't have columns for the new state here.
            state[0] = sbox_deg_7.clone();

            C::internal_linear_layer().permute_mut(&mut state);

            if r < C::r_p() - 1 {
                builder.assert_eq(s0[r], state[0].clone());
            }
        }
        state
    }
}

