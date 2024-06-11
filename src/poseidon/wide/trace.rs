// use crate::poseidon2_wide::columns::{
//     Poseidon2ColType, Poseidon2ColTypeMut, Poseidon2Cols, Poseidon2SBoxCols, NUM_POSEIDON2_COLS,
//     NUM_POSEIDON2_SBOX_COLS,
// };
// use crate::runtime::Opcode;
// use core::borrow::Borrow;
// use p3_air::{Air, BaseAir};
// use p3_field::{AbstractField, PrimeField32};
// use p3_matrix::dense::RowMajorMatrix;
// use p3_matrix::Matrix;
// use std::borrow::BorrowMut;
// use tracing::instrument;
// use wp1_core::air::{BaseAirBuilder, MachineAir};
// use wp1_core::utils::pad_rows_fixed;
// use wp1_primitives::RC_16_30_U32;

// use crate::air::SP1RecursionAirBuilder;
// use crate::memory::MemoryCols;

// use crate::poseidon2_wide::{external_linear_layer, internal_linear_layer};
// use crate::runtime::{ExecutionRecord, RecursionProgram};

// use super::columns::Poseidon2MemCols;

use std::borrow::BorrowMut;

use p3_baby_bear::BabyBear;
use p3_field::AbstractField;
use p3_field::PrimeField32;

use super::{columns::Poseidon2WideCols, NUM_EXTERNAL_ROUNDS, NUM_INTERNAL_ROUNDS, WIDTH};
use crate::poseidon::{
    constants::{FULL_RC_16_8, MATRIX_DIAG_16_BABYBEAR, PART_RC_16_13},
    util::{matmul_exterior, matmul_internal},
};

type F = BabyBear;

// fn populate_external_round(
//     poseidon2_cols: &mut Poseidon2WideCols<F>,
//     sbox: &mut Option<&mut [[F; WIDTH]; NUM_EXTERNAL_ROUNDS]>,
//     r: usize,
// ) -> [F; WIDTH] {
//     let mut state = {
//         let round_state: &mut [F; WIDTH] = poseidon2_cols.external_rounds_state[r].borrow_mut();
//
//         // Add round constants.
//         //
//         // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
//         // columns for it, and instead include it in the constraint for the x^3 part of the sbox.
//         let round = if r < NUM_EXTERNAL_ROUNDS / 2 {
//             r
//         } else {
//             r + NUM_INTERNAL_ROUNDS
//         };
//         let mut add_rc = *round_state;
//         for i in 0..WIDTH {
//             add_rc[i] += (*FULL_RC_16_8)[round][i];
//         }
//
//         // Apply the sboxes.
//         // Optimization: since the linear layer that comes after the sbox is degree 1, we can
//         // avoid adding columns for the result of the sbox, and instead include the x^3 -> x^7
//         // part of the sbox in the constraint for the linear layer
//         let mut sbox_deg_7: [F; 16] = [F::zero(); WIDTH];
//         let mut sbox_deg_3: [F; 16] = [F::zero(); WIDTH];
//         for i in 0..WIDTH {
//             sbox_deg_3[i] = add_rc[i] * add_rc[i] * add_rc[i];
//             sbox_deg_7[i] = sbox_deg_3[i] * sbox_deg_3[i] * add_rc[i];
//         }
//
//         if let Some(sbox) = sbox.as_deref_mut() {
//             sbox[r] = sbox_deg_3;
//         }
//
//         sbox_deg_7
//     };
//
//     // Apply the linear layer.
//     matmul_exterior(&mut state);
//     state
// }
//
// fn populate_internal_rounds(
//     poseidon2_cols: &mut Poseidon2WideCols<F>,
//     sbox: &mut Option<&mut [F; NUM_INTERNAL_ROUNDS]>,
// ) -> [F; WIDTH] {
//     let mut state: [F; WIDTH] = poseidon2_cols.internal_rounds_state;
//     let mut sbox_deg_3: [F; NUM_INTERNAL_ROUNDS] = [F::zero(); NUM_INTERNAL_ROUNDS];
//     for r in 0..NUM_INTERNAL_ROUNDS {
//         // Add the round constant to the 0th state element.
//         // Optimization: Since adding a constant is a degree 1 operation, we can avoid adding
//         // columns for it, just like for external rounds.
//         let round = r + NUM_EXTERNAL_ROUNDS / 2;
//         let add_rc = state[0] + (*PART_RC_16_13)[round];
//
//         // Apply the sboxes.
//         // Optimization: since the linear layer that comes after the sbox is degree 1, we can
//         // avoid adding columns for the result of the sbox, just like for external rounds.
//         sbox_deg_3[r] = add_rc * add_rc * add_rc;
//         let sbox_deg_7 = sbox_deg_3[r] * sbox_deg_3[r] * add_rc;
//
//         // Apply the linear layer.
//         state[0] = sbox_deg_7;
//         matmul_internal(&mut state, *MATRIX_DIAG_16_BABYBEAR);
//
//         // Optimization: since we're only applying the sbox to the 0th state element, we only
//         // need to have columns for the 0th state element at every step. This is because the
//         // linear layer is degree 1, so all state elements at the end can be expressed as a
//         // degree-3 polynomial of the state at the beginning of the internal rounds and the 0th
//         // state element at rounds prior to the current round
//         if r < NUM_INTERNAL_ROUNDS - 1 {
//             poseidon2_cols.internal_rounds_s0[r] = state[0];
//         }
//     }
//
//     let ret_state = state;
//
//     if let Some(sbox) = sbox.as_deref_mut() {
//         *sbox = sbox_deg_3;
//     }
//
//     ret_state
// }
