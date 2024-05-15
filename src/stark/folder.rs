pub mod prover;

use crate::air::builder::{LookupBuilder, Relation};
use crate::stark::air::LogupBuilder;
use crate::stark::config::{PackedChallenge, PackedVal, StarkGenericConfig, Val};
use p3_air::{AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder};
use p3_field::AbstractField;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;



// type ViewPair<'a, T> = VerticalPair<RowMajorMatrixView<'a, T>, RowMajorMatrixView<'a, T>>;

// #[derive(Debug)]
// pub struct VerifierConstraintFolder<'a, SC: StarkGenericConfig> {
//     pub main: ViewPair<'a, SC::Challenge>,
//     pub public_values: &'a Vec<Val<SC>>,
//     pub is_first_row: SC::Challenge,
//     pub is_last_row: SC::Challenge,
//     pub is_transition: SC::Challenge,
//     pub alpha: SC::Challenge,
//     pub accumulator: SC::Challenge,
// }


// impl<'a, SC: StarkGenericConfig> AirBuilderWithPublicValues for ProverConstraintFolder<'a, SC> {
//     type PublicVar = Self::F;
//
//     fn public_values(&self) -> &[Self::F] {
//         self.public_values
//     }
// }

// impl<'a, SC: StarkGenericConfig> AirBuilder for VerifierConstraintFolder<'a, SC> {
//     type F = Val<SC>;
//     type Expr = SC::Challenge;
//     type Var = SC::Challenge;
//     type M = ViewPair<'a, SC::Challenge>;
//
//     fn main(&self) -> Self::M {
//         self.main
//     }
//
//     fn is_first_row(&self) -> Self::Expr {
//         self.is_first_row
//     }
//
//     fn is_last_row(&self) -> Self::Expr {
//         self.is_last_row
//     }
//
//     fn is_transition_window(&self, size: usize) -> Self::Expr {
//         if size == 2 {
//             self.is_transition
//         } else {
//             panic!("uni-stark only supports a window size of 2")
//         }
//     }
//
//     fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
//         let x: SC::Challenge = x.into();
//         self.accumulator *= self.alpha;
//         self.accumulator += x;
//     }
// }
//
// impl<'a, SC: StarkGenericConfig> AirBuilderWithPublicValues for VerifierConstraintFolder<'a, SC> {
//     type PublicVar = Self::F;
//
//     fn public_values(&self) -> &[Self::F] {
//         self.public_values
//     }
// }
