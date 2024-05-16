use p3_air::{ExtensionBuilder, PairBuilder};
use p3_matrix::Matrix;
use crate::air::builder::AirBuilderExt;

pub trait LogupBuilder: ExtensionBuilder + PairBuilder + AirBuilderExt {
    type MP: Matrix<Self::VarEF>;

    type RandomVar: Into<Self::ExprEF> + Copy;

    /// Challenge for random-linear combination of
    fn logup_challenge_z_trace(&self) -> Self::RandomVar;

    fn logup_challenge_r(&self) -> Self::RandomVar;

    fn logup_challenge_gammas(&self) -> &[Self::RandomVar];

    fn logup_sum(&self) -> Self::ExprEF;

    fn multiplicities(&self) -> Self::MP;

    fn permutation(&self) -> Self::MP;
}
