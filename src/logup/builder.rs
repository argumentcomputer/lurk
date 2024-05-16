use p3_air::{ExtensionBuilder, PairBuilder};
use p3_matrix::Matrix;

pub trait LogupBuilder: ExtensionBuilder + PairBuilder {
    type MP: Matrix<Self::VarEF>;

    type RandomVar: Into<Self::ExprEF> + Copy;

    /// Challenge for RLC of multiplicities
    fn logup_challenge_z_trace(&self) -> Self::RandomVar;

    /// Challenge for logUp root
    fn logup_challenge_r(&self) -> Self::RandomVar;

    /// Challenges for RLC of query values
    fn logup_challenge_gammas(&self) -> &[Self::RandomVar];

    /// Claimed logUp sum for trace
    fn logup_sum(&self) -> Self::ExprEF;

    /// Trace of RLC'd multiplicities. Width = |provides|.
    fn multiplicities(&self) -> Self::MP;

    /// Trace of logUp partial sums. Width = 1 + |provides| + |requires|
    fn permutation(&self) -> Self::MP;
}
