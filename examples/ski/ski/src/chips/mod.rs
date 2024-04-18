use p3_air::{Air, BaseAir};
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use wp1_core::stark::SP1AirBuilder;
use wp1_derive::AlignedBorrow;

use std::mem::size_of;

// struct EvalCols {}
// struct ApplyCols {}
// struct Eval1Cols {}
// struct SCols {}
// struct S1Cols {}
// struct S2Cols {}
// struct S3Cols {}
// struct KCols {}
// struct K1Cols {}
// struct K2Cols {}
// struct ICols {}
// struct I1Cols {}

#[derive(AlignedBorrow)]
struct CpuCols<T> {
    _x: T,
}

struct CpuChip {}

const NUM_CPU_COLS: usize = size_of::<CpuCols<u8>>();

impl<F: Send + Sync> BaseAir<F> for CpuChip {
    fn width(&self) -> usize {
        NUM_CPU_COLS
    }
}

impl CpuChip {
    #[allow(dead_code)]
    fn generate_trace<F: Field>() -> RowMajorMatrix<F> {
        todo!()
    }
}

impl<AB: SP1AirBuilder> Air<AB> for CpuChip {
    fn eval(&self, _builder: &mut AB) {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::AbstractField;
    use p3_matrix::dense::RowMajorMatrix;
    use wp1_core::{
        stark::StarkGenericConfig,
        utils::{uni_stark_prove as prove, uni_stark_verify as verify, BabyBearPoseidon2},
    };

    use super::*;

    #[allow(dead_code)]
    fn prove_trace() {
        let config = BabyBearPoseidon2::new();
        let mut challenger = config.challenger();

        let _f = BabyBear::from_canonical_usize;

        let trace: RowMajorMatrix<BabyBear> = CpuChip::generate_trace();

        let chip = CpuChip {};
        let proof = prove::<BabyBearPoseidon2, _>(&config, &chip, &mut challenger, trace);

        let mut challenger = config.challenger();
        verify(&config, &chip, &mut challenger, &proof).unwrap();
    }
}
