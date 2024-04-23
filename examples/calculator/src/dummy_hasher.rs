use p3_air::AirBuilder;
use p3_field::AbstractField;

#[derive(Default)]
pub(crate) struct DummyHasher;

const CONSTS: [u32; 4] = [306711781, 394232706, 773645533, 242448779];

impl DummyHasher {
    pub(crate) fn hash<F: AbstractField>(preimg: [F; 4]) -> F {
        let c0 = F::from_canonical_u32(CONSTS[0]);
        let c1 = F::from_canonical_u32(CONSTS[1]);
        let c2 = F::from_canonical_u32(CONSTS[2]);
        let c3 = F::from_canonical_u32(CONSTS[3]);
        let [pre0, pre1, pre2, pre3] = preimg;
        pre0.clone() * c0.clone()
            + pre0 * c1.clone()
            + pre1.clone() * c1
            + pre1 * c2.clone()
            + pre2.clone() * c2
            + pre2 * c3.clone()
            + pre3.clone() * c3
            + pre3 * c0
    }

    #[inline]
    pub(crate) fn eval<AB, I, O>(
        builder: &mut AB,
        input: [I; 4],
        output: O,
        is_real: impl Into<AB::Expr>,
    ) where
        AB: AirBuilder,
        I: Into<AB::Expr>,
        O: Into<AB::Expr>,
    {
        builder
            .when(is_real.into())
            .assert_eq(Self::hash(input.map(I::into)), output.into())
    }
}
