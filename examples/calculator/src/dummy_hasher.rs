use p3_air::AirBuilder;
use p3_field::AbstractField;
use std::mem::size_of;

#[derive(Default)]
pub(crate) struct DummyHasher<T> {
    pub(crate) pre0: T,
    pub(crate) pre1: T,
    pub(crate) pre2: T,
    pub(crate) pre3: T,
    pub(crate) img: T,
}

const NUM_COLS: usize = size_of::<DummyHasher<u8>>();

const CONSTS: [u32; 4] = [306711781, 394232706, 773645533, 242448779];

impl<F: AbstractField> DummyHasher<F> {
    pub(crate) fn hash(pre0: F, pre1: F, pre2: F, pre3: F) -> F {
        let consts: Vec<F> = CONSTS.iter().map(|c| F::from_canonical_u32(*c)).collect();
        pre0.clone() * consts[0].clone()
            + pre0 * consts[1].clone()
            + pre1.clone() * consts[1].clone()
            + pre1 * consts[2].clone()
            + pre2.clone() * consts[2].clone()
            + pre2 * consts[3].clone()
            + pre3.clone() * consts[3].clone()
            + pre3 * consts[0].clone()
    }

    pub(crate) fn compute_row(pre0: F, pre1: F, pre2: F, pre3: F) -> [F; NUM_COLS] {
        [
            pre0.clone(),
            pre1.clone(),
            pre2.clone(),
            pre3.clone(),
            Self::hash(pre0, pre1, pre2, pre3),
        ]
    }
}

impl<V> DummyHasher<V> {
    pub(crate) fn eval<AB: AirBuilder<Var = V>>(
        builder: &mut AB,
        is_real: V,
        pre0: V,
        pre1: V,
        pre2: V,
        pre3: V,
        img: V,
    ) where
        V: Into<AB::Expr>,
    {
        let consts: Vec<AB::Expr> = CONSTS
            .iter()
            .map(|c| AB::F::from_canonical_u32(*c).into())
            .collect();

        let pre0 = pre0.into();
        let pre1 = pre1.into();
        let pre2 = pre2.into();
        let pre3 = pre3.into();

        let out = pre0.clone() * consts[0].clone()
            + pre0 * consts[1].clone()
            + pre1.clone() * consts[1].clone()
            + pre1 * consts[2].clone()
            + pre2.clone() * consts[2].clone()
            + pre2 * consts[3].clone()
            + pre3.clone() * consts[3].clone()
            + pre3 * consts[0].clone();

        builder.when(is_real).assert_eq(out, img)
    }
}
