mod debug_builder;
mod symbolic_builder;

use crate::debug_builder::{debug_constraints, LookupSet};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field};
use p3_matrix::{dense::RowMajorMatrix, Matrix};

pub trait LookupAirBuilder<T> {
    fn require<V: Into<T>, R: Into<T>>(&mut self, values: impl IntoIterator<Item = V>, is_real: R);
    fn provide<V: Into<T>, M: Into<T>>(
        &mut self,
        values: impl IntoIterator<Item = V>,
        multiplicity: M,
    );
}

/// Columns:
/// * byte[1]
/// * is_byte[1]
struct MainChip;

impl<F: Send + Sync> BaseAir<F> for MainChip {
    fn width(&self) -> usize {
        2
    }
}

impl<AB: AirBuilder + LookupAirBuilder<AB::Expr>> Air<AB> for MainChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);

        let (byte, is_byte) = (local[0], local[1]);

        builder.assert_bool(is_byte);

        builder.require([byte], is_byte);
    }
}

/// Columns:
/// * byte[1]
/// * bits[8]
/// * multiplicity[1]
struct BytesChip;

impl<F: Send + Sync> BaseAir<F> for BytesChip {
    fn width(&self) -> usize {
        10
    }
}

impl<AB: AirBuilder + LookupAirBuilder<AB::Expr>> Air<AB> for BytesChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let byte = local[0];
        let bits = &local[1..9];
        let multiplicity = local[9];

        for bit in bits {
            builder.assert_bool(*bit);
        }

        let bases = [1, 2, 4, 8, 16, 32, 64, 128].map(AB::Expr::from_canonical_u16);

        let mut byte_expected = AB::Expr::zero();
        for (bit, base) in bits.iter().zip(bases) {
            byte_expected += *bit * base;
        }

        builder.assert_eq(byte_expected, byte);

        builder.provide([byte], multiplicity);
    }
}

#[inline]
fn mk_matrix<F: Send + Sync + Clone, const H: usize, const W: usize>(
    data: [[F; W]; H],
) -> RowMajorMatrix<F> {
    RowMajorMatrix::new(data.into_iter().flatten().collect(), W)
}

fn main() {
    let f = BabyBear::from_canonical_u16;
    let main_trace = mk_matrix([
        [f(0), f(1)],
        [f(0), f(0)],
        [f(4), f(1)],
        [f(4), f(1)],
        [f(3), f(0)],
        [f(5), f(1)],
        [f(255), f(1)],
        [f(256), f(0)],
    ]);

    let bytes_trace = mk_matrix([
        [f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(4), f(0), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(2)],
        [f(5), f(1), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(255), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1)],
    ]);

    let mut lookups = LookupSet::default();
    debug_constraints(&MainChip, &main_trace, &mut lookups);
    debug_constraints(&BytesChip, &bytes_trace, &mut lookups);

    for m in lookups.values() {
        assert!(m.is_zero())
    }
}
