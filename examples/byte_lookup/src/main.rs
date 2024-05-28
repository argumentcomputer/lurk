use loam::air::builder::{LookupBuilder, QueryType};
use loam::air::debug::{debug_constraints_collecting_queries, Query};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use std::collections::BTreeSet;

fn assert_zero_sum<F: PrimeField>(interactions_vecs: Vec<Vec<Query<F>>>) {
    let mut provided = BTreeSet::<Vec<F>>::default();
    let mut required = BTreeSet::<Vec<F>>::default();
    for interactions in interactions_vecs {
        for Query { query_type, values } in interactions {
            match query_type {
                QueryType::Receive | QueryType::Provide => {
                    provided.insert(values);
                }
                QueryType::Send | QueryType::Require => {
                    required.insert(values);
                }
            };
        }
    }
    assert_eq!(provided, required);
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

impl<AB: AirBuilder + LookupBuilder> Air<AB> for MainChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);

        let (byte, is_byte) = (local[0], local[1]);

        builder.assert_bool(is_byte);

        builder.when(is_byte).require([byte]);
    }
}

/// Columns:
/// * byte[1]
/// * bits[8]
/// * is_real[1]
struct BytesChip;

impl<F: Send + Sync> BaseAir<F> for BytesChip {
    fn width(&self) -> usize {
        10
    }
}

const BYTE_BASES: [u16; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

impl<AB: AirBuilder + LookupBuilder> Air<AB> for BytesChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let byte = local[0];
        let bits = &local[1..9];
        let is_real = local[9];

        builder.assert_bool(is_real);

        for bit in bits {
            builder.when(is_real).assert_bool(*bit);
        }

        let bases = BYTE_BASES.map(AB::Expr::from_canonical_u16);

        let mut byte_expected = AB::Expr::zero();
        for (bit, base) in bits.iter().zip(bases) {
            byte_expected += *bit * base;
        }

        builder.when(is_real).assert_eq(byte_expected, byte);

        builder.when(is_real).provide([byte]);
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
        [f(4), f(0), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(5), f(1), f(0), f(1), f(0), f(0), f(0), f(0), f(0), f(1)],
        [f(255), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(1)],
        [f(256), f(5), f(1), f(1), f(1), f(1), f(1), f(1), f(1), f(0)],
    ]);

    let _multiplicities = [[1], [2], [1], [1], [0]].map(|row| row.map(f));

    let main_interactions = debug_constraints_collecting_queries(&MainChip, &[], &main_trace);
    let bytes_interactions = debug_constraints_collecting_queries(&BytesChip, &[], &bytes_trace);

    assert_zero_sum(vec![main_interactions, bytes_interactions]);
}
