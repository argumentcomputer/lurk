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
                QueryType::Require | QueryType::RequireOnce => {
                    required.insert(values);
                }
                QueryType::Provide | QueryType::ProvideOnce => {
                    provided.insert(values);
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

        // TODO: replace with builder.when(is_byte).require([byte]) when plonky3-air is updated
        builder.query(QueryType::Require, [byte], Some(is_byte.into()));
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

const BYTE_BASES: [u16; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

impl<AB: AirBuilder + LookupBuilder> Air<AB> for BytesChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();

        let local = main.row_slice(0);
        let byte = local[0];
        let bits = &local[1..9];
        let multiplicity = local[9];

        for bit in bits {
            builder.assert_bool(*bit);
        }

        let bases = BYTE_BASES.map(AB::Expr::from_canonical_u16);

        let mut byte_expected = AB::Expr::zero();
        for (bit, base) in bits.iter().zip(bases) {
            byte_expected += *bit * base;
        }

        builder.assert_eq(byte_expected, byte);

        // TODO: replace with builder.when(multiplicity).provide([byte]) when plonky3-air is updated
        builder.query(QueryType::Provide, [byte], Some(multiplicity.into()));
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

    let main_interactions = debug_constraints_collecting_queries(&MainChip, &[], &main_trace);
    let bytes_interactions =
        debug_constraints_collecting_queries(&BytesChip, &[], &bytes_trace);

    assert_zero_sum(vec![main_interactions, bytes_interactions]);
}
