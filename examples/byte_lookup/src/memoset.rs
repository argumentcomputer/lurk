use lurk::air::builder::{LookupBuilder, ProvideRecord, RequireRecord};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use rand::distributions::{Distribution, Standard, Uniform};
use rand::{Rng, SeedableRng};
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};

const QUERY_WIDTH: usize = 8;
type Query<F> = [F; QUERY_WIDTH];

#[derive(AlignedBorrow, Clone, Copy)]
#[repr(C)]
struct DemoCols<T: Copy> {
    is_require: T,
    is_provide: T,
    nonce: T,
    query: Query<T>,
    record: Record<T>,
}

const NUM_DEMO_COLS: usize = size_of::<DemoCols<u8>>();

#[derive(AlignedBorrow, Clone, Copy)]
#[repr(C)]
pub union Record<T: Copy> {
    require: RequireRecord<T>,
    provide: ProvideRecord<T>,
}

pub struct DemoChip;

impl<F: Field> BaseAir<F> for DemoChip {
    fn width(&self) -> usize {
        NUM_DEMO_COLS
    }
}

impl<AB: AirBuilder + LookupBuilder> Air<AB> for DemoChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &DemoCols<AB::Var> = (*local).borrow();
        let next = main.row_slice(1);
        let next: &DemoCols<AB::Var> = (*next).borrow();

        builder.assert_bool(local.is_provide);
        builder.assert_bool(local.is_require);
        let is_real = local.is_provide + local.is_require;
        builder.assert_bool(is_real.clone());

        builder.when_first_row().assert_zero(local.nonce);
        builder
            .when_transition()
            .assert_eq(local.nonce + AB::Expr::one(), next.nonce);

        builder.require(
            local.query,
            local.nonce,
            *local.record.require(),
            local.is_require,
        );
        builder.provide(local.query, *local.record.provide(), local.is_provide);
    }
}

// SAFETY: Each view is a valid interpretation of the underlying array.
impl<T: Copy> Record<T> {
    pub fn require(&self) -> &RequireRecord<T> {
        unsafe { &self.require }
    }

    pub fn require_mut(&mut self) -> &mut RequireRecord<T> {
        unsafe { &mut self.require }
    }

    pub fn provide(&self) -> &ProvideRecord<T> {
        unsafe { &self.provide }
    }

    pub fn provide_mut(&mut self) -> &mut ProvideRecord<T> {
        unsafe { &mut self.provide }
    }
}

impl DemoChip {
    pub fn generate_demo_trace<F: PrimeField32>(
        num_rows: usize,
        num_queries: usize,
    ) -> RowMajorMatrix<F>
    where
        Standard: Distribution<[F; QUERY_WIDTH]>,
    {
        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(0);
        let width = NUM_DEMO_COLS;
        let height = num_rows.next_power_of_two();

        let queries: Vec<Query<F>> = rng.sample_iter(Standard).take(num_queries).collect();

        // Generate the queries, with a Vec for logging the nonces of the accesses
        let mut records = vec![Vec::<usize>::new(); num_queries];

        // (query_index, count)
        let accesses: Vec<(usize, usize)> = rng
            .sample_iter(Uniform::from(0..num_queries))
            .take(num_rows)
            .enumerate()
            .map(|(row, query_index)| {
                let records = &mut records[query_index];

                let count = records.len();
                let nonce = if count == 0 { 0 } else { row };
                records.push(nonce);

                (query_index, count)
            })
            .collect();

        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace.par_rows_mut().zip(accesses).enumerate().for_each(
            |(nonce, (row, (query_index, count)))| {
                let cols: &mut DemoCols<F> = row.borrow_mut();

                cols.nonce = F::from_canonical_usize(nonce);
                cols.query = queries[query_index];
                let records = &records[query_index];

                match count {
                    // Provide
                    0 => {
                        cols.is_provide = F::one();
                        let last_count = records.len() - 1;
                        let last_nonce = records[last_count];
                        cols.record.provide = ProvideRecord {
                            last_nonce: F::from_canonical_usize(last_nonce),
                            last_count: F::from_canonical_usize(last_count),
                        }
                    }
                    // Require
                    count => {
                        cols.is_require = F::one();
                        let prev_count = count - 1;
                        let prev_nonce = records[prev_count];

                        cols.record.require = RequireRecord {
                            prev_nonce: F::from_canonical_usize(prev_nonce),
                            prev_count: F::from_canonical_usize(prev_count),
                            count_inv: F::from_canonical_usize(count).inverse(),
                        }
                    }
                }
            },
        );

        trace
    }
}
