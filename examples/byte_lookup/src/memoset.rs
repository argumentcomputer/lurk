use loam::air::builder::{LookupBuilder, ProvideRecord, RequireRecord};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use rand::distributions::{Distribution, Standard, Uniform};
use rand::{Rng, SeedableRng};
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};
use std::collections::BTreeMap;
use std::mem::size_of;

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

#[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd)]
struct Count(usize);
#[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd)]
struct Nonce(u32);

#[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd)]
struct Access {
    nonce: Nonce,
    count: Count,
}

#[derive(AlignedBorrow, Clone, Copy)]
#[repr(C)]
union Record<T: Copy> {
    require: RequireRecord<T>,
    provide: ProvideRecord<T>,
}

impl<F: PrimeField32> Record<F> {
    fn new_require_record(prev_access: &Access) -> Self {
        let Access {
            nonce: Nonce(prev_nonce),
            count: Count(prev_count),
        } = prev_access;
        let count = prev_count + 1;
        let prev_nonce = F::from_canonical_u32(*prev_nonce);
        let prev_count = F::from_canonical_u32(*prev_count as u32);
        let count_inv = F::from_canonical_u32(count as u32).inverse();

        Record {
            require: RequireRecord {
                prev_nonce,
                prev_count,
                count_inv,
            },
        }
    }
    fn new_provide_record(last_access: &Access) -> Self {
        let Access {
            nonce: Nonce(last_nonce),
            count: Count(last_count),
        } = last_access;
        let last_nonce = F::from_canonical_u32(*last_nonce);
        let last_count = F::from_canonical_u32(*last_count as u32);

        Record {
            provide: ProvideRecord {
                last_nonce,
                last_count,
            },
        }
    }
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
        builder.provide(
            local.query,
            local.nonce,
            *local.record.provide(),
            local.is_provide,
        );
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
        log_height: usize,
        num_queries: usize,
    ) -> RowMajorMatrix<F>
    where
        Standard: Distribution<[F; QUERY_WIDTH]>,
    {
        #[derive(Copy, Clone, Default, Eq, PartialEq, Ord, PartialOrd)]
        struct Index(usize);

        let rng = &mut rand_chacha::ChaChaRng::seed_from_u64(0);
        let width = NUM_DEMO_COLS;
        let height = 1 << log_height;

        // Generate the queries, with a Vec for logging all accesses
        let mut records: BTreeMap<Index, (Query<F>, Vec<Access>)> = rng
            .sample_iter(Standard)
            .take(num_queries)
            .enumerate()
            .map(|(index, query)| (Index(index), (query, vec![])))
            .collect();

        let accesses: Vec<(Index, Access)> = rng
            .sample_iter(Uniform::from(0..num_queries))
            .take(height)
            .enumerate()
            .map(|(row, query_index)| {
                let nonce = Nonce(row as u32);
                let index = Index(query_index);

                let (_query, accesses) = records
                    .get_mut(&index)
                    .expect("query index should be valid");
                let count = Count(accesses.len());

                let access = Access { nonce, count };
                accesses.push(access);

                (index, access)
            })
            .collect();

        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace.par_rows_mut().zip(accesses).enumerate().for_each(
            |(nonce, (row, (index, access)))| {
                let cols: &mut DemoCols<F> = row.borrow_mut();

                let (query, accesses) = records
                    .get(&index)
                    .expect("records should contain a query for the index");

                cols.nonce = F::from_canonical_usize(nonce);
                cols.query = *query;

                match access.count {
                    Count(0) => {
                        cols.is_provide = F::one();
                        let last_access = accesses.last().expect("accesses should not be empty");
                        cols.record = Record::new_provide_record(last_access)
                    }
                    Count(count) => {
                        cols.is_require = F::one();
                        let prev_count = count - 1;
                        let prev_access = accesses
                            .get(prev_count)
                            .expect("accesses should not be empty");
                        cols.record = Record::new_require_record(prev_access)
                    }
                }
            },
        );

        trace
    }
}
