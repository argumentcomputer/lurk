#[allow(unused)]
pub mod memoset;

use crate::memoset::DemoChip;
use loam::air::builder::{LookupBuilder, ProvideRecord, RequireRecord};
use loam::air::debug::{debug_constraints_collecting_queries, TraceQueries};
use p3_air::{Air, AirBuilder, BaseAir, PairBuilder};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_maybe_rayon::prelude::*;
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};
use std::collections::BTreeMap;

#[derive(Copy, Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
struct RangePreprocessedCols<T> {
    value: T,
}

#[derive(Copy, Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
struct RangeMainCols<T> {
    is_real: T,
    record: ProvideRecord<T>,
}

const NUM_RANGE_PREPROCESSED_COLS: usize = core::mem::size_of::<RangePreprocessedCols<u8>>();
const NUM_RANGE_MAIN_COLS: usize = core::mem::size_of::<RangeMainCols<u8>>();

struct RangeChip;

impl<F: Field> BaseAir<F> for RangeChip {
    fn width(&self) -> usize {
        NUM_RANGE_MAIN_COLS
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        const RANGE: u8 = u8::MAX;
        let height = RANGE as usize;
        let width = NUM_RANGE_PREPROCESSED_COLS;
        let values = 0..(RANGE);
        let mut rows = RowMajorMatrix::new(vec![F::zero(); width * height], width);

        rows.par_rows_mut().zip(values).for_each(|(row, value)| {
            let cols: &mut RangePreprocessedCols<F> = row.borrow_mut();

            cols.value = F::from_canonical_u8(value);
        });
        Some(rows)
    }
}

#[derive(Copy, Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
struct Cols<T> {
    is_real: T,
    nonce: T,
    value: T,
    record: RequireRecord<T>,
}

const NUM_CHIP_COLS: usize = core::mem::size_of::<Cols<u8>>();

struct Chip;

impl<F> BaseAir<F> for Chip {
    fn width(&self) -> usize {
        NUM_CHIP_COLS
    }
}

impl<AB: AirBuilder + LookupBuilder> Air<AB> for Chip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &Cols<AB::Var> = (*local).borrow();
        let next = main.row_slice(1);
        let next: &Cols<AB::Var> = (*next).borrow();

        // Enforce nonce is increasing and starts with 0
        builder.when_first_row().assert_zero(local.nonce);
        builder
            .when_transition()
            .assert_eq(local.nonce + AB::Expr::one(), next.nonce);

        builder.assert_bool(local.is_real);

        builder.require([local.value], local.nonce, local.record, local.is_real);
    }
}

impl<AB: AirBuilder + LookupBuilder + PairBuilder> Air<AB> for RangeChip {
    fn eval(&self, builder: &mut AB) {
        let preprocessed = builder.preprocessed();
        let preprocessed = preprocessed.row_slice(0);
        let preprocessed: &RangePreprocessedCols<AB::Var> = (*preprocessed).borrow();
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &RangeMainCols<AB::Var> = (*local).borrow();

        builder.provide([preprocessed.value], local.record, local.is_real);
    }
}

fn main() {
    type F = BabyBear;

    let tests = [0, 128, 0, 4, 0, 3, 127, F::neg_one().as_canonical_u32()];
    let main_width = NUM_CHIP_COLS;
    let main_height = tests.len();

    #[derive(Default)]
    struct Access<F> {
        nonce: F,
        count: F,
    }

    let mut require_record = BTreeMap::<u8, Access<F>>::new();

    let main = Chip;
    let mut main_trace = RowMajorMatrix::new(vec![F::zero(); main_width * main_height], main_width);
    main_trace
        .rows_mut()
        .zip(tests.iter())
        .enumerate()
        .for_each(|(nonce, (row, &test))| {
            let cols: &mut Cols<F> = row.borrow_mut();
            cols.nonce = F::from_canonical_usize(nonce);
            if let Ok(byte) = test.try_into() {
                cols.is_real = F::one();
                cols.value = F::from_canonical_u8(byte);

                let access = require_record.entry(byte).or_default();

                let prev_nonce = access.nonce;
                let prev_count = access.count;

                access.count += F::one();
                access.nonce = F::from_canonical_usize(nonce);

                cols.record = RequireRecord {
                    prev_nonce,
                    prev_count,
                    count_inv: access.count.inverse(),
                }
            }
        });
    let range = RangeChip;
    let range_width = NUM_RANGE_MAIN_COLS;
    let range_height = u8::MAX as usize;
    let range_preprocessed_trace = range.preprocessed_trace().unwrap();
    let mut range_main_trace =
        RowMajorMatrix::new(vec![F::zero(); range_width * range_height], range_width);
    range_main_trace
        .par_rows_mut()
        .enumerate()
        .for_each(|(index, row)| {
            let byte = index as u8;
            if let Some(record) = require_record.get(&byte) {
                let cols: &mut RangeMainCols<F> = row.borrow_mut();
                cols.is_real = F::one();
                cols.record = ProvideRecord {
                    last_nonce: record.nonce,
                    last_count: record.count,
                }
            }
        });

    let main_interactions = debug_constraints_collecting_queries(&main, &[], None, &main_trace);
    let range_interactions = debug_constraints_collecting_queries(
        &range,
        &[],
        Some(&range_preprocessed_trace),
        &range_main_trace,
    );

    TraceQueries::verify_many([main_interactions, range_interactions]);

    let demo_chip = DemoChip;
    let demo_trace = DemoChip::generate_demo_trace::<F>(1 << 10, 128);
    let demo_interaction = debug_constraints_collecting_queries(&demo_chip, &[], None, &demo_trace);
    demo_interaction.verify();
}
