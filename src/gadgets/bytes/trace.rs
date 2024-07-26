use crate::air::builder::{LookupBuilder, ProvideRecord};
use crate::gadgets::bytes::record::BytesRecord;
use crate::gadgets::bytes::relation::ByteRelation;
use crate::gadgets::bytes::ByteInput;
use itertools::zip_eq;
use p3_air::{Air, BaseAir, PairBuilder};
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};
use std::marker::PhantomData;
use std::mem::size_of;

#[derive(Default)]
pub struct BytesChip<F> {
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct PreprocessedBytesCols<T> {
    input: (T, T),
    less_than: T,
    and: T,
    xor: T,
    or: T,
    msb: T,
}

const PREPROCESSED_BYTES_NUM_COLS: usize = size_of::<PreprocessedBytesCols<u8>>();

const NUM_PROVIDES: usize = 7;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct MainBytesCols<T> {
    is_real: T,
    provides: [ProvideRecord<T>; NUM_PROVIDES],
}
const MAIN_BYTES_NUM_COLS: usize = size_of::<MainBytesCols<u8>>();

impl<F: Field> BaseAir<F> for BytesChip<F> {
    fn width(&self) -> usize {
        MAIN_BYTES_NUM_COLS
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let height = 1 << 16;
        let width = PREPROCESSED_BYTES_NUM_COLS;
        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace.par_rows_mut().enumerate().for_each(|(i, row)| {
            let index = i as u16;
            let row: &mut PreprocessedBytesCols<F> = row.borrow_mut();

            let input = ByteInput::from_u16(index);
            row.input = input.as_field_u8_pair();

            row.less_than = F::from_bool(input.less_than());
            row.and = F::from_canonical_u8(input.and());
            row.xor = F::from_canonical_u8(input.xor());
            row.or = F::from_canonical_u8(input.or());
        });
        Some(trace)
    }
}

impl<F: PrimeField32> BytesChip<F> {
    pub fn name(&self) -> String {
        "Bytes".to_string()
    }

    pub fn generate_trace(&self, bytes_record: &BytesRecord) -> RowMajorMatrix<F> {
        let height = 1 << 16;
        let width = MAIN_BYTES_NUM_COLS;
        let is_real = self.included(bytes_record);
        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        // When not real, the empty trace is valid and will not provide any events
        if !is_real {
            return trace;
        }
        trace.par_rows_mut().enumerate().for_each(|(index, row)| {
            let index = index as u16;
            let input = ByteInput::from_u16(index);
            let row: &mut MainBytesCols<F> = row.borrow_mut();

            row.is_real = F::from_bool(is_real);

            if let Some(row_records) = bytes_record.get(input) {
                for (record, provide) in zip_eq(row_records.iter_records(), row.provides.iter_mut())
                {
                    provide.populate(record);
                }
            }
        });

        trace
    }

    pub fn included(&self, byte_record: &BytesRecord) -> bool {
        !byte_record.is_empty()
    }

    pub fn preprocessed_width(&self) -> usize {
        PREPROCESSED_BYTES_NUM_COLS
    }

    pub fn generate_preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        self.preprocessed_trace()
    }
}

impl<AB: LookupBuilder + PairBuilder> Air<AB> for BytesChip<AB::F> {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep = prep.row_slice(0);
        let prep: &PreprocessedBytesCols<AB::Var> = (*prep).borrow();

        let main = builder.main();
        let main = main.row_slice(0);
        let main: &MainBytesCols<AB::Var> = (*main).borrow();

        builder.assert_bool(main.is_real);

        let input_u16 = prep.input.0 + prep.input.1 * AB::F::from_canonical_u16(1 << 8);

        let relations = [
            ByteRelation::range_u8_pair(prep.input.0, prep.input.1),
            ByteRelation::range_u16(input_u16),
            ByteRelation::less_than(prep.input.0, prep.input.1, prep.less_than),
            ByteRelation::and(prep.input.0, prep.input.1, prep.and),
            ByteRelation::xor(prep.input.0, prep.input.1, prep.xor),
            ByteRelation::or(prep.input.0, prep.input.1, prep.or),
        ];

        for (relation, provide) in relations.into_iter().zip(main.provides.into_iter()) {
            builder.provide(relation, provide, main.is_real);
        }
    }
}
