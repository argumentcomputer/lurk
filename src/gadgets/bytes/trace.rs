use crate::air::builder::{LookupBuilder, ProvideRecord};
use crate::gadgets::bytes::record::BytesRecord;
use crate::gadgets::bytes::relation::ByteRelation;
use crate::gadgets::bytes::ByteInput;
use crate::lair::execute::QueryRecord;
use crate::lair::lair_chip::LairMachineProgram;
use itertools::zip_eq;
use p3_air::{Air, BaseAir, PairBuilder};
use p3_field::{AbstractField, Field, PrimeField32};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use sphinx_core::air::{EventLens, MachineAir, WithEvents};
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};
use std::iter::zip;
use std::marker::PhantomData;
use std::mem::size_of;

struct BytesChip<F> {
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct PreprocessedBytesCols<T> {
    input1: T,
    input2: T,
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
    provides: [ProvideRecord<T>; NUM_PROVIDES],
}
const MAIN_BYTES_NUM_COLS: usize = size_of::<MainBytesCols<u8>>();

impl<F: Field> BaseAir<F> for BytesChip<F> {
    fn width(&self) -> usize {
        MAIN_BYTES_NUM_COLS
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let height = u16::MAX as usize;
        let width = PREPROCESSED_BYTES_NUM_COLS;
        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace.par_rows_mut().enumerate().for_each(|(i, row)| {
            let index = i as u16;
            let [input1, input2] = index.to_le_bytes();
            let row: &mut PreprocessedBytesCols<F> = row.borrow_mut();
            row.input1 = F::from_canonical_u8(input1);
            row.input2 = F::from_canonical_u8(input2);

            let input = ByteInput::new(input1, input2);

            row.less_than = F::from_bool(input.less_than());
            row.and = F::from_canonical_u8(input.and());
            row.xor = F::from_canonical_u8(input.xor());
            row.or = F::from_canonical_u8(input.or());

            // since msb only works over bytes, the result is duplicated 2^8 times.
            // this is okay since we can ignore them
            row.msb = F::from_bool(input.msb());
        });
        Some(trace)
    }
}

impl<F: Field> EventLens<BytesChip<F>> for QueryRecord<F> {
    fn events(&self) -> <BytesChip<F> as WithEvents<'_>>::Events {
        &self.byte_records
    }
}

impl<'a, F> WithEvents<'a> for BytesChip<F> {
    type Events = &'a BytesRecord;
}

impl<F: PrimeField32> MachineAir<F> for BytesChip<F> {
    type Record = QueryRecord<F>;
    type Program = LairMachineProgram;

    fn name(&self) -> String {
        "Bytes".to_string()
    }

    fn generate_trace<EL: EventLens<Self>>(
        &self,
        input: &EL,
        _output: &mut Self::Record,
    ) -> RowMajorMatrix<F> {
        let all_records = input.events();

        let height = u16::MAX as usize;
        let width = MAIN_BYTES_NUM_COLS;
        let mut trace = RowMajorMatrix::new(vec![F::zero(); height * width], width);

        trace.par_rows_mut().enumerate().for_each(|(index, row)| {
            let index = index as u16;
            let [i1, i2] = index.to_le_bytes();
            let input = ByteInput::new(i1, i2);
            let row: &mut MainBytesCols<F> = row.borrow_mut();

            if let Some(row_records) = all_records.get(input) {
                for (record, provide) in zip_eq(row_records.iter_records(), row.provides.iter_mut())
                {
                    provide.populate(record);
                }
            }
        });

        trace
    }

    fn generate_dependencies<EL: EventLens<Self>>(&self, _input: &EL, _output: &mut Self::Record) {}

    fn included(&self, shard: &Self::Record) -> bool {
        !shard.byte_records.is_empty()
    }

    fn preprocessed_width(&self) -> usize {
        PREPROCESSED_BYTES_NUM_COLS
    }

    fn generate_preprocessed_trace(&self, _program: &Self::Program) -> Option<RowMajorMatrix<F>> {
        self.preprocessed_trace()
    }
}

impl<AB: LookupBuilder + PairBuilder> Air<AB> for BytesChip<AB::F> {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep = prep.row_slice(0);
        let prep: &PreprocessedBytesCols<AB::Var> = (*prep).borrow();

        let main = builder.preprocessed();
        let main = main.row_slice(0);
        let main: &MainBytesCols<AB::Var> = (*main).borrow();

        let relations = [
            ByteRelation::range_u8_pair(prep.input1, prep.input2),
            ByteRelation::range_u16(prep.input1 + prep.input2 * AB::F::from_canonical_u16(1 << 8)),
            ByteRelation::less_than(prep.input1, prep.input2, prep.less_than),
            ByteRelation::and(prep.input1, prep.input2, prep.and),
            ByteRelation::xor(prep.input1, prep.input2, prep.xor),
            ByteRelation::xor(prep.input1, prep.input2, prep.or),
            ByteRelation::msb(prep.input1, prep.msb),
        ];

        for (relation, provide) in zip(relations, main.provides) {
            builder.provide(relation, provide, AB::F::one());
        }
    }
}
