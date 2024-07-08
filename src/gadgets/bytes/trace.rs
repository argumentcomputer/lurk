use crate::air::builder::{LookupBuilder, ProvideRecord, Relation};
use crate::gadgets::bytes::{ByteInput, ByteRecord};
use crate::lair::execute::QueryRecord;
use crate::lair::lair_chip::LairMachineProgram;
use itertools::chain;
use p3_air::{Air, BaseAir, PairBuilder};
use p3_field::{AbstractField, Field};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use sphinx_core::air::{EventLens, MachineAir, WithEvents};
use sphinx_derive::AlignedBorrow;
use std::borrow::{Borrow, BorrowMut};
use std::marker::PhantomData;
use std::mem::size_of;

const BYTE_TAG: u8 = 3;

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

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct MainBytesCols<T> {
    range_u8_pair: ProvideRecord<T>,
    range_u16: ProvideRecord<T>,
    less_than: ProvideRecord<T>,
    and: ProvideRecord<T>,
    xor: ProvideRecord<T>,
    or: ProvideRecord<T>,
    msb: ProvideRecord<T>,
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

// impl<F: Field> EventLens<BytesChip<F>> for QueryRecord<F> {
//     fn events(&self) -> <BytesChip<F> as WithEvents<'_>>::Events {
//         self.mem_queries.as_slice()
//     }
// }
//
//
// impl<'a, F> WithEvents<'a> for BytesChip<F> {
//     type Events =ByteRecord<F>;
// }

// impl<F: Field> MachineAir<F> for BytesChip<F> {
//     type Record = QueryRecord<F>;
//     type Program = LairMachineProgram;
//
//     fn name(&self) -> String {
//         "Bytes".to_string()
//     }
//
//     fn generate_trace<EL: EventLens<Self>>(
//         &self,
//         input: &EL,
//         _output: &mut Self::Record,
//     ) -> RowMajorMatrix<F> {
//         todo!()
//     }
//
//     fn generate_dependencies<EL: EventLens<Self>>(&self, _input: &EL, _output: &mut Self::Record) {}
//
//     fn included(&self, _shard: &Self::Record) -> bool {
//         true
//     }
//
//     fn preprocessed_width(&self) -> usize {
//         PREPROCESSED_BYTES_NUM_COLS
//     }
//
//     fn generate_preprocessed_trace(&self, _program: &Self::Program) -> Option<RowMajorMatrix<F>> {
//         self.preprocessed_trace()
//     }
// }

pub enum ByteRelation<T> {
    RangeU8Pair { i1: T, i2: T },
    RangeU16 { i: T },
    LessThan { i1: T, i2: T, less_than: T },
    And { i1: T, i2: T, and: T },
    Xor { i1: T, i2: T, xor: T },
    Or { i1: T, i2: T, or: T },
    Msb { i: T, msb: T },
}

impl<T> ByteRelation<T> {
    pub fn tag(&self) -> u8 {
        match self {
            Self::RangeU8Pair { .. } => 1,
            Self::RangeU16 { .. } => 2,
            Self::LessThan { .. } => 3,
            Self::And { .. } => 4,
            Self::Xor { .. } => 5,
            Self::Or { .. } => 6,
            Self::Msb { .. } => 7,
        }
    }
}

impl<F: AbstractField> Relation<F> for ByteRelation<F> {
    fn values(self) -> impl IntoIterator<Item = F> {
        let relation_tag = F::from_canonical_u8(BYTE_TAG);
        let operation_tag = F::from_canonical_u8(self.tag());
        let operation = match self {
            ByteRelation::RangeU8Pair { i1, i2 } => vec![i1, i2],
            ByteRelation::RangeU16 { i } => vec![i],
            ByteRelation::LessThan { i1, i2, less_than } => vec![i1, i2, less_than],
            ByteRelation::And { i1, i2, and } => vec![i1, i2, and],
            ByteRelation::Xor { i1, i2, xor } => vec![i1, i2, xor],
            ByteRelation::Or { i1, i2, or } => vec![i1, i2, or],
            ByteRelation::Msb { i, msb } => vec![i, msb],
        };
        chain([relation_tag, operation_tag], operation)
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

        builder.provide(
            ByteRelation::RangeU8Pair {
                i1: prep.input1.into(),
                i2: prep.input2.into(),
            },
            main.range_u8_pair,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::RangeU16 {
                i: prep.input1 + prep.input2 * AB::F::from_canonical_u16(1 << 8),
            },
            main.range_u16,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::LessThan {
                i1: prep.input1.into(),
                i2: prep.input2.into(),
                less_than: prep.less_than.into(),
            },
            main.less_than,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::And {
                i1: prep.input1.into(),
                i2: prep.input2.into(),
                and: prep.and.into(),
            },
            main.and,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::Xor {
                i1: prep.input1.into(),
                i2: prep.input2.into(),
                xor: prep.xor.into(),
            },
            main.xor,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::Or {
                i1: prep.input1.into(),
                i2: prep.input2.into(),
                or: prep.or.into(),
            },
            main.or,
            AB::F::one(),
        );
        builder.provide(
            ByteRelation::Msb {
                i: prep.input1.into(),
                msb: prep.or.into(),
            },
            main.msb,
            AB::F::one(),
        );
    }
}
