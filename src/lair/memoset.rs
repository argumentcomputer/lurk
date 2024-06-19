use itertools::chain;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{AbstractField, Field};
use p3_matrix::Matrix;
use sphinx_core::air::{AirInteraction, BaseAirBuilder};
use sphinx_core::lookup::InteractionKind;
use std::iter::zip;
use std::marker::PhantomData;

pub struct MemoSetChip<F> {
    len: usize,
    _marker: PhantomData<F>,
}

impl<F: Field> BaseAir<F> for MemoSetChip<F> {
    fn width(&self) -> usize {
        2 + self.len
    }
}

impl<AB> Air<AB> for MemoSetChip<AB::F>
where
    AB: BaseAirBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &[AB::Var] = &main.row_slice(0);
        let next: &[AB::Var] = &main.row_slice(1);

        let (is_require, is_provide, query_local) = (local[0], local[1], &local[2..]);
        let (is_require_next, is_provide_next, query_next) = (next[0], next[1], &next[2..]);

        builder.assert_bool(is_require);
        builder.assert_bool(is_provide);

        let is_real = is_require + is_provide;

        let is_real_next = is_require_next + is_provide_next;
        builder.assert_bool(is_real.clone());
        // is_real starts with one
        builder.when_first_row().assert_one(is_real.clone());
        // if next is real, local is real
        builder
            .when_transition()
            .when(is_real_next.clone())
            .assert_one(is_real.clone());

        // The current row is real, and either it is the last row, or the next row is not real.
        let is_last_real = is_real.clone()
            * (builder.is_last_row() + builder.is_transition() * (AB::Expr::one() - is_real_next));

        // when the next row is not real, ensure the last query was provided
        builder.when(is_last_real).assert_one(is_provide);

        // A require query must repeat to the next row, until it is provided.
        for (&val_local, &val_next) in zip(query_local, query_next) {
            builder.when(is_require).assert_eq(val_local, val_next);
        }

        const REQUIRE_TAG: u32 = 1;
        const PROVIDE_TAG: u32 = 2;

        let tag = AB::Expr::from_canonical_u32(REQUIRE_TAG) * is_require
            + AB::Expr::from_canonical_u32(PROVIDE_TAG) * is_provide;

        builder.send(AirInteraction {
            values: chain([tag], query_local.iter().copied().map(Into::into)).collect(),
            multiplicity: is_real,
            kind: InteractionKind::Instruction,
        })
    }
}

// impl<F: Field> EventLens<MemoSetChip<F>> for QueryRecord<F> {
//     fn events(&self) -> <MemoSetChip<F> as WithEvents<'_>>::Events {
//         // self.mem_queries.as_slice()
//     }
// }
//
// impl<'a, F: Field> WithEvents<'a> for MemoSetChip<F> {
//     type Events = &'a [MemMap<F>];
// }
//
// impl<F: Field> MachineAir<F> for MemoSetChip<F> {
//     type Record = QueryRecord<F>;
//     type Program = QueryRecord<F>;
//
//     fn name(&self) -> String {
//         format!("mem {}", self.len).to_string()
//     }
//
//     fn generate_trace<EL: EventLens<Self>>(
//         &self,
//         input: &EL,
//         _output: &mut Self::Record,
//     ) -> RowMajorMatrix<F> {
//         let len = self.len;
//         let mem_idx = mem_index_from_len(len);
//         let mem = &input.events()[mem_idx];
//         let width = self.width();
//     }
//
//     fn included(&self, _shard: &Self::Record) -> bool {
//         true
//     }
// }
