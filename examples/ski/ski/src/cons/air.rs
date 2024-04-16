use crate::air::builder::LurkAirBuilder;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::AbstractField;
use p3_matrix::MatrixRowSlices;
use std::{borrow::Borrow, mem::size_of};

use crate::cons::columns::ConsCols;
use crate::cons::{ConsChip, CAR_TAG, CDR_TAG, CONST_PTR_TAG};

pub const NUM_CONS_COLS: usize = size_of::<ConsCols<u8>>();

impl<F> BaseAir<F> for ConsChip {
    fn width(&self) -> usize {
        NUM_CONS_COLS
    }
}

impl<AB> Air<AB> for ConsChip
where
    AB: LurkAirBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &ConsCols<AB::Var> = main.row_slice(0).borrow();
        let next: &ConsCols<AB::Var> = main.row_slice(1).borrow();

        // Ensure the first pointer has index 0
        builder.when_first_row().assert_zero(local.c_ptr.idx);

        // Ensure the pointer index increases at every row
        builder
            .when_transition()
            .assert_eq(local.c_ptr.idx + AB::F::one(), next.c_ptr.idx);

        builder.assert_eq(local.c_ptr.tag, AB::F::from_canonical_u16(CONST_PTR_TAG));

        builder.prove_cons(local.a_ptr, local.b_ptr, local.c_ptr, local.mult_cons);
        builder.prove_relation(
            AB::F::from_canonical_u16(CAR_TAG),
            local.a_ptr,
            local.c_ptr,
            local.mult_car,
        );
        builder.prove_relation(
            AB::F::from_canonical_u16(CDR_TAG),
            local.b_ptr,
            local.c_ptr,
            local.mult_car,
        );
    }
}
