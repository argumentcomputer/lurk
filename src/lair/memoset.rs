use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::AbstractField;
use p3_matrix::Matrix;
use std::iter::zip;

pub struct MemoSetChip {
    len: usize,
}

impl<F> BaseAir<F> for MemoSetChip {
    fn width(&self) -> usize {
        2 + self.len
    }
}

impl<AB> Air<AB> for MemoSetChip
where
    AB: AirBuilder,
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
        {
            let is_real_next = is_require_next + is_provide_next;
            builder.assert_bool(is_real.clone());
            // is_real starts with one
            builder.when_first_row().assert_one(is_real.clone());
            // if next is real, local is real
            builder
                .when_transition()
                .when(is_real_next.clone())
                .assert_one(is_real.clone());

            let is_last_real = builder.is_transition() * (AB::Expr::one() - is_real_next)
                + builder.is_last_row() * is_real;
            // when the next row is not real, ensure the last query was provided
            builder.when(is_last_real).assert_one(is_provide)
        }

        // A require query must repeat to the next row
        for (&val_local, &val_next) in zip(query_local, query_next) {
            builder.when(is_require).assert_eq(val_local, val_next);
        }

        const REQUIRE_TAG: u32 = 1;
        const PROVIDE_TAG: u32 = 2;

        let tag = AB::Expr::from_canonical_u32(REQUIRE_TAG) * is_require
            + AB::Expr::from_canonical_u32(PROVIDE_TAG) * is_provide;

        // builder.when(is_real).send([tag, query]);
    }
}
