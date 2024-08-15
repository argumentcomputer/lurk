use crate::gadgets::bytes::ByteAirRecord;
use crate::gadgets::unsigned::add::AddOne;
use crate::gadgets::unsigned::less_than::LessThanWitness;
use crate::gadgets::unsigned::Word;
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use std::borrow::Borrow;

/// Use `u24` for depth.
const DEPTH_W: usize = 3;

type Depth<F> = Word<F, DEPTH_W>;

pub fn populate_max<F: PrimeField>(depths: Vec<u32>, witness: &mut [F]) {
    todo!()
}

pub fn witness_size(num_depths: usize) -> usize {
    todo!()
}

pub fn eval_max<AB: AirBuilder>(
    builder: &mut AB,
    depths: Vec<Depth<AB::Var>>,
    witness: &[AB::Var],
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) -> Depth<AB::Expr> {
    let is_real = is_real.into();
    if depths.len() == 1 {
        let add_one_witness: &AddOne<AB::Var, DEPTH_W> = witness.borrow();
        let (depth, carry) =
            add_one_witness.eval(builder, depths[0].clone().into(), is_real.clone());
        builder.when(is_real).assert_zero(carry);
        depth.into()
    } else {
        let (depth_witness, mut witness) = witness.split_at(DEPTH_W);
        let depth: &Depth<AB::Var> = depth_witness.borrow();
        let depth = depth.clone().into();

        for other_depth in depths {
            let less_than_witness;
            (less_than_witness, witness) =
                witness.split_at(LessThanWitness::<AB::Var, DEPTH_W>::witness_size());
            let less_than_witness: &LessThanWitness<AB::Var, DEPTH_W> = less_than_witness.borrow();
            less_than_witness.assert_is_less_than(
                builder,
                &other_depth.into(),
                &depth,
                AB::Expr::one(),
                record,
                is_real.clone(),
            );
        }
        assert!(witness.is_empty());

        depth
    }
}
