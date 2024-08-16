use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::add::AddOne;
use crate::gadgets::unsigned::less_than::LessThanWitness;
use crate::gadgets::unsigned::{UncheckedWord, Word};
use p3_air::AirBuilder;
use p3_field::PrimeField;
use std::borrow::{Borrow, BorrowMut};
use std::iter::zip;

/// Use `u32` for depth.
const DEPTH_W: usize = 4;

type Depth<F> = Word<F, DEPTH_W>;
type UncheckedDepth<F> = UncheckedWord<F, DEPTH_W>;

type DepthLessThan<F> = LessThanWitness<F, DEPTH_W>;
type DepthAddOne<F> = AddOne<F, DEPTH_W>;
const DEPTH_LESS_THAN_SIZE: usize = DepthLessThan::<u8>::witness_size();
const DEPTH_ADD_ONE_SIZE: usize = DepthAddOne::<u8>::witness_size();

pub fn populate_max<F: PrimeField>(
    depths: &[u32],
    witness: &mut [F],
    record: &mut impl ByteRecord,
) -> u32 {
    match depths.len() {
        0 => 0,
        1 => {
            let witness: &mut DepthAddOne<F> = witness.borrow_mut();
            witness.populate(&depths[0])
        }
        _ => {
            let depth = depths.iter().max().unwrap() + 1;
            let (unchecked_depth, witness) = witness.split_at_mut(DEPTH_W);
            let unchecked_depth: &mut UncheckedDepth<F> = unchecked_depth.borrow_mut();
            unchecked_depth.assign_bytes(&depth.to_le_bytes(), record);

            for (other_depth, witness) in
                zip(depths, witness.chunks_exact_mut(DEPTH_LESS_THAN_SIZE))
            {
                let less_than_witness: &mut DepthLessThan<F> = witness.borrow_mut();
                less_than_witness.populate(other_depth, &depth, record);
            }

            depth
        }
    }
}

pub const fn witness_size(num_depths: usize) -> usize {
    match num_depths {
        0 => 0,
        1 => DEPTH_ADD_ONE_SIZE,
        _ => DEPTH_W + num_depths * DEPTH_LESS_THAN_SIZE,
    }
}

pub const fn num_requires(num_depths: usize) -> usize {
    match num_depths {
        0 | 1 => 0,
        _ => {
            DEPTH_W/2 // Range-check output depth
                + num_depths * DepthLessThan::<u8>::num_requires()
        } // Less than,
    }
}

pub fn eval_max<AB: AirBuilder>(
    builder: &mut AB,
    depths: Vec<Depth<AB::Var>>,
    witness: &[AB::Var],
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) -> Depth<AB::Expr> {
    let is_real = is_real.into();
    match depths.len() {
        0 => Depth::zero(),
        1 => {
            let add_one_witness: &DepthAddOne<AB::Var> = witness.borrow();
            let (depth, carry) =
                add_one_witness.eval(builder, depths[0].clone().into(), is_real.clone());
            builder.when(is_real).assert_zero(carry);
            depth.into()
        }
        _ => {
            // Load the max depth and check the range
            let (depth_unchecked, witness) = witness.split_at(DEPTH_W);
            let depth_unchecked: UncheckedDepth<AB::Var> = *depth_unchecked.borrow();
            let depth: Depth<AB::Expr> =
                depth_unchecked.into_checked(record, is_real.clone()).into();

            // For each other depth, ensure it is less than the other depths
            for (other_depth, less_than_witness) in
                zip(depths, witness.chunks_exact(DEPTH_LESS_THAN_SIZE))
            {
                let less_than_witness: &DepthLessThan<AB::Var> = less_than_witness.borrow();

                less_than_witness.assert_less_than(
                    builder,
                    &other_depth.into(),
                    &depth,
                    record,
                    is_real.clone(),
                );
            }

            depth
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gadgets::debug::{ByteRecordTester, GadgetTester};
    use expect_test::expect;
    use itertools::Itertools;
    use p3_baby_bear::BabyBear;

    #[test]
    fn test_witness_size() {
        expect!["6"].assert_eq(&DEPTH_LESS_THAN_SIZE.to_string());
        expect!["8"].assert_eq(&DEPTH_ADD_ONE_SIZE.to_string());

        expect!["0"].assert_eq(&witness_size(0).to_string());
        expect!["8"].assert_eq(&witness_size(1).to_string());
        expect!["16"].assert_eq(&witness_size(2).to_string());
        expect!["22"].assert_eq(&witness_size(3).to_string());
        expect!["28"].assert_eq(&witness_size(4).to_string());
    }

    #[test]
    fn test_num_requires() {
        expect!["0"].assert_eq(&num_requires(0).to_string());
        expect!["0"].assert_eq(&num_requires(1).to_string());
        expect!["4"].assert_eq(&num_requires(2).to_string());
        expect!["5"].assert_eq(&num_requires(3).to_string());
        expect!["6"].assert_eq(&num_requires(4).to_string());
    }

    type F = BabyBear;

    fn test_depth_vec<F: PrimeField>(depths: Vec<u32>) {
        let record = &mut ByteRecordTester::default();

        let witness_size = witness_size(depths.len());
        let num_requires = num_requires(depths.len());
        let mut witness = vec![F::zero(); witness_size];
        let depth = populate_max(&depths, &mut witness, record);

        let depths_f = depths
            .iter()
            .map(|depth| Depth::<F>::from_unsigned(depth))
            .collect_vec();
        let depth_f = eval_max(
            &mut GadgetTester::passing(),
            depths_f,
            &witness,
            &mut record.passing(num_requires),
            F::one(),
        );
        assert_eq!(depth_f, Depth::<F>::from_unsigned(&depth));
    }

    #[test]
    fn test_depth() {
        test_depth_vec::<F>(vec![]);
        test_depth_vec::<F>(vec![0]);
        test_depth_vec::<F>(vec![1]);
        test_depth_vec::<F>(vec![0, 1, 2]);
        test_depth_vec::<F>(vec![0, 2]);
        test_depth_vec::<F>(vec![0, 2, 2, 5]);
    }
}
