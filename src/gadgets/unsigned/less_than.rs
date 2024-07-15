use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::Word;
use hybrid_array::{Array, ArraySize};
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;

#[derive(Clone, Debug, Default, AlignedBorrow)]
#[repr(C)]
pub struct LessThanWitness<T, W: ArraySize> {
    is_comp: Array<T, W>,
    lhs_comp_limb: T,
    rhs_comp_limb: T,
    diff_comp_inv: T,
}

impl<F: PrimeField, W: ArraySize> LessThanWitness<F, W> {
    pub fn populate(
        &mut self,
        lhs: &Word<u8, W>,
        rhs: &Word<u8, W>,
        byte_record: &mut impl ByteRecord,
    ) -> bool {
        // Iterate over limbs in reverse order
        for i in (0..W::USIZE).rev() {
            // Stop at first unequal limb
            if lhs[i] != rhs[i] {
                self.is_comp[i] = F::one();
                self.lhs_comp_limb = F::from_canonical_u8(lhs[i]);
                self.rhs_comp_limb = F::from_canonical_u8(rhs[i]);
                self.diff_comp_inv = (self.lhs_comp_limb - self.rhs_comp_limb).inverse();

                return byte_record.less_than(lhs[i], rhs[i]);
            }
        }
        byte_record.less_than(0, 0)
    }

    const fn num_requires() -> usize {
        1
    }
}

pub fn eval_less_than<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (lhs, rhs): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    out: impl Into<AB::Expr>,
    witness: &LessThanWitness<AB::Var, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    let lhs = lhs.into();
    let rhs = rhs.into();
    let out = out.into();
    let is_real = is_real.into();
    let builder = &mut builder.when(is_real.clone());

    let mut lhs_comp = AB::Expr::zero();
    let mut rhs_comp = AB::Expr::zero();

    let mut comp_set = AB::Expr::zero();

    for i in (0..W::USIZE).rev() {
        let is_comp = witness.is_comp[i];
        builder.assert_bool(is_comp);

        // Select the current limbs is the comparison flag is set
        lhs_comp += lhs[i].clone() * is_comp;
        rhs_comp += rhs[i].clone() * is_comp;

        // If the comparison happened, set the equality flag for next limbs
        comp_set += is_comp.into();

        // If the word is equal, or if the comparison happened in any previous limb,
        // then the i-th limbs must be equal.
        let is_equal = AB::Expr::one() - comp_set.clone();
        builder
            .when(is_equal.clone())
            .assert_eq(lhs[i].clone(), rhs[i].clone());
    }
    // Either the words are equal, or exactly one limb is used for comparison
    builder.assert_bool(comp_set.clone());

    // Ensure the limbs used for comparison are the ones selected by `is_comp`
    builder.assert_eq(lhs_comp, witness.lhs_comp_limb);
    builder.assert_eq(rhs_comp, witness.rhs_comp_limb);

    // If the words are not equal, then the comparison limbs must be different,
    // so their difference must have an inverse.
    let diff_comp = witness.lhs_comp_limb - witness.rhs_comp_limb;
    builder.assert_eq(diff_comp * witness.diff_comp_inv, comp_set);

    // Check the comparison
    record.less_than(witness.lhs_comp_limb, witness.rhs_comp_limb, out, is_real);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::air::builder::RequireRecord;
    use crate::gadgets::bytes::builder::BytesAirRecordWithContext;
    use crate::gadgets::bytes::record::BytesRecord;
    use crate::gadgets::debug::GadgetAirBuilder;
    use crate::gadgets::unsigned::{Word32, Word64};
    use p3_baby_bear::BabyBear;
    use proptest::proptest;

    type F = BabyBear;

    fn test_less_than<W: ArraySize>(in1: Word<u8, W>, in2: Word<u8, W>, expected: bool) {
        let mut record = BytesRecord::default();
        let mut builder = GadgetAirBuilder::<F>::default();
        let mut requires =
            vec![RequireRecord::<F>::default(); LessThanWitness::<F, W>::num_requires()];

        assert_eq!(in1.clone() < in2.clone(), expected);
        let mut witness = LessThanWitness::<F, W>::default();

        let result = witness.populate(&in1, &in2, &mut record.with_context(0, requires.iter_mut()));
        assert_eq!(result, expected);

        let mut air_record = BytesAirRecordWithContext::default();

        eval_less_than(
            &mut builder,
            (in1.into_field::<F>(), in2.into_field::<F>()),
            F::from_bool(result),
            &witness,
            &mut air_record,
            F::one(),
        );

        air_record.check();
        // air_record.require_all(&mut builder, F::from_canonical_u32(nonce), requires);
    }

    proptest! {

    #[test]
    fn test_less_than_32(a: u32, b: u32) {
        let r = a < b;
        test_less_than(Word32::from(a), Word32::from(b), r);
    }

    #[test]
    fn test_less_than_64(a: u64, b: u64) {
        let r = a < b;
        test_less_than(Word64::from(a), Word64::from(b), r);
    }

    }
}
