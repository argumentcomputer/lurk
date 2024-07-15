use crate::gadgets::bytes::{ByteAirRecord, ByteRecord};
use crate::gadgets::unsigned::add::eval_sum;
use crate::gadgets::unsigned::less_than::{eval_less_than, LessThanWitness};
use crate::gadgets::unsigned::mul::{eval_mul, MulWitness};
use crate::gadgets::unsigned::Word;
use hybrid_array::ArraySize;
use p3_air::AirBuilder;
use p3_field::{AbstractField, PrimeField};
use sphinx_derive::AlignedBorrow;

#[derive(Clone, Default, AlignedBorrow)]
#[repr(C)]
pub struct DivRemWitness<T, W: ArraySize> {
    /// q = a // b
    q: Word<T, W>,
    /// r = a % b
    r: Word<T, W>,
    /// qb = q * b
    qb: Word<T, W>,
    mul_q_b: MulWitness<T, W, W>,
    r_lt_b: LessThanWitness<T, W>,
    /// is_qb_lt_a = qb < a
    is_qb_lt_a: T,
    qb_lt_a: LessThanWitness<T, W>,
}

impl<F: PrimeField, W: ArraySize> DivRemWitness<F, W> {
    pub fn populate(
        &mut self,
        a: &Word<u8, W>,
        b: &Word<u8, W>,
        byte_record: &mut impl ByteRecord,
    ) -> (Word<u8, W>, Word<u8, W>) {
        // TODO: Compute result
        let (q, r) = (Word::<u8, W>::default(), Word::<u8, W>::default());
        self.q = q.clone().into_field();
        self.r = r.clone().into_field();
        let qb = self.mul_q_b.populate(&q, b, byte_record);
        let is_r_lt_b = self.r_lt_b.populate(&r, b, byte_record);
        debug_assert!(is_r_lt_b);
        let is_qb_lt_a = self.qb_lt_a.populate(&qb, a, byte_record);
        debug_assert!(is_qb_lt_a || (qb == *a));
        self.is_qb_lt_a = F::from_bool(is_qb_lt_a);
        (q, r)
    }

    const fn num_requires() -> usize {
        MulWitness::<F, W, W>::num_requires()
            + 2 * LessThanWitness::<F, W>::num_requires()
            + 2 * (W::USIZE / 2) // q, r range
    }
}

pub fn eval_div_rem<AB: AirBuilder, W: ArraySize>(
    builder: &mut AB,
    (a, b): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    (q, r): (Word<impl Into<AB::Expr>, W>, Word<impl Into<AB::Expr>, W>),
    witness: &DivRemWitness<AB::Var, W>,
    record: &mut impl ByteAirRecord<AB::Expr>,
    is_real: impl Into<AB::Expr>,
) {
    // Following Jolt (https://eprint.iacr.org/2023/1217.pdf) 6.3
    // Assume a, b are range checked
    let a = a.into();
    let b = b.into();

    let q = q.into();
    let r = r.into();
    let is_real = is_real.into();

    record.range_check_u8_iter(r.clone(), is_real.clone());
    record.range_check_u8_iter(q.clone(), is_real.clone());

    // q * b
    eval_mul(
        builder,
        (q.clone(), b.clone()),
        witness.qb.clone(),
        &witness.mul_q_b,
        record,
        is_real.clone(),
    );

    // a = q * b + r
    // we use sum to avoid the range check of a
    eval_sum(
        builder,
        (witness.qb.clone().into(), r.clone()),
        a.clone(),
        is_real.clone(),
    );

    // r < b
    let is_r_lt_b = AB::F::one();
    let _ = eval_less_than(
        builder,
        (r.clone(), b.clone()),
        is_r_lt_b,
        &witness.r_lt_b,
        record,
        is_real.clone(),
    );

    // q * b <= a
    let is_qb_eq_a = eval_less_than(
        builder,
        (witness.qb.clone(), a.clone()),
        witness.is_qb_lt_a,
        &witness.qb_lt_a,
        record,
        is_real.clone(),
    );
    let is_qb_leq_a = is_qb_eq_a + witness.is_qb_lt_a;
    builder.when(is_real.clone()).assert_one(is_qb_leq_a);
}
