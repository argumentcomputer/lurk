use crate::gadgets::bytes::relation::ByteRelation;
use crate::gadgets::bytes::{ByteAirRecord, ByteInput, ByteRecord};
use p3_air::AirBuilder;
use p3_field::{AbstractField, Field};
use p3_matrix::dense::RowMajorMatrix;
use std::collections::VecDeque;
use std::marker::PhantomData;

pub struct GadgetTester<F> {
    should_fail: bool,
    has_failed: bool,
    _marker: PhantomData<F>,
}

impl<F> GadgetTester<F> {
    pub fn passing() -> Self {
        Self {
            should_fail: false,
            has_failed: false,
            _marker: Default::default(),
        }
    }

    pub fn failing() -> Self {
        Self {
            should_fail: false,
            has_failed: false,
            _marker: Default::default(),
        }
    }
}

impl<F: Field> AirBuilder for GadgetTester<F> {
    type F = F;
    type Expr = F;
    type Var = F;
    type M = RowMajorMatrix<F>;

    fn main(&self) -> Self::M {
        panic!("gadget should not call main")
    }

    fn is_first_row(&self) -> Self::Expr {
        panic!("gadget should not call is_first_row")
    }

    fn is_last_row(&self) -> Self::Expr {
        panic!("gadget should not call is_last_row")
    }

    fn is_transition_window(&self, _size: usize) -> Self::Expr {
        panic!("gadget should not call is_transition_window")
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        if !x.into().is_zero() {
            self.has_failed = true;
        }
        assert!(self.should_fail && self.has_failed, "invalid constraint");
    }
}

impl<F> Drop for GadgetTester<F> {
    fn drop(&mut self) {
        assert!(
            self.should_fail && !self.has_failed,
            "expected failing condition"
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct ByteRecordTester<F: Field> {
    populate_events: VecDeque<ByteRelation<F>>,
}

impl<F: Field> ByteRecord for ByteRecordTester<F> {
    fn range_check_u8_pair(&mut self, i1: u8, i2: u8) {
        self.populate_events.push_back(ByteRelation::range_u8_pair(
            F::from_canonical_u8(i1),
            F::from_canonical_u8(i2),
        ))
    }

    fn range_check_u16(&mut self, i: u16) {
        self.populate_events
            .push_back(ByteRelation::range_u16(F::from_canonical_u16(i)))
    }

    fn less_than(&mut self, i1: u8, i2: u8) -> bool {
        let input = ByteInput::from_u8_pair(i1, i2);
        let (i1, i2) = input.as_field_u8_pair::<F>();
        let r = input.less_than();
        self.populate_events
            .push_back(ByteRelation::less_than(i1, i2, F::from_bool(r)));
        r
    }

    fn and(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let (i1, i2) = input.as_field_u8_pair::<F>();
        let r = input.and();
        self.populate_events
            .push_back(ByteRelation::and(i1, i2, F::from_canonical_u8(r)));
        r
    }

    fn xor(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let (i1, i2) = input.as_field_u8_pair::<F>();
        let r = input.xor();
        self.populate_events
            .push_back(ByteRelation::xor(i1, i2, F::from_canonical_u8(r)));
        r
    }

    fn or(&mut self, i1: u8, i2: u8) -> u8 {
        let input = ByteInput::from_u8_pair(i1, i2);
        let (i1, i2) = input.as_field_u8_pair::<F>();
        let r = input.or();
        self.populate_events
            .push_back(ByteRelation::or(i1, i2, F::from_canonical_u8(r)));
        r
    }

    fn msb(&mut self, i: u8) -> bool {
        let input = ByteInput::from_u8(i);
        let r = input.msb();
        self.populate_events
            .push_back(ByteRelation::msb(F::from_canonical_u8(i), F::from_bool(r)));
        r
    }
}

impl<F: Field> ByteRecordTester<F> {
    pub fn passing(&mut self, num_requires: usize) -> ByteAirRecordPassingTester<'_, F> {
        ByteAirRecordPassingTester {
            num_requires,
            record: self,
        }
    }
    pub fn ignoring(&self) -> ByteAirRecordIgnoringTester {
        ByteAirRecordIgnoringTester
    }
}

#[derive(Debug)]
pub struct ByteAirRecordPassingTester<'a, F: Field> {
    num_requires: usize,
    record: &'a mut ByteRecordTester<F>,
}

impl<'a, F: Field> Drop for ByteAirRecordPassingTester<'a, F> {
    fn drop(&mut self) {
        assert_eq!(self.num_requires, 0);
    }
}

impl<'a, F: Field> ByteAirRecordPassingTester<'a, F> {
    fn push_air_event(&mut self, relation: ByteRelation<F>, is_real: impl Into<F>) {
        self.num_requires -= 1;
        let is_real = is_real.into();
        if is_real.is_zero() {
            return;
        }
        assert!(is_real.is_one(), "is_real must be a bool");
        let expected = self
            .record
            .populate_events
            .pop_front()
            .expect("record should contain the relation");
        assert_eq!(relation, expected);
    }
}

impl<'a, F: Field> ByteAirRecord<F> for ByteAirRecordPassingTester<'a, F> {
    fn range_check_u8_pair(&mut self, i1: impl Into<F>, i2: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::range_u8_pair(i1, i2), is_real);
    }

    fn range_check_u16(&mut self, i: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::range_u16(i), is_real);
    }

    fn less_than(
        &mut self,
        i1: impl Into<F>,
        i2: impl Into<F>,
        r: impl Into<F>,
        is_real: impl Into<F>,
    ) {
        self.push_air_event(ByteRelation::less_than(i1, i2, r), is_real);
    }

    fn and(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::and(i1, i2, r), is_real);
    }

    fn xor(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::xor(i1, i2, r), is_real);
    }

    fn or(&mut self, i1: impl Into<F>, i2: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::or(i1, i2, r), is_real);
    }

    fn msb(&mut self, i: impl Into<F>, r: impl Into<F>, is_real: impl Into<F>) {
        self.push_air_event(ByteRelation::msb(i, r), is_real);
    }
}

#[derive(Debug)]
pub struct ByteAirRecordIgnoringTester;

impl<F: AbstractField> ByteAirRecord<F> for ByteAirRecordIgnoringTester {
    fn range_check_u8_pair(
        &mut self,
        _i1: impl Into<F>,
        _i2: impl Into<F>,
        _is_real: impl Into<F>,
    ) {
    }

    fn range_check_u16(&mut self, _i: impl Into<F>, _is_real: impl Into<F>) {}

    fn less_than(
        &mut self,
        _i1: impl Into<F>,
        _i2: impl Into<F>,
        _r: impl Into<F>,
        _is_real: impl Into<F>,
    ) {
    }

    fn and(
        &mut self,
        _i1: impl Into<F>,
        _i2: impl Into<F>,
        _r: impl Into<F>,
        _is_real: impl Into<F>,
    ) {
    }

    fn xor(
        &mut self,
        _i1: impl Into<F>,
        _i2: impl Into<F>,
        _r: impl Into<F>,
        _is_real: impl Into<F>,
    ) {
    }

    fn or(
        &mut self,
        _i1: impl Into<F>,
        _i2: impl Into<F>,
        _r: impl Into<F>,
        _is_real: impl Into<F>,
    ) {
    }

    fn msb(&mut self, _i: impl Into<F>, _r: impl Into<F>, _is_real: impl Into<F>) {}
}
