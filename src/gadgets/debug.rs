use p3_air::AirBuilder;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use std::marker::PhantomData;

#[derive(Default)]
pub struct GadgetAirBuilder<F: Field> {
    _marker: PhantomData<F>,
}

impl<F: Field> AirBuilder for GadgetAirBuilder<F> {
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
        assert!(x.into().is_zero());
    }
}
