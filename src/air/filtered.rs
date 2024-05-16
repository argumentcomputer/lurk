///! We copy FilteredAirBuilder because we need to access `condition`
use p3_air::{AirBuilder, ExtensionBuilder};

#[derive(Debug)]
pub struct FilteredAirBuilder<'a, AB: AirBuilder> {
    pub inner: &'a mut AB,
    // This should be public in upstream
    pub condition: AB::Expr,
}

impl<'a, AB: AirBuilder> AirBuilder for FilteredAirBuilder<'a, AB> {
    type F = AB::F;
    type Expr = AB::Expr;
    type Var = AB::Var;
    type M = AB::M;

    fn main(&self) -> Self::M {
        self.inner.main()
    }

    fn is_first_row(&self) -> Self::Expr {
        self.inner.is_first_row()
    }

    fn is_last_row(&self) -> Self::Expr {
        self.inner.is_last_row()
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.inner.is_transition_window(size)
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.inner.assert_zero(self.condition.clone() * x.into());
    }
}

impl<'a, AB: ExtensionBuilder> ExtensionBuilder for FilteredAirBuilder<'a, AB> {
    type EF = AB::EF;
    type ExprEF = AB::ExprEF;
    type VarEF = AB::VarEF;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.inner
            .assert_zero_ext(x.into() * self.condition.clone());
    }
}
