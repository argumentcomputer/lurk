use crate::{lair::chipset::Chipset, lurk::zstore::DIGEST_SIZE};

/// Gadgets for operations over `i64`, assumed to be encoded in two's complement
#[derive(Clone)]
pub enum I64Gadgets {
    IntoSignAbs,
    FromSignAbs,
}

impl<F> Chipset<F> for I64Gadgets {
    fn input_size(&self) -> usize {
        match self {
            Self::IntoSignAbs => DIGEST_SIZE,
            Self::FromSignAbs => 1 + DIGEST_SIZE,
        }
    }

    fn output_size(&self) -> usize {
        match self {
            Self::FromSignAbs => DIGEST_SIZE,
            Self::IntoSignAbs => 1 + DIGEST_SIZE,
        }
    }

    fn witness_size(&self) -> usize {
        todo!()
    }

    fn require_size(&self) -> usize {
        todo!()
    }

    fn execute_simple(&self, _input: &[F]) -> Vec<F> {
        todo!()
    }

    fn populate_witness(&self, _input: &[F], _witness: &mut [F]) -> Vec<F> {
        todo!()
    }

    fn eval<AB: p3_air::AirBuilder<F = F> + crate::air::builder::LookupBuilder>(
        &self,
        _builder: &mut AB,
        _is_real: AB::Expr,
        _input: Vec<AB::Expr>,
        _witness: &[AB::Var],
        _nonce: AB::Expr,
        _requires: &[crate::air::builder::RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        todo!()
    }
}
