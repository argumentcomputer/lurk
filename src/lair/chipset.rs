use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::air::builder::{LookupBuilder, Record, RequireRecord};

use super::execute::QueryRecord;

pub trait Chipset<F>: Sync {
    fn input_size(&self) -> usize;

    fn output_size(&self) -> usize;

    fn witness_size(&self) -> usize;

    fn require_size(&self) -> usize;

    fn execute_simple(&self, _input: &[F]) -> Vec<F> {
        unimplemented!("please use `execute`")
    }

    fn execute(
        &self,
        input: &[F],
        _nonce: u32,
        _queries: &mut QueryRecord<F>,
        _requires: &mut Vec<Record>,
    ) -> Vec<F>
    where
        F: PrimeField32,
    {
        self.execute_simple(input)
    }

    fn populate_witness(&self, _input: &[F], _witness: &mut [F]) -> Vec<F>;

    #[allow(clippy::too_many_arguments)]
    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        input: Vec<AB::Expr>,
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr>;
}

pub struct Nochip;

impl<F> Chipset<F> for Nochip {
    fn input_size(&self) -> usize {
        unimplemented!()
    }

    fn output_size(&self) -> usize {
        unimplemented!()
    }

    fn require_size(&self) -> usize {
        unimplemented!()
    }

    fn witness_size(&self) -> usize {
        unimplemented!()
    }

    fn execute_simple(&self, _: &[F]) -> Vec<F> {
        unimplemented!()
    }

    fn populate_witness(&self, _: &[F], _: &mut [F]) -> Vec<F> {
        unimplemented!()
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        _: &mut AB,
        _: AB::Expr,
        _: Vec<AB::Expr>,
        _: &[AB::Var],
        _: AB::Expr,
        _: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        unimplemented!()
    }
}
