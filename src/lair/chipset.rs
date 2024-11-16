use either::Either;
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
        _query_index: usize,
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

impl<F, C1: Chipset<F>, C2: Chipset<F>> Chipset<F> for &Either<C1, C2> {
    fn input_size(&self) -> usize {
        match self {
            Either::Left(c) => c.input_size(),
            Either::Right(c) => c.input_size(),
        }
    }

    fn output_size(&self) -> usize {
        match self {
            Either::Left(c) => c.output_size(),
            Either::Right(c) => c.output_size(),
        }
    }

    fn execute(
        &self,
        input: &[F],
        nonce: u32,
        query_index: usize,
        queries: &mut QueryRecord<F>,
        requires: &mut Vec<Record>,
    ) -> Vec<F>
    where
        F: PrimeField32,
    {
        match self {
            Either::Left(c) => c.execute(input, nonce, query_index, queries, requires),
            Either::Right(c) => c.execute(input, nonce, query_index, queries, requires),
        }
    }

    fn execute_simple(&self, input: &[F]) -> Vec<F> {
        match self {
            Either::Left(c) => c.execute_simple(input),
            Either::Right(c) => c.execute_simple(input),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            Either::Left(c) => c.witness_size(),
            Either::Right(c) => c.witness_size(),
        }
    }

    fn require_size(&self) -> usize {
        match self {
            Either::Left(c) => c.require_size(),
            Either::Right(c) => c.require_size(),
        }
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        match self {
            Either::Left(c) => c.populate_witness(input, witness),
            Either::Right(c) => c.populate_witness(input, witness),
        }
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        input: Vec<AB::Expr>,
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        match self {
            Either::Left(c) => c.eval(builder, is_real, input, witness, nonce, requires),
            Either::Right(c) => c.eval(builder, is_real, input, witness, nonce, requires),
        }
    }
}

#[derive(Default)]
pub struct NoChip;

impl<F> Chipset<F> for NoChip {
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
