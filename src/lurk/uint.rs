use std::sync::{Arc, RwLock};

use hybrid_array::sizes::U4;
use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{
    air::builder::{LookupBuilder, Record, RequireRecord},
    gadgets::{
        bytes::{builder::BytesAirRecordWithContext, record::BytesRecordWithContext},
        unsigned::{
            add::{eval_add, eval_sub, num_requires, populate_add, populate_sub},
            mul::{eval_mul, Mul32Witness},
            Word32,
        },
    },
    lair::{chipset::Chipset, execute::QueryRecord},
};

#[derive(Clone)]
pub enum U32<F> {
    Add,
    Sub,
    Mul(Arc<RwLock<Mul32Witness<F>>>),
}

fn into_wrd<T: Clone + std::fmt::Debug>(iter: impl Iterator<Item = T>) -> Word32<T> {
    <[T; 4]>::try_from(iter.collect::<Vec<_>>()).unwrap().into()
}

fn into_u8_wrd<F: PrimeField32>(slice: &[F]) -> Word32<u8> {
    <[u8; 4]>::try_from(
        slice
            .iter()
            .map(|f| F::as_canonical_u32(f).try_into().unwrap())
            .collect::<Vec<u8>>(),
    )
    .unwrap()
    .into()
}

impl<F: PrimeField32> Chipset<F> for U32<F> {
    fn input_size(&self) -> usize {
        8
    }

    fn output_size(&self) -> usize {
        4
    }

    fn require_size(&self) -> usize {
        match self {
            U32::Add | U32::Sub => num_requires::<U4>(),
            U32::Mul(..) => Mul32Witness::<F>::num_requires(),
        }
    }

    fn witness_size(&self) -> usize {
        match self {
            U32::Add | U32::Sub => 0,
            U32::Mul(..) => 4,
        }
    }

    fn execute(
        &self,
        input: &[F],
        nonce: u32,
        queries: &mut QueryRecord<F>,
        requires: &mut Vec<Record>,
    ) -> Vec<F> {
        let in1 = into_u8_wrd(&input[0..4]);
        let in2 = into_u8_wrd(&input[4..8]);
        let bytes = &mut BytesRecordWithContext {
            nonce,
            requires,
            record: &mut queries.bytes,
        };
        match self {
            U32::Add => {
                let add = populate_add(in1, in2, bytes);
                add.into_field().into_iter().collect()
            }
            U32::Sub => {
                let sub = populate_sub(in1, in2, bytes);
                sub.into_field().into_iter().collect()
            }
            U32::Mul(witness) => {
                let mul = witness.write().unwrap().populate(&in1, &in2, bytes);
                mul.into_field().into_iter().collect()
            }
        }
    }

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F> {
        let in1 = into_u8_wrd(&input[0..4]);
        let in2 = into_u8_wrd(&input[4..8]);
        match self {
            U32::Add => {
                let add = in1 + in2;
                add.into_field().into_iter().collect()
            }
            U32::Sub => {
                let sub = in1 - in2;
                sub.into_field().into_iter().collect()
            }
            U32::Mul(mul_witness) => {
                let mul = in1 * in2;
                for (i, carry) in mul_witness.read().unwrap().carry.iter().enumerate() {
                    witness[i] = *carry;
                }
                mul.into_field().into_iter().collect()
            }
        }
    }

    fn eval<AB: AirBuilder<F = F> + LookupBuilder>(
        &self,
        builder: &mut AB,
        is_real: AB::Expr,
        ins: Vec<AB::Expr>,
        out: &[AB::Var],
        witness: &[AB::Var],
        nonce: AB::Expr,
        requires: &[RequireRecord<AB::Var>],
    ) {
        let in1 = into_wrd(ins[0..4].iter().cloned());
        let in2 = into_wrd(ins[4..8].iter().cloned());
        let out = into_wrd(out.iter().map(|&o| o.into()));
        let mut air_record = BytesAirRecordWithContext::default();
        match self {
            U32::Add => eval_add(builder, (in1, in2), out, &mut air_record, is_real),
            U32::Sub => eval_sub(builder, (in1, in2), out, &mut air_record, is_real),
            U32::Mul(..) => {
                let mul_witness = Mul32Witness {
                    carry: witness.try_into().unwrap(),
                };
                eval_mul(
                    builder,
                    (in1, in2),
                    out,
                    &mul_witness,
                    &mut air_record,
                    is_real,
                )
            }
        }
        air_record.require_all(builder, nonce, requires.iter().cloned());
    }
}
