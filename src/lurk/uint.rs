use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::{gadgets::unsigned::Word32, lair::chipset::Chipset};

pub enum U32 {
    Add,
    Sub,
    Mul,
}

impl<F: PrimeField32> Chipset<F> for U32 {
    fn input_size(&self) -> usize {
        8
    }

    fn output_size(&self) -> usize {
        4
    }

    fn witness_size(&self) -> usize {
        match self {
            U32::Mul => 8,
            _ => 0,
        }
    }

    fn execute(&self, input: &[F]) -> Vec<F> {
        let input_size = <U32 as Chipset<F>>::input_size(self);
        assert_eq!(input.len(), input_size);
        let into_wrd = |slice: &[F]| -> Word32<u8> {
            <[u8; 4]>::try_from(
                slice
                    .iter()
                    .map(|f| F::as_canonical_u32(f).try_into().unwrap())
                    .collect::<Vec<u8>>(),
            )
            .unwrap()
            .into()
        };
        let fst_wrd = into_wrd(&input[0..4]);
        let snd_wrd = into_wrd(&input[4..8]);

        match self {
            U32::Add => {
                let add = fst_wrd + snd_wrd;
                add.into_field().into_iter().collect()
            }
            U32::Sub => {
                let sub = fst_wrd - snd_wrd;
                sub.into_field().into_iter().collect()
            }
            U32::Mul => {
                let mul = fst_wrd * snd_wrd;
                mul.into_field().into_iter().collect()
            }
        }
    }

    fn populate_witness(&self, _input: &[F], _witness: &mut [F]) -> Vec<F> {
        todo!()
    }

    fn eval<AB: AirBuilder<F = F>>(
        &self,
        _builder: &mut AB,
        _input: Vec<AB::Expr>,
        _output: &[AB::Var],
        _witness: &[AB::Var],
        _is_real: AB::Expr,
    ) {
        todo!()
    }
}
