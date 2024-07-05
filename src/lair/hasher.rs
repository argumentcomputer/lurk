use p3_air::AirBuilder;
use p3_baby_bear::BabyBear;
use p3_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use crate::poseidon::{
    config::{
        BabyBearConfig24, BabyBearConfig32, BabyBearConfig48, InternalDiffusion, PoseidonConfig,
    },
    wide::{air::eval_input, columns::Poseidon2Cols, trace::populate_witness},
};

pub trait Chipset<F>: Default + Sync {
    fn output_size(&self) -> usize;

    fn execute(&self, input: &[F]) -> Vec<F>;

    fn populate_witness(&self, input: &[F], witness: &mut [F]) -> Vec<F>;

    fn witness_size(&self, input_size: usize) -> usize;

    fn eval<AB: AirBuilder<F = F>>(
        &self,
        builder: &mut AB,
        input: Vec<AB::Expr>,
        output: &[AB::Var],
        witness: &[AB::Var],
        is_real: AB::Expr,
    );
}

#[derive(Clone)]
pub struct LurkHasher {
    hasher_24_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig24>,
        24,
        7,
    >,
    hasher_32_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig32>,
        32,
        7,
    >,
    hasher_48_8: Poseidon2<
        BabyBear,
        Poseidon2ExternalMatrixGeneral,
        InternalDiffusion<BabyBearConfig48>,
        48,
        7,
    >,
}

impl Default for LurkHasher {
    fn default() -> Self {
        let hasher_24_8 = BabyBearConfig24::hasher();
        let hasher_32_8 = BabyBearConfig32::hasher();
        let hasher_48_8 = BabyBearConfig48::hasher();
        Self {
            hasher_24_8,
            hasher_32_8,
            hasher_48_8,
        }
    }
}

macro_rules! sized {
    ($vector:ident) => {
        $vector.try_into().unwrap()
    };
}

impl Chipset<BabyBear> for LurkHasher {
    #[inline]
    fn output_size(&self) -> usize {
        8
    }

    fn execute(&self, preimg: &[BabyBear]) -> Vec<BabyBear> {
        macro_rules! hash_with {
            ($name:ident) => {
                self.$name.permute(sized!(preimg))[..self.output_size()].into()
            };
        }
        match preimg.len() {
            24 => hash_with!(hasher_24_8),
            32 => hash_with!(hasher_32_8),
            48 => hash_with!(hasher_48_8),
            _ => unimplemented!(),
        }
    }

    fn populate_witness(&self, preimg: &[BabyBear], witness: &mut [BabyBear]) -> Vec<BabyBear> {
        let mut out: Vec<_> = match preimg.len() {
            24 => populate_witness::<BabyBearConfig24, 24>(sized!(preimg), witness).into(),
            32 => populate_witness::<BabyBearConfig32, 32>(sized!(preimg), witness).into(),
            48 => populate_witness::<BabyBearConfig48, 48>(sized!(preimg), witness).into(),
            _ => unimplemented!(),
        };
        out.truncate(8);
        out
    }

    fn witness_size(&self, preimg_size: usize) -> usize {
        match preimg_size {
            24 => Poseidon2Cols::<BabyBear, BabyBearConfig24, 24>::num_cols(),
            32 => Poseidon2Cols::<BabyBear, BabyBearConfig32, 32>::num_cols(),
            48 => Poseidon2Cols::<BabyBear, BabyBearConfig48, 48>::num_cols(),
            _ => unimplemented!(),
        }
    }

    fn eval<AB: AirBuilder<F = BabyBear>>(
        &self,
        builder: &mut AB,
        preimg: Vec<AB::Expr>,
        img: &[AB::Var],
        witness: &[AB::Var],
        is_real: AB::Expr,
    ) {
        match preimg.len() {
            24 => eval_input::<AB, BabyBearConfig24, 24>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
            32 => eval_input::<AB, BabyBearConfig32, 32>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
            48 => eval_input::<AB, BabyBearConfig48, 48>(
                builder,
                sized!(preimg),
                img,
                witness,
                is_real,
            ),
            _ => unimplemented!(),
        }
    }
}
