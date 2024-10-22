//! This module defines the Poseidon2 configurations and implements the traits for all the supported
//! widths between 4 and 40.

use std::ops::Sub;
use std::slice;

use hybrid_array::{typenum::*, Array, ArraySize};
use p3_baby_bear::BabyBear;
use p3_field::{AbstractField, PrimeField};
use p3_poseidon2::{DiffusionPermutation, Poseidon2, Poseidon2ExternalMatrixGeneral};
use p3_symmetric::Permutation;

use super::constants::*;

/// A sealed trait that provides the constants required for the Poseidon configuration
trait ConstantsProvided {}

/// The Poseidon configuration trait storing the data needed for
#[allow(non_camel_case_types, private_bounds)]
pub trait PoseidonConfig<const WIDTH: usize>:
    Clone + Copy + Send + Sync + ConstantsProvided
{
    type F: PrimeField;
    type R_P: ArraySize + Sub<B1>;
    type R_F: ArraySize;
    type R: ArraySize;

    fn width() -> usize {
        WIDTH
    }

    #[inline]
    fn r_f() -> usize {
        Self::R_F::USIZE
    }

    #[inline]
    fn r_p() -> usize {
        Self::R_P::USIZE
    }

    #[inline]
    fn external_linear_layer() -> Poseidon2ExternalMatrixGeneral {
        Poseidon2ExternalMatrixGeneral
    }

    #[inline]
    fn internal_linear_layer() -> InternalDiffusion<Self> {
        InternalDiffusion {
            _marker: Default::default(),
        }
    }

    fn external_constants() -> &'static Array<[Self::F; WIDTH], Self::R_F>;
    fn internal_constants() -> &'static Array<Self::F, Self::R_P>;

    /// Returns the diagonal matrix for the internal Poseidon permutation
    fn matrix_diag() -> &'static [Self::F; WIDTH];

    /// Returns an iterator of the hasher's round constants
    fn round_constants_iter() -> impl IntoIterator<Item = &'static [Self::F]> {
        let first_half = Self::external_constants()
            .iter()
            .map(|c| c.as_slice())
            .take(Self::r_f() / 2);
        let second_half = Self::external_constants()
            .iter()
            .map(|c| c.as_slice())
            .skip(Self::r_f() / 2);

        let partial_round_constants = Self::internal_constants().iter().map(slice::from_ref);

        first_half.chain(partial_round_constants).chain(second_half)
    }

    /// Returns a Poseidon 2 hasher
    fn hasher(
    ) -> Poseidon2<Self::F, Poseidon2ExternalMatrixGeneral, InternalDiffusion<Self>, WIDTH, 7> {
        let rounds_f = Self::r_f();
        let rounds_p = Self::r_p();

        let external_constants = Self::external_constants().to_vec();
        let internal_constants = Self::internal_constants().to_vec();

        let external_linear_layer = Self::external_linear_layer();
        let internal_linear_layer = Self::internal_linear_layer();

        Poseidon2::new(
            rounds_f,
            external_constants,
            external_linear_layer,
            rounds_p,
            internal_constants,
            internal_linear_layer,
        )
    }
}

/// The internal diffusion layer for the Poseidon chip, implements the `Permutation` and
/// `DiffusionPermutation` traits needed to compute the Poseidon permutation.
#[derive(Clone)]
pub struct InternalDiffusion<T> {
    _marker: std::marker::PhantomData<T>,
}

impl<AF, C: PoseidonConfig<WIDTH>, const WIDTH: usize> Permutation<[AF; WIDTH]>
    for InternalDiffusion<C>
where
    AF: AbstractField + From<C::F>,
{
    fn permute_mut(&self, input: &mut [AF; WIDTH]) {
        // Copied from matmul_external until we fix the traits
        let diag = C::matrix_diag();

        let sum: AF = input.iter().cloned().sum();
        for i in 0..WIDTH {
            input[i] *= AF::from(diag[i]);
            input[i] += sum.clone();
        }
    }
}

impl<C: PoseidonConfig<WIDTH>, const WIDTH: usize> DiffusionPermutation<C::F, WIDTH>
    for InternalDiffusion<C>
{
}

macro_rules! impl_poseidon_config {
    ($name:ident, $field:ident, $width:literal, $r_p:ident, $r_f:ident, $full_rc:ident, $part_rc:ident, $diag:ident) => {
        #[derive(Clone, Copy)]
        pub struct $name;

        impl ConstantsProvided for $name {}

        impl PoseidonConfig<$width> for $name {
            type F = $field;
            type R_F = $r_f;
            type R_P = $r_p;
            type R = Sum<$r_f, $r_p>;

            #[inline]
            fn matrix_diag() -> &'static [$field; $width] {
                $diag.as_ref()
            }

            #[inline]
            fn external_constants() -> &'static Array<[Self::F; $width], Self::R_F> {
                $full_rc.as_ref()
            }

            #[inline]
            fn internal_constants() -> &'static Array<Self::F, Self::R_P> {
                $part_rc.as_ref()
            }
        }
    };
}

impl_poseidon_config!(
    BabyBearConfig4,
    BabyBear,
    4,
    U21,
    U8,
    FULL_RC_4_8,
    PART_RC_4_21,
    MATRIX_DIAG_4_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig8,
    BabyBear,
    8,
    U12,
    U8,
    FULL_RC_8_8,
    PART_RC_8_12,
    MATRIX_DIAG_8_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig12,
    BabyBear,
    12,
    U10,
    U8,
    FULL_RC_12_8,
    PART_RC_12_10,
    MATRIX_DIAG_12_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig16,
    BabyBear,
    16,
    U13,
    U8,
    FULL_RC_16_8,
    PART_RC_16_13,
    MATRIX_DIAG_16_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig20,
    BabyBear,
    20,
    U18,
    U8,
    FULL_RC_20_8,
    PART_RC_20_18,
    MATRIX_DIAG_20_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig24,
    BabyBear,
    24,
    U21,
    U8,
    FULL_RC_24_8,
    PART_RC_24_21,
    MATRIX_DIAG_24_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig28,
    BabyBear,
    28,
    U25,
    U8,
    FULL_RC_28_8,
    PART_RC_28_25,
    MATRIX_DIAG_28_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig32,
    BabyBear,
    32,
    U30,
    U8,
    FULL_RC_32_8,
    PART_RC_32_30,
    MATRIX_DIAG_32_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig36,
    BabyBear,
    36,
    U34,
    U8,
    FULL_RC_36_8,
    PART_RC_36_34,
    MATRIX_DIAG_36_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig40,
    BabyBear,
    40,
    U38,
    U8,
    FULL_RC_40_8,
    PART_RC_40_38,
    MATRIX_DIAG_40_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig44,
    BabyBear,
    44,
    U42,
    U8,
    FULL_RC_44_8,
    PART_RC_44_42,
    MATRIX_DIAG_44_BABYBEAR
);

impl_poseidon_config!(
    BabyBearConfig48,
    BabyBear,
    48,
    U46,
    U8,
    FULL_RC_48_8,
    PART_RC_48_46,
    MATRIX_DIAG_48_BABYBEAR
);
