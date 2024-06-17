use crate::poseidon::config::PoseidonConfig;
use std::iter::zip;

use hybrid_array::{typenum::*, ArraySize};

use crate::poseidon::wide::columns::{Poseidon2Cols, Poseidon2PermutationCols};
use p3_air::AirBuilder;
use p3_field::AbstractField;
use p3_symmetric::Permutation;

/// Given a witness of size `Poseidon2Cols::num_cols`, apply the Poseidon2 permutation over the input and return the output.
/// When is_real = 0, the output is unconstrained.
pub fn eval_input<AB: AirBuilder, C: PoseidonConfig<WIDTH, F = AB::F>, const WIDTH: usize>(
    builder: &mut AB,
    input: [AB::Expr; WIDTH],
    witness: &[AB::Var],
    is_real: AB::Expr,
) -> [AB::Var; WIDTH]
where
    Sub1<C::R_P>: ArraySize,
{
    let cols = Poseidon2Cols::<AB::Var, C, WIDTH>::from_slice(witness);
    cols.eval(builder, input, is_real)
}

impl<T, C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2Cols<T, C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    pub fn eval<AB: AirBuilder<F = C::F, Var = T>>(
        &self,
        builder: &mut AB,
        input: [AB::Expr; WIDTH],
        is_real: AB::Expr,
    ) -> [AB::Var; WIDTH]
    where
        T: Copy + Into<AB::Expr>,
    {
        self.perm
            .eval(builder, input, self.output.map(Into::into), is_real);
        self.output
    }
}

impl<T, C: PoseidonConfig<WIDTH>, const WIDTH: usize> Poseidon2PermutationCols<T, C, WIDTH>
where
    Sub1<C::R_P>: ArraySize,
{
    pub fn eval<AB: AirBuilder<F = C::F, Var = T>>(
        &self,
        builder: &mut AB,
        input: [AB::Expr; WIDTH],
        output: [AB::Expr; WIDTH],
        is_real: impl Into<AB::Expr>,
    ) where
        T: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();
        // When is_real = 0, the constraints apply the identity to [0; WIDTH]
        let mut state: [AB::Expr; WIDTH] = input.map(|x| is_real.clone() * x);

        // Apply the initial round.
        C::external_linear_layer().permute_mut(&mut state);

        // Apply the first half of external rounds.
        for round in 0..C::r_f() / 2 {
            self.eval_external_round(builder, &mut state, is_real.clone(), round);
        }

        // Apply the internal rounds.
        for round in 0..C::r_p() {
            self.eval_internal_round(builder, &mut state, is_real.clone(), round);
        }

        // Apply the second half of external rounds.
        for round in C::r_f() / 2..C::r_f() {
            self.eval_external_round(builder, &mut state, is_real.clone(), round);
        }

        for (state, output) in zip(state, output) {
            builder.assert_eq(state, output * is_real.clone());
        }
    }

    fn eval_external_round<AB: AirBuilder<F = C::F, Var = T>>(
        &self,
        builder: &mut AB,
        state: &mut [AB::Expr; WIDTH],
        is_real: impl Into<AB::Expr>,
        round: usize,
    ) where
        T: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        // Check that the input state matches the expected round state, and replace it to ensure `state` is linear
        for (state, &state_expected) in zip(state.iter_mut(), &self.external_rounds_state[round]) {
            builder.assert_eq(state.clone(), state_expected);
            *state = state_expected.into();
        }

        // add round constants
        for (state, constant) in zip(state.iter_mut(), C::external_constants()[round]) {
            *state += is_real.clone() * constant;
        }

        // apply sbox
        for (state, &sbox_3) in zip(state.iter_mut(), &self.external_rounds_sbox[round]) {
            builder.assert_eq(state.cube(), sbox_3);

            *state *= sbox_3.into().square();
        }

        // apply external linear layer
        C::external_linear_layer().permute_mut(state)
    }

    fn eval_internal_round<AB: AirBuilder<F = C::F, Var = T>>(
        &self,
        builder: &mut AB,
        state: &mut [AB::Expr; WIDTH],
        is_real: impl Into<AB::Expr>,
        round: usize,
    ) where
        T: Copy + Into<AB::Expr>,
    {
        let is_real = is_real.into();

        // Compare degree 3 state against checkpoint variables and replace them to ensure the input to the sbox is linear
        if round == 0 {
            // In the first round, we need to ensure the entire state is linear since in the next round, the first element will
            // be a linear combination of the input to the first round.
            for (state, &state_expected) in zip(state.iter_mut(), &self.internal_rounds_state_init)
            {
                builder.assert_eq(state.clone(), state_expected);
                *state = state_expected.into();
            }
        } else {
            // In the later rounds, only the first component is not linear, so we replace it with a variable which we assert is equal.
            let state_expected = self.internal_rounds_state0[round - 1];
            builder.assert_eq(state[0].clone(), state_expected);
            state[0] = state_expected.into();
        };

        // add round constant
        let constant = is_real * C::internal_constants()[round];
        state[0] += constant;

        // apply sbox
        let sbox_3 = self.internal_rounds_sbox[round];
        builder.assert_eq(state[0].cube(), sbox_3);
        state[0] *= sbox_3.into().square();

        // apply internal linear layer
        C::internal_linear_layer().permute_mut(state);
    }
}
