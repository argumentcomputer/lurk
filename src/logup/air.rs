use crate::air::symbolic::Interaction;
use crate::logup::builder::LogupBuilder;
use itertools::{chain, enumerate, izip};
use p3_air::ExtensionBuilder;
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::Matrix;
use std::iter;
use std::iter::zip;
use std::ops::{Mul, Neg};

pub fn eval_logup_constraints<AB: LogupBuilder>(
    builder: &mut AB,
    provides: &[Interaction<AB::F>],
    requires: &[Interaction<AB::F>],
) {
    let permutations = builder.permutation();
    let permutations_local: &[AB::VarEF] = &(*permutations.row_slice(0));
    let permutations_next: &[AB::VarEF] = &(*permutations.row_slice(1));

    let (&partial_sum, inverses) = permutations_local.split_first().unwrap();
    let partial_sum_next = permutations_next.first().unwrap();
    let final_sum = builder.logup_sum();

    let multiplicities = builder.multiplicities();

    let preprocessed = builder.preprocessed();
    let preprocessed: &[AB::Var] = &preprocessed.row_slice(0);

    let main = builder.main();
    let main: &[AB::Var] = &main.row_slice(0);

    let r = builder.logup_challenge_r();
    let z_trace: AB::ExprEF = builder.logup_challenge_z_trace().into();

    let interactions = chain(requires, provides);

    // if provide, m_k is the prover-supplied witness
    let provide_multiplicities = multiplicities.row(0).map(Into::into);
    // if require, m_k = -zeta^trace
    let require_multiplicities = iter::repeat(z_trace.neg());
    let multiplicities = chain(provide_multiplicities, require_multiplicities);

    // t = ∑k m_k/d_k
    let mut running_sum = AB::ExprEF::zero();

    for (interaction, m_k, &inverse_d_k) in izip!(interactions, multiplicities, inverses) {
        let gammas = builder.logup_challenge_gammas();

        let d_k: AB::ExprEF = interaction.apply(preprocessed, main, r, gammas);
        let inverse_d_k: AB::ExprEF = inverse_d_k.into();
        let mut w_k = m_k * inverse_d_k.clone();

        if let Some(is_real) = &interaction.is_real {
            let is_real: AB::Expr = is_real.apply(preprocessed, main);
            builder
                .when(is_real.clone())
                .assert_one_ext(d_k * inverse_d_k);
            // TODO: this actually requires is_real to be boolean
            //   Find a way to allow arbitrary selectors
            w_k *= is_real;
        } else {
            builder.assert_one_ext(d_k * inverse_d_k);
        };
        running_sum += w_k;
    }

    // s_0 = 0
    builder.when_first_row().assert_zero_ext(partial_sum);
    // s_{i+1} = s_i + t
    builder
        .when_transition()
        .assert_eq_ext(running_sum.clone() + partial_sum.into(), *partial_sum_next);
    // S = s_{n-1} + t
    builder
        .when_last_row()
        .assert_eq_ext(running_sum, final_sum);
}

impl<F: Field> Interaction<F> {
    pub fn apply<Expr, ExprEF, Var, Challenge>(
        &self,
        preprocessed: &[Var],
        main: &[Var],
        r: Challenge,
        gamma_powers: &[Challenge],
    ) -> ExprEF
    where
        F: Into<Expr>,
        Expr: AbstractField + Mul<F, Output = Expr>,
        ExprEF: AbstractExtensionField<Expr>,
        Var: Into<Expr> + Copy,
        Challenge: Into<ExprEF> + Copy,
    {
        let mut result: ExprEF = r.into();

        for (i, (v_i, &gamma_i)) in enumerate(zip(&self.values, gamma_powers)) {
            let gamma: ExprEF = gamma_i.into();
            let v: Expr = v_i.apply(preprocessed, main);
            if i == 0 {
                result += v;
            } else {
                result += gamma * v;
            }
        }
        result
    }
}
