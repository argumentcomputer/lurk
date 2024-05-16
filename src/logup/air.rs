use crate::air::symbolic::Interaction;
use crate::logup::builder::LogupBuilder;
use itertools::{chain, enumerate, izip};
use p3_air::ExtensionBuilder;
use p3_field::{AbstractExtensionField, AbstractField, Field};
use p3_matrix::Matrix;
use std::iter;
use std::iter::zip;
use std::ops::Mul;

pub fn eval_logup_constraints<AB: LogupBuilder>(
    builder: &mut AB,
    provides: &[Interaction<AB::F>],
    requires: &[Interaction<AB::F>],
) {
    let permutations = builder.permutation();
    let permutations_local: &[AB::VarEF] = &(*permutations.row_slice(0));
    let permutations_next: &[AB::VarEF] = &(*permutations.row_slice(1));

    let (&partial_sum, inverses) = permutations_local.split_first().unwrap();
    let partial_sum_next = permutations_next.last().unwrap();
    let final_sum = builder.logup_sum();

    let multiplicities = builder.multiplicities();

    let preprocessed = builder.preprocessed();
    let preprocessed: &[AB::Var] = &preprocessed.row_slice(0);

    let main = builder.main();
    let main: &[AB::Var] = &main.row_slice(0);

    let r = builder.logup_challenge_r();
    let z_trace: AB::ExprEF = builder.logup_challenge_z_trace().into();

    let interactions = chain(requires, provides);

    //
    let provide_multiplicities = multiplicities.row(0).map(Into::into);
    let require_multiplicities = iter::repeat(z_trace);
    let multiplicities = chain(provide_multiplicities, require_multiplicities);

    let mut running_sum = AB::ExprEF::zero();

    for (interaction, m, &inverse) in izip!(interactions, multiplicities, inverses) {
        let gammas = builder.logup_challenge_gammas();

        let v: AB::ExprEF = interaction.apply(preprocessed, main, &r, gammas);
        let inverse: AB::ExprEF = inverse.into();

        if let Some(is_real) = &interaction.is_real {
            let is_real: AB::Expr = is_real.apply(preprocessed, main);
            builder
                .when(is_real.clone())
                .assert_one_ext(v * inverse.clone());
            running_sum += m * inverse * is_real
        } else {
            builder.assert_one_ext(v * inverse.clone());
            running_sum += m * inverse
        }
    }

    builder.when_first_row().assert_zero_ext(partial_sum);
    builder
        .when_transition()
        .assert_eq_ext(running_sum.clone() + partial_sum.into(), *partial_sum_next);
    builder
        .when_last_row()
        .assert_eq_ext(running_sum.clone(), final_sum);
}

impl<F: Field> Interaction<F> {
    pub fn apply<Expr, ExprEF, Var, Challenge>(
        &self,
        preprocessed: &[Var],
        main: &[Var],
        r: &Challenge,
        gamma_powers: &[Challenge],
    ) -> ExprEF
    where
        F: Into<Expr>,
        Expr: AbstractField + Mul<F, Output = Expr>,
        ExprEF: AbstractExtensionField<Expr>,
        Var: Into<Expr> + Copy,
        Challenge: Into<ExprEF> + Copy,
    {
        let mut result: ExprEF = (*r).into();

        for (i, (v_i, gamma_i)) in enumerate(zip(&self.values, gamma_powers)) {
            let gamma: ExprEF = (*gamma_i).into();
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
