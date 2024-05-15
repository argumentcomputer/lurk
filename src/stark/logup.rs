use crate::air::symbolic::Interaction;
use crate::stark::air::LogupBuilder;
use itertools::{chain, izip};
use p3_air::{ ExtensionBuilder};
use p3_field::AbstractField;
use p3_matrix::Matrix;
use std::iter;

pub fn eval_logup_constraints<AB: LogupBuilder>(
    builder: &mut AB,
    requires: &[Interaction<AB::F>],
    provides: &[Interaction<AB::F>],
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

    let require_multiplicities = iter::repeat(z_trace).take(requires.len());
    let provide_multiplicities = multiplicities.row(0).map(Into::into);
    let multiplicities = chain(require_multiplicities, provide_multiplicities);


    let mut running_sum = AB::ExprEF::zero();

    for (interaction, m, &inverse) in izip!(interactions, multiplicities, inverses) {
        let gammas = builder.logup_challenge_gammas();

        let v: AB::ExprEF = interaction.apply(preprocessed, main, &r, gammas);
        let inverse: AB::ExprEF = inverse.into();

        let is_real: AB::Expr = interaction.is_real.apply(preprocessed, main);

        builder.assert_one_ext(v * inverse.clone());

        running_sum +=  m * inverse * is_real
    }

    builder.when_first_row().assert_zero_ext(partial_sum);
    builder
        .when_transition()
        .assert_eq_ext( running_sum.clone() + partial_sum.into(), *partial_sum_next);
    builder
        .when_last_row()
        .assert_eq_ext(running_sum.clone(), final_sum);
}
