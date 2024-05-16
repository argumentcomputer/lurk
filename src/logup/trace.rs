use crate::air::symbolic::Interaction;
use crate::logup::Multiplicities;
use itertools::{chain, enumerate, Itertools};
use p3_field::{ExtensionField, PrimeField};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use std::iter;
use std::iter::zip;

pub(crate) fn generate_multiplicities_trace<F: PrimeField, EF: ExtensionField<F>>(
    multiplicities: &[Multiplicities],
    challenge_z: &EF,
) -> RowMajorMatrix<EF> {
    let width = multiplicities.len();
    let height = multiplicities
        .iter()
        .map(|m| m.counts.height())
        .all_equal_value()
        .unwrap();
    let num_z_powers = multiplicities
        .iter()
        .flat_map(|m| &m.traces)
        .copied()
        .max()
        .unwrap();

    let z_powers = challenge_z
        .powers()
        .skip(1)
        .take(num_z_powers)
        .collect_vec();

    let mut values = RowMajorMatrix::new(vec![EF::zero(); width * height], width);

    for (i, m) in enumerate(multiplicities) {
        let z_powers = m.traces.iter().map(|trace| z_powers[*trace]).collect_vec();

        values
            .par_rows_mut()
            .zip(m.counts.par_row_slices())
            .for_each(|(row, m)| {
                // TODO: with an updated plonky3::field, we can access `dot_product`
                for (&m_i, &z_i) in zip(m, &z_powers) {
                    row[i] += z_i * F::from_canonical_u32(m_i);
                }
            })
    }

    values
}
pub(crate) fn generate_permutation_trace<F: PrimeField, EF: ExtensionField<F>>(
    preprocessed: &RowMajorMatrix<F>,
    main: &RowMajorMatrix<F>,
    multiplicities: &RowMajorMatrix<EF>,
    provides: &[Interaction<F>],
    requires: &[Interaction<F>],
    challenge_z: &EF,
    challenge_r: &EF,
    challenge_gamma: &EF,
) -> RowMajorMatrix<EF> {
    let height = main.height();
    debug_assert_eq!(preprocessed.height(), height);
    debug_assert_eq!(multiplicities.height(), height);

    let num_requires = requires.len();
    let num_provides = provides.len();
    let num_interactions = num_provides + num_requires;
    debug_assert!(num_interactions > 0);

    let interactions = chain(provides, requires).collect_vec();

    let num_gammas = interactions
        .iter()
        .map(|interaction| interaction.num_entries())
        .max()
        .unwrap();
    let gammas = challenge_gamma.powers().take(num_gammas).collect_vec();

    let width = 1 + num_interactions;

    let mut values = RowMajorMatrix::new(vec![EF::zero(); width * height], width);

    values
        .par_rows_mut()
        .zip(preprocessed.par_row_slices().zip(main.par_row_slices()))
        .for_each(|(values, (preprocessed, main))| {
            let (_, inverses) = values.split_first_mut().unwrap();
            for (value, interaction) in zip(inverses, &interactions) {
                if let Some(is_real) = &interaction.is_real {
                    let is_real: F = is_real.apply(preprocessed, main);
                    if is_real.is_zero() {
                        continue;
                    }
                }

                *value = interaction.apply(preprocessed, main, challenge_r, &gammas);
            }
        });

    values
        .par_rows_mut()
        .zip(multiplicities.par_row_slices())
        .for_each(|(values, multiplicities)| {
            let (sum, inverses) = values.split_first_mut().unwrap();
            let multiplicities = multiplicities.iter().chain(iter::repeat(challenge_z));
            for (inverse, &multiplicity) in zip(inverses, multiplicities) {
                if inverse.is_zero() {
                    continue;
                }
                *inverse = inverse.inverse();

                *sum += *inverse * multiplicity;
            }
        });

    // Compute partial sums column
    let mut running_sum = EF::zero();
    for i in 0..height {
        let row = values.row_mut(i);
        let row_sum = row.first_mut().unwrap();

        running_sum += *row_sum;
        *row_sum = running_sum;
    }

    values
}
