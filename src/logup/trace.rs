use crate::air::symbolic::Interaction;
use crate::logup::Multiplicities;
use itertools::{chain, enumerate, Itertools};
use p3_field::{ExtensionField, PrimeField};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rayon::iter::IndexedParallelIterator;
use rayon::iter::ParallelIterator;
use rayon::prelude::IntoParallelRefIterator;
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
    identity_col: &[F],
    preprocessed: &RowMajorMatrix<F>,
    main: &RowMajorMatrix<F>,
    multiplicities: &RowMajorMatrix<EF>,
    provides: &[Interaction<F>],
    requires: &[Interaction<F>],
    challenge_z: EF,
    challenge_r: EF,
    challenge_gamma: EF,
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

    // Each row is [s, w_0, w_1, ...], where
    // - w_k = m_k/(r + ∑j gamma^j v_{k,j})
    // - s' = s + ∑k w_k, is the running sum of all w_k
    // v_{k,j} is the j-th value of the k-th interaction
    // m_k is the multiplicity for the k-th interaction
    //   if k is a require query
    //      m_k = -zeta^trace
    //   else
    //      m_k is a witness computed by `generate_multiplicities_trace`
    let mut values = RowMajorMatrix::new(vec![EF::zero(); width * height], width);

    // For each interaction k with values [v_{k,j}]_j,
    // compute all denominators `d_k = r + ∑_j gamma^j v_{k,j}`
    values
        .par_rows_mut()
        .zip(
            identity_col
                .par_iter()
                .zip(preprocessed.par_row_slices().zip(main.par_row_slices())),
        )
        .for_each(|(values, (identity, (preprocessed, main)))| {
            let (_, inverses) = values.split_first_mut().unwrap();
            for (value, interaction) in zip(inverses, &interactions) {
                if let Some(is_real) = &interaction.is_real {
                    let is_real: F = is_real.apply(identity, preprocessed, main);
                    if is_real.is_zero() {
                        continue;
                    }
                }

                *value = interaction.apply(identity, preprocessed, main, challenge_r, &gammas);
            }
        });

    // map denominators `d_k` to `w_k = m_k/d_k`
    // compute row sum t = ∑k w_k
    values
        .par_rows_mut()
        .zip(multiplicities.par_row_slices())
        .for_each(|(values, multiplicities)| {
            let (sum, inverses) = values.split_first_mut().unwrap();
            let multiplicities = multiplicities
                .iter()
                .copied()
                .chain(iter::repeat(-challenge_z));
            for (inverse, multiplicity) in zip(inverses, multiplicities) {
                if inverse.is_zero() {
                    continue;
                }
                *inverse = inverse.inverse();

                *sum += *inverse * multiplicity;
            }
        });

    // Compute partial sums column
    // s_0 = 0
    // s_{i+1} = s_i + t_i
    let mut running_sum = EF::zero();
    for i in 0..height {
        let row = values.row_mut(i);
        let t = row[0];
        running_sum += t;
        row[0] = running_sum;
    }

    values
}
