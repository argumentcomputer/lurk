use crate::air::symbolic::Interaction;
use crate::lookup::Multiplicities;
use crate::stark::config::{
    Domain, PackedChallenge, PackedVal, PcsCommit, PcsData, StarkGenericConfig, Val,
};

use crate::stark::folder::prover::ProverConstraintFolder;
use crate::stark::proof::{Commitments, OpenedValues, Proof};
use itertools::*;
use p3_air::Air;
use p3_challenger::{CanObserve, CanSample, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{AbstractExtensionField, AbstractField, ExtensionField, Field, PackedValue};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use rayon::prelude::*;
use std::iter;

struct Config<SC: StarkGenericConfig> {
    requires: Vec<Interaction<Val<SC>>>,
    provides: Vec<Interaction<Val<SC>>>,
    trace_domain: Domain<SC>,
}

struct Phase0<SC: StarkGenericConfig> {
    config: Config<SC>,
    main: RowMajorMatrix<Val<SC>>,
    multiplicities: Vec<Multiplicities>,
}

struct Phase1<SC: StarkGenericConfig> {
    config: Config<SC>,
    main: (PcsCommit<SC>, PcsData<SC>),
    multiplicities: Vec<Multiplicities>,
}

struct Phase2<SC: StarkGenericConfig> {
    config: Config<SC>,
    main: (PcsCommit<SC>, PcsData<SC>),
    multiplicities: (PcsCommit<SC>, PcsData<SC>),
}

struct Phase3<SC: StarkGenericConfig> {
    config: Config<SC>,
    main: (PcsCommit<SC>, PcsData<SC>),
    multiplicities: (PcsCommit<SC>, PcsData<SC>),
    permutation: (PcsCommit<SC>, PcsData<SC>),
}

/// Mult
pub fn prove<SC, A>(
    config: &SC,
    air: &A,
    challenger: &mut SC::Challenger,
    main: RowMajorMatrix<Val<SC>>,
    multiplicities: Vec<Multiplicities>,
) -> Proof<SC>
where
    SC: StarkGenericConfig,
    A: for<'a> Air<ProverConstraintFolder<'a, SC>>,
    // A: Air<SymbolicAirBuilder<Val<SC>>> + for<'a> Air<ProverConstraintFolder<'a, SC>>,
{
    //
    // Setup
    //
    //
    // let degree = main.height();
    // debug_assert_eq!(main.height(), multiplicities.height());
    //
    // let log_degree = log2_strict_usize(degree);
    //
    // let constraint_degree = 3;
    // let log_quotient_degree = log2_ceil_usize(constraint_degree - 1);
    // // let log_quotient_degree = get_log_quotient_degree::<Val<SC>, A>(air, public_values.len());
    // let quotient_degree = 1 << log_quotient_degree;
    //
    // // Get interactions from Air
    // let provides = (0..43).collect_vec();
    // // let (provides, requires) = get_interactions(air, public_values.len())
    // // assert_eq!(requires.len(),
    //
    // let pcs = config.pcs();
    // let trace_domain = pcs.natural_domain_for_degree(degree);
    //
    // //
    // // Commit
    // //
    //
    // let (main_commit, main_data) = pcs.commit(vec![(trace_domain, main)]);
    //
    // challenger.observe(main_commit.clone());
    //
    // // Challenge for RLC of multiplicities
    // let mu: SC::Challenge = challenger.sample_ext_element();
    //
    // // Compute RLC of multiplicities
    // let multiplicities = {
    //     let values_transposed: Vec<_> = multiplicities
    //         .into_par_iter()
    //         .flat_map(|m| m.rlc(mu))
    //         .collect();
    //
    //     let values_transposed = RowMajorMatrix::new(values_transposed, provides.len());
    //
    //     let values = values_transposed.transpose();
    //     values.flatten_to_base()
    // };
    //
    // // Commit to multiplicities
    // let (multiplicities_commit, multiplicities_data) =
    //     pcs.commit(vec![(trace_domain, multiplicities)]);
    // challenger.observe(multiplicities_commit.clone());

    // Commit to permutations

    //
    // Quotient
    //

    todo!();
    // // Challenge for RLC of constraints
    // let alpha: SC::Challenge = challenger.sample_ext_element();
    //
    // let quotient_domain =
    //     trace_domain.create_disjoint_domain(1 << (log_degree + log_quotient_degree));
    //
    // let main_on_quotient_domain = pcs.get_evaluations_on_domain(&main_data, 0, quotient_domain);
    // let multiplicities_on_quotient_domain =
    //     pcs.get_evaluations_on_domain(&multiplicities_data, 0, quotient_domain);
    //
    // let quotient_values = quotient_values(
    //     air,
    //     public_values,
    //     trace_domain,
    //     quotient_domain,
    //     trace_on_quotient_domain,
    //     alpha,
    // );
    // let quotient_flat = RowMajorMatrix::new_col(quotient_values).flatten_to_base();
    // let quotient_chunks = quotient_domain.split_evals(quotient_degree, quotient_flat);
    // let qc_domains = quotient_domain.split_domains(quotient_degree);
    //
    // let (quotient_commit, quotient_data) =
    //     pcs.commit(izip!(qc_domains, quotient_chunks).collect_vec());
    // challenger.observe(quotient_commit.clone());
    //
    // let commitments = Commitments {
    //     trace: trace_commit,
    //     quotient_chunks: quotient_commit,
    // };
    //
    // let zeta: SC::Challenge = challenger.sample();
    // let zeta_next = trace_domain.next_point(zeta).unwrap();
    //
    // let (opened_values, opening_proof) = pcs.open(
    //     vec![
    //         (&trace_data, vec![vec![zeta, zeta_next]]),
    //         (
    //             &quotient_data,
    //             // open every chunk at zeta
    //             (0..quotient_degree).map(|_| vec![zeta]).collect_vec(),
    //         ),
    //     ],
    //     challenger,
    // );
    // let trace_local = opened_values[0][0][0].clone();
    // let trace_next = opened_values[0][0][1].clone();
    // let quotient_chunks = opened_values[1].iter().map(|v| v[0].clone()).collect_vec();
    // let opened_values = OpenedValues {
    //     trace_local,
    //     trace_next,
    //     quotient_chunks,
    // };
    // Proof {
    //     commitments,
    //     opened_values,
    //     opening_proof,
    //     degree_bits: log_degree,
    // }
}

// fn quotient_values<SC, A, Mat>(
//     air: &A,
//     public_values: &Vec<Val<SC>>,
//     trace_domain: Domain<SC>,
//     quotient_domain: Domain<SC>,
//     trace_on_quotient_domain: Mat,
//     alpha: SC::Challenge,
// ) -> Vec<SC::Challenge>
// where
//     SC: StarkGenericConfig,
//     A: for<'a> Air<ProverConstraintFolder<'a, SC>>,
//     Mat: Matrix<Val<SC>> + Sync,
// {
//     let quotient_size = quotient_domain.size();
//     let width = trace_on_quotient_domain.width();
//     let mut sels = trace_domain.selectors_on_coset(quotient_domain);
//
//     let qdb = log2_strict_usize(quotient_domain.size()) - log2_strict_usize(trace_domain.size());
//     let next_step = 1 << qdb;
//
//     // We take PackedVal::<SC>::WIDTH worth of values at a time from a quotient_size slice, so we need to
//     // pad with default values in the case where quotient_size is smaller than PackedVal::<SC>::WIDTH.
//     for _ in quotient_size..PackedVal::<SC>::WIDTH {
//         sels.is_first_row.push(Val::<SC>::default());
//         sels.is_last_row.push(Val::<SC>::default());
//         sels.is_transition.push(Val::<SC>::default());
//         sels.inv_zeroifier.push(Val::<SC>::default());
//     }
//
//     (0..quotient_size)
//         .into_par_iter()
//         .step_by(PackedVal::<SC>::WIDTH)
//         .flat_map_iter(|i_start| {
//             let i_range = i_start..i_start + PackedVal::<SC>::WIDTH;
//
//             let is_first_row = *PackedVal::<SC>::from_slice(&sels.is_first_row[i_range.clone()]);
//             let is_last_row = *PackedVal::<SC>::from_slice(&sels.is_last_row[i_range.clone()]);
//             let is_transition = *PackedVal::<SC>::from_slice(&sels.is_transition[i_range.clone()]);
//             let inv_zeroifier = *PackedVal::<SC>::from_slice(&sels.inv_zeroifier[i_range.clone()]);
//
//             let main = RowMajorMatrix::new(
//                 iter::empty()
//                     .chain(trace_on_quotient_domain.vertically_packed_row(i_start))
//                     .chain(trace_on_quotient_domain.vertically_packed_row(i_start + next_step))
//                     .collect_vec(),
//                 width,
//             );
//
//             let accumulator = PackedChallenge::<SC>::zero();
//             let mut folder = ProverConstraintFolder {
//                 main,
//                 public_values,
//                 is_first_row,
//                 is_last_row,
//                 is_transition,
//                 alpha,
//                 accumulator,
//             };
//             air.eval(&mut folder);
//
//             // quotient(x) = constraints(x) / Z_H(x)
//             let quotient = folder.accumulator * inv_zeroifier;
//
//             // "Transpose" D packed base coefficients into WIDTH scalar extension coefficients.
//             (0..core::cmp::min(quotient_size, PackedVal::<SC>::WIDTH)).map(move |idx_in_packing| {
//                 let quotient_value = (0..<SC::Challenge as AbstractExtensionField<Val<SC>>>::D)
//                     .map(|coeff_idx| quotient.as_base_slice()[coeff_idx].as_slice()[idx_in_packing])
//                     .collect::<Vec<_>>();
//                 SC::Challenge::from_base_slice(&quotient_value)
//             })
//         })
//         .collect()
// }
