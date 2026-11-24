//! CUDA hiding 2× interleaved odd-coset FRI PCS (`v6-zk`, ePrint 2024/1037).
//!
//! Mirrors the CPU [`crate::p3_adapter::spill_zk::HidingSpillableTwoAdicFriPcs`]
//! semantics and wire format byte-for-byte while executing coset LDEs, salted
//! Merkle tree construction, barycentric OOD interpolation, reduced-opening
//! accumulation, and FRI commit-phase folding on CUDA.

use core::iter;
use core::marker::PhantomData;
use core::mem::size_of;
use std::borrow::Cow;
use std::path::{Path, PathBuf};

use itertools::Itertools;
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::{Mmcs, OpenedValues, Pcs, PeriodicLdeTable};
use p3_dft::{Radix2DFTSmallBatch, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{
    ExtensionField, Field, PackedFieldExtension, PrimeCharacteristicRing, PrimeField64,
    TwoAdicField, dot_product,
};
use p3_fri::verifier::FriError;
use p3_fri::{
    BatchMultiOpening, CommitPhaseMultiStep, CommitmentWithOpeningPoints, FriParameters, FriProof,
    ProverDataWithOpeningPoints, TwoAdicFriFolding, TwoAdicFriFoldingForMmcs,
    build_periodic_lde_table_two_adic, compute_log_arity_for_round, prover,
};
use p3_goldilocks::Goldilocks;
use p3_matrix::Matrix;
use p3_matrix::bitrev::{BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixCow};
use p3_matrix::interpolation::{Interpolate, compute_adjusted_weights};
use p3_maybe_rayon::prelude::*;
use p3_util::linear_map::LinearMap;
use p3_util::{log2_strict_usize, reverse_slice_index_bits};
use tracing::debug_span;

use super::hiding_mmcs::{HidingCudaFriMmcs, HidingCudaMmcs, HidingCudaMmcsData};
use super::pcs::{
    CudaPcsDft, bit_reversed_coset, compute_inverse_denominators_for_dims, cuda_ext_degree_and_w,
    ext_from_goldilocks, ext_to_goldilocks, interpolate_spilled_coset_generic,
};
use super::{
    CudaDft, CudaFriWorkspace, CudaInterpolationTasks, CudaLde, CudaReducedOpening,
    CudaReductionTasks,
};
use crate::p3_adapter::cap::{CapValidatingMmcs, validate_fri_commitment_caps};
use crate::p3_adapter::fri_batching::{
    FriBatching, FriBatchingSchedule, pack_ext_weights, verify_fri_with_batching,
};
use crate::p3_adapter::spill::{STREAM_BLOCK_BYTES, SpillPackWriter, SpilledMatrix};
use crate::p3_adapter::zk::{interleave_random_rows, preprocessed_salt_seed, random_seed};
use p3_symmetric::MerkleCap;

/// CUDA hiding 2× interleaved odd-coset FRI PCS (`const ZK: bool = true`) for
/// Protocol `v6-zk`.
#[derive(Clone, Debug)]
pub struct HidingCudaTwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    pub(crate) dft: Dft,
    pub(crate) mmcs: InputMmcs,
    pub(crate) fri: FriParameters<FriMmcs>,
    pub(crate) batching: FriBatching,
    pub(crate) spill_dir: Option<PathBuf>,
    _phantom: PhantomData<Val>,
}

impl<Val, Dft, InputMmcs, FriMmcs> HidingCudaTwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    pub const fn new(dft: Dft, mmcs: InputMmcs, fri: FriParameters<FriMmcs>) -> Self {
        Self {
            dft,
            mmcs,
            fri,
            batching: FriBatching::Horner,
            spill_dir: None,
            _phantom: PhantomData,
        }
    }

    /// Configures the FRI opening batching strategy (`Horner` or `Tensor`).
    pub const fn with_batching(mut self, batching: FriBatching) -> Self {
        self.batching = batching;
        self
    }

    /// Returns the configured disk-spill directory, if enabled.
    pub fn spill_dir(&self) -> Option<&Path> {
        self.spill_dir.as_deref()
    }
}

impl<Dft, FriMmcs> HidingCudaTwoAdicFriPcs<Goldilocks, Dft, HidingCudaMmcs, FriMmcs> {
    /// Configures the disk-spill directory on both this PCS and its underlying
    /// [`HidingCudaMmcs`].
    pub fn set_spill_dir(&mut self, spill_dir: Option<PathBuf>) {
        self.mmcs.set_spill_dir(spill_dir.clone());
        self.spill_dir = spill_dir;
    }
}

#[allow(clippy::too_many_arguments)]
fn prove_fri_cuda_resident_hiding<Challenge, InputMmcs, FriMmcs, Challenger>(
    params: &FriParameters<FriMmcs>,
    mut inputs: Vec<CudaReducedOpening>,
    challenger: &mut Challenger,
    log_global_max_height: usize,
    prover_data_with_opening_points: &[ProverDataWithOpeningPoints<
        '_,
        Challenge,
        InputMmcs::ProverData<RowMajorMatrix<Goldilocks>>,
    >],
    input_mmcs: &InputMmcs,
    ext_w: Goldilocks,
    ext_degree: usize,
) -> FriProof<Challenge, FriMmcs, Challenger::Witness, Vec<BatchMultiOpening<Goldilocks, InputMmcs>>>
where
    Challenge: ExtensionField<Goldilocks>,
    InputMmcs: Mmcs<Goldilocks>,
    FriMmcs: HidingCudaFriMmcs<Goldilocks, Challenge>,
    Challenger: FieldChallenger<Goldilocks> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    assert!(!inputs.is_empty());
    assert!(ext_degree == 2 || ext_degree == 3);
    assert!(
        params.num_queries > 0,
        "num_queries must be at least 1 for FRI soundness"
    );
    assert!(
        params.max_log_arity > 0,
        "max_log_arity must be at least 1 to guarantee folding progress"
    );
    assert!(
        inputs
            .windows(2)
            .all(|pair| pair[0].height() > pair[1].height()),
        "inputs are not sorted in strictly descending order of height"
    );
    assert_eq!(
        log_global_max_height,
        log2_strict_usize(inputs[0].height()),
        "log_global_max_height must match the largest input height"
    );
    let log_min_height = log2_strict_usize(inputs.last().unwrap().height());
    if params.log_final_poly_len > 0 {
        assert!(log_min_height > params.log_final_poly_len + params.log_blowup);
    }

    let mut codeword = inputs.remove(0).into_lde();
    let mut commits = Vec::new();
    let mut rounds = Vec::new();
    let mut log_arities = Vec::new();
    let mut commit_pow_witnesses = Vec::new();
    let final_height = params.blowup() * params.final_poly_len();

    while codeword.height() > final_height {
        let log_height = log2_strict_usize(codeword.height());
        let next_log_height = inputs
            .first()
            .map(|input| log2_strict_usize(input.height()));
        let log_arity = compute_log_arity_for_round(
            log_height,
            next_log_height,
            params.log_blowup + params.log_final_poly_len,
            params.max_log_arity,
        );
        let (commitment, round) = tracing::info_span!("stark/fri_round_commit")
            .in_scope(|| params.mmcs.commit_cuda_fri_hiding(codeword, log_arity));
        challenger.observe(commitment.clone());
        commits.push(commitment);
        commit_pow_witnesses.push(
            tracing::info_span!("stark/fri_commit_grind")
                .in_scope(|| challenger.grind(params.commit_proof_of_work_bits)),
        );
        let beta: Challenge = challenger.sample_algebra_element();
        let mut beta_step = beta;
        let mut betas_flat = Vec::with_capacity(log_arity * ext_degree);
        for _ in 0..log_arity {
            let (buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(beta_step, ext_degree);
            betas_flat.extend_from_slice(&buf[..d]);
            beta_step = beta_step.square();
        }
        let folded_height = round.codeword.height() >> log_arity;
        let add_next = inputs
            .first()
            .is_some_and(|input| input.height() == folded_height);
        let (beta_power_buf, _) =
            ext_to_goldilocks::<Goldilocks, Challenge>(beta.exp_power_of_2(log_arity), ext_degree);
        let g_inv = Goldilocks::two_adic_generator(log_height).inverse();
        codeword = round.codeword.fri_fold(
            add_next.then(|| &inputs[0]),
            &betas_flat,
            log_arity,
            &beta_power_buf[..ext_degree],
            g_inv,
            ext_w,
            ext_degree,
        );
        if add_next {
            inputs.remove(0);
        }
        rounds.push(round);
        log_arities.push(log_arity);
    }
    assert!(inputs.is_empty());

    let final_matrix = codeword.to_row_major_matrix();
    let mut final_values = final_matrix
        .values
        .chunks_exact(ext_degree)
        .take(params.final_poly_len())
        .map(ext_from_goldilocks::<Goldilocks, Challenge>)
        .collect_vec();
    reverse_slice_index_bits(&mut final_values);
    let final_poly = Radix2DFTSmallBatch::default().idft_algebra(final_values);
    challenger.observe_algebra_slice(&final_poly);

    for &log_arity in &log_arities {
        challenger.observe(Goldilocks::from_usize(log_arity));
    }
    let _query_span = tracing::info_span!("stark/fri_queries").entered();
    let query_pow_witness = tracing::info_span!("stark/fri_query_grind")
        .in_scope(|| challenger.grind(params.query_proof_of_work_bits));
    let query_indices = iter::repeat_with(|| challenger.sample_bits(log_global_max_height))
        .take(params.num_queries)
        .collect_vec();
    let input_openings_span = tracing::info_span!("stark/fri_input_openings").entered();
    let input_openings = prover_data_with_opening_points
        .iter()
        .map(|(data, _)| {
            let log_height = log2_strict_usize(input_mmcs.get_max_height(data));
            let indices = query_indices
                .iter()
                .map(|&index| index >> (log_global_max_height - log_height))
                .collect_vec();
            let (opened_values, opening_proof) = input_mmcs.open_multi_batch(&indices, data);
            BatchMultiOpening {
                opened_values,
                opening_proof,
            }
        })
        .collect_vec();
    drop(input_openings_span);

    let mut current_indices = query_indices;
    let commit_phase_openings = rounds
        .iter()
        .zip(&log_arities)
        .map(|(round, &log_arity)| {
            let arity = 1usize << log_arity;
            let positions = current_indices
                .iter()
                .map(|&index| index % arity)
                .collect_vec();
            let group_indices = current_indices
                .iter()
                .map(|&index| index >> log_arity)
                .collect_vec();
            let (opened_rows, opening_proof) =
                tracing::info_span!("stark/fri_commit_phase_opening").in_scope(|| {
                    params
                        .mmcs
                        .open_cuda_fri_hiding_batch(round, &group_indices)
                });
            current_indices = group_indices;
            let sibling_values = positions
                .into_iter()
                .zip(opened_rows)
                .map(|(index_in_group, opened)| {
                    assert_eq!(opened.len(), arity, "FRI opening has the wrong arity");
                    opened
                        .into_iter()
                        .enumerate()
                        .filter_map(|(column, value)| (column != index_in_group).then_some(value))
                        .collect()
                })
                .collect_vec();
            CommitPhaseMultiStep {
                log_arity: u8::try_from(log_arity).expect("FRI arity exceeds u8"),
                sibling_values,
                opening_proof,
            }
        })
        .collect_vec();

    FriProof {
        commit_phase_commits: commits,
        commit_pow_witnesses,
        input_openings,
        commit_phase_openings,
        final_poly,
        query_pow_witness,
    }
}

type HidingCudaCommitOutput = (
    MerkleCap<Goldilocks, [u8; 32]>,
    HidingCudaMmcsData<RowMajorMatrix<Goldilocks>>,
);

impl<FriMmcs> HidingCudaTwoAdicFriPcs<Goldilocks, CudaDft, HidingCudaMmcs, FriMmcs> {
    /// Streams public preprocessed matrices onto the `2N · B` LDE coset WITHOUT
    /// random rows and using the deterministic public [`preprocessed_salt_seed`].
    pub(crate) fn commit_preprocessed_streaming(
        &self,
        evaluations: &mut dyn Iterator<
            Item = (
                TwoAdicMultiplicativeCoset<Goldilocks>,
                RowMajorMatrix<Goldilocks>,
                bool,
            ),
        >,
    ) -> Option<HidingCudaCommitOutput> {
        self.commit_streaming_inner(evaluations, false, preprocessed_salt_seed())
    }

    /// Streams witness matrices onto the `2N · B` LDE coset WITH uniform random
    /// rows on the odd coset and a fresh CSPRNG `salt_seed`, retaining 1×
    /// original traces (on NVMe or in RAM) when `retain_1x` is set.
    pub(crate) fn commit_streaming_with_originals(
        &self,
        evaluations: &mut dyn Iterator<
            Item = (
                TwoAdicMultiplicativeCoset<Goldilocks>,
                RowMajorMatrix<Goldilocks>,
                bool,
            ),
        >,
    ) -> Option<HidingCudaCommitOutput> {
        self.commit_streaming_inner(evaluations, true, random_seed())
    }

    fn commit_streaming_inner(
        &self,
        evaluations: &mut dyn Iterator<
            Item = (
                TwoAdicMultiplicativeCoset<Goldilocks>,
                RowMajorMatrix<Goldilocks>,
                bool,
            ),
        >,
        blind_rows: bool,
        salt_seed: [u8; 32],
    ) -> Option<HidingCudaCommitOutput> {
        let Some(dir) = self.spill_dir.as_deref() else {
            let mut items = Vec::new();
            let mut retained = Vec::new();
            let mut any_retained = false;
            for (domain, evals, retain_1x) in evaluations {
                if retain_1x {
                    any_retained = true;
                    retained.push(Some(evals.clone()));
                } else {
                    retained.push(None);
                }
                items.push((domain, evals));
            }
            if items.is_empty() {
                return None;
            }
            let (commit, data) = self.commit_inner(items, blind_rows, salt_seed);
            if any_retained {
                // Attach retained 1× original traces for zero-FFT lookup/trace access.
                // (No-op for Cpu variant which has its own LDEs.)
                data.set_retained_traces(retained);
            }
            return Some((commit, data));
        };

        let started = std::time::Instant::now();
        let added_bits = if blind_rows {
            self.fri.log_blowup
        } else {
            self.fri.log_blowup + 1
        };
        let device_id = self.mmcs.device_id();
        let leaf_domain = self.mmcs.leaf_domain();
        let (keep_budget, reserve) = super::resident_keep_budget(device_id);

        let mut lde_pack: Option<SpillPackWriter> = None;
        let mut orig_pack: Option<SpillPackWriter> = None;
        let mut resident: Vec<Option<CudaLde>> = Vec::new();
        let mut host_matrices: Vec<Option<RowMajorMatrix<Goldilocks>>> = Vec::new();
        let mut spilled: Vec<Option<SpilledMatrix>> = Vec::new();
        let mut prehashed: Vec<Option<Vec<[u8; 32]>>> = Vec::new();
        let mut spilled_traces: Vec<Option<SpilledMatrix>> = Vec::new();
        let mut retained_traces: Vec<Option<RowMajorMatrix<Goldilocks>>> = Vec::new();
        let mut first_idx_for_height: std::collections::HashMap<usize, Option<usize>> =
            std::collections::HashMap::new();
        let mut resident_bytes = 0usize;
        let mut tier1_count = 0usize;
        let mut tier2_count = 0usize;
        let mut tier3_count = 0usize;

        for (domain, evals, retain_1x) in evaluations {
            assert_eq!(domain.size(), evals.height());
            if retain_1x {
                let orig_bytes = evals
                    .height()
                    .saturating_mul(evals.width())
                    .saturating_mul(size_of::<Goldilocks>());
                if orig_bytes > (64 << 20) || orig_bytes > keep_budget {
                    let writer = orig_pack.get_or_insert_with(|| SpillPackWriter::create(dir));
                    spilled_traces.push(Some(writer.append_matrix(&evals)));
                    retained_traces.push(None);
                } else {
                    spilled_traces.push(None);
                    retained_traces.push(Some(evals.clone()));
                }
            } else {
                spilled_traces.push(None);
                retained_traces.push(None);
            }

            let mat = if blind_rows {
                interleave_random_rows(&evals)
            } else {
                evals
            };
            let height = mat.height();
            let width = mat.width();
            let lde_height = height
                .checked_shl(u32::try_from(added_bits).expect("LDE blowup exceeds u32"))
                .expect("LDE height overflows usize");
            let shift = Goldilocks::GENERATOR / domain.shift();
            let idx = resident.len();
            let is_unique_so_far = match first_idx_for_height.get_mut(&lde_height) {
                None => {
                    first_idx_for_height.insert(lde_height, Some(idx));
                    true
                }
                Some(prev) => {
                    if let Some(prev_idx) = prev.take() {
                        prehashed[prev_idx] = None;
                    }
                    false
                }
            };

            let lde_bytes = lde_height
                .saturating_mul(width)
                .saturating_mul(size_of::<Goldilocks>());
            let trace_bytes = height
                .saturating_mul(width)
                .saturating_mul(size_of::<Goldilocks>());
            let can_use_cuda = CudaDft::supports_cuda_coset_lde(height, width, added_bits);
            let projected_resident = resident_bytes.saturating_add(lde_bytes);

            let mut keep_resident = can_use_cuda && projected_resident <= keep_budget;
            if keep_resident {
                let plan = self.dft.lde_plan(height, width, added_bits, shift);
                let needed = lde_bytes
                    .saturating_add(trace_bytes)
                    .saturating_add(plan.scratch_bytes())
                    .saturating_add(plan.constant_bytes())
                    .saturating_add(lde_height.saturating_mul(96))
                    .saturating_add(reserve);
                if needed > super::device_memory_info(device_id).0 {
                    keep_resident = false;
                }
            }

            if keep_resident {
                let lde = self.dft.coset_lde_batch_resident(&mat, added_bits, shift);
                // SAFETY: `coset_lde_batch_resident` completed synchronously.
                unsafe { lde.release_trace() };
                resident_bytes = projected_resident;
                resident.push(Some(lde));
                host_matrices.push(None);
                spilled.push(None);
                prehashed.push(None);
                tier1_count += 1;
            } else if super::host_spill_headroom(device_id, lde_bytes) {
                let leaf_spec = is_unique_so_far.then_some((leaf_domain, Some(&salt_seed)));
                let (host_mat, digests) = self
                    .dft
                    .coset_lde_to_host(&mat, added_bits, shift, leaf_spec);
                resident.push(None);
                host_matrices.push(Some(host_mat));
                spilled.push(None);
                prehashed.push(digests);
                tier2_count += 1;
            } else {
                let writer = lde_pack.get_or_insert_with(|| SpillPackWriter::create(dir));
                let leaf_spec = is_unique_so_far.then_some((leaf_domain, Some(&salt_seed)));
                let (sp, digests) = self
                    .dft
                    .coset_lde_spilled(&mat, added_bits, shift, writer, leaf_spec);
                resident.push(None);
                host_matrices.push(None);
                spilled.push(Some(sp));
                prehashed.push(digests);
                tier3_count += 1;
            }
        }

        if resident.is_empty() {
            return None;
        }
        if let Some(writer) = &mut lde_pack {
            writer.flush();
        }
        if let Some(writer) = &mut orig_pack {
            writer.flush();
        }
        let lde_s = started.elapsed().as_secs_f64();
        let merkle_started = std::time::Instant::now();
        let spilled_traces_arg = if orig_pack.is_some() {
            spilled_traces
        } else {
            Vec::new()
        };
        let out = self.mmcs.commit_cuda_mixed_spilled_with_seed(
            resident,
            host_matrices,
            spilled,
            prehashed,
            retained_traces,
            spilled_traces_arg,
            salt_seed,
        );
        if super::memory_diagnostics_enabled() {
            eprintln!(
                "[multi-stark/cuda] v6-zk streaming commit (blind={blind_rows}): mats={} tier1_vram={} tier2_host={} tier3_nvme={} lde={:.3}s merkle={:.3}s",
                tier1_count + tier2_count + tier3_count,
                tier1_count,
                tier2_count,
                tier3_count,
                lde_s,
                merkle_started.elapsed().as_secs_f64(),
            );
        }
        Some(out)
    }
}

impl<Dft, FriMmcs> HidingCudaTwoAdicFriPcs<Goldilocks, Dft, HidingCudaMmcs, FriMmcs>
where
    Dft: TwoAdicSubgroupDft<Goldilocks> + CudaPcsDft<Goldilocks> + Sync,
{
    /// Commits public preprocessed matrices onto the `2N · B` LDE coset WITHOUT
    /// random rows and using the deterministic public [`preprocessed_salt_seed`]
    /// so independent prover and verifier setups (including CPU and CUDA) produce
    /// identical `preprocessed_commit` roots.
    #[cfg(test)]
    pub(crate) fn commit_preprocessed(
        &self,
        evaluations: impl IntoIterator<
            Item = (
                TwoAdicMultiplicativeCoset<Goldilocks>,
                RowMajorMatrix<Goldilocks>,
            ),
        >,
    ) -> (
        <HidingCudaMmcs as Mmcs<Goldilocks>>::Commitment,
        <HidingCudaMmcs as Mmcs<Goldilocks>>::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        let evals: Vec<_> = evaluations.into_iter().collect();
        self.commit_inner(evals, false, preprocessed_salt_seed())
    }

    fn commit_inner(
        &self,
        evaluations: Vec<(
            TwoAdicMultiplicativeCoset<Goldilocks>,
            RowMajorMatrix<Goldilocks>,
        )>,
        blind_rows: bool,
        salt_seed: [u8; 32],
    ) -> (
        <HidingCudaMmcs as Mmcs<Goldilocks>>::Commitment,
        <HidingCudaMmcs as Mmcs<Goldilocks>>::ProverData<RowMajorMatrix<Goldilocks>>,
    ) {
        assert!(
            !evaluations.is_empty(),
            "commit requires at least one matrix"
        );
        let added_bits = if blind_rows {
            self.fri.log_blowup
        } else {
            self.fri.log_blowup + 1
        };
        let prepared: Vec<(
            TwoAdicMultiplicativeCoset<Goldilocks>,
            RowMajorMatrix<Goldilocks>,
        )> = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert_eq!(domain.size(), evals.height());
                let mat = if blind_rows {
                    interleave_random_rows(&evals)
                } else {
                    evals
                };
                (domain, mat)
            })
            .collect();

        let source_cells: usize = prepared
            .iter()
            .map(|(_, mat)| mat.height().saturating_mul(mat.width()))
            .sum();
        let max_transform_workspace = prepared
            .iter()
            .map(|(domain, mat)| {
                self.dft.coset_lde_workspace_bytes(
                    mat.height(),
                    mat.width(),
                    added_bits,
                    Goldilocks::GENERATOR / domain.shift(),
                )
            })
            .max()
            .unwrap_or(0);
        let (initial_free, total_device_bytes) = super::device_memory_info(self.mmcs.device_id());
        let minimum_free = super::minimum_free_bytes();
        let lde_bytes = source_cells
            .saturating_mul(size_of::<Goldilocks>())
            .checked_shl(u32::try_from(added_bits).expect("LDE blowup exceeds u32"))
            .unwrap_or(usize::MAX);
        // An LDE uploads its whole trace beside its values, and a trace
        // released after construction is still resident while its own LDE
        // runs, so the all-device path always needs the largest trace.
        let max_trace_bytes = prepared
            .iter()
            .map(|(_, mat)| {
                mat.height()
                    .saturating_mul(mat.width())
                    .saturating_mul(size_of::<Goldilocks>())
            })
            .max()
            .unwrap_or(0);
        let max_lde_height = prepared
            .iter()
            .map(|(_, mat)| {
                mat.height()
                    .checked_shl(u32::try_from(added_bits).expect("LDE blowup exceeds u32"))
                    .unwrap_or(usize::MAX)
            })
            .max()
            .unwrap_or(0);
        // The salted Merkle tree built immediately after the LDE loop holds
        // all binary digest layers plus one injected frontier (~96 bytes/row).
        let tree_workspace_bytes = max_lde_height.saturating_mul(96);
        let peak_workspace = max_trace_bytes
            .saturating_add(max_transform_workspace)
            .max(tree_workspace_bytes);

        if let Some(dir) = self.mmcs.spill_dir() {
            let reserve = minimum_free.saturating_add(128 << 20);
            let round_resident_budget = initial_free
                .saturating_sub(reserve)
                .checked_div(4)
                .unwrap_or(0)
                .min(total_device_bytes / 6);
            if lde_bytes
                .saturating_add(peak_workspace)
                .saturating_add(reserve)
                > initial_free
                || lde_bytes > round_resident_budget
            {
                let mut pack = SpillPackWriter::create(dir);
                let mut height_counts = std::collections::HashMap::<usize, usize>::new();
                for (_, mat) in &prepared {
                    *height_counts.entry(mat.height() << added_bits).or_insert(0) += 1;
                }
                let leaf_domain = self.mmcs.leaf_domain();
                let mut spilled = Vec::with_capacity(prepared.len());
                let mut prehashed = Vec::with_capacity(prepared.len());
                for (domain, mat) in prepared {
                    let shift = Goldilocks::GENERATOR / domain.shift();
                    let lde_height = mat.height() << added_bits;
                    let leaf_spec = (height_counts[&lde_height] == 1)
                        .then_some((leaf_domain, Some(&salt_seed)));
                    let (sp, digests) = self
                        .dft
                        .coset_lde_spilled(&mat, added_bits, shift, &mut pack, leaf_spec);
                    spilled.push(Some(sp));
                    prehashed.push(digests);
                }
                pack.flush();
                let count = spilled.len();
                return self.mmcs.commit_cuda_mixed_spilled_with_seed(
                    (0..count).map(|_| None).collect(),
                    (0..count).map(|_| None).collect(),
                    spilled,
                    prehashed,
                    Vec::new(),
                    Vec::new(),
                    salt_seed,
                );
            }
        }

        if lde_bytes
            .saturating_add(peak_workspace)
            .saturating_add(minimum_free)
            > initial_free
        {
            let dft = &self.dft;
            let ldes: Vec<RowMajorMatrix<Goldilocks>> = prepared
                .into_par_iter()
                .map(|(domain, evals)| {
                    let shift = Goldilocks::GENERATOR / domain.shift();
                    if let Some(lde) = dft.try_coset_lde_batch_host(&evals, added_bits, shift) {
                        return lde;
                    }
                    let cpu = Radix2DitParallel::<Goldilocks>::default();
                    let mut lde = cpu
                        .coset_lde_batch(evals, added_bits, shift)
                        .bit_reverse_rows()
                        .to_row_major_matrix();
                    lde.values.par_iter_mut().for_each(|v| {
                        *v = Goldilocks::from_u64(v.as_canonical_u64());
                    });
                    lde
                })
                .collect();
            return self.mmcs.commit_cpu_with_seed(ldes, salt_seed);
        }

        let mut ldes = Vec::with_capacity(prepared.len());
        for (domain, evals) in &prepared {
            let shift = Goldilocks::GENERATOR / domain.shift();
            let lde = self.dft.coset_lde_batch_resident(evals, added_bits, shift);
            // SAFETY: `coset_lde_batch_resident` completed synchronously; `v6-zk`
            // does not retain separate 1× GPU trace buffers after LDE creation.
            unsafe { lde.release_trace() };
            ldes.push(lde);
        }
        if self.mmcs.spill_dir().is_some() {
            let count = ldes.len();
            self.mmcs.commit_cuda_mixed_spilled_with_seed(
                ldes.into_iter().map(Some).collect(),
                (0..count).map(|_| None).collect(),
                (0..count).map(|_| None).collect(),
                (0..count).map(|_| None).collect(),
                Vec::new(),
                Vec::new(),
                salt_seed,
            )
        } else {
            self.mmcs.commit_cuda_resident_with_seed(ldes, salt_seed)
        }
    }

    fn re_evaluate_from_lde<'a>(
        &self,
        lde_mat: RowMajorMatrix<Goldilocks>,
        poly_height: usize,
        domain: TwoAdicMultiplicativeCoset<Goldilocks>,
    ) -> BitReversedMatrixView<RowMajorMatrixCow<'a, Goldilocks>> {
        let mut coeffs = self.dft.coset_idft_batch(lde_mat, Goldilocks::GENERATOR);
        let width = coeffs.width();
        coeffs.values.truncate(poly_height * width);
        let target_size = domain.size();
        if target_size >= poly_height {
            coeffs.values.resize(target_size * width, Goldilocks::ZERO);
        } else {
            // Fold modulo `(X^m - shift^m)` so evaluating a degree `< 2N` blinded
            // polynomial on a smaller coset `shift * H_m` (e.g. `H_N`) is exact.
            debug_assert!(poly_height.is_multiple_of(target_size));
            let blocks = poly_height / target_size;
            let shift_pow_m = domain
                .shift()
                .exp_u64(u64::try_from(target_size).expect("domain size exceeds u64"));
            let mut factor = shift_pow_m;
            for b in 1..blocks {
                let src_off = b * target_size * width;
                for i in 0..(target_size * width) {
                    let v = coeffs.values[src_off + i];
                    coeffs.values[i] += factor * v;
                }
                factor *= shift_pow_m;
            }
            coeffs.values.truncate(target_size * width);
        }
        let result = self
            .dft
            .coset_dft_batch(coeffs, domain.shift())
            .bit_reverse_rows()
            .to_row_major_matrix();
        let result_width = result.width();
        RowMajorMatrixCow::new(Cow::Owned(result.values), result_width).bit_reverse_rows()
    }
}

impl<Dft, FriMmcs, Challenge, Challenger> Pcs<Challenge, Challenger>
    for HidingCudaTwoAdicFriPcs<Goldilocks, Dft, HidingCudaMmcs, FriMmcs>
where
    Dft: TwoAdicSubgroupDft<Goldilocks> + CudaPcsDft<Goldilocks> + Sync,
    FriMmcs: CapValidatingMmcs<Challenge> + HidingCudaFriMmcs<Goldilocks, Challenge>,
    Challenge: ExtensionField<Goldilocks>,
    Challenger: FieldChallenger<Goldilocks>
        + CanObserve<FriMmcs::Commitment>
        + GrindingChallenger<Witness = Goldilocks>,
{
    type Domain = TwoAdicMultiplicativeCoset<Goldilocks>;
    type Commitment = <HidingCudaMmcs as Mmcs<Goldilocks>>::Commitment;
    type ProverData = <HidingCudaMmcs as Mmcs<Goldilocks>>::ProverData<RowMajorMatrix<Goldilocks>>;
    type EvaluationsOnDomain<'a> = BitReversedMatrixView<RowMajorMatrixCow<'a, Goldilocks>>;
    type Proof = FriProof<
        Challenge,
        FriMmcs,
        Goldilocks,
        Vec<BatchMultiOpening<Goldilocks, HidingCudaMmcs>>,
    >;
    type Error = FriError<FriMmcs::Error, <HidingCudaMmcs as Mmcs<Goldilocks>>::Error>;
    const ZK: bool = true;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        TwoAdicMultiplicativeCoset::new(Goldilocks::ONE, log2_strict_usize(degree)).unwrap()
    }

    fn log_max_lde_height(&self) -> usize {
        Goldilocks::TWO_ADICITY
    }

    fn commit(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Goldilocks>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        let evals: Vec<_> = evaluations.into_iter().collect();
        self.commit_inner(evals, true, random_seed())
    }

    fn get_quotient_ldes(
        &self,
        evaluations: impl IntoIterator<Item = (Self::Domain, RowMajorMatrix<Goldilocks>)>,
        _num_chunks: usize,
    ) -> Vec<RowMajorMatrix<Goldilocks>> {
        evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert_eq!(domain.size(), evals.height());
                let interleaved = interleave_random_rows(&evals);
                let shift = Goldilocks::GENERATOR / domain.shift();
                self.dft
                    .coset_lde_batch(interleaved, self.fri.log_blowup, shift)
                    .bit_reverse_rows()
                    .to_row_major_matrix()
            })
            .collect()
    }

    fn commit_ldes(
        &self,
        ldes: Vec<RowMajorMatrix<Goldilocks>>,
    ) -> (Self::Commitment, Self::ProverData) {
        let min_height = 1usize << (self.fri.log_blowup + 1);
        for lde in &ldes {
            assert!(
                lde.height() >= min_height,
                "committed ZK LDE height {} is smaller than 2 * blowup ({min_height})",
                lde.height()
            );
        }
        self.mmcs.commit_cuda_storage_with_seed(ldes, random_seed())
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        if let Some(spilled) = self.mmcs.spilled_matrices(prover_data)[idx] {
            if domain.shift() == Goldilocks::GENERATOR && spilled.height() >= domain.size() {
                let prefix = spilled.read_rows(0, domain.size());
                let width = prefix.width();
                return RowMajorMatrixCow::new(Cow::Owned(prefix.values), width).bit_reverse_rows();
            }
            if domain.shift() == Goldilocks::ONE
                && let Some(orig) = prover_data.spilled_original_trace(idx)
                && orig.height() == domain.size()
            {
                let natural = orig.read_all();
                let bitrev = natural.as_view().bit_reverse_rows().to_row_major_matrix();
                let width = bitrev.width();
                return RowMajorMatrixCow::new(Cow::Owned(bitrev.values), width).bit_reverse_rows();
            }
            if domain.shift() == Goldilocks::ONE
                && let Some(orig) = prover_data.clone_in_memory_original_trace(idx)
                && orig.height() == domain.size()
            {
                let bitrev = orig.as_view().bit_reverse_rows().to_row_major_matrix();
                let width = bitrev.width();
                return RowMajorMatrixCow::new(Cow::Owned(bitrev.values), width).bit_reverse_rows();
            }
            let poly_height = spilled.height() >> self.fri.log_blowup;
            let lde_mat = spilled
                .read_all()
                .as_view()
                .bit_reverse_rows()
                .to_row_major_matrix();
            return self.re_evaluate_from_lde(lde_mat, poly_height, domain);
        }
        if domain.shift() == Goldilocks::ONE
            && let Some(orig) = prover_data.clone_in_memory_original_trace(idx)
            && orig.height() == domain.size()
        {
            let bitrev = orig.as_view().bit_reverse_rows().to_row_major_matrix();
            let width = bitrev.width();
            return RowMajorMatrixCow::new(Cow::Owned(bitrev.values), width).bit_reverse_rows();
        }
        let lde = self.mmcs.get_matrices(prover_data)[idx];
        if domain.shift() == Goldilocks::GENERATOR && lde.height() >= domain.size() {
            return lde.split_rows(domain.size()).0.as_cow().bit_reverse_rows();
        }
        let poly_height = lde.height() >> self.fri.log_blowup;
        let lde_mat = lde.as_view().bit_reverse_rows().to_row_major_matrix();
        self.re_evaluate_from_lde(lde_mat, poly_height, domain)
    }

    fn open(
        &self,
        commitment_data_with_opening_points: Vec<
            ProverDataWithOpeningPoints<'_, Challenge, Self::ProverData>,
        >,
        challenger: &mut Challenger,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        // Fast path: keep all GPU-resident commitments on device through
        // barycentric OOD interpolation, reduced-opening accumulation, and
        // salted FRI commit-phase folding.
        if commitment_data_with_opening_points
            .iter()
            .all(|(data, _)| self.mmcs.is_cuda_resident(data))
        {
            let resident_rounds = commitment_data_with_opening_points
                .iter()
                .map(|(data, points)| (self.mmcs.resident_arc(data).unwrap(), points))
                .collect_vec();
            let resident_max_height = resident_rounds
                .iter()
                .flat_map(|(ldes, _)| ldes.iter())
                .map(CudaLde::height)
                .max()
                .unwrap_or(0);
            let final_fri_height = self.fri.blowup() * self.fri.final_poly_len();
            if resident_max_height > 1024 && resident_max_height > final_fri_height {
                let device_id = self.mmcs.device_id();
                let (ext_degree, ext_w) = cuda_ext_degree_and_w::<Goldilocks, Challenge>();
                let mut opened_max_width = 0usize;
                let mut openings_per_height = [0usize; 33];
                let mut max_log: LinearMap<Challenge, usize> = LinearMap::new();
                for (ldes, points) in &resident_rounds {
                    for (lde, ps) in ldes.iter().zip(points.iter()) {
                        if !ps.is_empty() {
                            opened_max_width = opened_max_width.max(lde.width());
                            let lh = log2_strict_usize(lde.height());
                            openings_per_height[lh] += ps.len();
                            for &z in ps {
                                if let Some(h) = max_log.get_mut(&z) {
                                    *h = (*h).max(lh);
                                } else {
                                    max_log.insert(z, lh);
                                }
                            }
                        }
                    }
                }
                let point_logs = max_log.into_iter().collect_vec();
                let inverse_elements: usize = point_logs.iter().map(|&(_, lh)| 1usize << lh).sum();
                let max_inverse_elements: usize = point_logs
                    .iter()
                    .map(|&(_, lh)| 1usize << lh)
                    .max()
                    .unwrap_or(0);
                let reduced_elements: usize = openings_per_height
                    .iter()
                    .enumerate()
                    .filter_map(|(lh, &count)| (count > 0).then_some(1usize << lh))
                    .sum();
                let (free_bytes, total_device_bytes) = super::device_memory_info(device_id);
                let minimum_free = super::minimum_free_bytes();
                let fri_workspace_bytes = inverse_elements
                    .saturating_mul(ext_degree * size_of::<Goldilocks>())
                    .saturating_add(resident_max_height.saturating_mul(size_of::<Goldilocks>()))
                    .saturating_add(
                        max_inverse_elements.saturating_mul(ext_degree * size_of::<Goldilocks>()),
                    )
                    .saturating_add(
                        reduced_elements.saturating_mul(ext_degree * size_of::<Goldilocks>()),
                    )
                    .saturating_add(
                        resident_max_height
                            .saturating_mul(ext_degree * size_of::<Goldilocks>() + 96),
                    )
                    .saturating_add(total_device_bytes / 64);
                if fri_workspace_bytes.saturating_add(minimum_free) <= free_bytes {
                    let _resident_guard = tracing::info_span!("stark/fri_resident_zk").entered();
                    let max_openings_per_height =
                        openings_per_height.into_iter().max().unwrap_or(0);
                    let log_global_max_height = log2_strict_usize(resident_max_height);
                    let coset_gold = bit_reversed_coset::<Goldilocks>(log_global_max_height);
                    let mut inv_offsets = LinearMap::new();
                    let mut inverse_points = Vec::new();
                    let mut inverse_counts = Vec::new();
                    let mut inverse_count = 0usize;
                    for (point, lh) in point_logs {
                        inv_offsets.insert(point, inverse_count);
                        let (buf, d) =
                            ext_to_goldilocks::<Goldilocks, Challenge>(point, ext_degree);
                        inverse_points.extend_from_slice(&buf[..d]);
                        let count = 1usize << lh;
                        inverse_counts.push(count);
                        inverse_count += count;
                    }
                    let mut workspace = CudaFriWorkspace::new(
                        device_id,
                        &inverse_points,
                        &inverse_counts,
                        &coset_gold,
                        ext_w,
                        ext_degree,
                    );
                    let mut interpolation_tasks = CudaInterpolationTasks::new(ext_degree);
                    let mut output_count = 0usize;
                    let layouts = resident_rounds
                        .iter()
                        .map(|(ldes, points)| {
                            ldes.iter()
                                .zip(points.iter())
                                .map(|(lde, ps)| {
                                    let h = lde.height() >> self.fri.log_blowup;
                                    let lh = log2_strict_usize(h);
                                    ps.iter()
                                        .map(|&point| {
                                            let offset = output_count;
                                            output_count += lde.width();
                                            let shift_pow =
                                                Goldilocks::GENERATOR.exp_power_of_2(lh);
                                            let scale = (point.exp_power_of_2(lh) - shift_pow)
                                                * (Goldilocks::from_usize(h) * shift_pow).inverse();
                                            let (scale_buf, d) =
                                                ext_to_goldilocks::<Goldilocks, Challenge>(
                                                    scale, ext_degree,
                                                );
                                            interpolation_tasks.push(
                                                lde,
                                                h,
                                                *inv_offsets.get(&point).unwrap(),
                                                offset,
                                                &scale_buf[..d],
                                            );
                                            (offset, lde.width())
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        })
                        .collect_vec();
                    let interpolated =
                        tracing::info_span!("stark/fri_interpolate").in_scope(|| {
                            workspace.interpolate(&interpolation_tasks, output_count, ext_w)
                        });
                    let all_opened_values = layouts
                        .into_iter()
                        .map(|round| {
                            round
                                .into_iter()
                                .map(|matrix| {
                                    matrix
                                        .into_iter()
                                        .map(|(offset, width)| {
                                            interpolated
                                                [offset * ext_degree..(offset + width) * ext_degree]
                                                .chunks_exact(ext_degree)
                                                .map(ext_from_goldilocks::<Goldilocks, Challenge>)
                                                .collect_vec()
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        })
                        .collect_vec();
                    for round in &all_opened_values {
                        for matrix in round {
                            for values in matrix {
                                challenger.observe_algebra_slice(values);
                            }
                        }
                    }
                    let schedule = FriBatchingSchedule::<Challenge>::sample(
                        self.batching,
                        opened_max_width,
                        max_openings_per_height,
                        challenger,
                    );
                    let col_weights: Vec<Challenge> = match &schedule {
                        FriBatchingSchedule::Horner { alpha } => {
                            alpha.powers().take(opened_max_width).collect()
                        }
                        FriBatchingSchedule::Tensor { col_weights, .. } => col_weights.clone(),
                    };
                    let mut col_weights_flat = Vec::with_capacity(col_weights.len() * ext_degree);
                    for &w in &col_weights {
                        let (buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(w, ext_degree);
                        col_weights_flat.extend_from_slice(&buf[..d]);
                    }
                    let mut num_reduced = [0usize; 33];
                    let mut opening_idx_by_height = [0usize; 33];
                    let mut reduced: [Option<CudaReducedOpening>; 33] =
                        core::array::from_fn(|_| None);
                    let mut reduction_tasks = CudaReductionTasks::new(ext_degree);
                    for ((ldes, points), openings_round) in
                        resident_rounds.iter().zip(all_opened_values.iter())
                    {
                        for ((lde, ps), openings) in
                            ldes.iter().zip(points.iter()).zip(openings_round.iter())
                        {
                            if ps.is_empty() {
                                continue;
                            }
                            let lh = log2_strict_usize(lde.height());
                            let target = reduced[lh].get_or_insert_with(|| {
                                CudaReducedOpening::new_with_degree(
                                    device_id,
                                    lde.height(),
                                    ext_degree,
                                )
                            });
                            for (&point, ys) in ps.iter().zip(openings.iter()) {
                                let reduced_y: Challenge =
                                    dot_product(col_weights.iter().copied(), ys.iter().copied());
                                let offset = match &schedule {
                                    FriBatchingSchedule::Horner { alpha } => alpha.exp_u64(
                                        u64::try_from(num_reduced[lh])
                                            .expect("reduced column count exceeds u64"),
                                    ),
                                    FriBatchingSchedule::Tensor { open_weights, .. } => {
                                        open_weights[opening_idx_by_height[lh]]
                                    }
                                };
                                let (y_buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(
                                    reduced_y, ext_degree,
                                );
                                let (off_buf, _) =
                                    ext_to_goldilocks::<Goldilocks, Challenge>(offset, ext_degree);
                                reduction_tasks.push(
                                    target,
                                    lde,
                                    *inv_offsets.get(&point).unwrap(),
                                    &y_buf[..d],
                                    &off_buf[..d],
                                );
                                num_reduced[lh] += lde.width();
                                opening_idx_by_height[lh] += 1;
                            }
                        }
                    }
                    if !reduction_tasks.is_empty() {
                        tracing::info_span!("stark/fri_reduce").in_scope(|| {
                            workspace.reduce(&reduction_tasks, &col_weights_flat, ext_w);
                        });
                    }
                    let fri_input = reduced.into_iter().rev().flatten().collect_vec();
                    let fri_proof = tracing::info_span!("stark/fri_prove").in_scope(|| {
                        prove_fri_cuda_resident_hiding(
                            &self.fri,
                            fri_input,
                            challenger,
                            log_global_max_height,
                            &commitment_data_with_opening_points,
                            &self.mmcs,
                            ext_w,
                            ext_degree,
                        )
                    });
                    return (all_opened_values, fri_proof);
                }
            }
        }

        // Streamed CUDA path: handles any mix of CUDA-resident, NVMe-spilled,
        // and host-resident commitments using 64 MiB chunked GPU interpolation
        // and reduction plus GPU salted FRI folding.
        let dimensions = commitment_data_with_opening_points
            .iter()
            .map(|(data, points)| {
                let dims = self.mmcs.matrix_dimensions(data);
                assert_eq!(
                    dims.len(),
                    points.len(),
                    "each matrix should have a corresponding set of evaluation points"
                );
                dims
            })
            .collect_vec();
        let opening_points = commitment_data_with_opening_points
            .iter()
            .map(|(_, points)| points)
            .collect_vec();
        let global_max_height = dimensions
            .iter()
            .flatten()
            .map(|d| d.height)
            .max()
            .expect("No Matrices Supplied?");
        let mut opened_max_width = 0usize;
        let mut openings_per_height = [0usize; 33];
        let mut max_log: LinearMap<Challenge, usize> = LinearMap::new();
        for ((_, points), round_dims) in commitment_data_with_opening_points
            .iter()
            .zip(dimensions.iter())
        {
            for (pts, dims) in points.iter().zip(round_dims.iter()) {
                if !pts.is_empty() {
                    opened_max_width = opened_max_width.max(dims.width);
                    let lh = log2_strict_usize(dims.height);
                    openings_per_height[lh] += pts.len();
                    for &z in pts {
                        if let Some(h) = max_log.get_mut(&z) {
                            *h = (*h).max(lh);
                        } else {
                            max_log.insert(z, lh);
                        }
                    }
                }
            }
        }
        let max_openings_per_height = openings_per_height.into_iter().max().unwrap_or(0);
        let final_fri_height = self.fri.blowup() * self.fri.final_poly_len();
        if global_max_height > 1024 && global_max_height > final_fri_height {
            let device_id = self.mmcs.device_id();
            let (ext_degree, ext_w) = cuda_ext_degree_and_w::<Goldilocks, Challenge>();
            let point_logs = max_log.into_iter().collect_vec();
            let inverse_elements: usize = point_logs.iter().map(|&(_, lh)| 1usize << lh).sum();
            let max_inverse_elements: usize = point_logs
                .iter()
                .map(|&(_, lh)| 1usize << lh)
                .max()
                .unwrap_or(0);
            let reduced_elements: usize = openings_per_height
                .iter()
                .enumerate()
                .filter_map(|(lh, &count)| (count > 0).then_some(1usize << lh))
                .sum();
            let (_, total_device_bytes) = super::device_memory_info(device_id);
            let minimum_free = super::minimum_free_bytes();
            let fri_workspace_bytes = inverse_elements
                .saturating_mul(ext_degree * size_of::<Goldilocks>())
                .saturating_add(global_max_height.saturating_mul(size_of::<Goldilocks>()))
                .saturating_add(
                    max_inverse_elements.saturating_mul(ext_degree * size_of::<Goldilocks>()),
                )
                .saturating_add(
                    reduced_elements.saturating_mul(ext_degree * size_of::<Goldilocks>()),
                )
                .saturating_add(
                    global_max_height.saturating_mul(ext_degree * size_of::<Goldilocks>() + 96),
                )
                .saturating_add(STREAM_BLOCK_BYTES)
                .saturating_add(total_device_bytes / 64);
            let admission_data = commitment_data_with_opening_points
                .iter()
                .map(|entry| entry.0)
                .collect_vec();
            let free_after_admission = self.mmcs.ensure_device_headroom_batch(
                &admission_data,
                fri_workspace_bytes.saturating_add(minimum_free),
                "fri",
            );
            if free_after_admission >= fri_workspace_bytes.saturating_add(minimum_free) {
                let _streamed_guard = tracing::info_span!("stark/fri_streamed_zk").entered();
                let log_global_max_height = log2_strict_usize(global_max_height);
                let coset_gold = bit_reversed_coset::<Goldilocks>(log_global_max_height);
                let mut inv_offsets = LinearMap::new();
                let mut inverse_points = Vec::new();
                let mut inverse_counts = Vec::new();
                let mut inverse_count = 0usize;
                for &(point, lh) in &point_logs {
                    inv_offsets.insert(point, inverse_count);
                    let (buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(point, ext_degree);
                    inverse_points.extend_from_slice(&buf[..d]);
                    let count = 1usize << lh;
                    inverse_counts.push(count);
                    inverse_count += count;
                }
                let cpu_round_matrices = commitment_data_with_opening_points
                    .iter()
                    .map(|(data, _)| self.mmcs.cpu_matrices(data))
                    .collect_vec();
                let spilled_round_matrices = commitment_data_with_opening_points
                    .iter()
                    .map(|(data, _)| self.mmcs.spilled_matrices(data))
                    .collect_vec();
                let any_cpu = cpu_round_matrices.iter().flatten().any(Option::is_some);
                let (cpu_inv_denoms, mut workspace) = std::thread::scope(|scope| {
                    let cpu_task = scope.spawn(|| {
                        if any_cpu {
                            compute_inverse_denominators_for_dims(
                                &dimensions,
                                &opening_points,
                                &coset_gold,
                            )
                        } else {
                            LinearMap::new()
                        }
                    });
                    let ws = CudaFriWorkspace::new(
                        device_id,
                        &inverse_points,
                        &inverse_counts,
                        &coset_gold,
                        ext_w,
                        ext_degree,
                    );
                    (cpu_task.join().unwrap(), ws)
                });
                let cpu_adjusted_weights: LinearMap<Challenge, Vec<Challenge>> = cpu_inv_denoms
                    .iter()
                    .map(|(point, denoms)| (*point, compute_adjusted_weights(*point, denoms)))
                    .collect();

                let fri_log_blowup = self.fri.log_blowup;
                let (cpu_opened, gpu_opened) = std::thread::scope(|scope| {
                    let cpu_task = scope.spawn(|| {
                        cpu_round_matrices
                            .iter()
                            .zip(opening_points.iter())
                            .map(|(mats, &points)| {
                                mats.par_iter()
                                    .copied()
                                    .zip(points.par_iter())
                                    .map(|(mat, pts)| {
                                        let mat = mat?;
                                        let h = mat.height() >> fri_log_blowup;
                                        let (low_coset, _) = mat.split_rows(h);
                                        Some(
                                            pts.iter()
                                                .map(|&point| {
                                                    low_coset.interpolate_coset_with_precomputation(
                                                        Goldilocks::GENERATOR,
                                                        point,
                                                        &cpu_adjusted_weights.get(&point).unwrap()
                                                            [..h],
                                                    )
                                                })
                                                .collect_vec(),
                                        )
                                    })
                                    .collect::<Vec<_>>()
                            })
                            .collect_vec()
                    });
                    let gpu_res = commitment_data_with_opening_points
                        .iter()
                        .zip(dimensions.iter())
                        .zip(spilled_round_matrices.iter())
                        .map(|(((data, points), round_dims), spilled_mats)| {
                            points
                                .iter()
                                .zip(round_dims.iter())
                                .zip(spilled_mats.iter())
                                .enumerate()
                                .map(|(mat_idx, ((pts, dims), spilled_mat))| {
                                    if let Some(spilled) = spilled_mat {
                                        if pts.is_empty() {
                                            return Some(Vec::new());
                                        }
                                        let h = spilled.height() >> fri_log_blowup;
                                        let lh = log2_strict_usize(h);
                                        let shift_pow = Goldilocks::GENERATOR.exp_power_of_2(lh);
                                        let mut mat_inv_offsets = Vec::with_capacity(pts.len());
                                        let mut mat_scales_flat =
                                            Vec::with_capacity(pts.len() * ext_degree);
                                        for &point in pts {
                                            let scale = (point.exp_power_of_2(lh) - shift_pow)
                                                * (Goldilocks::from_usize(h) * shift_pow).inverse();
                                            let (scale_buf, d) =
                                                ext_to_goldilocks::<Goldilocks, Challenge>(
                                                    scale, ext_degree,
                                                );
                                            mat_inv_offsets.push(*inv_offsets.get(&point).unwrap());
                                            mat_scales_flat.extend_from_slice(&scale_buf[..d]);
                                        }
                                        let flat = workspace.interpolate_spilled(
                                            spilled,
                                            h,
                                            &mat_inv_offsets,
                                            &mat_scales_flat,
                                            ext_w,
                                        );
                                        return Some(
                                            flat.chunks_exact(spilled.width() * ext_degree)
                                                .map(|vals| {
                                                    vals.chunks_exact(ext_degree)
                                                        .map(
                                                            ext_from_goldilocks::<
                                                                Goldilocks,
                                                                Challenge,
                                                            >,
                                                        )
                                                        .collect_vec()
                                                })
                                                .collect_vec(),
                                        );
                                    }
                                    if !self.mmcs.is_matrix_cuda_resident(data, mat_idx) {
                                        return None;
                                    }
                                    if pts.is_empty() {
                                        return Some(Vec::new());
                                    }
                                    Some(self.mmcs.with_resident_matrix(data, mat_idx, |lde| {
                                        assert_eq!(lde.height(), dims.height);
                                        assert_eq!(lde.width(), dims.width);
                                        let h = lde.height() >> fri_log_blowup;
                                        let lh = log2_strict_usize(h);
                                        let shift_pow = Goldilocks::GENERATOR.exp_power_of_2(lh);
                                        let mut tasks = CudaInterpolationTasks::new(ext_degree);
                                        for (pt_i, &point) in pts.iter().enumerate() {
                                            let scale = (point.exp_power_of_2(lh) - shift_pow)
                                                * (Goldilocks::from_usize(h) * shift_pow).inverse();
                                            let (scale_buf, d) =
                                                ext_to_goldilocks::<Goldilocks, Challenge>(
                                                    scale, ext_degree,
                                                );
                                            tasks.push(
                                                lde,
                                                h,
                                                *inv_offsets.get(&point).unwrap(),
                                                pt_i * lde.width(),
                                                &scale_buf[..d],
                                            );
                                        }
                                        workspace
                                            .interpolate(&tasks, pts.len() * lde.width(), ext_w)
                                            .chunks_exact(lde.width() * ext_degree)
                                            .map(|vals| {
                                                vals.chunks_exact(ext_degree)
                                                    .map(ext_from_goldilocks::<
                                                        Goldilocks,
                                                        Challenge,
                                                    >)
                                                    .collect_vec()
                                            })
                                            .collect_vec()
                                    }))
                                })
                                .collect_vec()
                        })
                        .collect_vec();
                    (cpu_task.join().unwrap(), gpu_res)
                });
                let all_opened_values = cpu_opened
                    .into_iter()
                    .zip(gpu_opened)
                    .map(|(cpu_round, gpu_round)| {
                        cpu_round
                            .into_iter()
                            .zip(gpu_round)
                            .map(|(c, g)| c.or(g).expect("v6-zk matrix has no opening backend"))
                            .collect_vec()
                    })
                    .collect_vec();
                for round in &all_opened_values {
                    for matrix in round {
                        for values in matrix {
                            challenger.observe_algebra_slice(values);
                        }
                    }
                }
                let schedule = FriBatchingSchedule::<Challenge>::sample(
                    self.batching,
                    opened_max_width,
                    max_openings_per_height,
                    challenger,
                );
                let col_weights: Vec<Challenge> = match &schedule {
                    FriBatchingSchedule::Horner { alpha } => {
                        alpha.powers().take(opened_max_width).collect()
                    }
                    FriBatchingSchedule::Tensor { col_weights, .. } => col_weights.clone(),
                };
                let mut col_weights_flat = Vec::with_capacity(col_weights.len() * ext_degree);
                for &w in &col_weights {
                    let (buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(w, ext_degree);
                    col_weights_flat.extend_from_slice(&buf[..d]);
                }
                let packed_col_weights: Vec<Challenge::ExtensionPacking> = match &schedule {
                    FriBatchingSchedule::Horner { alpha } => {
                        Challenge::ExtensionPacking::packed_ext_powers_capped(
                            *alpha,
                            opened_max_width,
                        )
                        .collect_vec()
                    }
                    FriBatchingSchedule::Tensor { col_weights, .. } => {
                        pack_ext_weights::<Goldilocks, Challenge>(col_weights)
                    }
                };
                let mut num_reduced = [0usize; 33];
                let mut opening_idx_by_height = [0usize; 33];
                let reduction_offsets: Vec<Vec<Vec<Challenge>>> =
                    commitment_data_with_opening_points
                        .iter()
                        .zip(dimensions.iter())
                        .map(|((_, points), round_dims)| {
                            points
                                .iter()
                                .zip(round_dims.iter())
                                .map(|(pts, dims)| {
                                    let lh = log2_strict_usize(dims.height);
                                    pts.iter()
                                        .map(|_| {
                                            let off = match &schedule {
                                                FriBatchingSchedule::Horner { alpha } => alpha
                                                    .exp_u64(
                                                        u64::try_from(num_reduced[lh])
                                                            .expect("reduced columns exceed u64"),
                                                    ),
                                                FriBatchingSchedule::Tensor {
                                                    open_weights,
                                                    ..
                                                } => open_weights[opening_idx_by_height[lh]],
                                            };
                                            num_reduced[lh] += dims.width;
                                            opening_idx_by_height[lh] += 1;
                                            off
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        })
                        .collect_vec();

                let (cpu_reduced, mut gpu_reduced) = std::thread::scope(|scope| {
                    let cpu_task = scope.spawn(|| {
                        let mut reduced: [Option<Vec<Challenge>>; 33] =
                            core::array::from_fn(|_| None);
                        for ((((mats, &points), round_dims), openings_round), offsets_round) in
                            cpu_round_matrices
                                .iter()
                                .zip(opening_points.iter())
                                .zip(dimensions.iter())
                                .zip(all_opened_values.iter())
                                .zip(reduction_offsets.iter())
                        {
                            for ((((mat, pts), dims), openings), offsets) in mats
                                .iter()
                                .copied()
                                .zip(points)
                                .zip(round_dims)
                                .zip(openings_round)
                                .zip(offsets_round)
                            {
                                let Some(mat) = mat else {
                                    continue;
                                };
                                if pts.is_empty() {
                                    continue;
                                }
                                let lh = log2_strict_usize(dims.height);
                                let target = reduced[lh]
                                    .get_or_insert_with(|| vec![Challenge::ZERO; dims.height]);
                                let compressed = mat
                                    .rowwise_packed_dot_product::<Challenge>(&packed_col_weights)
                                    .collect::<Vec<_>>();
                                for ((&point, vals), &alpha_offset) in
                                    pts.iter().zip(openings).zip(offsets)
                                {
                                    let reduced_y: Challenge = dot_product(
                                        col_weights.iter().copied(),
                                        vals.iter().copied(),
                                    );
                                    compressed
                                        .par_iter()
                                        .zip(target.par_iter_mut())
                                        .zip(cpu_inv_denoms.get(&point).unwrap().par_iter())
                                        .for_each(|((&row, out), &inv_d)| {
                                            *out += alpha_offset * (reduced_y - row) * inv_d;
                                        });
                                }
                            }
                        }
                        reduced
                    });
                    let mut reduced: [Option<CudaReducedOpening>; 33] =
                        core::array::from_fn(|_| None);
                    let mut reduction_tasks = CudaReductionTasks::new(ext_degree);
                    for (
                        ((((data, points), round_dims), openings_round), offsets_round),
                        spilled_mats,
                    ) in commitment_data_with_opening_points
                        .iter()
                        .zip(dimensions.iter())
                        .zip(all_opened_values.iter())
                        .zip(reduction_offsets.iter())
                        .zip(spilled_round_matrices.iter())
                    {
                        for (mat_idx, ((((pts, dims), openings), offsets), spilled_mat)) in points
                            .iter()
                            .zip(round_dims)
                            .zip(openings_round)
                            .zip(offsets_round)
                            .zip(spilled_mats.iter())
                            .enumerate()
                        {
                            if pts.is_empty() {
                                continue;
                            }
                            if let Some(spilled) = spilled_mat {
                                let lh = log2_strict_usize(dims.height);
                                let target = reduced[lh].get_or_insert_with(|| {
                                    CudaReducedOpening::new_with_degree(
                                        device_id,
                                        dims.height,
                                        ext_degree,
                                    )
                                });
                                let mut mat_inv_offsets = Vec::with_capacity(pts.len());
                                let mut mat_ys_flat = Vec::with_capacity(pts.len() * ext_degree);
                                let mut mat_offs_flat = Vec::with_capacity(pts.len() * ext_degree);
                                for ((&point, vals), &offset) in
                                    pts.iter().zip(openings).zip(offsets)
                                {
                                    let reduced_y: Challenge = dot_product(
                                        col_weights.iter().copied(),
                                        vals.iter().copied(),
                                    );
                                    let (y_buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(
                                        reduced_y, ext_degree,
                                    );
                                    let (off_buf, _) = ext_to_goldilocks::<Goldilocks, Challenge>(
                                        offset, ext_degree,
                                    );
                                    mat_inv_offsets.push(*inv_offsets.get(&point).unwrap());
                                    mat_ys_flat.extend_from_slice(&y_buf[..d]);
                                    mat_offs_flat.extend_from_slice(&off_buf[..d]);
                                }
                                workspace.reduce_spilled(
                                    target,
                                    spilled,
                                    &mat_inv_offsets,
                                    &mat_ys_flat,
                                    &mat_offs_flat,
                                    &col_weights_flat,
                                    ext_w,
                                );
                                continue;
                            }
                            if !self.mmcs.is_matrix_cuda_resident(data, mat_idx) {
                                continue;
                            }
                            let lh = log2_strict_usize(dims.height);
                            let target = reduced[lh].get_or_insert_with(|| {
                                CudaReducedOpening::new_with_degree(
                                    device_id,
                                    dims.height,
                                    ext_degree,
                                )
                            });
                            self.mmcs.with_resident_matrix(data, mat_idx, |lde| {
                                for ((&point, vals), &offset) in
                                    pts.iter().zip(openings).zip(offsets)
                                {
                                    let reduced_y: Challenge = dot_product(
                                        col_weights.iter().copied(),
                                        vals.iter().copied(),
                                    );
                                    let (y_buf, d) = ext_to_goldilocks::<Goldilocks, Challenge>(
                                        reduced_y, ext_degree,
                                    );
                                    let (off_buf, _) = ext_to_goldilocks::<Goldilocks, Challenge>(
                                        offset, ext_degree,
                                    );
                                    reduction_tasks.push(
                                        target,
                                        lde,
                                        *inv_offsets.get(&point).unwrap(),
                                        &y_buf[..d],
                                        &off_buf[..d],
                                    );
                                }
                            });
                        }
                    }
                    if !reduction_tasks.is_empty() {
                        workspace.reduce(&reduction_tasks, &col_weights_flat, ext_w);
                    }
                    (cpu_task.join().unwrap(), reduced)
                });
                drop(workspace);
                for (lh, cpu_values) in cpu_reduced.into_iter().enumerate() {
                    if let Some(cpu_values) = cpu_values {
                        let count = cpu_values.len();
                        let mut flat = Vec::with_capacity(count * ext_degree);
                        for value in cpu_values {
                            let (buf, d) =
                                ext_to_goldilocks::<Goldilocks, Challenge>(value, ext_degree);
                            flat.extend_from_slice(&buf[..d]);
                        }
                        gpu_reduced[lh]
                            .get_or_insert_with(|| {
                                CudaReducedOpening::new_with_degree(device_id, count, ext_degree)
                            })
                            .add_host_flat(&flat);
                    }
                }
                let fri_input = gpu_reduced.into_iter().rev().flatten().collect_vec();
                let fri_proof = tracing::info_span!("stark/fri_prove").in_scope(|| {
                    prove_fri_cuda_resident_hiding(
                        &self.fri,
                        fri_input,
                        challenger,
                        log_global_max_height,
                        &commitment_data_with_opening_points,
                        &self.mmcs,
                        ext_w,
                        ext_degree,
                    )
                });
                return (all_opened_values, fri_proof);
            }
        }

        // Streaming CPU fallback (small matrices `height <= 1024` or fully
        // reserved VRAM): never calls `get_matrices` on disk-spilled entries.
        let log_global_max_height = log2_strict_usize(global_max_height);
        let coset = {
            let coset =
                TwoAdicMultiplicativeCoset::new(Goldilocks::GENERATOR, log_global_max_height)
                    .unwrap();
            let mut coset_points = coset.iter().collect();
            reverse_slice_index_bits(&mut coset_points);
            coset_points
        };
        let inv_denoms =
            compute_inverse_denominators_for_dims(&dimensions, &opening_points, &coset);
        let adjusted_weights: LinearMap<Challenge, Vec<Challenge>> = inv_denoms
            .iter()
            .map(|(point, denoms)| (*point, compute_adjusted_weights(*point, denoms)))
            .collect();

        let all_opened_values = commitment_data_with_opening_points
            .iter()
            .zip(dimensions.iter())
            .map(|((data, points), round_dims)| {
                let spilled_mats = self.mmcs.spilled_matrices(data);
                let mut host_mats_cache: Option<Vec<&RowMajorMatrix<Goldilocks>>> = None;
                points
                    .iter()
                    .zip(round_dims.iter())
                    .zip(spilled_mats.iter())
                    .enumerate()
                    .map(|(mat_idx, ((points_for_mat, dims), spilled_mat))| {
                        if points_for_mat.is_empty() {
                            return Vec::new();
                        }
                        let h = dims.height >> self.fri.log_blowup;
                        if let Some(spilled) = spilled_mat {
                            let evals_per_point = interpolate_spilled_coset_generic::<
                                Goldilocks,
                                Challenge,
                            >(
                                spilled, h, points_for_mat, &adjusted_weights
                            );
                            for ys in &evals_per_point {
                                challenger.observe_algebra_slice(ys);
                            }
                            return evals_per_point;
                        }
                        let mats =
                            host_mats_cache.get_or_insert_with(|| self.mmcs.get_matrices(data));
                        let mat = mats[mat_idx].as_view();
                        let (low_coset, _) = mat.split_rows(h);
                        points_for_mat
                            .iter()
                            .map(|&point| {
                                let _guard =
                                    debug_span!("evaluate matrix", dims = %mat.dimensions())
                                        .entered();
                                let adjusted = &adjusted_weights.get(&point).unwrap()[..h];
                                let ys = low_coset.interpolate_coset_with_precomputation(
                                    Goldilocks::GENERATOR,
                                    point,
                                    adjusted,
                                );
                                challenger.observe_algebra_slice(&ys);
                                ys
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            })
            .collect_vec();

        let schedule = FriBatchingSchedule::<Challenge>::sample(
            self.batching,
            opened_max_width,
            max_openings_per_height,
            challenger,
        );
        let packed_col_weights: Vec<Challenge::ExtensionPacking> = match &schedule {
            FriBatchingSchedule::Horner { alpha } => {
                Challenge::ExtensionPacking::packed_ext_powers_capped(*alpha, opened_max_width)
                    .collect_vec()
            }
            FriBatchingSchedule::Tensor { col_weights, .. } => {
                pack_ext_weights::<Goldilocks, Challenge>(col_weights)
            }
        };
        let col_weights: Vec<Challenge> = match &schedule {
            FriBatchingSchedule::Horner { alpha } => {
                alpha.powers().take(opened_max_width).collect()
            }
            FriBatchingSchedule::Tensor { col_weights, .. } => col_weights.clone(),
        };

        let mut num_reduced = [0usize; 33];
        let mut opening_idx_by_height = [0usize; 33];
        let mut reduced_openings: [Option<Vec<Challenge>>; 33] = core::array::from_fn(|_| None);

        for (((data, points), round_dims), openings_for_round) in
            commitment_data_with_opening_points
                .iter()
                .zip(dimensions.iter())
                .zip(all_opened_values.iter())
        {
            let spilled_mats = self.mmcs.spilled_matrices(data);
            let mut host_mats_cache: Option<Vec<&RowMajorMatrix<Goldilocks>>> = None;
            for (mat_idx, (((points_for_mat, dims), openings_for_mat), spilled_mat)) in points
                .iter()
                .zip(round_dims.iter())
                .zip(openings_for_round.iter())
                .zip(spilled_mats.iter())
                .enumerate()
            {
                if points_for_mat.is_empty() {
                    continue;
                }
                let log_height = log2_strict_usize(dims.height);
                let reduced_opening_for_log_height = reduced_openings[log_height]
                    .get_or_insert_with(|| vec![Challenge::ZERO; dims.height]);
                let mut point_params = Vec::with_capacity(points_for_mat.len());
                for (&point, openings) in points_for_mat.iter().zip(openings_for_mat) {
                    let alpha_pow_offset = match &schedule {
                        FriBatchingSchedule::Horner { alpha } => alpha.exp_u64(
                            u64::try_from(num_reduced[log_height])
                                .expect("reduced column count exceeds u64"),
                        ),
                        FriBatchingSchedule::Tensor { open_weights, .. } => {
                            open_weights[opening_idx_by_height[log_height]]
                        }
                    };
                    let reduced_y: Challenge =
                        dot_product(col_weights.iter().copied(), openings.iter().copied());
                    num_reduced[log_height] += dims.width;
                    opening_idx_by_height[log_height] += 1;
                    point_params.push((
                        alpha_pow_offset,
                        reduced_y,
                        inv_denoms.get(&point).unwrap().as_slice(),
                    ));
                }
                if let Some(spilled) = spilled_mat {
                    let row_bytes = spilled.row_bytes().max(size_of::<u64>());
                    let chunk_rows = (STREAM_BLOCK_BYTES / row_bytes)
                        .clamp(1, 1 << 14)
                        .min(dims.height);
                    for row_start in (0..dims.height).step_by(chunk_rows) {
                        let n_rows = (dims.height - row_start).min(chunk_rows);
                        let row_end = row_start + n_rows;
                        let chunk = spilled.read_rows(row_start, n_rows);
                        let mat_compressed: Vec<Challenge> = chunk
                            .as_view()
                            .rowwise_packed_dot_product::<Challenge>(&packed_col_weights)
                            .collect();
                        for &(alpha_pow_offset, reduced_y, inv_denom) in &point_params {
                            mat_compressed
                                .par_iter()
                                .zip(
                                    reduced_opening_for_log_height[row_start..row_end]
                                        .par_iter_mut(),
                                )
                                .zip(inv_denom[row_start..row_end].par_iter())
                                .for_each(|((&reduced_row, ro), &inv_denom)| {
                                    *ro += alpha_pow_offset * (reduced_y - reduced_row) * inv_denom;
                                });
                        }
                    }
                } else {
                    let mats = host_mats_cache.get_or_insert_with(|| self.mmcs.get_matrices(data));
                    let mat = mats[mat_idx].as_view();
                    let mat_compressed = mat
                        .rowwise_packed_dot_product::<Challenge>(&packed_col_weights)
                        .collect::<Vec<_>>();
                    for &(alpha_pow_offset, reduced_y, inv_denom) in &point_params {
                        mat_compressed
                            .par_iter()
                            .zip(reduced_opening_for_log_height.par_iter_mut())
                            .zip(inv_denom.par_iter())
                            .for_each(|((&reduced_row, ro), &inv_denom)| {
                                *ro += alpha_pow_offset * (reduced_y - reduced_row) * inv_denom;
                            });
                    }
                }
            }
        }

        let fri_input = reduced_openings.into_iter().rev().flatten().collect_vec();
        let folding: TwoAdicFriFoldingForMmcs<Goldilocks, HidingCudaMmcs> =
            TwoAdicFriFolding(PhantomData);
        let fri_proof = prover::prove_fri(
            &folding,
            &self.fri,
            fri_input,
            challenger,
            log_global_max_height,
            &commitment_data_with_opening_points,
            &self.mmcs,
        );

        (all_opened_values, fri_proof)
    }

    fn verify(
        &self,
        commitments_with_opening_points: Vec<
            CommitmentWithOpeningPoints<Challenge, Self::Commitment, Self::Domain>,
        >,
        proof: &Self::Proof,
        challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        // Every committed polynomial in `v6-zk` has degree `< 2 * domain.size()`
        // and LDE height `2 * domain.size() * 2^log_blowup`. Double each domain
        // before cap validation and FRI verification.
        let mut doubled_commitments = Vec::with_capacity(commitments_with_opening_points.len());
        for (comm, mats) in commitments_with_opening_points {
            let mut doubled_mats = Vec::with_capacity(mats.len());
            for (domain, pts) in mats {
                let ext_log_size = domain.log_size() + 1;
                let ext_domain = TwoAdicMultiplicativeCoset::new(domain.shift(), ext_log_size)
                    .ok_or(FriError::GlobalMaxHeightTooLarge {
                        log_global_max_height: ext_log_size + self.fri.log_blowup,
                        two_adicity: Goldilocks::TWO_ADICITY,
                    })?;
                doubled_mats.push((ext_domain, pts));
            }
            doubled_commitments.push((comm, doubled_mats));
        }

        validate_fri_commitment_caps(&self.fri, proof, &doubled_commitments, &self.mmcs)?;
        for (_, round) in &doubled_commitments {
            for (_, mat) in round {
                for (_, point) in mat {
                    challenger.observe_algebra_slice(point);
                }
            }
        }

        let folding: TwoAdicFriFoldingForMmcs<Goldilocks, HidingCudaMmcs> =
            TwoAdicFriFolding(PhantomData);
        verify_fri_with_batching(
            &folding,
            &self.fri,
            proof,
            challenger,
            &doubled_commitments,
            &self.mmcs,
            self.batching,
        )?;

        Ok(())
    }

    fn build_periodic_lde_table(
        &self,
        periodic_cols: &[Vec<Goldilocks>],
        trace_domain: Self::Domain,
        quotient_domain: Self::Domain,
    ) -> PeriodicLdeTable<Goldilocks> {
        build_periodic_lde_table_two_adic::<Goldilocks, Dft>(
            &self.dft,
            periodic_cols,
            &trace_domain,
            &quotient_domain,
        )
    }
}

#[cfg(test)]
mod tests {
    use p3_commit::{ExtensionMmcs, Mmcs, Pcs};
    use p3_field::coset::TwoAdicMultiplicativeCoset;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
    use p3_fri::FriParameters;
    use p3_goldilocks::Goldilocks;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_util::log2_strict_usize;

    use super::HidingCudaTwoAdicFriPcs;
    use crate::config::ProofConfig;
    use crate::cuda::hiding_mmcs::HidingCudaMmcs;
    use crate::cuda::{CudaDft, DeviceMemoryReservation, configured_device};
    use crate::p3_adapter::fri_batching::FriBatching;
    use crate::types::{
        CommitmentParameters, ExtVal3, FriParameters as ConfigFriParameters,
        GoldilocksBlake3V6ZkConfig,
    };

    #[test]
    #[ignore = "requires exclusive access to a CUDA device: hides its free memory"]
    fn hiding_pcs_and_mmcs_honor_device_memory_reservation() {
        let device = configured_device();
        let mmcs = HidingCudaMmcs::new_v6_zk(0, device);
        let ext_mmcs: ExtensionMmcs<Goldilocks, ExtVal3, HidingCudaMmcs> =
            ExtensionMmcs::new(mmcs.clone());
        let fri = FriParameters {
            log_blowup: 2,
            log_final_poly_len: 1,
            max_log_arity: 2,
            num_queries: 8,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
            mmcs: ext_mmcs,
        };
        let pcs = HidingCudaTwoAdicFriPcs::new(CudaDft::new(device), mmcs.clone(), fri)
            .with_batching(FriBatching::Tensor);
        let config = GoldilocksBlake3V6ZkConfig::with_device(
            CommitmentParameters {
                log_blowup: 2,
                cap_height: 0,
            },
            ConfigFriParameters {
                log_final_poly_len: 1,
                max_log_arity: 2,
                num_queries: 8,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 0,
            },
            FriBatching::Tensor,
            Some(device),
        );

        // Height 512 -> LDE height 512 * 2 * 4 = 4096 (> 1024 GPU FRI threshold).
        let height = 512usize;
        let width = 8usize;
        let domain =
            TwoAdicMultiplicativeCoset::new(Goldilocks::ONE, log2_strict_usize(height)).unwrap();
        let matrix = RowMajorMatrix::new(
            (0..height * width)
                .map(|i| Goldilocks::from_u64((i as u64).wrapping_mul(0x9e37_79b9) ^ 0x5a5a))
                .collect(),
            width,
        );

        // 1. Unreserved: commit_preprocessed and commit stay CUDA-resident.
        let (gpu_prep_commit, gpu_prep_data) = pcs.commit_preprocessed([(domain, matrix.clone())]);
        assert!(
            mmcs.is_cuda_resident(&gpu_prep_data),
            "unreserved v6-zk preprocessed commit should be CUDA-resident"
        );
        type ZkChallenger = <GoldilocksBlake3V6ZkConfig as ProofConfig>::Challenger;
        let (gpu_commit, gpu_data) = <HidingCudaTwoAdicFriPcs<_, _, _, _> as Pcs<
            ExtVal3,
            ZkChallenger,
        >>::commit(&pcs, [(domain, matrix.clone())]);
        assert!(
            mmcs.is_cuda_resident(&gpu_data),
            "unreserved v6-zk commit should be CUDA-resident"
        );

        // 2. Under a reservation larger than VRAM, admission must spill to CPU
        //    and still produce identical commitments and verifying openings.
        let reservation = DeviceMemoryReservation::new(device, 1usize << 40);

        let (cpu_prep_commit, cpu_prep_data) = pcs.commit_preprocessed([(domain, matrix)]);
        assert!(
            !mmcs.is_cuda_resident(&cpu_prep_data),
            "reserved v6-zk preprocessed commit must fall back to CPU"
        );
        assert_eq!(
            cpu_prep_commit, gpu_prep_commit,
            "CPU fallback and GPU v6-zk preprocessed commitments must match"
        );

        // HidingCudaMmcs::commit_cuda_storage_with_seed & Mmcs::commit (> 1<<18 cells).
        let big_lde = RowMajorMatrix::new(
            (0..(1 << 16) * 5)
                .map(|i| Goldilocks::from_usize(i + 1))
                .collect(),
            5,
        );
        let salt_seed = [0x33u8; 32];
        let (reserved_storage_commit, reserved_storage_data) =
            mmcs.commit_cuda_storage_with_seed(vec![big_lde.clone()], salt_seed);
        assert!(
            !mmcs.is_cuda_resident(&reserved_storage_data),
            "reserved commit_cuda_storage_with_seed must fall back to CPU"
        );
        let (_, reserved_mmcs_data) = mmcs.commit(vec![big_lde.clone()]);
        assert!(
            !mmcs.is_cuda_resident(&reserved_mmcs_data),
            "reserved Mmcs::commit must fall back to CPU"
        );

        // Opening already-resident GPU data while VRAM is reserved falls back
        // cleanly to the CPU opening path and verifies.
        let z = ExtVal3::from_basis_coefficients_slice(&[
            Goldilocks::from_u64(11),
            Goldilocks::from_u64(19),
            Goldilocks::from_u64(29),
        ])
        .unwrap();
        let mut prover_challenger = config.initialise_challenger();
        let (opened, proof) = <HidingCudaTwoAdicFriPcs<_, _, _, _> as Pcs<ExtVal3, _>>::open(
            &pcs,
            vec![(&gpu_data, vec![vec![z]])],
            &mut prover_challenger,
        );
        let mut verifier_challenger = config.initialise_challenger();
        <HidingCudaTwoAdicFriPcs<_, _, _, _> as Pcs<ExtVal3, _>>::verify(
            &pcs,
            vec![(
                gpu_commit,
                vec![(domain, vec![(z, opened[0][0][0].clone())])],
            )],
            &proof,
            &mut verifier_challenger,
        )
        .expect("v6-zk proof opened under DeviceMemoryReservation must verify");

        drop(reservation);

        // After dropping the reservation, storage commit returns to GPU and matches.
        let (gpu_storage_commit, gpu_storage_data) =
            mmcs.commit_cuda_storage_with_seed(vec![big_lde], salt_seed);
        assert!(
            mmcs.is_cuda_resident(&gpu_storage_data),
            "unreserved commit_cuda_storage_with_seed should return to GPU"
        );
        assert_eq!(reserved_storage_commit, gpu_storage_commit);
    }
}
