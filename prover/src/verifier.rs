//! Multi-circuit STARK verifier (constraint-IR version).
//!
//! The out-of-domain check recomputes each circuit's composition polynomial by
//! running the compiled circuit's dense constraint sweep in the challenge field
//! at ζ, then folding the constraint values with the constraint challenge.
//! Opened stage-2 columns are fed as base columns directly (no `from_ext_basis`
//! reassembly): the coordinate-expanded constraints are base-field polynomial
//! identities, so evaluating them at the ζ-openings is correct.
//!
//! # Verification steps
//!
//! 1. **Shape check** ([`System::verify_shape`]): Validate the activation bitmap
//!    (it must cover the canonical circuit set and activate at least one circuit)
//!    and that the proof's array dimensions (opened values, accumulators, quotient
//!    chunks) match the ACTIVE circuit count and the canonical column widths.
//!
//! 2. **Accumulator balance**: Assert that the last intermediate accumulator is zero,
//!    ensuring that all lookup pushes and pulls cancel out across circuits.
//!
//! 3. **Fiat-Shamir replay**: Reconstruct the challenger state identically to the
//!    prover: starting from the parameter-seeded challenger, observe the system
//!    shape, the activation bitmap, commitments, trace heights, length-prefixed
//!    claims, and intermediate accumulators, sampling the same challenges (lookup,
//!    fingerprint, constraint alpha, OOD zeta) at the same points in the
//!    transcript.
//!
//! 4. **PCS verification**: Verify opening proofs against the committed
//!    polynomials at the sampled points.
//!
//! 5. **OOD evaluation**: For each ACTIVE circuit, recompute the composition
//!    polynomial at zeta from the opened values and verify that
//!    `composition(zeta) * inv_vanishing(zeta) == quotient(zeta)`.
//!
//! See [`VerificationError`] for the possible failure modes.
//!
//! # Security considerations
//!
//! This is a Rust reference verifier, not a formally verified implementation.
//! The separate Lean package currently proves supporting PCS facts, not this
//! STARK protocol. The discussion below explains the checks and assumptions;
//! it is not a complete concrete soundness or knowledge-extraction proof.
//!
//! ## PCS and FRI
//!
//! The generic verifier relies on its configured PCS to authenticate polynomial
//! evaluations and enforce degree bounds. The reference configuration uses a
//! non-hiding FRI PCS with BLAKE3 commitments and a degree-2 Goldilocks challenge
//! field (approximately 2^128 elements).
//!
//! With rate `ρ = 2^(-log_blowup)` and `n = num_queries`, `ρ^n` is a commonly
//! used conjectural query-phase estimate. For `log_blowup = 1` and `n = 100`,
//! that expression is 2^(-100). It is not an end-to-end security bound:
//! proximity/list-decoding assumptions, field size, polynomial degrees,
//! batching, commitment binding and Fiat-Shamir attacks also matter. This
//! repository does not establish a proven bit-security level for these settings.
//!
//! Commit grinding precedes each FRI folding
//! challenge and query grinding precedes the query indices. There is no
//! separate PCS batch-grinding parameter. Grinding adds prover work; its bits
//! should not simply be added to a claimed end-to-end security level.
//!
//! ## Algebraic checks
//!
//! Constraint folding combines `k` constraint values using powers of α. For
//! fixed values that are not all zero and an independent uniform α, the
//! resulting nonzero polynomial in α has degree at most `k - 1`.
//!
//! The out-of-domain check tests `C(ζ) / Z_H(ζ) = Q(ζ)`, where `C` is the
//! composition polynomial, `Z_H` the trace vanishing polynomial and `Q` the
//! committed quotient. After clearing the denominator, the relevant polynomial
//! is `C - Z_H * Q`; its degree, not just the quotient degree, governs the
//! Schwartz-Zippel term. Evaluation points with invalid denominators are rejected.
//!
//! Lookup messages are compressed as `β + fingerprint(γ, args)`. Away from
//! zero denominators, the chained constraints enforce the sum of signed
//! multiplicities divided by these messages. For an imbalance represented by
//! a nonzero rational function, clearing denominators gives a polynomial test.
//! Its error depends on the number and width of messages, as well as the field
//! size. Thus a 128-bit challenge field alone does not imply 128-bit security.
//! The application must define an unambiguous lookup vocabulary and constrain
//! multiplicities and public claims to express its intended statement.
//!
//! ## Transcript and statement binding
//!
//! Security assumes a binding PCS and a suitable Fiat-Shamir challenger. Traces
//! and length-prefixed claims are observed before lookup challenges; lookup
//! commitments precede constraint folding, and quotient commitments precede ζ.
//! The parameter seed and system-shape observations separate protocol settings.
//! Shape counts do not identify every constraint: the verifier must obtain the
//! intended `System` and public claims from trusted or independently checked data.
//! Batch users must also enforce the message policy described in [`crate::batch`].
//!
//! ## Sparse activation
//!
//! A proof covers only circuits marked active in [`Proof::active`]. Inactive
//! circuits contribute no trace constraints or lookup messages. The activation
//! bitmap is observed before any commitment or challenge, and active circuit
//! definitions come from the verifier's canonical system.
//!
//! If omitting a required circuit leaves unmatched lookup messages, the lookup
//! check detects that imbalance subject to its soundness error. A disconnected
//! circuit cannot force its own presence through padding constraints: the
//! application must require its activation or bind it through public claims.
//! Acceptance guarantees no constraints on inactive circuits.
//!
//! ## Witness privacy
//!
//! The reference FRI configuration is not zero-knowledge. Traces are committed
//! without blinding, and query responses reveal low-degree-extension values of
//! the witness. Applications requiring witness privacy need a hiding protocol.

use crate::config::{PcsError, ProofConfig, Val};
use crate::ensure_eq;
use crate::eval::VarValues;
use crate::lookup::try_claims_accumulator;
use crate::prover::{Proof, observe_claims, sample_lookup_challenges};
use crate::system::System;
use crate::traits::{Algebra, EvaluationDomain, ExtensionOf, Field, Pcs, Transcript, TwoAdicField};

use p3_util::log2_strict_usize;

/// Errors that can occur during proof verification.
#[derive(Debug)]
pub enum VerificationError<PcsErr> {
    /// A provided claim is invalid.
    ///
    /// Note: this variant is not currently returned by any verification path.
    /// It is reserved for future claim validation checks.
    InvalidClaim,
    /// A transcript challenge makes an evaluation or lookup denominator invalid.
    InvalidChallenge,
    /// The PCS opening proof failed to verify.
    InvalidOpeningArgument(PcsErr),
    /// The proof has an unexpected shape (wrong number of opened values, etc.).
    InvalidProofShape,
    /// The system configuration is invalid (e.g. no circuits).
    InvalidSystem,
    /// The recomputed composition polynomial does not match the quotient.
    OodEvaluationMismatch,
    /// The lookup accumulator did not balance to zero.
    UnbalancedChannel,
    /// A batch's preamble disagrees with its proofs (header count, or a
    /// header's activation bitmap, stage-1 commitment or heights differ from
    /// the shard proof it describes).
    BatchShapeMismatch,
    /// The shards' lookup residuals and the batch's public messages did not
    /// sum to zero.
    UnbalancedBatch,
}

impl<SC: ProofConfig> System<SC> {
    /// Verifies a STARK proof against a single claim.
    pub fn verify(
        &self,
        claim: &[Val<SC>],
        proof: &Proof<SC>,
    ) -> Result<(), VerificationError<PcsError<SC>>>
    where
        Val<SC>: TwoAdicField,
    {
        self.verify_multiple_claims(&[claim], proof)
    }

    /// Verifies a STARK proof against multiple claims.
    pub fn verify_multiple_claims(
        &self,
        claims: &[&[Val<SC>]],
        proof: &Proof<SC>,
    ) -> Result<(), VerificationError<PcsError<SC>>>
    where
        Val<SC>: TwoAdicField,
    {
        // first, verify the proof shape (also validates the activation bitmap)
        let quotient_degrees = self.verify_shape(proof)?;

        // Soundness: lookup argument. The accumulator was computed by the prover
        // under challenges (β, γ) that were sampled after the traces and claims were
        // committed. An imbalance represented by a nonzero rational function
        // can still evaluate to zero at the sampled challenges; its error
        // depends on message counts, widths and the challenge field size.
        ensure_eq!(
            proof.intermediate_accumulators.last(),
            Some(&<SC::Challenge as Algebra<SC::Challenge>>::ZERO),
            VerificationError::UnbalancedChannel
        );

        // Soundness: Fiat-Shamir. All challenges below are derived deterministically
        // from the transcript via the configuration's challenger, whose hash is
        // modeled as a random oracle. The verifier replays exactly the same
        // observations as the prover, so any divergence (e.g. different
        // commitments) produces different challenges, making it infeasible for a
        // cheating prover to predict them.
        let mut challenger = self.config.initialise_challenger();

        // Bind the system shape into the transcript. The protocol parameters
        // are already bound via the challenger seed.
        self.observe_shape(&mut challenger);

        // Bind the activation bitmap — before any commitment or challenge, so
        // every sample depends on which circuits this proof covers.
        for &is_active in &proof.active {
            challenger.observe_field(Val::<SC>::from_bool(is_active));
        }

        // observe preprocessed and stage_1 commitment
        if let Some(commit) = &self.preprocessed_commit {
            challenger.observe_commitment(commit.clone());
        }
        challenger.observe_commitment(proof.commitments.stage_1_trace.clone());

        // Observe trace heights to bind the proof to specific domain sizes.
        for log_degree in &proof.log_degrees {
            challenger.observe_field(Val::<SC>::from_u8(*log_degree));
        }

        // Soundness: claims must be observed BEFORE lookup challenges are sampled.
        // Otherwise, the prover could choose claims adaptively after seeing the
        // challenges, breaking the lookup argument's binding property. The claims
        // are length-prefixed so that distinct claim structures (e.g. [[a, b]]
        // vs [[a], [b]]) yield distinct transcripts.
        observe_claims::<SC>(&mut challenger, claims);

        // Soundness: lookup argument. The challenges are random elements of F_ext.
        // The message m_i = lookup_challenge + fingerprint(fingerprint_challenge, args_i)
        // is affine in β and polynomial in γ; fingerprint collision bounds
        // depend on the message width, not just the field size.
        let (lookup_argument_challenge, fingerprint_challenge) =
            sample_lookup_challenges::<SC>(&mut challenger);

        // construct the accumulator from the claims
        let acc = try_claims_accumulator(lookup_argument_challenge, &fingerprint_challenge, claims)
            .ok_or(VerificationError::InvalidChallenge)?;

        self.verify_after_challenges(
            proof,
            &quotient_degrees,
            challenger,
            lookup_argument_challenge,
            fingerprint_challenge,
            acc,
        )
    }

    /// Steps 3 (from the stage-2 commitment on), 4 and 5 of verification,
    /// given a transcript that has just sampled the lookup challenges and the
    /// initial accumulator derived from the proof's public messages. Shared by
    /// the single-proof protocol and the batch protocol, which differ only in
    /// how the transcript reached this point and in what the final accumulator
    /// must equal (zero, or a batch residual — see [`crate::batch`]).
    ///
    /// `quotient_degrees` is the output of [`Self::verify_shape`] for `proof`.
    pub fn verify_after_challenges(
        &self,
        proof: &Proof<SC>,
        quotient_degrees: &[usize],
        mut challenger: SC::Challenger,
        lookup_argument_challenge: SC::Challenge,
        fingerprint_challenge: SC::Challenge,
        mut acc: SC::Challenge,
    ) -> Result<(), VerificationError<PcsError<SC>>>
    where
        Val<SC>: TwoAdicField,
    {
        let Proof {
            active,
            commitments,
            intermediate_accumulators,
            log_degrees,
            opening_proof,
            quotient_opened_values,
            preprocessed_opened_values,
            stage_1_opened_values,
            stage_2_opened_values,
        } = proof;
        let pcs = self.config.pcs();
        // Canonical index of each active circuit; every per-circuit sequence
        // in the proof is indexed by position in this list.
        let active_indices: Vec<usize> = active
            .iter()
            .enumerate()
            .filter_map(|(i, &a)| a.then_some(i))
            .collect();

        // observe stage_2 commitment
        challenger.observe_commitment(commitments.stage_2_trace.clone());

        // Observe the intermediate accumulators. They enter the constraints as
        // public values, so later challenges (α, ζ) must depend on them
        // directly rather than only through the quotient commitment.
        for acc in intermediate_accumulators {
            challenger.observe_challenge(*acc);
        }

        // Soundness: constraint folding. All k constraints are combined via powers
        // of α. The folded sum has degree k-1 in α, so by Schwartz-Zippel a violated
        // constraint survives folding with probability ≥ 1 - (k-1)/|F_ext|.
        let constraint_challenge: SC::Challenge = challenger.sample_challenge();

        // observe quotient commitment
        challenger.observe_commitment(commitments.quotient_chunks.clone());

        // Sample ζ after all commitments are fixed. The OOD identity checks
        // C - Z_H * Q at this point; see the module's algebraic-check discussion.
        let zeta: SC::Challenge = challenger.sample_challenge();
        // Zero merges rotated opening points, while roots of a trace domain
        // make the selector and quotient denominators undefined.
        crate::ensure!(!zeta.is_zero(), VerificationError::InvalidChallenge);

        // Reconstruct the PCS opening rounds (identical to the prover).
        let mut stage_1_trace_evaluations = vec![];
        let mut stage_2_trace_evaluations = vec![];
        let mut quotient_chunks_evaluations = vec![];
        for pos in 0..active_indices.len() {
            let log_degree = log_degrees[pos];
            let trace_domain = pcs.natural_domain_for_degree(1 << log_degree);
            let unshifted = zeta * SC::Challenge::from(trace_domain.first_point().inverse());
            crate::ensure!(
                unshifted.exp_power_of_2(usize::from(log_degree))
                    != <SC::Challenge as Algebra<SC::Challenge>>::ONE,
                VerificationError::InvalidChallenge
            );
            let zeta_next = trace_domain.next_point(zeta);
            stage_1_trace_evaluations.push((
                trace_domain,
                [zeta, zeta_next]
                    .into_iter()
                    .zip(stage_1_opened_values[pos].iter().cloned())
                    .collect(),
            ));
            stage_2_trace_evaluations.push((
                trace_domain,
                vec![
                    (zeta, stage_2_opened_values[pos][0].clone()),
                    (zeta_next, stage_2_opened_values[pos][1].clone()),
                ],
            ));
            // All of a circuit's quotient coefficient slices live in one
            // matrix on the trace domain, opened once at ζ.
            quotient_chunks_evaluations.push((
                trace_domain,
                vec![(zeta, quotient_opened_values[pos][0].clone())],
            ));
        }
        // The preprocessed commitment covers ALL preprocessed matrices, in
        // canonical slot order. Inactive openings follow the PCS boundary policy.
        let mut preprocessed_trace_evaluations = vec![];
        {
            let mut active_pos: Vec<Option<usize>> = vec![None; active.len()];
            for (pos, &ci) in active_indices.iter().enumerate() {
                active_pos[ci] = Some(pos);
            }
            for (ci, &slot) in self.preprocessed_indices.iter().enumerate() {
                if let Some(slot) = slot {
                    match active_pos[ci] {
                        Some(pos) => {
                            let trace_domain = pcs.natural_domain_for_degree(1 << log_degrees[pos]);
                            let zeta_next = trace_domain.next_point(zeta);
                            let preprocessed_opened_values =
                                preprocessed_opened_values.as_ref().unwrap();
                            preprocessed_trace_evaluations.push((
                                trace_domain,
                                [zeta, zeta_next]
                                    .into_iter()
                                    .zip(preprocessed_opened_values[slot].iter().cloned())
                                    .collect(),
                            ));
                        }
                        None => {
                            // Opened at ζ alone so the PCS can pin the matrix
                            // width (see the prover's round construction);
                            // the value itself feeds no constraint.
                            let domain = pcs
                                .natural_domain_for_degree(self.circuits[ci].preprocessed_height);
                            let preprocessed_opened_values =
                                preprocessed_opened_values.as_ref().unwrap();
                            preprocessed_trace_evaluations.push((
                                domain,
                                if self.config.omit_inactive_preprocessed_openings() {
                                    vec![]
                                } else {
                                    vec![(zeta, preprocessed_opened_values[slot][0].clone())]
                                },
                            ));
                        }
                    }
                }
            }
        }
        let mut coms_to_verify = vec![
            (commitments.stage_1_trace.clone(), stage_1_trace_evaluations),
            (commitments.stage_2_trace.clone(), stage_2_trace_evaluations),
            (
                commitments.quotient_chunks.clone(),
                quotient_chunks_evaluations,
            ),
        ];
        if let Some(preprocessed_commitment) = &self.preprocessed_commit {
            coms_to_verify.push((
                preprocessed_commitment.clone(),
                preprocessed_trace_evaluations,
            ));
        }
        // The configured PCS authenticates the evaluations and checks the
        // claimed degree bounds. FRI query estimates alone do not bound the
        // complete STARK protocol; see the module's security considerations.
        pcs.verify(coms_to_verify, opening_proof, &mut challenger)
            .map_err(VerificationError::InvalidOpeningArgument)?;

        // use the opened values to compute the composition polynomial for each circuit
        // and check that the evaluation of the composition polynomial equals the
        // product of the zerofier with the quotient
        let extension_d = <SC::Challenge as ExtensionOf<Val<SC>>>::D;
        let empty: [SC::Challenge; 0] = [];
        for (pos, &ci) in active_indices.iter().enumerate() {
            let circuit = &self.circuits[ci];
            let degree = 1 << log_degrees[pos];
            let quotient_degree = quotient_degrees[pos];
            let next_acc = intermediate_accumulators[pos];
            let trace_domain = pcs.natural_domain_for_degree(degree);
            let sels = trace_domain.selectors_at_point(zeta);
            // The logUp boundary injection absorbs the last-row selector's
            // normalization constant into Δ (mirroring the prover): p3's
            // unnormalized L_last has value n·g at the last row.
            let n_val = Val::<SC>::from_usize(degree);
            let g = Val::<SC>::two_adic_generator(usize::from(log_degrees[pos]));
            let inj_norm = SC::Challenge::from((n_val * g).inverse());

            // The four lookup publics (β, γ, acc, next_acc) as base
            // coordinates embedded into the challenge field.
            let mut publics: Vec<SC::Challenge> = Vec::with_capacity(4 * extension_d);
            for ef in [
                lookup_argument_challenge,
                fingerprint_challenge,
                acc,
                next_acc,
            ] {
                for &coord in ef.as_basis_coefficients_slice() {
                    publics.push(SC::Challenge::from(coord));
                }
            }

            let (preprocessed_cur, preprocessed_next): (&[SC::Challenge], &[SC::Challenge]) =
                if let Some(slot) = self.preprocessed_indices[ci] {
                    let values = preprocessed_opened_values.as_ref().unwrap();
                    (
                        &values[slot][0],
                        values[slot].get(1).map_or(&[][..], Vec::as_slice),
                    )
                } else {
                    (&empty, &empty)
                };
            let view = VarValues {
                preprocessed: [preprocessed_cur, preprocessed_next],
                main: [
                    &stage_1_opened_values[pos][0],
                    stage_1_opened_values[pos]
                        .get(1)
                        .map_or(&[][..], Vec::as_slice),
                ],
                stage2: [
                    &stage_2_opened_values[pos][0],
                    &stage_2_opened_values[pos][1],
                ],
                publics: &publics,
                is_first_row: sels.is_first_row,
                is_last_row: sels.is_last_row,
                is_transition: sels.is_transition,
            };
            // One sweep serves both the user-constraint roots and the
            // evaluated lookup expressions; the logUp constraint values are
            // then computed directly (never compiled) and folded after the
            // user roots, in the canonical protocol order.
            let mut buf = Vec::new();
            circuit.graph.sweep(&view, &mut buf);
            let mut constraint_values = circuit.graph.constraint_values(&buf);
            let delta_scaled: Vec<SC::Challenge> = (0..extension_d)
                .map(|k| (publics[3 * extension_d + k] - publics[2 * extension_d + k]) * inj_norm)
                .collect();
            crate::lookup::logup_constraint_values(
                &circuit.graph.lookups,
                &buf,
                view.stage2[0],
                view.stage2[1],
                &publics,
                &delta_scaled,
                // p3's (unnormalized) last-row selector; the normalization
                // constant is pre-absorbed into `delta_scaled`.
                view.is_last_row,
                crate::system::extension_params::<SC>().w,
                extension_d,
                circuit.lookup_group_size,
                &mut constraint_values,
            );
            debug_assert_eq!(constraint_values.len(), circuit.constraint_count());
            // Fold with α (Horner): Σ_i α^{k-1-i} · value_i, matching the
            // prover's reversed α-power weighting.
            let composition = constraint_values.iter().fold(
                <SC::Challenge as Algebra<SC::Challenge>>::ZERO,
                |acc, &v| acc * constraint_challenge + v,
            );

            // Recombine the quotient from its coefficient slices:
            // `Q(ζ) = Σᵢ ζ^{i·n}·cᵢ(ζ)`, with each slice's value read from
            // the wide quotient matrix opened at ζ.
            let quotient_row = &quotient_opened_values[pos][0];
            debug_assert_eq!(quotient_row.len(), quotient_degree * extension_d);
            let zeta_pow_n = zeta.exp_power_of_2(log2_strict_usize(degree));
            let quotient = quotient_row
                .chunks_exact(extension_d)
                .zip(zeta_pow_n.powers())
                .map(|(chunk, zeta_pow)| zeta_pow * from_ext_basis::<Val<SC>, SC::Challenge>(chunk))
                .fold(<SC::Challenge as Algebra<SC::Challenge>>::ZERO, |a, b| {
                    a + b
                });

            // Check the folded constraint identity at ζ. After clearing the
            // nonzero vanishing denominator this tests C(ζ) - Z_H(ζ) * Q(ζ) = 0;
            // the degree of that polynomial governs the algebraic error term.
            ensure_eq!(
                composition * sels.inv_vanishing,
                quotient,
                VerificationError::OodEvaluationMismatch;
                circuit = ci,
                active_position = pos,
                degree,
                quotient_degree,
                "out-of-domain constraint evaluation mismatch"
            );
            // the accumulator must become the next accumulator for the next iteration
            acc = next_acc;
        }
        Ok(())
    }

    /// Validates the structural shape of the proof without checking any cryptographic
    /// properties. Returns the quotient degrees per active circuit on success.
    pub fn verify_shape(
        &self,
        proof: &Proof<SC>,
    ) -> Result<Vec<usize>, VerificationError<PcsError<SC>>> {
        let Proof {
            active,
            intermediate_accumulators,
            log_degrees,
            quotient_opened_values,
            preprocessed_opened_values,
            stage_1_opened_values,
            stage_2_opened_values,
            ..
        } = proof;
        let num_circuits = self.circuits.len();
        crate::ensure!(
            num_circuits > 0,
            VerificationError::InvalidSystem;
            num_circuits,
            "system has no circuits"
        );
        ensure_eq!(
            active.len(),
            num_circuits,
            VerificationError::InvalidProofShape;
            actual = active.len(),
            expected = num_circuits,
            "unexpected number of activation flags"
        );
        let active_indices: Vec<usize> = active
            .iter()
            .enumerate()
            .filter_map(|(i, &a)| a.then_some(i))
            .collect();
        let num_active = active_indices.len();
        crate::ensure!(
            num_active > 0,
            VerificationError::InvalidProofShape;
            num_active,
            num_circuits,
            "proof has no active circuits"
        );
        ensure_eq!(
            log_degrees.len(),
            num_active,
            VerificationError::InvalidProofShape;
            actual = log_degrees.len(),
            expected = num_active,
            "unexpected number of trace heights"
        );
        let num_preprocessed = self
            .preprocessed_indices
            .iter()
            .map(|i| usize::from(i.is_some()))
            .sum::<usize>();
        ensure_eq!(
            self.preprocessed_commit.is_none(),
            num_preprocessed == 0,
            VerificationError::InvalidSystem;
            commitment_present = self.preprocessed_commit.is_some(),
            num_preprocessed,
            "preprocessed commitment does not match configured circuits"
        );
        // Stage 0 round: the preprocessed commitment is built once over ALL
        // preprocessed traces at system construction, so its round carries one
        // entry per preprocessed matrix. Inactive matrices need one full-width
        // opening unless the PCS authenticates their boundaries independently.
        ensure_eq!(
            preprocessed_opened_values
                .as_ref()
                .map_or(0, |values| values.len()),
            num_preprocessed,
            VerificationError::InvalidProofShape;
            actual = preprocessed_opened_values.as_ref().map_or(0, |values| values.len()),
            expected = num_preprocessed,
            "unexpected number of preprocessed matrices"
        );
        for (ci, (&prep_index, &is_active)) in
            self.preprocessed_indices.iter().zip(active).enumerate()
        {
            if let Some(slot) = prep_index
                && !is_active
            {
                let opened = &preprocessed_opened_values.as_ref().unwrap()[slot];
                let count = usize::from(!self.config.omit_inactive_preprocessed_openings());
                ensure_eq!(
                    opened.len(),
                    count,
                    VerificationError::InvalidProofShape;
                    circuit = ci,
                    preprocessed_slot = slot,
                    actual = opened.len(),
                    expected = count,
                    "unexpected number of inactive preprocessed openings"
                );
                for (opening_position, row) in opened.iter().enumerate() {
                    ensure_eq!(
                        row.len(),
                        self.circuits[ci].preprocessed_width,
                        VerificationError::InvalidProofShape;
                        circuit = ci,
                        preprocessed_slot = slot,
                        opening_position,
                        actual = row.len(),
                        expected = self.circuits[ci].preprocessed_width,
                        "unexpected inactive preprocessed opening width"
                    );
                }
            }
        }
        ensure_eq!(
            stage_1_opened_values.len(),
            num_active,
            VerificationError::InvalidProofShape;
            actual = stage_1_opened_values.len(),
            expected = num_active,
            "unexpected number of main matrices"
        );
        ensure_eq!(
            stage_2_opened_values.len(),
            num_active,
            VerificationError::InvalidProofShape;
            actual = stage_2_opened_values.len(),
            expected = num_active,
            "unexpected number of stage-2 matrices"
        );
        for (pos, &ci) in active_indices.iter().enumerate() {
            let circuit = &self.circuits[ci];
            let preprocessed_i = self.preprocessed_indices[ci];
            // zeta and zeta_next
            let num_openings = 2;
            ensure_eq!(
                stage_1_opened_values[pos].len(),
                1 + usize::from(self.opens_next_row(ci, crate::expr::Source::Main)),
                VerificationError::InvalidProofShape;
                circuit = ci,
                active_position = pos,
                actual = stage_1_opened_values[pos].len(),
                expected = 1 + usize::from(self.opens_next_row(ci, crate::expr::Source::Main)),
                "unexpected number of main openings"
            );
            ensure_eq!(
                stage_2_opened_values[pos].len(),
                num_openings,
                VerificationError::InvalidProofShape;
                circuit = ci,
                active_position = pos,
                actual = stage_2_opened_values[pos].len(),
                expected = num_openings,
                "unexpected number of stage-2 openings"
            );
            if let Some(slot) = preprocessed_i {
                ensure_eq!(
                    preprocessed_opened_values.as_ref().unwrap()[slot].len(),
                    1 + usize::from(self.opens_next_row(ci, crate::expr::Source::Preprocessed)),
                    VerificationError::InvalidProofShape;
                    circuit = ci,
                    active_position = pos,
                    preprocessed_slot = slot,
                    actual = preprocessed_opened_values.as_ref().unwrap()[slot].len(),
                    expected = 1 + usize::from(self.opens_next_row(ci, crate::expr::Source::Preprocessed)),
                    "unexpected number of preprocessed openings"
                );
            }
            if let Some(slot) = preprocessed_i {
                for (opening_position, row) in preprocessed_opened_values.as_ref().unwrap()[slot]
                    .iter()
                    .enumerate()
                {
                    ensure_eq!(
                        row.len(),
                        circuit.preprocessed_width,
                        VerificationError::InvalidProofShape;
                        circuit = ci,
                        active_position = pos,
                        preprocessed_slot = slot,
                        opening_position,
                        actual = row.len(),
                        expected = circuit.preprocessed_width,
                        "unexpected preprocessed opening width"
                    );
                }
            }
            for (opening_position, row) in stage_1_opened_values[pos].iter().enumerate() {
                ensure_eq!(
                    row.len(),
                    circuit.main_width,
                    VerificationError::InvalidProofShape;
                    circuit = ci,
                    active_position = pos,
                    opening_position,
                    actual = row.len(),
                    expected = circuit.main_width,
                    "unexpected main opening width"
                );
            }
            for (opening_position, row) in stage_2_opened_values[pos].iter().enumerate() {
                // Stage-2 is committed as flattened base columns, so the
                // opened width is already the flattened width.
                ensure_eq!(
                    row.len(),
                    circuit.stage_2_width,
                    VerificationError::InvalidProofShape;
                    circuit = ci,
                    active_position = pos,
                    opening_position,
                    actual = row.len(),
                    expected = circuit.stage_2_width,
                    "unexpected stage-2 opening width"
                );
            }
        }
        let mut quotient_degrees = vec![];
        for (pos, (&ci, log_degree)) in active_indices.iter().zip(log_degrees).enumerate() {
            let circuit = &self.circuits[ci];
            // Fixed columns describe rows on the setup-time trace domain.
            // Pin that domain here as well as in witness construction: a
            // prover must not reinterpret fixed tables, selectors or wiring
            // on a different-sized trace. Inactive circuits have no degree.
            if circuit.preprocessed_height != 0 {
                ensure_eq!(
                    1usize.checked_shl(u32::from(*log_degree)),
                    Some(circuit.preprocessed_height),
                    VerificationError::InvalidProofShape;
                    circuit = ci,
                    active_position = pos,
                    log_degree = *log_degree,
                    expected_height = circuit.preprocessed_height,
                    "trace height does not match preprocessed height"
                );
            }
            let quotient_degree = circuit.quotient_degree();
            // The claimed log degree must be small enough that the quotient
            // domain can still be committed and opened by the PCS. This also
            // guards the `1 << log_degree` shifts used during verification
            // against overflow on adversarial proofs.
            crate::ensure!(
                usize::from(*log_degree) <= self.config.max_log_degree()
                    && usize::from(*log_degree) < usize::BITS as usize
                    && usize::from(*log_degree) + log2_strict_usize(quotient_degree)
                        <= self.config.max_log_quotient_domain(),
                VerificationError::InvalidProofShape;
                circuit = ci,
                active_position = pos,
                log_degree = *log_degree,
                quotient_degree,
                max_log_degree = self.config.max_log_degree(),
                max_log_quotient_domain = self.config.max_log_quotient_domain(),
                "trace or quotient domain exceeds supported size"
            );
            quotient_degrees.push(quotient_degree);
        }
        // One wide quotient matrix per active circuit, holding all its
        // coefficient slices, opened at the single point ζ.
        ensure_eq!(
            quotient_opened_values.len(),
            num_active,
            VerificationError::InvalidProofShape;
            actual = quotient_opened_values.len(),
            expected = num_active,
            "unexpected number of quotient matrices"
        );
        let extension_d = <SC::Challenge as ExtensionOf<Val<SC>>>::D;
        for (pos, quotient_degree) in quotient_degrees.iter().enumerate() {
            ensure_eq!(
                quotient_opened_values[pos].len(),
                1,
                VerificationError::InvalidProofShape;
                circuit = active_indices[pos],
                active_position = pos,
                actual = quotient_opened_values[pos].len(),
                expected = 1,
                quotient_degree = *quotient_degree,
                extension_degree = extension_d,
                "unexpected number of quotient openings"
            );
            ensure_eq!(
                quotient_opened_values[pos][0].len(),
                quotient_degree * extension_d,
                VerificationError::InvalidProofShape;
                circuit = active_indices[pos],
                active_position = pos,
                actual = quotient_opened_values[pos][0].len(),
                expected = quotient_degree * extension_d,
                quotient_degree = *quotient_degree,
                extension_degree = extension_d,
                "unexpected quotient opening width"
            );
        }
        ensure_eq!(
            intermediate_accumulators.len(),
            num_active,
            VerificationError::InvalidProofShape;
            actual = intermediate_accumulators.len(),
            expected = num_active,
            "unexpected number of intermediate accumulators"
        );
        Ok(quotient_degrees)
    }
}

#[cfg(test)]
#[path = "verifier/challenge_tests.rs"]
mod challenge_tests;

/// Reassembles an extension element from its base coordinates.
fn from_ext_basis<F: Field, EF: ExtensionOf<F>>(coeffs: &[EF]) -> EF {
    coeffs
        .iter()
        .enumerate()
        .fold(<EF as Algebra<EF>>::ZERO, |acc, (i, c)| {
            let basis = EF::from_basis_coefficients_fn(|j| if j == i { F::ONE } else { F::ZERO });
            acc + *c * basis
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        p3_adapter::LookupAir,
        prover::Proof,
        system::{ProverKey, SystemWitness},
        types::{CommitmentParameters, ExtVal, FriParameters, GoldilocksBlake3Config, Val},
    };
    use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
    use p3_blake3::Blake3;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_symmetric::CryptographicHasher;

    enum CS {
        Pythagorean,
        Complex,
    }
    impl<F> BaseAir<F> for CS {
        fn width(&self) -> usize {
            match self {
                Self::Pythagorean => 3,
                Self::Complex => 6,
            }
        }
    }
    impl<AB> Air<AB> for CS
    where
        AB: AirBuilder,
        AB::Var: Copy,
    {
        fn eval(&self, builder: &mut AB) {
            match self {
                Self::Pythagorean => {
                    let main = builder.main();
                    let local = main.current_slice();
                    let expr1 = local[0] * local[0] + local[1] * local[1];
                    let expr2 = local[2] * local[2];
                    // this extra `local[0]` multiplication is there to increase the maximum constraint degree
                    builder.assert_eq(local[0] * expr1, local[0] * expr2);
                }
                Self::Complex => {
                    let main = builder.main();
                    let local = main.current_slice();
                    // (a + ib)(c + id) = (ac - bd) + i(ad + bc)
                    let expr1 = local[0] * local[2] - local[1] * local[3];
                    let expr2 = local[4];
                    let expr3 = local[0] * local[3] + local[1] * local[2];
                    let expr4 = local[5];
                    builder.assert_eq(expr1, expr2);
                    builder.assert_eq(expr3, expr4);
                }
            }
        }
    }
    const COMMITMENT_PARAMETERS: CommitmentParameters = CommitmentParameters {
        log_blowup: 1,
        cap_height: 0,
    };

    const FRI_PARAMETERS: FriParameters = FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 64,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
    };

    fn system() -> (
        System<GoldilocksBlake3Config>,
        ProverKey<GoldilocksBlake3Config>,
    ) {
        let config = GoldilocksBlake3Config::new(COMMITMENT_PARAMETERS, FRI_PARAMETERS);
        let pythagorean_circuit = LookupAir::new(CS::Pythagorean, vec![]);
        let complex_circuit = LookupAir::new(CS::Complex, vec![]);
        System::new(config, [pythagorean_circuit, complex_circuit])
    }

    #[test]
    fn certifri_test() {
        let (system, key) = system();
        let f = Val::from_u32;
        let witness = SystemWitness::from_stage_1(
            vec![
                RowMajorMatrix::new(
                    [3, 4, 5, 5, 12, 13, 8, 15, 17, 7, 24, 25].map(f).to_vec(),
                    3,
                ),
                RowMajorMatrix::new([4, 2, 3, 1, 10, 10, 3, 2, 5, 1, 13, 13].map(f).to_vec(), 6),
            ],
            &system,
        );
        let no_claims = &[];
        let proof = system.prove_multiple_claims(&key, no_claims, witness);
        system.verify_multiple_claims(no_claims, &proof).unwrap();
    }

    #[test]
    fn certifri_proof_bytes_contract() {
        let (system, key) = system();
        let f = Val::from_u32;
        // 2^4 = 16 rows — small enough for fast CI
        let mut pythagorean_trace = [3, 4, 5].map(f).to_vec();
        let mut complex_trace = [4, 2, 3, 1, 10, 10].map(f).to_vec();
        for _ in 0..4 {
            pythagorean_trace.extend(pythagorean_trace.clone());
            complex_trace.extend(complex_trace.clone());
        }
        let traces = vec![
            RowMajorMatrix::new(pythagorean_trace, 3),
            RowMajorMatrix::new(complex_trace, 6),
        ];
        let no_claims = &[];
        let proof = system.prove_multiple_claims(
            &key,
            no_claims,
            SystemWitness::from_stage_1(traces.clone(), &system),
        );
        let second_proof = system.prove_multiple_claims(
            &key,
            no_claims,
            SystemWitness::from_stage_1(traces, &system),
        );

        // Proving is deterministic at these zero-PoW parameters, so this
        // serialization is a protocol-compatibility contract for alternate
        // backends rather than merely a round-trip smoke test.
        let proof_bytes = proof.to_bytes().expect("Failed to serialize proof");
        let second_proof_bytes = second_proof.to_bytes().expect("Failed to serialize proof");
        assert_eq!(proof_bytes, second_proof_bytes);
        assert_eq!(
            proof_bytes.len(),
            22_017,
            "proof encoding changed; update only with an intentional protocol review"
        );
        assert_eq!(
            Blake3.hash_slice(&proof_bytes),
            [
                17, 55, 200, 132, 9, 170, 249, 195, 35, 120, 241, 110, 48, 5, 20, 38, 250, 196, 78,
                102, 166, 45, 101, 2, 221, 109, 185, 39, 56, 102, 245, 182,
            ],
            "proof bytes changed; update only with an intentional protocol review"
        );

        let proof2 = Proof::from_bytes(&proof_bytes).expect("Failed to deserialize proof");
        system.verify_multiple_claims(no_claims, &proof2).unwrap();
    }

    /// Serial proof bytes match the same workload on main at 347b2d5.
    /// Parallel grinding can select a different valid nonce.
    #[cfg(not(feature = "parallel"))]
    #[test]
    fn proof_bytes_pin() {
        use p3_symmetric::CryptographicHasher;
        let (system, key) = system();
        let f = Val::from_u32;
        let mut pythagorean_trace = [3, 4, 5].map(f).to_vec();
        let mut complex_trace = [4, 2, 3, 1, 10, 10].map(f).to_vec();
        for _ in 0..4 {
            pythagorean_trace.extend(pythagorean_trace.clone());
            complex_trace.extend(complex_trace.clone());
        }
        let witness = SystemWitness::from_stage_1(
            vec![
                RowMajorMatrix::new(pythagorean_trace, 3),
                RowMajorMatrix::new(complex_trace, 6),
            ],
            &system,
        );
        let claim = [f(3), f(4), f(5)];
        let proof = system.prove_multiple_claims(&key, &[&claim], witness);
        let bytes = proof.to_bytes().expect("serialize");
        let hash: [u8; 32] = Blake3.hash_iter(bytes.iter().copied());
        let hex: String = hash.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(
            hex,
            "454ca22efca26ebfb4cae3dc867985ea62da843874dba07162ad903fecca10d9",
            "serialized proof bytes changed ({} bytes)",
            bytes.len()
        );
    }

    // -- Negative / adversarial tests --

    /// Helper: creates a small system and valid proof for negative tests.
    fn small_system_and_proof() -> (
        System<GoldilocksBlake3Config>,
        Proof<GoldilocksBlake3Config>,
    ) {
        let (system, key) = system();
        let f = Val::from_u32;
        let witness = SystemWitness::from_stage_1(
            vec![
                RowMajorMatrix::new(
                    [3, 4, 5, 5, 12, 13, 8, 15, 17, 7, 24, 25].map(f).to_vec(),
                    3,
                ),
                RowMajorMatrix::new([4, 2, 3, 1, 10, 10, 3, 2, 5, 1, 13, 13].map(f).to_vec(), 6),
            ],
            &system,
        );
        let no_claims = &[];
        let proof = system.prove_multiple_claims(&key, no_claims, witness);
        (system, proof)
    }

    #[test]
    fn test_wrong_claim_rejected() {
        let (system, proof) = small_system_and_proof();
        let f = Val::from_u32;
        // Verify with a bogus claim — the prover used no claims, so any claim should fail.
        let result = system.verify(&[f(42)], &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_tampered_stage_1_values_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // Mutate a value in the stage 1 opened values — FRI should catch this.
        proof.stage_1_opened_values[0][0][0] += <ExtVal as Algebra<ExtVal>>::ONE;
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_tampered_opening_proof_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // The context-building helper deliberately does not consume the PCS
        // proof, but the public verifier must pass it to FRI verification.
        proof.opening_proof.final_poly[0] += <ExtVal as p3_field::PrimeCharacteristicRing>::ONE;
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(matches!(
            result,
            Err(VerificationError::InvalidOpeningArgument(_))
        ));
    }

    #[test]
    fn test_tampered_accumulator_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // Set the last intermediate accumulator to non-zero.
        let last = proof.intermediate_accumulators.len() - 1;
        proof.intermediate_accumulators[last] = <ExtVal as Algebra<ExtVal>>::ONE;
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_truncated_log_degrees_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // Remove a log degree — the shape check must reject this instead of
        // the verifier panicking on an out-of-bounds index.
        proof.log_degrees.pop();
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_oversized_log_degree_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // A log degree beyond the field's two-adicity must be rejected instead
        // of causing a shift overflow or a panic inside the PCS.
        proof.log_degrees[0] = 200;
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_truncated_proof_rejected() {
        let (system, mut proof) = small_system_and_proof();
        // Remove a quotient opened value — shape check should fail.
        proof.quotient_opened_values.pop();
        let no_claims: &[&[Val]] = &[];
        let result = system.verify_multiple_claims(no_claims, &proof);
        assert!(result.is_err());
    }

    #[test]
    fn test_serialization_round_trip() {
        let (system, proof) = small_system_and_proof();
        let bytes = proof.to_bytes().expect("serialize");
        let proof2 = Proof::from_bytes(&bytes).expect("deserialize");
        let no_claims: &[&[Val]] = &[];
        system.verify_multiple_claims(no_claims, &proof2).unwrap();
    }
}
