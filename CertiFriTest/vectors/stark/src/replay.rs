//! The verifier's transcript, replayed on multi-stark's challenger with its
//! public helpers, to obtain the challenges written under `debug`.
//!
//! The replay follows `System::verify_multiple_claims` and
//! `System::verify_after_challenges` (`src/verifier.rs`), and for a batch
//! `System::batch_challenger` and `verify_batch_shard_from` (`src/batch.rs`).
//! It can also start from the bytes that the transcript absorbs before its
//! first challenge, written out by hand, which pins what the helpers absorb.
//! Every challenge is then checked to be the one of an accepting run:
//!
//! * the lookup challenges, by handing the replayed transcript state to
//!   multi-stark's `verify_after_challenges`;
//! * the constraint challenge and `zeta`, by recomputing the out-of-domain
//!   identity of every active circuit with them (`check_ood`);
//! * the challenges of FRI, by the grinding checks and by folding every query
//!   down to the final polynomial (`fri::check_folds`).

use multi_stark::batch::BatchProof;
use multi_stark::config::ProofConfig;
use multi_stark::eval::VarValues;
use multi_stark::lookup::logup_constraint_values;
use multi_stark::p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField,
};
use multi_stark::prover::{Proof, observe_claims, sample_lookup_challenges};
use multi_stark::system::{System, extension_params};
use multi_stark::traits::{EvaluationDomain, Pcs, Transcript};
use p3_blake3::Blake3;

use crate::config::{Challenger, Commitment, Config, EXTENSION_DEGREE, ExtVal, Params, Val, root};
use crate::fri::{MatrixClaim, Round, check_folds, replay_challenges};

/// The challenges the verifier derives for one proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Debug {
    /// β.
    pub lookup_challenge: ExtVal,
    /// γ.
    pub fingerprint_challenge: ExtVal,
    /// α of the constraint folding.
    pub constraint_challenge: ExtVal,
    pub zeta: ExtVal,
    /// The first challenge sampled inside `pcs.verify`.
    pub fri_alpha: ExtVal,
    pub fri_betas: Vec<ExtVal>,
    pub fri_indices: Vec<usize>,
}

/// The challenges the verifier derives for a batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchDebug {
    pub lookup_challenge: ExtVal,
    pub fingerprint_challenge: ExtVal,
    pub shards: Vec<Debug>,
}

fn slices(claims: &[Vec<Val>]) -> Vec<&[Val]> {
    claims.iter().map(Vec::as_slice).collect()
}

/// `Σ multiplicity / (β + Σ_i args[i] γ^i)` over the given messages: what
/// multi-stark's `try_messages_accumulator` computes. A claim is a message of
/// multiplicity one.
fn accumulator<'a>(
    beta: ExtVal,
    gamma: ExtVal,
    messages: impl IntoIterator<Item = (&'a [Val], Val)>,
) -> ExtVal {
    let mut sum = ExtVal::ZERO;
    for (args, multiplicity) in messages {
        let fingerprint = args
            .iter()
            .rev()
            .fold(ExtVal::ZERO, |acc, &arg| acc * gamma + ExtVal::from(arg));
        let denominator = beta + fingerprint;
        assert!(!denominator.is_zero(), "a message denominator is zero");
        sum += denominator.inverse() * ExtVal::from(multiplicity);
    }
    sum
}

fn active_indices(proof: &Proof<Config>) -> Vec<usize> {
    (0..proof.active.len())
        .filter(|&i| proof.active[i])
        .collect()
}

/// The claims `verify_after_challenges` hands to `pcs.verify`, in its order:
/// the stage-1 commitment, the stage-2 commitment, the quotient commitment,
/// then the preprocessed commitment if the system has one.
fn pcs_rounds(system: &System<Config>, proof: &Proof<Config>, zeta: ExtVal) -> Vec<Round> {
    let pcs = system.config.pcs();
    let next = |log_degree: usize| {
        pcs.natural_domain_for_degree(1 << log_degree)
            .next_point(zeta)
    };
    let active = active_indices(proof);

    let mut stage_1 = vec![];
    let mut stage_2 = vec![];
    let mut quotient = vec![];
    for pos in 0..active.len() {
        let log_degree = proof.log_degrees[pos] as usize;
        let zeta_next = next(log_degree);
        stage_1.push(MatrixClaim {
            log_degree,
            points: [zeta, zeta_next]
                .into_iter()
                .zip(proof.stage_1_opened_values[pos].iter().cloned())
                .collect(),
        });
        stage_2.push(MatrixClaim {
            log_degree,
            points: vec![
                (zeta, proof.stage_2_opened_values[pos][0].clone()),
                (zeta_next, proof.stage_2_opened_values[pos][1].clone()),
            ],
        });
        quotient.push(MatrixClaim {
            log_degree,
            points: vec![(zeta, proof.quotient_opened_values[pos][0].clone())],
        });
    }
    let mut rounds = vec![stage_1, stage_2, quotient];

    if system.preprocessed_commit.is_some() {
        let values = proof.preprocessed_opened_values.as_ref().unwrap();
        let mut preprocessed = vec![];
        for (ci, slot) in system.preprocessed_indices.iter().enumerate() {
            let Some(slot) = *slot else { continue };
            match active.iter().position(|&a| a == ci) {
                // An active circuit: the domain of its trace, both points.
                Some(pos) => {
                    let log_degree = proof.log_degrees[pos] as usize;
                    preprocessed.push(MatrixClaim {
                        log_degree,
                        points: [zeta, next(log_degree)]
                            .into_iter()
                            .zip(values[slot].iter().cloned())
                            .collect(),
                    });
                }
                // An inactive circuit: the domain of the fixed trace, `zeta`
                // alone.
                None => {
                    let height = system.circuits[ci].preprocessed_height;
                    assert!(height.is_power_of_two());
                    preprocessed.push(MatrixClaim {
                        log_degree: height.trailing_zeros() as usize,
                        points: vec![(zeta, values[slot][0].clone())],
                    });
                }
            }
        }
        rounds.push(preprocessed);
    }
    rounds
}

/// The out-of-domain identity of every active circuit, recomputed as
/// `verify_after_challenges` does, with the given challenges: the constraint
/// values at `zeta`, folded with `alpha` and divided by the vanishing
/// polynomial, equal the quotient recombined from its chunks.
fn check_ood(
    system: &System<Config>,
    proof: &Proof<Config>,
    beta: ExtVal,
    gamma: ExtVal,
    mut acc: ExtVal,
    alpha: ExtVal,
    zeta: ExtVal,
) -> Result<(), String> {
    let pcs = system.config.pcs();
    let d = EXTENSION_DEGREE;
    let modulus = extension_params::<Config>().modulus;
    // The second element of the basis of the extension over the base field.
    let x = ExtVal::from_basis_coefficients_fn(|i| if i == 1 { Val::ONE } else { Val::ZERO });
    let embed = |values: [ExtVal; 4]| -> Vec<ExtVal> {
        values
            .into_iter()
            .flat_map(|e| {
                let coeffs: &[Val] = e.as_basis_coefficients_slice();
                coeffs.iter().map(|&c| ExtVal::from(c)).collect::<Vec<_>>()
            })
            .collect()
    };
    let empty: &[ExtVal] = &[];

    for (pos, ci) in active_indices(proof).into_iter().enumerate() {
        let circuit = &system.circuits[ci];
        let log_degree = proof.log_degrees[pos] as usize;
        let degree = 1usize << log_degree;
        let next_acc = proof.intermediate_accumulators[pos];
        let sels = pcs
            .natural_domain_for_degree(degree)
            .selectors_at_point(zeta);
        let g = Val::two_adic_generator(log_degree);
        let inj_norm = ExtVal::from((Val::from_usize(degree) * g).inverse());

        // The eight public values: the coordinates of β, γ, the accumulator
        // entering the circuit and the one leaving it.
        let publics = embed([beta, gamma, acc, next_acc]);
        let (preprocessed_cur, preprocessed_next) = match system.preprocessed_indices[ci] {
            Some(slot) => {
                let values = &proof.preprocessed_opened_values.as_ref().unwrap()[slot];
                (
                    values[0].as_slice(),
                    values.get(1).map_or(empty, Vec::as_slice),
                )
            }
            None => (empty, empty),
        };
        let stage_1 = &proof.stage_1_opened_values[pos];
        let stage_2 = &proof.stage_2_opened_values[pos];
        let view = VarValues {
            preprocessed: [preprocessed_cur, preprocessed_next],
            main: [
                stage_1[0].as_slice(),
                stage_1.get(1).map_or(empty, Vec::as_slice),
            ],
            stage2: [stage_2[0].as_slice(), stage_2[1].as_slice()],
            publics: &publics,
            is_first_row: sels.is_first_row,
            is_last_row: sels.is_last_row,
            is_transition: sels.is_transition,
        };
        let mut buf = Vec::new();
        circuit.graph.sweep(&view, &mut buf);
        let mut constraint_values = circuit.graph.constraint_values(&buf);
        let delta_scaled: Vec<ExtVal> = (0..d)
            .map(|k| (publics[3 * d + k] - publics[2 * d + k]) * inj_norm)
            .collect();
        logup_constraint_values::<Val, ExtVal>(
            &circuit.graph.lookups,
            &buf,
            view.stage2[0],
            view.stage2[1],
            &publics,
            &delta_scaled,
            view.is_last_row,
            modulus,
            d,
            circuit.lookup_group_size,
            &mut constraint_values,
        );
        if constraint_values.len() != circuit.constraint_count() {
            return Err(format!("circuit {ci}: unexpected number of constraints"));
        }
        let composition = constraint_values
            .iter()
            .fold(ExtVal::ZERO, |sum, &value| sum * alpha + value);

        // Chunk `i` of the quotient is `row[2i] + X * row[2i + 1]`, and the
        // quotient is `Σ_i zeta^(i * degree) * chunk_i`.
        let row = &proof.quotient_opened_values[pos][0];
        if row.len() != circuit.quotient_degree() * d {
            return Err(format!("circuit {ci}: unexpected quotient width"));
        }
        let zeta_pow_n = zeta.exp_power_of_2(log_degree);
        let mut quotient = ExtVal::ZERO;
        let mut zeta_pow = ExtVal::ONE;
        for chunk in row.chunks_exact(d) {
            quotient += zeta_pow * (chunk[0] + x * chunk[1]);
            zeta_pow *= zeta_pow_n;
        }
        if composition * sels.inv_vanishing != quotient {
            return Err(format!(
                "circuit {ci}: the out-of-domain identity fails with the replayed challenges"
            ));
        }
        acc = next_acc;
    }
    Ok(())
}

/// The verifier from the stage-2 commitment on. `challenger` has just sampled
/// the lookup challenges (and, in a batch, observed the shard index); `acc` is
/// the accumulator of the proof's claims.
fn after_challenges(
    system: &System<Config>,
    params: &Params,
    mut challenger: Challenger,
    beta: ExtVal,
    gamma: ExtVal,
    acc: ExtVal,
    proof: &Proof<Config>,
) -> Debug {
    // multi-stark continues from the replayed state and accepts.
    let quotient_degrees = system
        .verify_shape(proof)
        .expect("multi-stark rejects the shape of the proof");
    let continue_with = |beta, gamma, acc| {
        system.verify_after_challenges(
            proof,
            &quotient_degrees,
            challenger.clone(),
            beta,
            gamma,
            acc,
        )
    };
    continue_with(beta, gamma, acc)
        .expect("multi-stark rejects the proof from the replayed transcript state");
    // No check here is vacuous: each one rejects a changed challenge.
    let one = ExtVal::ONE;
    assert!(continue_with(beta + one, gamma, acc).is_err());
    assert!(continue_with(beta, gamma + one, acc).is_err());
    assert!(continue_with(beta, gamma, acc + one).is_err());

    challenger.observe_commitment(proof.commitments.stage_2_trace.clone());
    for accumulator in &proof.intermediate_accumulators {
        challenger.observe_challenge(*accumulator);
    }
    let alpha = challenger.sample_challenge();
    challenger.observe_commitment(proof.commitments.quotient_chunks.clone());
    let zeta = challenger.sample_challenge();
    assert!(!zeta.is_zero(), "zeta is zero");
    check_ood(system, proof, beta, gamma, acc, alpha, zeta).unwrap();
    assert!(check_ood(system, proof, beta, gamma, acc, alpha + one, zeta).is_err());
    assert!(check_ood(system, proof, beta, gamma, acc, alpha, zeta + one).is_err());

    let rounds = pcs_rounds(system, proof, zeta);
    let fri = replay_challenges(params, &mut challenger, &rounds, &proof.opening_proof);
    check_folds(params, &rounds, &proof.opening_proof, &fri).unwrap();
    // When the tallest trace has two rows, every polynomial is of degree at
    // most one and its quotient `(p(z) - p(x)) / (z - x)` is a constant. The
    // only folding round then folds two equal values, and its beta, which
    // multiplies their difference, has no effect.
    let tallest = rounds.iter().flatten().map(|m| m.log_degree).max();
    for (is_beta, changed) in fri.changed() {
        let rejected = check_folds(params, &rounds, &proof.opening_proof, &changed).is_err();
        assert_eq!(rejected, !(is_beta && tallest == Some(1)));
    }

    Debug {
        lookup_challenge: beta,
        fingerprint_challenge: gamma,
        constraint_challenge: alpha,
        zeta,
        fri_alpha: fri.alpha,
        fri_betas: fri.betas,
        fri_indices: fri.indices,
    }
}

/// Where a replay starts.
pub enum Start<'a> {
    /// From this challenger, absorbing with multi-stark's helpers.
    Challenger(Challenger),
    /// From this seed, with everything absorbed before the first challenge
    /// written out as bytes.
    Bytes(&'a [u8]),
}

/// What the transcript absorbs before the first challenge, written out as
/// bytes the way the README states it: a number or a field element as its
/// value in eight little-endian bytes, a commitment as its 32 bytes.
struct Prefix(Vec<u8>);

impl Prefix {
    fn num(&mut self, n: usize) {
        self.0.extend_from_slice(&(n as u64).to_le_bytes());
    }

    fn val(&mut self, x: Val) {
        self.0
            .extend_from_slice(&x.as_canonical_u64().to_le_bytes());
    }

    fn commitment(&mut self, commitment: &Commitment) {
        self.0.extend_from_slice(&root(commitment));
    }

    fn flags(&mut self, flags: &[bool]) {
        for &flag in flags {
            self.num(flag as usize);
        }
    }

    fn log_degrees(&mut self, log_degrees: &[u8]) {
        for &log_degree in log_degrees {
            self.num(log_degree as usize);
        }
    }

    fn claims(&mut self, claims: &[Vec<Val>]) {
        self.num(claims.len());
        for claim in claims {
            self.num(claim.len());
            for &x in claim {
                self.val(x);
            }
        }
    }

    /// The seed, then the shape of the system.
    fn new(seed: &[u8], system: &System<Config>) -> Self {
        let mut prefix = Self(seed.to_vec());
        prefix.num(system.circuits.len());
        for circuit in &system.circuits {
            prefix.num(circuit.constraint_count());
            prefix.num(circuit.max_constraint_degree());
            prefix.num(circuit.preprocessed_height);
            prefix.num(circuit.preprocessed_width);
            prefix.num(circuit.main_width);
            prefix.num(circuit.stage_2_width);
            prefix.num(circuit.lookup_group_size);
        }
        prefix
    }

    /// The challenger that has absorbed these bytes: its input buffer is the
    /// initial state followed by everything absorbed since.
    fn challenger(self) -> Challenger {
        Challenger::from_hasher(self.0, Blake3)
    }
}

/// The challenges of a single proof.
pub fn replay_single(
    system: &System<Config>,
    params: &Params,
    start: Start,
    claims: &[Vec<Val>],
    proof: &Proof<Config>,
) -> Debug {
    let mut challenger = match start {
        Start::Challenger(mut challenger) => {
            system.observe_shape(&mut challenger);
            for &is_active in &proof.active {
                challenger.observe_field(Val::from_bool(is_active));
            }
            if let Some(commit) = &system.preprocessed_commit {
                challenger.observe_commitment(commit.clone());
            }
            challenger.observe_commitment(proof.commitments.stage_1_trace.clone());
            for &log_degree in &proof.log_degrees {
                challenger.observe_field(Val::from_u8(log_degree));
            }
            observe_claims::<Config>(&mut challenger, &slices(claims));
            challenger
        }
        Start::Bytes(seed) => {
            let mut prefix = Prefix::new(seed, system);
            prefix.flags(&proof.active);
            if let Some(commit) = &system.preprocessed_commit {
                prefix.commitment(commit);
            }
            prefix.commitment(&proof.commitments.stage_1_trace);
            prefix.log_degrees(&proof.log_degrees);
            prefix.claims(claims);
            prefix.challenger()
        }
    };
    let (beta, gamma) = sample_lookup_challenges::<Config>(&mut challenger);
    let acc = accumulator(
        beta,
        gamma,
        claims.iter().map(|claim| (claim.as_slice(), Val::ONE)),
    );
    after_challenges(system, params, challenger, beta, gamma, acc, proof)
}

/// The challenges of a batch. Also checks the balance of the batch: the
/// residuals of the shards and the accumulator of the preamble's messages sum
/// to zero.
pub fn replay_batch(
    system: &System<Config>,
    params: &Params,
    start: Start,
    batch: &BatchProof<Config>,
) -> BatchDebug {
    let preamble = &batch.preamble;
    assert_eq!(preamble.headers.len(), batch.proofs.len());

    // `batch_challenger`.
    let mut challenger = match start {
        Start::Challenger(mut challenger) => {
            system.observe_shape(&mut challenger);
            if let Some(commit) = &system.preprocessed_commit {
                challenger.observe_commitment(commit.clone());
            }
            challenger.observe_field(Val::from_usize(preamble.headers.len()));
            for header in &preamble.headers {
                for &is_active in &header.active {
                    challenger.observe_field(Val::from_bool(is_active));
                }
                challenger.observe_commitment(header.stage_1_trace.clone());
                challenger.observe_field(Val::from_usize(header.log_degrees.len()));
                for &log_degree in &header.log_degrees {
                    challenger.observe_field(Val::from_u8(log_degree));
                }
                observe_claims::<Config>(&mut challenger, &slices(&header.claims));
            }
            challenger.observe_field(Val::from_usize(preamble.messages.len()));
            for message in &preamble.messages {
                challenger.observe_field(Val::from_usize(message.args.len()));
                challenger.observe_field_slice(&message.args);
                challenger.observe_field(message.multiplicity);
            }
            challenger
        }
        Start::Bytes(seed) => {
            let mut prefix = Prefix::new(seed, system);
            if let Some(commit) = &system.preprocessed_commit {
                prefix.commitment(commit);
            }
            prefix.num(preamble.headers.len());
            for header in &preamble.headers {
                prefix.flags(&header.active);
                prefix.commitment(&header.stage_1_trace);
                prefix.num(header.log_degrees.len());
                prefix.log_degrees(&header.log_degrees);
                prefix.claims(&header.claims);
            }
            prefix.num(preamble.messages.len());
            for message in &preamble.messages {
                prefix.num(message.args.len());
                for &arg in &message.args {
                    prefix.val(arg);
                }
                prefix.val(message.multiplicity);
            }
            prefix.challenger()
        }
    };
    let (beta, gamma) = sample_lookup_challenges::<Config>(&mut challenger);

    // multi-stark's own helper reaches the same state.
    let (mut theirs, their_beta, their_gamma) = system.batch_challenger(preamble);
    assert_eq!((beta, gamma), (their_beta, their_gamma));
    assert_eq!(
        challenger.clone().sample_challenge(),
        theirs.sample_challenge()
    );

    let mut total = accumulator(
        beta,
        gamma,
        preamble
            .messages
            .iter()
            .map(|message| (message.args.as_slice(), message.multiplicity)),
    );
    let mut shards = vec![];
    for (shard, (header, proof)) in preamble.headers.iter().zip(&batch.proofs).enumerate() {
        // `verify_batch_shard_from`.
        assert!(
            header.active == proof.active
                && header.stage_1_trace == proof.commitments.stage_1_trace
                && header.log_degrees == proof.log_degrees,
            "header {shard} does not describe its proof"
        );
        let mut fork = challenger.clone();
        fork.observe_field(Val::from_usize(shard));
        let acc = accumulator(
            beta,
            gamma,
            header
                .claims
                .iter()
                .map(|claim| (claim.as_slice(), Val::ONE)),
        );
        shards.push(after_challenges(
            system, params, fork, beta, gamma, acc, proof,
        ));
        total += *proof.intermediate_accumulators.last().unwrap();
    }
    assert!(total.is_zero(), "the batch does not balance");

    BatchDebug {
        lookup_challenge: beta,
        fingerprint_challenge: gamma,
        shards,
    }
}
