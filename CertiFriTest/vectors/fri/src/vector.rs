//! Production of one vector: commit and open with Plonky3, check the proof
//! with Plonky3's verifier, and collect what a verifier needs.

use core::marker::PhantomData;

use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_commit::{BatchOpeningRef, Mmcs, Pcs};
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::PrimeCharacteristicRing;
use p3_fri::{BatchMultiOpening, CommitPhaseMultiStep, FriFoldingStrategy, TwoAdicFriFolding};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Dimensions;

use crate::config::{
    challenge_mmcs, fresh_challenger, fri_pcs, root, val_mmcs, Challenge, ChallengeMmcs,
    Challenger, Commitment, Digest, FriPcs, Params, SplitMix64, Val, ValMmcs,
};
use crate::merkle::{restore_paths, Dim};
use crate::reference::{self, flatten_row};
use crate::types::{
    BatchClaim, CommitPhaseOpening, InputOpening, MatrixClaim, OpeningProof, PointClaim, Proof,
    Trace, Vector,
};

type Domain = TwoAdicMultiplicativeCoset<Val>;
type P3Proof = <FriPcs as Pcs<Challenge, Challenger>>::Proof;
type P3ProverData = <FriPcs as Pcs<Challenge, Challenger>>::ProverData;
type P3Claims = Vec<(Commitment, Vec<(Domain, Vec<(Challenge, Vec<Challenge>)>)>)>;

/// One committed matrix: its size and the opening points, as indices into the
/// list of points of the case.
pub struct MatrixSpec {
    pub log_degree: usize,
    pub width: usize,
    pub points: &'static [usize],
}

pub struct CaseSpec {
    pub name: &'static str,
    /// Seed of the matrix entries and the opening points.
    pub seed: u64,
    pub params: Params,
    pub num_points: usize,
    pub batches: Vec<Vec<MatrixSpec>>,
}

/// The challenger after the fixed preamble: every batch commitment in batch
/// order, then every opening point in the order batch, matrix, point.
fn preamble(commitments: &[Commitment], points: &[Vec<Vec<Challenge>>]) -> Challenger {
    let mut challenger = fresh_challenger();
    for commitment in commitments {
        challenger.observe(commitment.clone());
    }
    for batch in points {
        for matrix in batch {
            for point in matrix {
                challenger.observe_algebra_element(*point);
            }
        }
    }
    challenger
}

/// The challenges of `verify_fri`, replayed with Plonky3's own challenger in
/// the order `TwoAdicFriPcs::verify` and `verify_fri` use it.
fn replay_challenges(
    params: &Params,
    mut challenger: Challenger,
    claims: &P3Claims,
    proof: &P3Proof,
) -> (usize, Challenge, Vec<Challenge>, Vec<usize>) {
    for (_, batch) in claims {
        for (_, matrix) in batch {
            for (_, values) in matrix {
                challenger.observe_algebra_slice(values);
            }
        }
    }
    let alpha: Challenge = challenger.sample_algebra_element();
    let log_arities: Vec<usize> = proof
        .commit_phase_openings
        .iter()
        .map(|opening| opening.log_arity as usize)
        .collect();
    let log_global_max_height =
        log_arities.iter().sum::<usize>() + params.log_blowup + params.log_final_poly_len;
    let mut betas = vec![];
    for (commit, witness) in proof
        .commit_phase_commits
        .iter()
        .zip(&proof.commit_pow_witnesses)
    {
        challenger.observe(commit.clone());
        assert!(challenger.check_witness(params.commit_proof_of_work_bits, *witness));
        betas.push(challenger.sample_algebra_element());
    }
    challenger.observe_algebra_slice(&proof.final_poly);
    for &log_arity in &log_arities {
        challenger.observe(Val::from_usize(log_arity));
    }
    assert!(challenger.check_witness(params.query_proof_of_work_bits, proof.query_pow_witness));
    let indices = (0..params.num_queries)
        .map(|_| challenger.sample_bits(log_global_max_height))
        .collect();
    (log_global_max_height, alpha, betas, indices)
}

fn p3_dims(dims: &[Dim]) -> Vec<Dimensions> {
    dims.iter()
        .map(|d| Dimensions {
            width: d.width,
            height: 1 << d.log_height,
        })
        .collect()
}

/// Unpack the pruned proof of one input batch and check both forms with
/// Plonky3: the pruned form with `verify_multi_batch`, each full path with the
/// one-index `verify_batch`, and each full path against the path Plonky3's
/// prover gives for that index.
fn input_opening_proof(
    mmcs: &ValMmcs,
    commitment: &Commitment,
    data: &P3ProverData,
    dims: &[Dim],
    indices: &[usize],
    opening: &BatchMultiOpening<Val, ValMmcs>,
) -> OpeningProof {
    let dimensions = p3_dims(dims);
    let pruned = opening.opening_proof.sibling_hashes.clone();
    mmcs.verify_multi_batch(
        commitment,
        &dimensions,
        indices,
        &opening.opened_values,
        &opening.opening_proof,
    )
    .expect("Plonky3 rejects the pruned input opening at the replayed indices");

    let schedule = mmcs.proof_arity_schedule(&dimensions).unwrap();
    assert!(schedule.iter().all(|&step| step == 2));

    let (paths, restored_root) = restore_paths(dims, indices, &opening.opened_values, &pruned);
    assert_eq!(restored_root, root(commitment));
    for (query, &index) in indices.iter().enumerate() {
        let path: &Vec<Digest> = &paths[query];
        assert_eq!(path.len(), schedule.len());
        mmcs.verify_batch(
            commitment,
            &dimensions,
            index,
            BatchOpeningRef::new(&opening.opened_values[query], path),
        )
        .expect("Plonky3 rejects a restored input path");
        let (rows, prover_path) = mmcs.open_batch(index, data).unpack();
        assert_eq!(rows, opening.opened_values[query]);
        assert_eq!(&prover_path, path);
    }
    OpeningProof { pruned, paths }
}

/// The same for one folding round, whose rows the verifier reconstructs.
fn round_opening_proof(
    mmcs: &ChallengeMmcs,
    commitment: &Commitment,
    log_height: usize,
    indices: &[usize],
    rows: &[[Challenge; 2]],
    opening: &CommitPhaseMultiStep<Challenge, ChallengeMmcs>,
) -> OpeningProof {
    let dimensions = [Dimensions {
        width: 2,
        height: 1 << log_height,
    }];
    let pruned = opening.opening_proof.sibling_hashes.clone();
    let ext_rows: Vec<Vec<Vec<Challenge>>> = rows.iter().map(|row| vec![row.to_vec()]).collect();
    mmcs.verify_multi_batch(
        commitment,
        &dimensions,
        indices,
        &ext_rows,
        &opening.opening_proof,
    )
    .expect("Plonky3 rejects the pruned commit-phase opening");

    let base_dims = [Dim {
        width: 4,
        log_height,
    }];
    let base_rows: Vec<Vec<Vec<Val>>> = rows.iter().map(|row| vec![flatten_row(row)]).collect();
    let (paths, restored_root) = restore_paths(&base_dims, indices, &base_rows, &pruned);
    assert_eq!(restored_root, root(commitment));
    for (query, &index) in indices.iter().enumerate() {
        assert_eq!(paths[query].len(), log_height);
        mmcs.verify_batch(
            commitment,
            &dimensions,
            index,
            BatchOpeningRef::new(&ext_rows[query], &paths[query]),
        )
        .expect("Plonky3 rejects a restored commit-phase path");
    }
    OpeningProof { pruned, paths }
}

/// The folded values of the reference verifier against Plonky3's `fold_row`.
fn check_folds(trace: &Trace) {
    let folding = TwoAdicFriFolding::<(), ()>(PhantomData);
    for (round, step) in trace.rounds.iter().enumerate() {
        let beta = trace.betas[round];
        for query in 0..trace.indices.len() {
            let mut expected: Challenge = FriFoldingStrategy::<Val, Challenge>::fold_row(
                &folding,
                step.indices[query],
                step.log_height,
                1,
                beta,
                step.rows[query].into_iter(),
            );
            if let Some((_, opening)) = trace.reduced_openings[query]
                .iter()
                .find(|(log_height, _)| *log_height == step.log_height)
            {
                expected += beta.square() * *opening;
            }
            assert_eq!(expected, step.folded[query]);
        }
    }
}

fn convert_proof(proof: &P3Proof) -> Proof {
    Proof {
        commit_phase_commits: proof.commit_phase_commits.iter().map(root).collect(),
        commit_pow_witnesses: proof.commit_pow_witnesses.clone(),
        final_poly: proof.final_poly.clone(),
        query_pow_witness: proof.query_pow_witness,
        input_openings: proof
            .input_openings
            .iter()
            .map(|opening| InputOpening {
                opened_values: opening.opened_values.clone(),
                opening_proof: OpeningProof {
                    pruned: opening.opening_proof.sibling_hashes.clone(),
                    paths: vec![],
                },
            })
            .collect(),
        commit_phase_openings: proof
            .commit_phase_openings
            .iter()
            .map(|opening| CommitPhaseOpening {
                log_arity: opening.log_arity as usize,
                sibling_values: opening.sibling_values.clone(),
                opening_proof: OpeningProof {
                    pruned: opening.opening_proof.sibling_hashes.clone(),
                    paths: vec![],
                },
            })
            .collect(),
    }
}

fn convert_claims(claims: &P3Claims) -> Vec<BatchClaim> {
    claims
        .iter()
        .map(|(commitment, matrices)| BatchClaim {
            commitment: root(commitment),
            matrices: matrices
                .iter()
                .map(|(domain, points)| MatrixClaim {
                    log_degree: domain.log_size(),
                    points: points
                        .iter()
                        .map(|(point, values)| PointClaim {
                            point: *point,
                            values: values.clone(),
                        })
                        .collect(),
                })
                .collect(),
        })
        .collect()
}

fn p3_verify(
    pcs: &FriPcs,
    commitments: &[Commitment],
    points: &[Vec<Vec<Challenge>>],
    claims: P3Claims,
    proof: &P3Proof,
) -> Result<(), String> {
    let mut challenger = preamble(commitments, points);
    <FriPcs as Pcs<Challenge, Challenger>>::verify(pcs, claims, proof, &mut challenger)
        .map_err(|e| format!("{e:?}"))
}

pub fn generate(spec: &CaseSpec) -> Vector {
    let params = spec.params;
    let pcs = fri_pcs(&params);
    let mmcs = val_mmcs();
    let fri_mmcs = challenge_mmcs();
    let mut rng = SplitMix64::new(spec.seed);

    // The opening points, then the matrices, from the seeded generator.
    let all_points: Vec<Challenge> = (0..spec.num_points).map(|_| rng.ext()).collect();
    let mut domains: Vec<Vec<Domain>> = vec![];
    let mut commitments: Vec<Commitment> = vec![];
    let mut prover_data: Vec<P3ProverData> = vec![];
    let mut points: Vec<Vec<Vec<Challenge>>> = vec![];
    for batch in &spec.batches {
        let mut batch_domains = vec![];
        let mut evaluations = vec![];
        let mut batch_points = vec![];
        for matrix in batch {
            let height = 1usize << matrix.log_degree;
            let values: Vec<Val> = (0..height * matrix.width).map(|_| rng.val()).collect();
            let domain =
                <FriPcs as Pcs<Challenge, Challenger>>::natural_domain_for_degree(&pcs, height);
            batch_domains.push(domain);
            evaluations.push((domain, RowMajorMatrix::new(values, matrix.width)));
            batch_points.push(matrix.points.iter().map(|&i| all_points[i]).collect());
        }
        let (commitment, data) = <FriPcs as Pcs<Challenge, Challenger>>::commit(&pcs, evaluations);
        domains.push(batch_domains);
        commitments.push(commitment);
        prover_data.push(data);
        points.push(batch_points);
    }

    // Open. The prover starts from the preamble.
    let mut prover_challenger = preamble(&commitments, &points);
    let data_and_points = prover_data.iter().zip(points.iter().cloned()).collect();
    let (opened_values, p3_proof): (_, P3Proof) =
        <FriPcs as Pcs<Challenge, Challenger>>::open(&pcs, data_and_points, &mut prover_challenger);

    // The claims, in the shape of `commitments_with_opening_points`.
    let p3_claims: P3Claims = (0..spec.batches.len())
        .map(|b| {
            let matrices = (0..spec.batches[b].len())
                .map(|m| {
                    let claims = points[b][m]
                        .iter()
                        .zip(&opened_values[b][m])
                        .map(|(point, values)| (*point, values.clone()))
                        .collect();
                    (domains[b][m], claims)
                })
                .collect();
            (commitments[b].clone(), matrices)
        })
        .collect();

    // Plonky3's verifier accepts the proof, and rejects it once one claimed
    // value is changed.
    p3_verify(&pcs, &commitments, &points, p3_claims.clone(), &p3_proof)
        .expect("Plonky3 rejects its own proof");
    let mut tampered_claims = p3_claims.clone();
    tampered_claims[0].1[0].1[0].1[0] += Challenge::ONE;
    p3_verify(
        &pcs,
        &commitments,
        &points,
        tampered_claims.clone(),
        &p3_proof,
    )
    .expect_err("Plonky3 accepts a changed claimed value");

    // The reference verifier, first without the paths, which do not exist yet.
    let claims = convert_claims(&p3_claims);
    let mut proof = convert_proof(&p3_proof);
    let trace = reference::verify(&params, &claims, &proof, false)
        .expect("the reference verifier rejects the proof");

    // Its challenges are those of Plonky3's challenger.
    let (log_global_max_height, alpha, betas, indices) = replay_challenges(
        &params,
        preamble(&commitments, &points),
        &p3_claims,
        &p3_proof,
    );
    assert_eq!(trace.log_global_max_height, log_global_max_height);
    assert_eq!(trace.alpha, alpha);
    assert_eq!(trace.betas, betas);
    assert_eq!(trace.indices, indices);
    check_folds(&trace);

    // Unpack the pruned proofs into full paths.
    for b in 0..spec.batches.len() {
        proof.input_openings[b].opening_proof = input_opening_proof(
            &mmcs,
            &commitments[b],
            &prover_data[b],
            &trace.input_batches[b].dimensions,
            &trace.input_batches[b].indices,
            &p3_proof.input_openings[b],
        );
    }
    for (round, step) in trace.rounds.iter().enumerate() {
        proof.commit_phase_openings[round].opening_proof = round_opening_proof(
            &fri_mmcs,
            &p3_proof.commit_phase_commits[round],
            step.log_height,
            &step.indices,
            &step.rows,
            &p3_proof.commit_phase_openings[round],
        );
    }

    // The reference verifier accepts what goes into the file, paths included,
    // and rejects a changed claimed value and a changed path.
    let full_trace = reference::verify(&params, &claims, &proof, true)
        .expect("the reference verifier rejects the vector");
    assert_eq!(full_trace, trace);
    reference::verify(&params, &convert_claims(&tampered_claims), &proof, true)
        .expect_err("the reference verifier accepts a changed claimed value");
    let mut tampered_proof = proof.clone();
    tampered_proof.input_openings[0].opening_proof.paths[0][0][0] ^= 1;
    reference::verify(&params, &claims, &tampered_proof, true)
        .expect_err("the reference verifier accepts a changed input path");
    let mut tampered_proof = proof.clone();
    tampered_proof
        .commit_phase_openings
        .last_mut()
        .unwrap()
        .opening_proof
        .paths[0][0][31] ^= 0x80;
    reference::verify(&params, &claims, &tampered_proof, true)
        .expect_err("the reference verifier accepts a changed commit-phase path");

    Vector {
        name: spec.name,
        params,
        claims,
        proof,
        debug: trace,
    }
}

/// A one-line description of a vector, for the log of a run.
pub fn summary(vector: &Vector) -> String {
    let trace = &vector.debug;
    let mut distinct = trace.indices.clone();
    distinct.sort_unstable();
    distinct.dedup();
    let pruned: usize = vector
        .proof
        .input_openings
        .iter()
        .map(|o| o.opening_proof.pruned.len())
        .chain(
            vector
                .proof
                .commit_phase_openings
                .iter()
                .map(|o| o.opening_proof.pruned.len()),
        )
        .sum();
    let full: usize = vector
        .proof
        .input_openings
        .iter()
        .map(|o| o.opening_proof.paths.iter().map(Vec::len).sum::<usize>())
        .chain(
            vector
                .proof
                .commit_phase_openings
                .iter()
                .map(|o| o.opening_proof.paths.iter().map(Vec::len).sum::<usize>()),
        )
        .sum();
    format!(
        "{}: log_global_max_height {}, {} rounds, {} queries ({} distinct), {} pruned digests, {} path digests",
        vector.name,
        trace.log_global_max_height,
        trace.rounds.len(),
        trace.indices.len(),
        distinct.len(),
        pruned,
        full
    )
}
