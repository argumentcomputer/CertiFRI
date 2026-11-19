//! A plain restatement of what Plonky3's `TwoAdicFriPcs::verify` computes,
//! for binary folding, reading nothing but the content of a vector file
//! (`params`, `claims`, `proof`) and using the byte-level transcript and
//! Merkle definitions of `model.rs` and `merkle.rs`.
//!
//! It serves two purposes. It produces the `debug` object of a vector, and it
//! shows that the file holds everything a verifier needs: the generator
//! requires it to accept every vector it writes, with the same challenges
//! Plonky3's own challenger produces.
//!
//! It mirrors `fri/src/two_adic_pcs.rs` (`verify`) and `fri/src/verifier.rs`
//! (`verify_fri`, `open_inputs`, `fold_query`). Opening proofs are checked in
//! the `paths` form.

use std::collections::BTreeMap;

use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_util::reverse_bits_len;

use crate::config::{ext_coeffs, Challenge, Params, Val};
use crate::merkle::{root_from_path, Dim};
use crate::model::ModelChallenger;
use crate::types::{BatchClaim, BatchTrace, Proof, RoundTrace, Trace};

fn ensure(condition: bool, message: &str) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.to_string())
    }
}

/// The point of index `index` in the bit-reversed subgroup of order
/// `2^log_height`: `g^(bitrev(index))`, with `g` the generator of that order.
fn subgroup_point(log_height: usize, index: usize) -> Val {
    Val::two_adic_generator(log_height).exp_u64(reverse_bits_len(index, log_height) as u64)
}

/// Check a proof. With `check_paths` off the Merkle paths are not looked at;
/// the generator uses that to learn the rows the paths have to open.
pub fn verify(
    params: &Params,
    claims: &[BatchClaim],
    proof: &Proof,
    check_paths: bool,
) -> Result<Trace, String> {
    let log_blowup = params.log_blowup;
    let num_queries = params.num_queries;
    ensure(num_queries > 0, "zero queries")?;

    // The transcript. The preamble: every commitment, then every opening point.
    let mut challenger = ModelChallenger::new();
    for batch in claims {
        challenger.observe_digest(&batch.commitment);
    }
    for batch in claims {
        for matrix in &batch.matrices {
            for claim in &matrix.points {
                challenger.observe_ext(claim.point);
            }
        }
    }
    // `TwoAdicFriPcs::verify`: every claimed value.
    for batch in claims {
        for matrix in &batch.matrices {
            for claim in &matrix.points {
                for value in &claim.values {
                    challenger.observe_ext(*value);
                }
            }
        }
    }
    // `verify_fri` from here on.
    let alpha = challenger.sample_ext();

    let num_rounds = proof.commit_phase_commits.len();
    ensure(
        proof.commit_phase_openings.len() == num_rounds,
        "one opening per round expected",
    )?;
    for opening in &proof.commit_phase_openings {
        // Plonky3 takes any log-arity from 1 to `max_log_arity`.
        ensure(
            opening.log_arity == 1 && opening.log_arity <= params.max_log_arity,
            "only binary folding is handled",
        )?;
        ensure(
            opening.sibling_values.len() == num_queries,
            "one sibling list per query expected",
        )?;
        ensure(
            opening.sibling_values.iter().all(|s| s.len() == 1),
            "one sibling value per query expected",
        )?;
    }
    let log_global_max_height = num_rounds + log_blowup + params.log_final_poly_len;
    ensure(
        log_global_max_height <= Val::TWO_ADICITY,
        "domain too large",
    )?;
    let tallest = claims
        .iter()
        .flat_map(|batch| batch.matrices.iter().map(|m| m.log_degree + log_blowup))
        .max();
    if let Some(tallest) = tallest {
        ensure(
            tallest == log_global_max_height,
            "the number of rounds does not match the tallest matrix",
        )?;
    }
    ensure(
        proof.commit_pow_witnesses.len() == num_rounds,
        "one grinding witness per round expected",
    )?;

    let mut betas = vec![];
    for (commit, witness) in proof
        .commit_phase_commits
        .iter()
        .zip(&proof.commit_pow_witnesses)
    {
        challenger.observe_digest(commit);
        ensure(
            challenger.check_witness(params.commit_proof_of_work_bits, *witness),
            "bad commit-phase grinding witness",
        )?;
        betas.push(challenger.sample_ext());
    }
    ensure(
        proof.final_poly.len() == 1 << params.log_final_poly_len,
        "final polynomial of the wrong length",
    )?;
    for coeff in &proof.final_poly {
        challenger.observe_ext(*coeff);
    }
    for opening in &proof.commit_phase_openings {
        challenger.observe_base(Val::from_usize(opening.log_arity));
    }
    ensure(
        challenger.check_witness(params.query_proof_of_work_bits, proof.query_pow_witness),
        "bad query grinding witness",
    )?;
    let indices: Vec<usize> = (0..num_queries)
        .map(|_| challenger.sample_bits(log_global_max_height))
        .collect();

    // The input openings (`open_inputs`).
    ensure(
        proof.input_openings.len() == claims.len(),
        "one input opening per batch expected",
    )?;
    let mut input_batches = vec![];
    for (batch, opening) in claims.iter().zip(&proof.input_openings) {
        ensure(
            opening.opened_values.len() == num_queries,
            "one set of rows per query expected",
        )?;
        ensure(
            opening
                .opened_values
                .iter()
                .all(|rows| rows.len() == batch.matrices.len()),
            "one row per matrix expected",
        )?;
        // The width of a matrix is the number of values claimed at its first point.
        let mut dims = vec![];
        for matrix in &batch.matrices {
            let first = matrix.points.first().ok_or("matrix opened at no point")?;
            dims.push(Dim {
                width: first.values.len(),
                log_height: matrix.log_degree + log_blowup,
            });
        }
        let batch_log_height = dims
            .iter()
            .map(|d| d.log_height)
            .max()
            .ok_or("empty batch")?;
        // A batch shorter than the tallest one is opened at the index shifted down.
        let reduced: Vec<usize> = indices
            .iter()
            .map(|index| index >> (log_global_max_height - batch_log_height))
            .collect();
        if check_paths {
            ensure(
                opening.opening_proof.paths.len() == num_queries,
                "one path per query expected",
            )?;
            let paths = &opening.opening_proof.paths;
            for ((index, rows), path) in reduced.iter().zip(&opening.opened_values).zip(paths) {
                let root = root_from_path(&dims, *index, rows, path)?;
                ensure(root == batch.commitment, "input opening does not verify")?;
            }
        }
        input_batches.push(BatchTrace {
            dimensions: dims,
            indices: reduced,
        });
    }

    // The reduced openings: per query and per height, the alpha-combination of
    // the quotients `(p(z) - p(x)) / (z - x)` of the matrices of that height.
    let mut reduced_openings = vec![];
    for (query, &index) in indices.iter().enumerate() {
        // log_height -> (next power of alpha, sum so far)
        let mut by_height: BTreeMap<usize, (Challenge, Challenge)> = BTreeMap::new();
        for (batch, opening) in claims.iter().zip(&proof.input_openings) {
            for (matrix, row) in batch.matrices.iter().zip(&opening.opened_values[query]) {
                let log_height = matrix.log_degree + log_blowup;
                let reduced_index = index >> (log_global_max_height - log_height);
                // The committed codeword is over the coset `GENERATOR * H`.
                let x = Val::GENERATOR * subgroup_point(log_height, reduced_index);
                let (alpha_pow, sum) = by_height
                    .entry(log_height)
                    .or_insert((Challenge::ONE, Challenge::ZERO));
                for claim in &matrix.points {
                    ensure(
                        claim.values.len() == row.len(),
                        "claimed values do not match the row width",
                    )?;
                    let denominator = claim.point - x;
                    ensure(
                        !denominator.is_zero(),
                        "opening point on the evaluation domain",
                    )?;
                    let quotient = denominator.inverse();
                    for (&p_at_x, &p_at_z) in row.iter().zip(&claim.values) {
                        *sum += *alpha_pow * (p_at_z - p_at_x) * quotient;
                        *alpha_pow *= alpha;
                    }
                }
            }
        }
        // A matrix of one row is a constant; its quotient must vanish.
        if let Some((_, sum)) = by_height.get(&log_blowup) {
            ensure(
                sum.is_zero(),
                "nonzero reduced opening at the blowup height",
            )?;
        }
        let descending: Vec<(usize, Challenge)> = by_height
            .into_iter()
            .rev()
            .map(|(log_height, (_, sum))| (log_height, sum))
            .collect();
        reduced_openings.push(descending);
    }

    // The fold chains (`fold_query`) and the final polynomial.
    let log_final_height = log_blowup + params.log_final_poly_len;
    let half = Val::TWO.inverse();
    let mut rounds: Vec<RoundTrace> = (0..num_rounds)
        .map(|round| RoundTrace {
            log_height: log_global_max_height - round - 1,
            indices: vec![],
            rows: vec![],
            folded: vec![],
        })
        .collect();
    let mut final_points = vec![];
    let mut final_evals = vec![];
    for (query, &index) in indices.iter().enumerate() {
        let mut openings = reduced_openings[query].iter().peekable();
        let (first_height, first) = *openings.next().ok_or("nothing to fold")?;
        ensure(
            first_height == log_global_max_height,
            "no reduced opening at the top height",
        )?;
        let mut folded = first;
        let mut domain_index = index;
        let mut log_height = log_global_max_height;
        for round in 0..num_rounds {
            let beta = betas[round];
            let sibling = proof.commit_phase_openings[round].sibling_values[query][0];
            // The value carried so far sits at the low bit of the index.
            let row = if domain_index & 1 == 0 {
                [folded, sibling]
            } else {
                [sibling, folded]
            };
            domain_index >>= 1;
            log_height -= 1;
            // The row holds the values at `x` and `-x`, with
            // `x = g^(bitrev(domain_index))` and `g` of order `2^(log_height + 1)`.
            let x = Val::two_adic_generator(log_height + 1)
                .exp_u64(reverse_bits_len(domain_index, log_height) as u64);
            folded = (row[0] + row[1]) * half + beta * (row[0] - row[1]) * (half * x.inverse());
            // Roll in the matrices of the height just reached, scaled by beta^2.
            if let Some((_, opening)) = openings.next_if(|(h, _)| *h == log_height) {
                folded += beta.square() * *opening;
            }
            rounds[round].indices.push(domain_index);
            rounds[round].rows.push(row);
            rounds[round].folded.push(folded);
        }
        ensure(log_height == log_final_height, "wrong final height")?;
        ensure(openings.next().is_none(), "a reduced opening was not used")?;
        // The final polynomial, lowest coefficient first, at the point of the
        // final domain the index leads to.
        let x = subgroup_point(log_final_height, domain_index);
        let eval = proof
            .final_poly
            .iter()
            .rev()
            .fold(Challenge::ZERO, |acc, coeff| acc * x + *coeff);
        ensure(eval == folded, "final polynomial mismatch")?;
        final_points.push(x);
        final_evals.push(eval);
    }

    // The commit-phase openings: round `r` commits to one matrix of two
    // extension columns, four base-field columns once flattened.
    if check_paths {
        for (round, trace) in rounds.iter().enumerate() {
            let dims = [Dim {
                width: 4,
                log_height: trace.log_height,
            }];
            let paths = &proof.commit_phase_openings[round].opening_proof.paths;
            ensure(paths.len() == num_queries, "one path per query expected")?;
            for ((index, row), path) in trace.indices.iter().zip(&trace.rows).zip(paths) {
                let root = root_from_path(&dims, *index, &[flatten_row(row)], path)?;
                ensure(
                    root == proof.commit_phase_commits[round],
                    "commit-phase opening does not verify",
                )?;
            }
        }
    }

    Ok(Trace {
        log_global_max_height,
        alpha,
        betas,
        indices,
        input_batches,
        reduced_openings,
        rounds,
        final_points,
        final_evals,
    })
}

/// A row of extension elements as base-field elements: the coefficients of
/// each element in turn, `c0` first.
pub fn flatten_row(row: &[Challenge]) -> Vec<Val> {
    row.iter().flat_map(|e| ext_coeffs(*e)).collect()
}
