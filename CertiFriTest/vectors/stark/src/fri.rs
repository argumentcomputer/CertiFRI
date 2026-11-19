//! The part of the verifier that Plonky3 runs inside `pcs.verify`: the
//! challenges of `TwoAdicFriPcs::verify` and `verify_fri`, replayed on
//! multi-stark's challenger, and a check that they lead every query to the
//! final polynomial.
//!
//! Both follow the generator of the bare FRI vectors (`../fri/src/vector.rs`
//! and `../fri/src/reference.rs`), whose README states the transcript and the
//! folding rule.

use std::collections::BTreeMap;

use multi_stark::p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use multi_stark::traits::Transcript;
use multi_stark::types::PcsProof;
use p3_challenger::{CanSampleBits, GrindingChallenger};

use crate::config::{Challenger, ExtVal, Params, Val};

/// One committed matrix as `pcs.verify` receives it: the log of its row count
/// before the blowup, and the claimed values at each opening point.
pub struct MatrixClaim {
    pub log_degree: usize,
    pub points: Vec<(ExtVal, Vec<ExtVal>)>,
}

/// The matrices of one commitment, in the order they were committed.
pub type Round = Vec<MatrixClaim>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriChallenges {
    pub alpha: ExtVal,
    pub betas: Vec<ExtVal>,
    pub indices: Vec<usize>,
}

impl FriChallenges {
    /// Copies with one challenge changed: `alpha`, each `beta`, each index.
    /// The flag says whether the changed challenge is a `beta`.
    pub fn changed(&self) -> Vec<(bool, FriChallenges)> {
        let mut copies = vec![];
        let mut copy = self.clone();
        copy.alpha += ExtVal::ONE;
        copies.push((false, copy));
        for round in 0..self.betas.len() {
            let mut copy = self.clone();
            copy.betas[round] += ExtVal::ONE;
            copies.push((true, copy));
        }
        for query in 0..self.indices.len() {
            let mut copy = self.clone();
            copy.indices[query] ^= 1;
            copies.push((false, copy));
        }
        copies
    }
}

/// The challenges of `pcs.verify`, in the order `TwoAdicFriPcs::verify`
/// (`fri/src/two_adic_pcs.rs`) and `verify_fri` (`fri/src/verifier.rs`) use
/// the challenger. Panics if a grinding witness fails its check.
pub fn replay_challenges(
    params: &Params,
    challenger: &mut Challenger,
    rounds: &[Round],
    proof: &PcsProof,
) -> FriChallenges {
    // `TwoAdicFriPcs::verify`: every claimed value, in the order round,
    // matrix, point, column.
    for round in rounds {
        for matrix in round {
            for (_, values) in &matrix.points {
                for value in values {
                    challenger.observe_challenge(*value);
                }
            }
        }
    }
    // `verify_fri` from here on.
    let alpha = challenger.sample_challenge();
    let mut betas = vec![];
    assert_eq!(
        proof.commit_phase_commits.len(),
        proof.commit_pow_witnesses.len()
    );
    for (commit, witness) in proof
        .commit_phase_commits
        .iter()
        .zip(&proof.commit_pow_witnesses)
    {
        challenger.observe_commitment(commit.clone());
        assert!(
            challenger.check_witness(params.commit_proof_of_work_bits, *witness),
            "a commit-phase grinding witness fails on the replayed challenger"
        );
        betas.push(challenger.sample_challenge());
    }
    for coeff in &proof.final_poly {
        challenger.observe_challenge(*coeff);
    }
    for opening in &proof.commit_phase_openings {
        challenger.observe_field(Val::from_u8(opening.log_arity));
    }
    assert!(
        challenger.check_witness(params.query_proof_of_work_bits, proof.query_pow_witness),
        "the query grinding witness fails on the replayed challenger"
    );
    let log_global_max_height = log_global_max_height(params, proof);
    let indices = (0..params.num_queries)
        .map(|_| challenger.sample_bits(log_global_max_height))
        .collect();
    FriChallenges {
        alpha,
        betas,
        indices,
    }
}

/// The log of the size of the first folding domain.
pub fn log_global_max_height(params: &Params, proof: &PcsProof) -> usize {
    let folds: usize = proof
        .commit_phase_openings
        .iter()
        .map(|opening| opening.log_arity as usize)
        .sum();
    folds + params.log_blowup + params.log_final_poly_len
}

fn reverse_bits_len(x: usize, bits: usize) -> usize {
    if bits == 0 {
        0
    } else {
        x.reverse_bits() >> (usize::BITS as usize - bits)
    }
}

/// The point of index `index` in the bit-reversed subgroup of order
/// `2^log_height`.
fn subgroup_point(log_height: usize, index: usize) -> Val {
    Val::two_adic_generator(log_height).exp_u64(reverse_bits_len(index, log_height) as u64)
}

fn ensure(condition: bool, message: &str) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.to_string())
    }
}

/// Check that the given challenges are those of an accepting run: for every
/// query, the reduced openings computed with `alpha` at the query's index,
/// folded with the `betas` and the proof's sibling values, end at the value of
/// the final polynomial. The Merkle proofs are not looked at.
///
/// A wrong `alpha`, `beta` or index changes a folded value and breaks the
/// last equality, so this pins all of them.
pub fn check_folds(
    params: &Params,
    rounds: &[Round],
    proof: &PcsProof,
    challenges: &FriChallenges,
) -> Result<(), String> {
    let log_blowup = params.log_blowup;
    let num_rounds = proof.commit_phase_commits.len();
    let log_global_max_height = log_global_max_height(params, proof);
    let tallest = rounds
        .iter()
        .flat_map(|round| round.iter().map(|m| m.log_degree + log_blowup))
        .max();
    ensure(
        tallest == Some(log_global_max_height),
        "the number of folding rounds does not match the tallest matrix",
    )?;
    ensure(
        proof.commit_phase_openings.len() == num_rounds && challenges.betas.len() == num_rounds,
        "one opening and one beta per round expected",
    )?;
    ensure(
        proof
            .commit_phase_openings
            .iter()
            .all(|opening| opening.log_arity == 1),
        "only binary folding is handled",
    )?;
    ensure(
        proof.final_poly.len() == 1 << params.log_final_poly_len,
        "final polynomial of the wrong length",
    )?;
    ensure(
        proof.input_openings.len() == rounds.len(),
        "one input opening per commitment expected",
    )?;
    ensure(
        challenges.indices.len() == params.num_queries,
        "one index per query expected",
    )?;

    let log_final_height = log_blowup + params.log_final_poly_len;
    let half = Val::TWO.inverse();
    for (query, &index) in challenges.indices.iter().enumerate() {
        // The reduced openings: per height, the alpha-combination of the
        // quotients `(p(z) - p(x)) / (z - x)` of the matrices of that height,
        // with one running power of alpha per height.
        let mut by_height: BTreeMap<usize, (ExtVal, ExtVal)> = BTreeMap::new();
        for (round, opening) in rounds.iter().zip(&proof.input_openings) {
            ensure(
                opening.opened_values.len() == params.num_queries
                    && opening.opened_values[query].len() == round.len(),
                "one row per query and matrix expected",
            )?;
            for (matrix, row) in round.iter().zip(&opening.opened_values[query]) {
                let log_height = matrix.log_degree + log_blowup;
                let reduced_index = index >> (log_global_max_height - log_height);
                // The committed codeword is over the coset `GENERATOR * H`.
                let x = Val::GENERATOR * subgroup_point(log_height, reduced_index);
                let (alpha_pow, sum) = by_height
                    .entry(log_height)
                    .or_insert((ExtVal::ONE, ExtVal::ZERO));
                for (point, values) in &matrix.points {
                    ensure(
                        values.len() == row.len(),
                        "claimed values do not match the row width",
                    )?;
                    let quotient = (*point - x).inverse();
                    for (&p_at_x, &p_at_z) in row.iter().zip(values) {
                        *sum += *alpha_pow * (p_at_z - p_at_x) * quotient;
                        *alpha_pow *= challenges.alpha;
                    }
                }
            }
        }
        let descending: Vec<(usize, ExtVal)> = by_height
            .into_iter()
            .rev()
            .map(|(log_height, (_, sum))| (log_height, sum))
            .collect();

        // The fold chain.
        let mut openings = descending.iter().peekable();
        let (first_height, first) = *openings.next().ok_or("nothing to fold")?;
        ensure(
            first_height == log_global_max_height,
            "no reduced opening at the top height",
        )?;
        let mut folded = first;
        let mut domain_index = index;
        let mut log_height = log_global_max_height;
        for round in 0..num_rounds {
            let beta = challenges.betas[round];
            let siblings = &proof.commit_phase_openings[round].sibling_values;
            ensure(
                siblings.len() == params.num_queries && siblings[query].len() == 1,
                "one sibling value per query expected",
            )?;
            let sibling = siblings[query][0];
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
            .fold(ExtVal::ZERO, |acc, coeff| acc * x + *coeff);
        ensure(
            eval == folded,
            "a query does not end at the final polynomial",
        )?;
    }
    Ok(())
}
