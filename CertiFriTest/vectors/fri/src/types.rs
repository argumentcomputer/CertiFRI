//! What a vector file holds, and its JSON encoding. The schema is documented
//! in the README.

use crate::config::{
    j_bytes, j_digests, j_ext, j_exts, j_nums, j_val, j_vals, Challenge, Digest, Params, Val,
    PLONKY3_REV,
};
use crate::json::Json;
use crate::merkle::Dim;

/// The claimed values of every column of one matrix at one point.
#[derive(Clone, Debug)]
pub struct PointClaim {
    pub point: Challenge,
    pub values: Vec<Challenge>,
}

#[derive(Clone, Debug)]
pub struct MatrixClaim {
    /// Log of the number of rows before the blowup.
    pub log_degree: usize,
    pub points: Vec<PointClaim>,
}

#[derive(Clone, Debug)]
pub struct BatchClaim {
    pub commitment: Digest,
    pub matrices: Vec<MatrixClaim>,
}

/// One multi-opening proof, in both forms.
#[derive(Clone, Debug)]
pub struct OpeningProof {
    /// `PrunedMerklePaths::sibling_hashes`, as Plonky3 has it.
    pub pruned: Vec<Digest>,
    /// One full authentication path per query.
    pub paths: Vec<Vec<Digest>>,
}

#[derive(Clone, Debug)]
pub struct InputOpening {
    /// `opened_values[query][matrix][column]`.
    pub opened_values: Vec<Vec<Vec<Val>>>,
    pub opening_proof: OpeningProof,
}

#[derive(Clone, Debug)]
pub struct CommitPhaseOpening {
    pub log_arity: usize,
    /// `sibling_values[query]`: one value per query for binary folding.
    pub sibling_values: Vec<Vec<Challenge>>,
    pub opening_proof: OpeningProof,
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub commit_phase_commits: Vec<Digest>,
    pub commit_pow_witnesses: Vec<Val>,
    pub final_poly: Vec<Challenge>,
    pub query_pow_witness: Val,
    pub input_openings: Vec<InputOpening>,
    pub commit_phase_openings: Vec<CommitPhaseOpening>,
}

/// What the verifier derives about one input batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchTrace {
    pub dimensions: Vec<Dim>,
    /// The index each query opens this batch at.
    pub indices: Vec<usize>,
}

/// What the verifier derives about one folding round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundTrace {
    /// Log of the number of rows of the round's committed matrix.
    pub log_height: usize,
    /// The row each query opens.
    pub indices: Vec<usize>,
    /// The two values of that row, per query.
    pub rows: Vec<[Challenge; 2]>,
    /// The folded value each query carries out of the round.
    pub folded: Vec<Challenge>,
}

/// The values the verifier derives on its way to accepting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace {
    pub log_global_max_height: usize,
    pub alpha: Challenge,
    pub betas: Vec<Challenge>,
    pub indices: Vec<usize>,
    pub input_batches: Vec<BatchTrace>,
    /// Per query, `(log_height, value)` by descending height.
    pub reduced_openings: Vec<Vec<(usize, Challenge)>>,
    pub rounds: Vec<RoundTrace>,
    /// Per query, the point the final polynomial is evaluated at.
    pub final_points: Vec<Val>,
    /// Per query, the value of the final polynomial there.
    pub final_evals: Vec<Challenge>,
}

pub struct Vector {
    pub name: &'static str,
    pub params: Params,
    pub claims: Vec<BatchClaim>,
    pub proof: Proof,
    pub debug: Trace,
}

fn j_params(p: &Params) -> Json {
    Json::Obj(vec![
        ("log_blowup", Json::num(p.log_blowup)),
        ("log_final_poly_len", Json::num(p.log_final_poly_len)),
        ("max_log_arity", Json::num(p.max_log_arity)),
        ("num_queries", Json::num(p.num_queries)),
        (
            "commit_proof_of_work_bits",
            Json::num(p.commit_proof_of_work_bits),
        ),
        (
            "query_proof_of_work_bits",
            Json::num(p.query_proof_of_work_bits),
        ),
    ])
}

fn j_claims(claims: &[BatchClaim]) -> Json {
    Json::arr(claims, |batch| {
        Json::Obj(vec![
            ("commitment", j_bytes(&batch.commitment)),
            (
                "matrices",
                Json::arr(&batch.matrices, |matrix| {
                    Json::Obj(vec![
                        ("log_degree", Json::num(matrix.log_degree)),
                        (
                            "points",
                            Json::arr(&matrix.points, |claim| {
                                Json::Obj(vec![
                                    ("point", j_ext(claim.point)),
                                    ("values", j_exts(&claim.values)),
                                ])
                            }),
                        ),
                    ])
                }),
            ),
        ])
    })
}

fn j_opening_proof(proof: &OpeningProof) -> Json {
    Json::Obj(vec![
        (
            "pruned",
            Json::Obj(vec![("sibling_hashes", j_digests(&proof.pruned))]),
        ),
        ("paths", Json::arr(&proof.paths, |path| j_digests(path))),
    ])
}

fn j_proof(proof: &Proof) -> Json {
    Json::Obj(vec![
        (
            "commit_phase_commits",
            j_digests(&proof.commit_phase_commits),
        ),
        ("commit_pow_witnesses", j_vals(&proof.commit_pow_witnesses)),
        ("final_poly", j_exts(&proof.final_poly)),
        ("query_pow_witness", j_val(proof.query_pow_witness)),
        (
            "input_openings",
            Json::arr(&proof.input_openings, |opening| {
                Json::Obj(vec![
                    (
                        "opened_values",
                        Json::arr(&opening.opened_values, |rows| {
                            Json::arr(rows, |row| j_vals(row))
                        }),
                    ),
                    ("opening_proof", j_opening_proof(&opening.opening_proof)),
                ])
            }),
        ),
        (
            "commit_phase_openings",
            Json::arr(&proof.commit_phase_openings, |opening| {
                Json::Obj(vec![
                    ("log_arity", Json::num(opening.log_arity)),
                    (
                        "sibling_values",
                        Json::arr(&opening.sibling_values, |values| j_exts(values)),
                    ),
                    ("opening_proof", j_opening_proof(&opening.opening_proof)),
                ])
            }),
        ),
    ])
}

fn j_debug(trace: &Trace) -> Json {
    Json::Obj(vec![
        (
            "log_global_max_height",
            Json::num(trace.log_global_max_height),
        ),
        ("alpha", j_ext(trace.alpha)),
        ("betas", j_exts(&trace.betas)),
        ("indices", j_nums(&trace.indices)),
        (
            "input_batches",
            Json::arr(&trace.input_batches, |batch| {
                Json::Obj(vec![
                    (
                        "dimensions",
                        Json::arr(&batch.dimensions, |dim| {
                            Json::Obj(vec![
                                ("width", Json::num(dim.width)),
                                ("log_height", Json::num(dim.log_height)),
                            ])
                        }),
                    ),
                    ("indices", j_nums(&batch.indices)),
                ])
            }),
        ),
        (
            "reduced_openings",
            Json::arr(&trace.reduced_openings, |openings| {
                Json::arr(openings, |(log_height, value)| {
                    Json::Obj(vec![
                        ("log_height", Json::num(*log_height)),
                        ("value", j_ext(*value)),
                    ])
                })
            }),
        ),
        (
            "rounds",
            Json::arr(&trace.rounds, |round| {
                Json::Obj(vec![
                    ("log_height", Json::num(round.log_height)),
                    ("indices", j_nums(&round.indices)),
                    ("rows", Json::arr(&round.rows, |row| j_exts(row))),
                    ("folded", j_exts(&round.folded)),
                ])
            }),
        ),
        ("final_points", j_vals(&trace.final_points)),
        ("final_evals", j_exts(&trace.final_evals)),
    ])
}

impl Vector {
    pub fn to_json(&self) -> Json {
        Json::Obj(vec![
            ("name", Json::str(self.name)),
            ("plonky3_rev", Json::str(PLONKY3_REV)),
            ("params", j_params(&self.params)),
            ("claims", j_claims(&self.claims)),
            ("proof", j_proof(&self.proof)),
            ("debug", j_debug(&self.debug)),
        ])
    }
}
