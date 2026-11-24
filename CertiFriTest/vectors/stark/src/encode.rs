//! The JSON encoding of what a vector file holds. The schema is documented in
//! the README.

use multi_stark::batch::BatchProof;
use multi_stark::expr::{RowOffset, Source};
use multi_stark::graph::{ConstraintGraph, Node, NodeId};
use multi_stark::prover::Proof;
use multi_stark::system::{Circuit, System};
use multi_stark::types::PcsProof;

use crate::config::{
    Config, ExtVal, Val, j_bools, j_bytes, j_commitment, j_digests, j_ext, j_exts, j_nums, j_val,
    j_vals,
};
use crate::json::Json;
use crate::replay::{BatchDebug, Debug};

fn j_id(id: NodeId) -> Json {
    Json::num(id.index())
}

fn j_node(node: &Node<Val>) -> Json {
    let op = |name: &str| ("op", Json::str(name));
    match *node {
        Node::Const(value) => Json::Obj(vec![op("const"), ("value", j_val(value))]),
        Node::Var(col) => Json::Obj(vec![
            op("var"),
            (
                "source",
                Json::str(match col.source {
                    Source::Preprocessed => "preprocessed",
                    Source::Main => "main",
                    Source::Stage2 => "stage2",
                }),
            ),
            ("next", Json::Bool(col.offset == RowOffset::Next)),
            ("index", Json::num(col.index as usize)),
        ]),
        Node::Public(index) => Json::Obj(vec![op("public"), ("index", Json::num(index as usize))]),
        Node::IsFirstRow => Json::Obj(vec![op("is_first_row")]),
        Node::IsLastRow => Json::Obj(vec![op("is_last_row")]),
        Node::IsTransition => Json::Obj(vec![op("is_transition")]),
        Node::Add(a, b) => Json::Obj(vec![op("add"), ("a", j_id(a)), ("b", j_id(b))]),
        Node::Sub(a, b) => Json::Obj(vec![op("sub"), ("a", j_id(a)), ("b", j_id(b))]),
        Node::Mul(a, b) => Json::Obj(vec![op("mul"), ("a", j_id(a)), ("b", j_id(b))]),
        Node::Neg(a) => Json::Obj(vec![op("neg"), ("a", j_id(a))]),
    }
}

fn j_graph(graph: &ConstraintGraph<Val>) -> Json {
    Json::Obj(vec![
        ("nodes", Json::arr(&graph.nodes, j_node)),
        ("zeros", Json::arr(&graph.zeros, |id| j_id(*id))),
        (
            "lookups",
            Json::arr(&graph.lookups, |lookup| {
                Json::Obj(vec![
                    ("multiplicity", j_id(lookup.multiplicity)),
                    ("args", Json::arr(&lookup.args, |id| j_id(*id))),
                ])
            }),
        ),
    ])
}

fn j_circuit(circuit: &Circuit<Val>) -> Json {
    Json::Obj(vec![
        ("main_width", Json::num(circuit.main_width)),
        ("preprocessed_width", Json::num(circuit.preprocessed_width)),
        (
            "preprocessed_height",
            Json::num(circuit.preprocessed_height),
        ),
        ("num_lookups", Json::num(circuit.num_lookups)),
        ("stage_2_width", Json::num(circuit.stage_2_width)),
        ("num_publics", Json::num(circuit.num_publics)),
        ("lookup_group_size", Json::num(circuit.lookup_group_size)),
        ("constraint_count", Json::num(circuit.constraint_count())),
        (
            "max_constraint_degree",
            Json::num(circuit.max_constraint_degree()),
        ),
        ("quotient_degree", Json::num(circuit.quotient_degree())),
        ("graph", j_graph(&circuit.graph)),
    ])
}

pub fn j_system(system: &System<Config>) -> Json {
    Json::Obj(vec![
        (
            "preprocessed_commit",
            Json::opt(system.preprocessed_commit.as_ref(), j_commitment),
        ),
        (
            "preprocessed_indices",
            Json::arr(&system.preprocessed_indices, |slot| {
                Json::opt(*slot, Json::num)
            }),
        ),
        ("circuits", Json::arr(&system.circuits, j_circuit)),
    ])
}

fn j_pruned(sibling_hashes: &[[u8; 32]]) -> Json {
    Json::Obj(vec![(
        "pruned",
        Json::Obj(vec![("sibling_hashes", j_digests(sibling_hashes))]),
    )])
}

fn j_fri_proof(proof: &PcsProof) -> Json {
    Json::Obj(vec![
        (
            "commit_phase_commits",
            Json::arr(&proof.commit_phase_commits, j_commitment),
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
                    (
                        "opening_proof",
                        j_pruned(&opening.opening_proof.sibling_hashes),
                    ),
                ])
            }),
        ),
        (
            "commit_phase_openings",
            Json::arr(&proof.commit_phase_openings, |opening| {
                Json::Obj(vec![
                    ("log_arity", Json::num(opening.log_arity as usize)),
                    (
                        "sibling_values",
                        Json::arr(&opening.sibling_values, |values| j_exts(values)),
                    ),
                    (
                        "opening_proof",
                        j_pruned(&opening.opening_proof.sibling_hashes),
                    ),
                ])
            }),
        ),
    ])
}

/// `[matrix][point][column]`.
fn j_opened(round: &Vec<Vec<Vec<ExtVal>>>) -> Json {
    Json::arr(round, |matrix| Json::arr(matrix, |point| j_exts(point)))
}

pub fn j_stark_proof(proof: &Proof<Config>) -> Json {
    let log_degrees: Vec<usize> = proof.log_degrees.iter().map(|&d| d as usize).collect();
    Json::Obj(vec![
        ("active", j_bools(&proof.active)),
        (
            "commitments",
            Json::Obj(vec![
                (
                    "stage_1_trace",
                    j_commitment(&proof.commitments.stage_1_trace),
                ),
                (
                    "stage_2_trace",
                    j_commitment(&proof.commitments.stage_2_trace),
                ),
                (
                    "quotient_chunks",
                    j_commitment(&proof.commitments.quotient_chunks),
                ),
            ]),
        ),
        (
            "intermediate_accumulators",
            j_exts(&proof.intermediate_accumulators),
        ),
        ("log_degrees", j_nums(&log_degrees)),
        (
            "quotient_opened_values",
            j_opened(&proof.quotient_opened_values),
        ),
        (
            "preprocessed_opened_values",
            Json::opt(proof.preprocessed_opened_values.as_ref(), j_opened),
        ),
        (
            "stage_1_opened_values",
            j_opened(&proof.stage_1_opened_values),
        ),
        (
            "stage_2_opened_values",
            j_opened(&proof.stage_2_opened_values),
        ),
        ("opening_proof", j_fri_proof(&proof.opening_proof)),
    ])
}

fn j_claims(claims: &[Vec<Val>]) -> Json {
    Json::arr(claims, |claim| j_vals(claim))
}

pub fn j_debug(debug: &Debug) -> Json {
    Json::Obj(vec![
        ("lookup_challenge", j_ext(debug.lookup_challenge)),
        ("fingerprint_challenge", j_ext(debug.fingerprint_challenge)),
        ("constraint_challenge", j_ext(debug.constraint_challenge)),
        ("zeta", j_ext(debug.zeta)),
        ("fri_alpha", j_ext(debug.fri_alpha)),
        ("fri_betas", j_exts(&debug.fri_betas)),
        ("fri_indices", j_nums(&debug.fri_indices)),
    ])
}

pub fn j_single(claims: &[Vec<Val>], proof: &Proof<Config>, debug: &Debug) -> Json {
    Json::Obj(vec![
        ("claims", j_claims(claims)),
        ("proof", j_stark_proof(proof)),
        ("debug", j_debug(debug)),
    ])
}

pub fn j_batch(batch: &BatchProof<Config>, debug: &BatchDebug) -> Json {
    let preamble = &batch.preamble;
    Json::Obj(vec![
        (
            "preamble",
            Json::Obj(vec![
                (
                    "headers",
                    Json::arr(&preamble.headers, |header| {
                        let log_degrees: Vec<usize> =
                            header.log_degrees.iter().map(|&d| d as usize).collect();
                        Json::Obj(vec![
                            ("active", j_bools(&header.active)),
                            ("stage_1_trace", j_commitment(&header.stage_1_trace)),
                            ("log_degrees", j_nums(&log_degrees)),
                            ("claims", j_claims(&header.claims)),
                        ])
                    }),
                ),
                (
                    "messages",
                    Json::arr(&preamble.messages, |message| {
                        Json::Obj(vec![
                            ("args", j_vals(&message.args)),
                            ("multiplicity", j_val(message.multiplicity)),
                        ])
                    }),
                ),
            ]),
        ),
        ("proofs", Json::arr(&batch.proofs, j_stark_proof)),
        (
            "debug",
            Json::Obj(vec![
                ("lookup_challenge", j_ext(debug.lookup_challenge)),
                ("fingerprint_challenge", j_ext(debug.fingerprint_challenge)),
                ("shards", Json::arr(&debug.shards, j_debug)),
            ]),
        ),
    ])
}

/// The bytes of the challenger seed.
pub fn j_seed(seed: &[u8]) -> Json {
    j_bytes(seed)
}
