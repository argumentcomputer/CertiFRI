//! Generator of the STARK test vectors read by the Lean tests.
//!
//! It proves small statements with multi-stark's prover in its production
//! configuration (`GoldilocksBlake3Config`), checks every proof with
//! multi-stark's own verifier, and writes everything that verifier reads as
//! JSON, next to the challenges it derives. See the README for the schema.
//!
//! `cargo run --release` rewrites the checked-in files in this directory.
//! `cargo run --release -- --out <dir>` writes them to another directory.

mod circuits;
mod config;
mod encode;
mod fri;
mod json;
mod replay;

use std::path::{Path, PathBuf};

use multi_stark::batch::{BatchMessage, BatchProof, ShardInput};
use multi_stark::config::ProofConfig;
use multi_stark::expr::{RowOffset, Source};
use multi_stark::graph::Node;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::p3_matrix::dense::RowMajorMatrix;
use multi_stark::prover::Proof;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use p3_blake3::Blake3;

use circuits::{cubes, empty, fibonacci};
use config::{
    Challenger, Config, EXTENSION_DEGREE, ExtVal, MULTI_STARK_REV, PLONKY3_REV, Params, Val,
};
use json::Json;
use replay::Start;

/// Checked-in files stay below this size.
const MAX_CHECKED_IN_BYTES: usize = 150 * 1024;

/// One shard of a batch: its claims and its traces.
struct Shard {
    claims: Vec<Vec<Val>>,
    traces: Vec<RowMajorMatrix<Val>>,
}

enum Statement {
    /// `prove_multiple_claims` / `verify_multiple_claims`.
    Single {
        claims: Vec<Vec<Val>>,
        traces: Vec<RowMajorMatrix<Val>>,
    },
    /// `prove_batch` / `verify_batch`.
    Batch {
        shards: Vec<Shard>,
        messages: Vec<BatchMessage<Config>>,
    },
}

struct Case {
    name: &'static str,
    params: Params,
    circuits: Vec<CircuitInputs<Val>>,
    statement: Statement,
}

/// The vectors kept in the repository.
fn cases() -> Vec<Case> {
    let pairs = [(1, 2), (3, 4), (2, 7)];
    let cube_claims: Vec<Vec<Val>> = pairs.iter().map(|&pair| cubes::claim(pair)).collect();
    vec![
        // Two circuits of different heights joined by lookups, two claims,
        // every row selector, no fixed columns, one quotient chunk each.
        Case {
            name: "lookup",
            params: Params {
                log_blowup: 1,
                cap_height: 0,
                log_final_poly_len: 0,
                max_log_arity: 1,
                num_queries: 3,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 0,
            },
            circuits: fibonacci::circuits(),
            statement: Statement::Single {
                claims: vec![fibonacci::claim(5), fibonacci::claim(7)],
                traces: vec![
                    fibonacci::sequence(3, &[2, 5, 7]),
                    fibonacci::reader(&[Some((2, false)), Some((5, true)), Some((7, true)), None]),
                ],
            },
        },
        // Fixed columns, grouped lookups, extension constraints, quotients of
        // one, two and four chunks, an inactive circuit, grinding.
        Case {
            name: "fixed",
            params: Params {
                log_blowup: 2,
                cap_height: 0,
                log_final_poly_len: 0,
                max_log_arity: 1,
                num_queries: 4,
                commit_proof_of_work_bits: 2,
                query_proof_of_work_bits: 4,
            },
            circuits: cubes::circuits(),
            statement: Statement::Single {
                claims: cube_claims.clone(),
                traces: vec![
                    cubes::sums(&pairs, 2),
                    cubes::table(&pairs),
                    empty(cubes::SPARE_WIDTH),
                    cubes::rounds(),
                ],
            },
        },
        // Two shards of the Fibonacci system. Shard 0 holds the sequence and
        // reads one row of it; shard 1 reads two more. One claim sits in a
        // header; the preamble's messages stand in for a second claim and
        // pull the row that no shard reads.
        Case {
            name: "batch",
            params: Params {
                log_blowup: 1,
                cap_height: 0,
                log_final_poly_len: 0,
                max_log_arity: 1,
                num_queries: 3,
                commit_proof_of_work_bits: 1,
                query_proof_of_work_bits: 0,
            },
            circuits: fibonacci::circuits(),
            statement: Statement::Batch {
                shards: vec![
                    Shard {
                        claims: vec![fibonacci::claim(2)],
                        traces: vec![
                            fibonacci::sequence(3, &[2, 4, 5, 7]),
                            fibonacci::reader(&[Some((2, true)), None]),
                        ],
                    },
                    Shard {
                        claims: vec![],
                        traces: vec![
                            empty(fibonacci::SEQUENCE_WIDTH),
                            fibonacci::reader(&[Some((5, true)), Some((7, false))]),
                        ],
                    },
                ],
                messages: vec![
                    BatchMessage::push(fibonacci::claim(5)),
                    BatchMessage::pull(fibonacci::row_message(4)),
                ],
            },
        },
        // The system of `fixed` with a final polynomial of two coefficients,
        // and with `rounds` inactive: its fixed trace stays committed and is
        // opened at one point.
        Case {
            name: "sparse",
            params: Params {
                log_blowup: 2,
                cap_height: 0,
                log_final_poly_len: 1,
                max_log_arity: 1,
                num_queries: 3,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 3,
            },
            circuits: cubes::circuits(),
            statement: Statement::Single {
                claims: cube_claims,
                traces: vec![
                    cubes::sums(&pairs, 2),
                    cubes::table(&pairs),
                    empty(cubes::SPARE_WIDTH),
                    empty(cubes::ROUNDS_WIDTH),
                ],
            },
        },
    ]
}

fn slices(claims: &[Vec<Val>]) -> Vec<&[Val]> {
    claims.iter().map(Vec::as_slice).collect()
}

/// Copies of the proof with one opened value changed, one per kind of
/// opening.
fn tampered(proof: &Proof<Config>) -> Vec<(&'static str, Proof<Config>)> {
    let mut copies = vec![];
    let mut copy = proof.clone();
    copy.stage_1_opened_values[0][0][0] += ExtVal::ONE;
    copies.push(("stage 1", copy));
    let mut copy = proof.clone();
    *copy.stage_2_opened_values.last_mut().unwrap()[1]
        .last_mut()
        .unwrap() += ExtVal::ONE;
    copies.push(("stage 2", copy));
    let mut copy = proof.clone();
    copy.quotient_opened_values[0][0][0] += ExtVal::ONE;
    copies.push(("quotient", copy));
    if proof.preprocessed_opened_values.is_some() {
        let mut copy = proof.clone();
        copy.preprocessed_opened_values.as_mut().unwrap()[0][0][0] += ExtVal::ONE;
        copies.push(("preprocessed", copy));
    }
    copies
}

/// What a proof covers, for the log of a run.
fn describe(system: &System<Config>, proof: &Proof<Config>) -> String {
    let active: Vec<usize> = (0..proof.active.len())
        .filter(|&i| proof.active[i])
        .collect();
    let fri = &proof.opening_proof;
    format!(
        "active {:?}, log degrees {:?}, quotient degrees {:?}, {} folding rounds, {} final coefficients",
        active,
        proof.log_degrees,
        active
            .iter()
            .map(|&i| system.circuits[i].quotient_degree())
            .collect::<Vec<_>>(),
        fri.commit_phase_commits.len(),
        fri.final_poly.len(),
    )
}

/// Whether some node of some circuit satisfies the predicate.
fn some_node(system: &System<Config>, predicate: impl Fn(&Node<Val>) -> bool) -> bool {
    system
        .circuits
        .iter()
        .any(|circuit| circuit.graph.nodes.iter().any(&predicate))
}

fn next_row_of(source: Source) -> impl Fn(&Node<Val>) -> bool {
    move |node| matches!(node, Node::Var(col) if col.source == source && col.offset == RowOffset::Next)
}

/// The features each vector is kept for. A change to the circuits that loses
/// one of them fails here and not silently.
fn check_coverage(name: &str, system: &System<Config>, proofs: &[&Proof<Config>]) {
    let inactive = |with_fixed: bool| {
        proofs.iter().any(|proof| {
            (0..proof.active.len())
                .any(|i| !proof.active[i] && system.preprocessed_indices[i].is_some() == with_fixed)
        })
    };
    let selectors = some_node(system, |n| matches!(n, Node::IsFirstRow))
        && some_node(system, |n| matches!(n, Node::IsLastRow))
        && some_node(system, |n| matches!(n, Node::IsTransition));
    match name {
        "lookup" | "batch" => {
            assert!(system.preprocessed_commit.is_none());
            assert!(selectors && some_node(system, next_row_of(Source::Main)));
            assert!(system.circuits.iter().all(|c| c.quotient_degree() == 1));
            assert!(proofs[0].log_degrees.len() == 2);
            assert!(proofs[0].log_degrees[0] != proofs[0].log_degrees[1]);
            if name == "batch" {
                assert!(proofs.len() >= 2 && inactive(false));
            }
        }
        "fixed" | "sparse" => {
            assert!(system.preprocessed_commit.is_some());
            assert!(selectors && some_node(system, next_row_of(Source::Preprocessed)));
            assert!(some_node(system, |n| matches!(n, Node::Public(_))));
            assert!(some_node(
                system,
                |n| matches!(n, Node::Var(col) if col.source == Source::Stage2)
            ));
            assert!(system.circuits.iter().any(|c| {
                c.lookup_group_size >= 2
                    && c.num_lookups >= 3
                    && c.num_lookups % c.lookup_group_size != 0
            }));
            assert!(system.circuits.iter().any(|c| c.num_lookups == 0));
            assert!(inactive(false));
            if name == "fixed" {
                assert!(!inactive(true));
                let degrees: Vec<usize> = (0..system.circuits.len())
                    .filter(|&i| proofs[0].active[i])
                    .map(|i| system.circuits[i].quotient_degree())
                    .collect();
                assert!([1, 2, 4].iter().all(|q| degrees.contains(q)));
            } else {
                assert!(inactive(true));
                assert!(proofs[0].opening_proof.final_poly.len() == 2);
            }
        }
        other => panic!("no coverage is stated for {other}"),
    }
}

/// Whether two queries draw the same index.
fn has_repeated_index(indices: &[usize]) -> bool {
    (0..indices.len()).any(|i| indices[..i].contains(&indices[i]))
}

/// Prove the case, check the proof and the replayed transcript, and return
/// the content of its file with lines for the log.
fn generate(case: Case) -> (Json, Vec<String>) {
    let params = case.params;
    assert_eq!((params.max_log_arity, params.cap_height), (1, 0));
    let config = params.config();

    // The seed, recomputed from the parameters, is the one multi-stark uses.
    let seed = params.seed();
    assert_eq!(seed, config.challenger_seed());
    let from_seed = || Challenger::from_hasher(seed.clone(), Blake3);
    let max_log_degree = config.max_log_degree();

    let (system, key) = System::new(config, case.circuits);
    let mut log = vec![format!(
        "{}: {} circuits, main widths {:?}, fixed widths {:?}, stage-2 widths {:?}, fixed slots {:?}",
        case.name,
        system.circuits.len(),
        system
            .circuits
            .iter()
            .map(|c| c.main_width)
            .collect::<Vec<_>>(),
        system
            .circuits
            .iter()
            .map(|c| c.preprocessed_width)
            .collect::<Vec<_>>(),
        system
            .circuits
            .iter()
            .map(|c| c.stage_2_width)
            .collect::<Vec<_>>(),
        system.preprocessed_indices,
    )];

    let statement = match case.statement {
        Statement::Single { claims, traces } => {
            let witness = SystemWitness::from_stage_1(traces, &system);
            let proof = system.prove_multiple_claims(&key, &slices(&claims), witness);

            // multi-stark accepts the proof, and rejects it once one opened
            // value is changed.
            system
                .verify_multiple_claims(&slices(&claims), &proof)
                .expect("multi-stark rejects its own proof");
            for (kind, copy) in tampered(&proof) {
                assert!(
                    system
                        .verify_multiple_claims(&slices(&claims), &copy)
                        .is_err(),
                    "multi-stark accepts a changed {kind} opening"
                );
            }

            // The transcript gives the same challenges replayed from the
            // recomputed seed, from multi-stark's own initial challenger, and
            // from the bytes absorbed before the first challenge.
            let replay_single =
                |start| replay::replay_single(&system, &params, start, &claims, &proof);
            let debug = replay_single(Start::Challenger(from_seed()));
            let from_config = system.config.initialise_challenger();
            assert_eq!(debug, replay_single(Start::Challenger(from_config)));
            assert_eq!(debug, replay_single(Start::Bytes(&seed)));

            assert!(!claims.is_empty());
            check_coverage(case.name, &system, &[&proof]);
            if case.name == "fixed" {
                assert!(has_repeated_index(&debug.fri_indices));
            }
            log.push(format!(
                "  {} claims, {}",
                claims.len(),
                describe(&system, &proof)
            ));
            ("single", encode::j_single(&claims, &proof, &debug))
        }
        Statement::Batch { shards, messages } => {
            let inputs = shards
                .into_iter()
                .map(|shard| ShardInput {
                    claims: shard.claims,
                    witness: SystemWitness::from_stage_1(shard.traces, &system),
                })
                .collect();
            let batch: BatchProof<Config> = system.prove_batch(&key, inputs, messages);

            system
                .verify_batch(&batch)
                .expect("multi-stark rejects its own batch");
            for shard in 0..batch.proofs.len() {
                for (kind, copy) in tampered(&batch.proofs[shard]) {
                    let mut changed = batch.clone();
                    changed.proofs[shard] = copy;
                    assert!(
                        system.verify_batch(&changed).is_err(),
                        "multi-stark accepts a changed {kind} opening in shard {shard}"
                    );
                }
            }

            let replay_batch = |start| replay::replay_batch(&system, &params, start, &batch);
            let debug = replay_batch(Start::Challenger(from_seed()));
            let from_config = system.config.initialise_challenger();
            assert_eq!(debug, replay_batch(Start::Challenger(from_config)));
            assert_eq!(debug, replay_batch(Start::Bytes(&seed)));

            let preamble = &batch.preamble;
            assert!(preamble.headers.iter().any(|h| !h.claims.is_empty()));
            assert!(preamble.messages.len() >= 2);
            check_coverage(case.name, &system, &batch.proofs.iter().collect::<Vec<_>>());
            log.push(format!("  {} messages", preamble.messages.len()));
            for (shard, proof) in batch.proofs.iter().enumerate() {
                log.push(format!(
                    "  shard {shard}: {} claims, {}",
                    preamble.headers[shard].claims.len(),
                    describe(&system, proof)
                ));
            }
            ("batch", encode::j_batch(&batch, &debug))
        }
    };

    let file = Json::Obj(vec![
        ("name", Json::str(case.name)),
        ("multi_stark_rev", Json::str(MULTI_STARK_REV)),
        ("plonky3_rev", Json::str(PLONKY3_REV)),
        ("seed", encode::j_seed(&seed)),
        ("params", params.to_json()),
        ("max_log_degree", Json::num(max_log_degree)),
        ("extension_degree", Json::num(EXTENSION_DEGREE)),
        ("system", encode::j_system(&system)),
        statement,
    ]);
    (file, log)
}

fn write(path: &Path, value: &Json) {
    let text = value.to_file_text();
    assert!(
        text.len() <= MAX_CHECKED_IN_BYTES,
        "{} is {} bytes, above the limit of {MAX_CHECKED_IN_BYTES}",
        path.display(),
        text.len()
    );
    std::fs::write(path, &text).unwrap_or_else(|e| panic!("writing {}: {e}", path.display()));
    println!("wrote {} ({} bytes)", path.display(), text.len());
}

fn main() {
    let mut out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => out_dir = PathBuf::from(args.next().expect("--out takes a directory")),
            other => panic!("unknown argument {other}; usage: [--out <dir>]"),
        }
    }
    for case in cases() {
        let name = case.name;
        let (file, log) = generate(case);
        for line in log {
            println!("{line}");
        }
        write(&out_dir.join(format!("{name}.json")), &file);
    }
}
