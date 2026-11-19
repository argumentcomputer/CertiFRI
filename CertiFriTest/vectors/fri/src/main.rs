//! Generator of the FRI test vectors read by the Lean tests.
//!
//! It commits to matrices and opens them with Plonky3's `TwoAdicFriPcs` in the
//! configuration of the certified verifier, checks every proof with Plonky3's
//! own verifier, and writes everything a verifier needs as JSON, next to
//! known-answer values for the primitives. See the README for the schema.
//!
//! `cargo run --release` rewrites the checked-in files in this directory.
//! `cargo run --release -- --prod <file>` also writes the large
//! production-sized vector to `<file>`.

mod config;
mod json;
mod merkle;
mod model;
mod primitives;
mod reference;
mod types;
mod vector;

use std::path::{Path, PathBuf};

use config::Params;
use json::Json;
use vector::{CaseSpec, MatrixSpec};

/// Checked-in files stay below this size.
const MAX_CHECKED_IN_BYTES: usize = 300 * 1024;

fn matrix(log_degree: usize, width: usize, points: &'static [usize]) -> MatrixSpec {
    MatrixSpec {
        log_degree,
        width,
        points,
    }
}

/// The vectors kept in the repository.
fn cases() -> Vec<CaseSpec> {
    vec![
        // One batch, two heights, one point each, no grinding.
        CaseSpec {
            name: "small",
            seed: 1,
            params: Params {
                log_blowup: 1,
                log_final_poly_len: 0,
                max_log_arity: 1,
                num_queries: 3,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 0,
            },
            num_points: 2,
            batches: vec![vec![matrix(3, 2, &[0]), matrix(2, 3, &[1])]],
        },
        // Two batches of different maximal heights, matrices sharing a height,
        // one or two points per matrix, a final polynomial of two
        // coefficients, grinding in both phases. The shortest matrix has 2^2
        // rows: when the final polynomial has more than one coefficient,
        // Plonky3's prover refuses a matrix whose codeword is not taller than
        // the final domain (the assertion on `log_min_height` in `prove_fri`).
        CaseSpec {
            name: "mixed",
            seed: 2,
            params: Params {
                log_blowup: 2,
                log_final_poly_len: 1,
                max_log_arity: 1,
                num_queries: 5,
                commit_proof_of_work_bits: 3,
                query_proof_of_work_bits: 5,
            },
            num_points: 3,
            batches: vec![
                vec![
                    matrix(5, 3, &[0, 1]),
                    matrix(3, 1, &[0]),
                    matrix(5, 2, &[2, 0]),
                ],
                vec![matrix(4, 2, &[1]), matrix(2, 4, &[0, 2])],
            ],
        },
        // Matrices of one row, next to a taller one and alone in a batch. With
        // this seed two of the four queries draw the same index.
        CaseSpec {
            name: "const",
            seed: 5,
            params: Params {
                log_blowup: 1,
                log_final_poly_len: 0,
                max_log_arity: 1,
                num_queries: 4,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 4,
            },
            num_points: 2,
            batches: vec![
                vec![matrix(3, 2, &[0]), matrix(0, 1, &[0])],
                vec![matrix(0, 2, &[1])],
            ],
        },
        // A matrix wide enough that one leaf and the transcript each span
        // several 1024-byte BLAKE3 chunks, and a final polynomial of four
        // coefficients.
        CaseSpec {
            name: "wide",
            seed: 6,
            params: Params {
                log_blowup: 1,
                log_final_poly_len: 2,
                max_log_arity: 1,
                num_queries: 3,
                commit_proof_of_work_bits: 0,
                query_proof_of_work_bits: 8,
            },
            num_points: 2,
            batches: vec![vec![matrix(4, 130, &[0, 1]), matrix(3, 5, &[0])]],
        },
    ]
}

/// A vector of production size. Too large to keep in the repository.
fn prod_case() -> CaseSpec {
    CaseSpec {
        name: "prod",
        seed: 4,
        params: Params {
            log_blowup: 2,
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 100,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 16,
        },
        num_points: 2,
        batches: vec![
            vec![matrix(10, 20, &[0, 1]), matrix(9, 8, &[0, 1])],
            vec![matrix(10, 12, &[0]), matrix(8, 6, &[0])],
        ],
    }
}

fn write(path: &Path, value: &Json, max_bytes: Option<usize>) {
    let text = value.to_file_text();
    if let Some(max_bytes) = max_bytes {
        assert!(
            text.len() <= max_bytes,
            "{} is {} bytes, above the limit of {max_bytes}",
            path.display(),
            text.len()
        );
    }
    std::fs::write(path, &text).unwrap_or_else(|e| panic!("writing {}: {e}", path.display()));
    println!("wrote {} ({} bytes)", path.display(), text.len());
}

fn main() {
    let mut out_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mut prod_path: Option<PathBuf> = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--out" => out_dir = PathBuf::from(args.next().expect("--out takes a directory")),
            "--prod" => prod_path = Some(PathBuf::from(args.next().expect("--prod takes a file"))),
            other => panic!("unknown argument {other}; usage: [--out <dir>] [--prod <file>]"),
        }
    }

    for spec in cases() {
        let vector = vector::generate(&spec);
        println!("{}", vector::summary(&vector));
        write(
            &out_dir.join(format!("{}.json", spec.name)),
            &vector.to_json(),
            Some(MAX_CHECKED_IN_BYTES),
        );
    }
    write(
        &out_dir.join("primitives.json"),
        &primitives::primitives(),
        Some(MAX_CHECKED_IN_BYTES),
    );
    if let Some(path) = prod_path {
        let vector = vector::generate(&prod_case());
        println!("{}", vector::summary(&vector));
        write(&path, &vector.to_json(), None);
    }
}
