//! Regression tests for audit finding IX-3 (lanes F4-1, O7-1, Z2): with
//! `cap_height > 0`, a Merkle cap did not bind a committed matrix shorter
//! than the cap layer, and a prover could forge a proof of a false claim.
//!
//! The verifier now rejects every opening of a commitment that holds such a
//! matrix. The forged proofs in `tests/fixtures/` were produced by the audit
//! (lane O7, job O7-3) against the unmodified verifier at CertiFRI `9543110`,
//! which accepted them.
#![cfg(not(feature = "cuda"))]

use multi_stark::expr::Expr;
use multi_stark::lookup::Lookup;
use multi_stark::p3_adapter::spill::SpillableMmcs;
use multi_stark::p3_adapter::spill_zk::HidingSpillableMmcs;
use multi_stark::prover::Proof;
use multi_stark::system::{CircuitInputs, ProverKey, System, SystemWitness};
use multi_stark::types::{CommitmentParameters, FriParameters, GoldilocksBlake3V6Config, Val};
use multi_stark::verifier::VerificationError;
use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::PrimeCharacteristicRing;
use p3_fri::verifier::FriError;
use p3_matrix::Dimensions;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeError;

fn mat(h: usize, w: usize, seed: u64) -> RowMajorMatrix<Val> {
    RowMajorMatrix::new(
        (0..h * w)
            .map(|i| Val::from_u64(seed.wrapping_mul(1_000_003).wrapping_add(i as u64 * 7 + 1)))
            .collect(),
        w,
    )
}

/// MMCS level (the audit's `poc/O7/f4-1/o7_cap.rs`, inverted): commit a
/// 64-row matrix and a short one. When the short matrix lies below the cap
/// layer every opening is rejected, honest or tampered; otherwise honest
/// openings verify and tampering with either matrix is rejected.
fn probe<M: Mmcs<Val, Error = MerkleTreeError>>(name: &str, mk: impl Fn(usize) -> M) {
    const TALL: usize = 64;
    for cap in 0..=6usize {
        for log_short in 0..=6usize {
            let short_h = 1usize << log_short;
            let mmcs = mk(cap);
            let dims = [
                Dimensions {
                    width: 4,
                    height: TALL,
                },
                Dimensions {
                    width: 3,
                    height: short_h,
                },
            ];
            let (commit, data) = mmcs.commit(vec![mat(TALL, 4, 1), mat(short_h, 3, 2)]);
            let unbound = short_h < (1usize << cap.min(6));
            let ctx = format!("{name} cap={cap} short_h={short_h}");
            for index in [0usize, 5, 37, 63] {
                let op = mmcs.open_batch(index, &data);
                let verify = |rows: &[Vec<Val>]| {
                    mmcs.verify_batch(
                        &commit,
                        &dims,
                        index,
                        BatchOpeningRef::new(rows, &op.opening_proof),
                    )
                };
                let honest = verify(&op.opened_values);
                let mut short_tampered = op.opened_values.clone();
                short_tampered[1][0] += Val::ONE;
                let mut tall_tampered = op.opened_values.clone();
                tall_tampered[0][0] += Val::ONE;
                assert!(
                    verify(&short_tampered).is_err(),
                    "{ctx} index={index}: tampered short row accepted"
                );
                assert!(
                    verify(&tall_tampered).is_err(),
                    "{ctx} index={index}: tampered tall row accepted"
                );
                if unbound {
                    assert!(
                        matches!(honest, Err(MerkleTreeError::CapMismatch)),
                        "{ctx} index={index}: unbound commitment accepted: {honest:?}"
                    );
                } else {
                    assert!(
                        honest.is_ok(),
                        "{ctx} index={index}: honest rejected: {honest:?}"
                    );
                }
            }
            let indices = [3usize, 7, 19];
            let (vals, mproof) = mmcs.open_multi_batch(&indices, &data);
            let honest = mmcs.verify_multi_batch(&commit, &dims, &indices, &vals, &mproof);
            let mut tampered = vals.clone();
            for row in &mut tampered {
                row[1][0] += Val::ONE;
            }
            assert!(
                mmcs.verify_multi_batch(&commit, &dims, &indices, &tampered, &mproof)
                    .is_err(),
                "{ctx}: tampered multi-batch short rows accepted"
            );
            if unbound {
                assert!(
                    matches!(honest, Err(MerkleTreeError::CapMismatch)),
                    "{ctx}: unbound multi-batch commitment accepted: {honest:?}"
                );
            } else {
                assert!(
                    honest.is_ok(),
                    "{ctx}: honest multi-batch rejected: {honest:?}"
                );
            }
        }
    }
}

#[test]
fn mmcs_rejects_matrices_shorter_than_the_cap_layer() {
    probe("v6-plain", SpillableMmcs::new_v6);
    probe("v6-zk-hiding", HidingSpillableMmcs::new_v6_zk);
}

// STARK level: the audit's forgery system (`poc/O7/forge/o7_forge_common.rs`).
// Circuit A: 64 rows, `a·a = b`, no lookups. Circuit B: 2 or 4 rows,
// `x·x = y`, pulling the claim `(77, x, y)` with multiplicity column 2.

const CH: u32 = 77;

fn f(v: u32) -> Val {
    Val::from_u32(v)
}

fn forgery_system(
    cap_height: usize,
) -> (
    System<GoldilocksBlake3V6Config>,
    ProverKey<GoldilocksBlake3V6Config>,
) {
    let a = CircuitInputs {
        main_width: 2,
        preprocessed: None,
        constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
        ext_constraints: vec![],
        lookups: vec![],
        lookup_group_size: 1,
    };
    let b = CircuitInputs {
        main_width: 3,
        preprocessed: None,
        constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
        ext_constraints: vec![],
        lookups: vec![Lookup::pull(
            Expr::main(2),
            vec![Expr::constant(f(CH)), Expr::main(0), Expr::main(1)],
        )],
        lookup_group_size: 1,
    };
    let config = GoldilocksBlake3V6Config::new(
        CommitmentParameters {
            log_blowup: 2,
            cap_height,
        },
        FriParameters {
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 64,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
        },
    );
    System::new(config, vec![a, b])
}

fn forgery_witness(
    system: &System<GoldilocksBlake3V6Config>,
    b_rows: usize,
    x: u32,
    y: u32,
) -> SystemWitness<Val> {
    let a: Vec<Val> = (0..64u32)
        .flat_map(|i| [f(i + 1), f((i + 1) * (i + 1))])
        .collect();
    let mut b = vec![Val::ZERO; 3 * b_rows];
    b[0] = f(x);
    b[1] = f(y);
    b[2] = Val::ONE;
    SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new(a, 2), RowMajorMatrix::new(b, 3)],
        system,
    )
}

#[test]
fn audit_o7_forged_proofs_of_a_false_claim_are_rejected() {
    // `(77, 3, 10)` is false for circuit B: 3·3 ≠ 10.
    let false_claim = [f(CH), f(3), f(10)];
    for (cap, bytes) in [
        (
            4usize,
            &include_bytes!("fixtures/o7-forged-cap4-rows2.bin")[..],
        ),
        (5, &include_bytes!("fixtures/o7-forged-cap5-rows4.bin")[..]),
    ] {
        let (system, _) = forgery_system(cap);
        let proof = Proof::<GoldilocksBlake3V6Config>::from_bytes(bytes)
            .expect("the audit's forged proof decodes");
        let result = system.verify_multiple_claims(&[&false_claim[..]], &proof);
        assert!(
            matches!(
                result,
                Err(VerificationError::InvalidOpeningArgument(
                    FriError::InputError(MerkleTreeError::CapMismatch)
                ))
            ),
            "cap {cap}: forged proof of a false claim must fail the Merkle check, got {result:?}"
        );
    }
}

#[test]
fn honest_proofs_verify_when_every_matrix_reaches_the_cap_layer() {
    // cap 4 with log_blowup 2: B's LDE height is 4 * rows. At 4 rows (LDE 16
    // = the cap layer's width) B is bound and the true claim verifies; at 2
    // rows (LDE 8) the verifier refuses the commitment instead of trusting it.
    let true_claim = [f(CH), f(3), f(9)];
    let (system, key) = forgery_system(4);
    let proof =
        system.prove_multiple_claims(&key, &[&true_claim[..]], forgery_witness(&system, 4, 3, 9));
    system
        .verify_multiple_claims(&[&true_claim[..]], &proof)
        .expect("honest proof whose matrices all reach the cap layer");

    let short =
        system.prove_multiple_claims(&key, &[&true_claim[..]], forgery_witness(&system, 2, 3, 9));
    assert!(matches!(
        system.verify_multiple_claims(&[&true_claim[..]], &short),
        Err(VerificationError::InvalidOpeningArgument(
            FriError::InputError(MerkleTreeError::CapMismatch)
        ))
    ));

    // cap 0 (every ix key): the short circuit is bound and verifies.
    let (system0, key0) = forgery_system(0);
    let proof0 = system0.prove_multiple_claims(
        &key0,
        &[&true_claim[..]],
        forgery_witness(&system0, 2, 3, 9),
    );
    system0
        .verify_multiple_claims(&[&true_claim[..]], &proof0)
        .expect("cap 0 binds every matrix");
}
