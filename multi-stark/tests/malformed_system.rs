//! Regression tests for audit findings IX-23 and IX-14 (multi-stark part):
//! `System` and `ConstraintGraph` have public fields (and derive
//! `Deserialize`), so the verifier cannot assume the invariants `compile`
//! establishes. A malformed system is refused with `InvalidSystem`, and the
//! public evaluation API panics instead of reading out of bounds or
//! uninitialized memory.

use multi_stark::batch::{BatchProof, ShardInput};
use multi_stark::eval::VarValues;
use multi_stark::expr::{ColRef, Expr, RowOffset, Source};
use multi_stark::graph::{Node, NodeId};
use multi_stark::lookup::Lookup;
use multi_stark::prover::Proof;
use multi_stark::system::{CircuitInputs, System, SystemWitness};
use multi_stark::types::{CommitmentParameters, FriParameters, GoldilocksBlake3V6Config, Val};
use multi_stark::verifier::VerificationError;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;

type Sys = System<GoldilocksBlake3V6Config>;

fn f(v: u32) -> Val {
    Val::from_u32(v)
}

/// Circuit 0: `x·x = y` pulling the claim `(77, x, y)`; circuit 1: `a·a = b`.
fn build() -> (
    Sys,
    multi_stark::system::ProverKey<GoldilocksBlake3V6Config>,
) {
    let pulls = CircuitInputs {
        main_width: 3,
        preprocessed: None,
        constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
        ext_constraints: vec![],
        lookups: vec![Lookup::pull(
            Expr::main(2),
            vec![Expr::constant(f(77)), Expr::main(0), Expr::main(1)],
        )],
        lookup_group_size: 1,
    };
    let square = CircuitInputs {
        main_width: 2,
        preprocessed: None,
        constraints: vec![Expr::main(0) * Expr::main(0) - Expr::main(1)],
        ext_constraints: vec![],
        lookups: vec![],
        lookup_group_size: 1,
    };
    let config = GoldilocksBlake3V6Config::new(
        CommitmentParameters {
            log_blowup: 2,
            cap_height: 0,
        },
        FriParameters {
            log_final_poly_len: 0,
            max_log_arity: 1,
            num_queries: 16,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 0,
        },
    );
    System::new(config, vec![pulls, square])
}

fn build_system() -> Sys {
    build().0
}

fn system_and_proof() -> (Sys, Vec<Val>, Proof<GoldilocksBlake3V6Config>) {
    let (system, key) = build();
    let mut pull_trace = vec![Val::ZERO; 3 * 4];
    pull_trace[..3].copy_from_slice(&[f(3), f(9), Val::ONE]);
    let square_trace: Vec<Val> = (1..=8u32).flat_map(|i| [f(i), f(i * i)]).collect();
    let witness = SystemWitness::from_stage_1(
        vec![
            RowMajorMatrix::new(pull_trace, 3),
            RowMajorMatrix::new(square_trace, 2),
        ],
        &system,
    );
    let claim = vec![f(77), f(3), f(9)];
    let proof = system.prove_multiple_claims(&key, &[&claim[..]], witness);
    system
        .verify_multiple_claims(&[&claim[..]], &proof)
        .expect("honest proof");
    (system, claim, proof)
}

fn rejected(system: &Sys, claim: &[Val], proof: &Proof<GoldilocksBlake3V6Config>) -> bool {
    matches!(
        system.verify_multiple_claims(&[claim], proof),
        Err(VerificationError::InvalidSystem)
    )
}

fn system_and_batch_proof() -> (Sys, BatchProof<GoldilocksBlake3V6Config>) {
    let (system, key) = build();
    let mut pull_trace = vec![Val::ZERO; 3 * 4];
    pull_trace[..3].copy_from_slice(&[f(3), f(9), Val::ONE]);
    let square_trace: Vec<Val> = (1..=8u32).flat_map(|i| [f(i), f(i * i)]).collect();
    let witness = SystemWitness::from_stage_1(
        vec![
            RowMajorMatrix::new(pull_trace, 3),
            RowMajorMatrix::new(square_trace, 2),
        ],
        &system,
    );
    let claim = vec![f(77), f(3), f(9)];
    let batch = system.prove_batch(
        &key,
        vec![ShardInput {
            claims: vec![claim],
            witness,
        }],
        vec![],
    );
    system.verify_batch(&batch).expect("honest batch proof");
    (system, batch)
}

fn batch_rejected(system: &Sys, batch: &BatchProof<GoldilocksBlake3V6Config>) -> bool {
    matches!(
        system.verify_batch(batch),
        Err(VerificationError::InvalidSystem)
    ) && matches!(
        system.verify_batch_shard(&batch.preamble, 0, &batch.proofs[0]),
        Err(VerificationError::InvalidSystem)
    )
}

fn first_binary_node(nodes: &[Node<Val>]) -> usize {
    nodes
        .iter()
        .position(|n| matches!(n, Node::Add(..) | Node::Sub(..) | Node::Mul(..)))
        .expect("a binary node")
}

#[test]
fn verifier_refuses_malformed_systems() {
    let (system, claim, proof) = system_and_proof();
    assert!(system.check_well_formed().is_ok());

    // A child at or after its parent.
    let mut s = build_system();
    let graph = &mut s.circuits[1].graph;
    let i = first_binary_node(&graph.nodes);
    graph.nodes[i] = Node::Mul(NodeId(u32::try_from(i).unwrap()), NodeId(0));
    assert!(rejected(&s, &claim, &proof));

    // A lookup prefix longer than the graph.
    let mut s = build_system();
    s.circuits[0].graph.lookup_prefix_len = s.circuits[0].graph.nodes.len() + 1;
    assert!(rejected(&s, &claim, &proof));

    // A column outside the circuit's width.
    let mut s = build_system();
    let graph = &mut s.circuits[1].graph;
    let v = graph
        .nodes
        .iter()
        .position(|n| matches!(n, Node::Var(_)))
        .unwrap();
    graph.nodes[v] = Node::Var(ColRef {
        source: Source::Main,
        offset: RowOffset::Current,
        index: 2,
    });
    assert!(rejected(&s, &claim, &proof));

    // Lookup expressions that read a stage-2 column or a public value
    // (`compile` refuses both; a deserialized graph must not carry them).
    for replacement in [
        Node::Var(ColRef {
            source: Source::Stage2,
            offset: RowOffset::Current,
            index: 0,
        }),
        Node::Public(0),
        Node::IsFirstRow,
    ] {
        let mut s = build_system();
        let graph = &mut s.circuits[0].graph;
        let lookup_arg = graph.lookups[0].args[1].index();
        assert!(matches!(graph.nodes[lookup_arg], Node::Var(_)));
        graph.nodes[lookup_arg] = replacement;
        assert!(rejected(&s, &claim, &proof));
    }

    // Metadata inconsistent with the graph.
    let mut s = build_system();
    s.circuits[0].stage_2_width += 1;
    assert!(rejected(&s, &claim, &proof));
    let mut s = build_system();
    s.circuits[0].lookup_group_size = 0;
    assert!(rejected(&s, &claim, &proof));
    let mut s = build_system();
    s.preprocessed_indices.push(None);
    assert!(rejected(&s, &claim, &proof));
    let mut s = build_system();
    s.circuits[0].graph.degrees.pop();
    assert!(rejected(&s, &claim, &proof));
    let mut s = build_system();
    s.circuits[0].max_constraint_degree = ((u32::MAX as usize) >> 2) + 1;
    assert!(rejected(&s, &claim, &proof));
    let mut s = build_system();
    s.circuits[0].preprocessed_height = 4;
    s.circuits[0].preprocessed_width = 0;
    s.preprocessed_indices[0] = Some(0);
    assert!(rejected(&s, &claim, &proof));
}

#[test]
fn batch_verifier_refuses_malformed_systems() {
    let (system, batch) = system_and_batch_proof();
    assert!(system.check_well_formed().is_ok());

    // Huge `max_constraint_degree` previously panicked inside
    // `verify_preamble_headers` (`next_power_of_two()` overflow) before
    // reaching `verify_shape`.
    for bad_degree in [usize::MAX, ((u32::MAX as usize) >> 2) + 1] {
        let mut s = build_system();
        s.circuits[0].max_constraint_degree = bad_degree;
        assert!(batch_rejected(&s, &batch));
    }

    // Mismatched `preprocessed_indices.len()`.
    let mut s = build_system();
    s.preprocessed_indices.push(None);
    assert!(batch_rejected(&s, &batch));

    // Mismatched `graph.degrees.len()`.
    let mut s = build_system();
    s.circuits[0].graph.degrees.pop();
    assert!(batch_rejected(&s, &batch));

    // Preprocessed slot with zero width.
    let mut s = build_system();
    s.circuits[0].preprocessed_height = 4;
    s.circuits[0].preprocessed_width = 0;
    s.preprocessed_indices[0] = Some(0);
    assert!(batch_rejected(&s, &batch));

    // Non-topological constraint graph.
    let mut s = build_system();
    let graph = &mut s.circuits[1].graph;
    let i = first_binary_node(&graph.nodes);
    graph.nodes[i] = Node::Mul(NodeId(u32::try_from(i).unwrap()), NodeId(0));
    assert!(batch_rejected(&s, &batch));
}

#[test]
#[should_panic(expected = "topologically ordered")]
fn sweep_panics_on_a_forward_reference() {
    let (system, _, _) = system_and_proof();
    let mut graph = system.circuits[1].graph.clone();
    let i = first_binary_node(&graph.nodes);
    graph.nodes[i] = Node::Add(NodeId(u32::try_from(i).unwrap() + 1), NodeId(0));
    let row = [f(2), f(4)];
    let values = VarValues {
        preprocessed: [&[], &[]],
        main: [&row, &row],
        stage2: [&[], &[]],
        publics: &[],
        is_first_row: Val::ZERO,
        is_last_row: Val::ZERO,
        is_transition: Val::ONE,
    };
    assert!(graph.validated().is_none());
    let mut buf = Vec::new();
    graph.sweep(&values, &mut buf);
}

#[test]
#[should_panic(expected = "sweep range exceeds the graph")]
fn sweep_panics_on_a_prefix_longer_than_the_graph() {
    let (system, _, _) = system_and_proof();
    let mut graph = system.circuits[0].graph.clone();
    graph.lookup_prefix_len = graph.nodes.len() + 3;
    let row = [f(3), f(9), Val::ONE];
    let values = VarValues {
        preprocessed: [&[], &[]],
        main: [&row, &row],
        stage2: [&[], &[]],
        publics: &[],
        is_first_row: Val::ZERO,
        is_last_row: Val::ZERO,
        is_transition: Val::ONE,
    };
    assert!(graph.validated().is_none());
    let mut buf = Vec::new();
    graph.sweep_lookup_prefix(&values, &mut buf);
}
