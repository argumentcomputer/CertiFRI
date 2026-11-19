//! Generator of the Plonky3 vectors pinned in `CertiFriTest/P3/Pruned.lean`.
//!
//! It commits to small batches of matrices of different heights with Plonky3's
//! `MerkleTreeMmcs`, opens them at several lists of indices with
//! `open_multi_batch`, checks every opening with `verify_multi_batch`, and
//! prints the batches as Lean definitions: the dimensions, the root, the
//! single-index opening at every index, and the pruned proof of every list of
//! indices. The hasher is the toy of `merkle_tree.rs`, which the Lean tests
//! reimplement.
//!
//! It also asserts what the Lean tests rely on without pinning it:
//!
//! * the rows of a multi-opening are those of the single-index openings;
//! * Plonky3 rejects the tampered openings that the Lean tests reject;
//! * Plonky3 rejects rows that differ from those of another query but hash
//!   alike, which the Lean instance accepts.
//!
//! To regenerate, copy this file to `merkle-tree/tests/lean_pruned_vectors.rs`
//! in a Plonky3 checkout and run
//!
//!     cargo test -p p3-merkle-tree --test lean_pruned_vectors -- --nocapture
//!
//! Revision 3152b14a89067c83775a8076cc262ffc48a1fd7c prints the pinned values.

use p3_commit::Mmcs;
use p3_matrix::Dimensions;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::{
    MerkleCap, MerkleTree, MerkleTreeError, MerkleTreeMmcs, PrunedMerklePaths, PrunedProofError,
};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};

const M: u128 = 4294967291;

#[derive(Clone)]
struct ToyHash;

impl CryptographicHasher<u64, [u64; 1]> for ToyHash {
    fn hash_iter<I: IntoIterator<Item = u64>>(&self, input: I) -> [u64; 1] {
        let mut acc: u128 = 7;
        for x in input {
            acc = (acc * 1000003 + x as u128 + 1) % M;
        }
        [acc as u64]
    }
}

#[derive(Clone)]
struct ToyCompress;

impl PseudoCompressionFunction<[u64; 1], 2> for ToyCompress {
    fn compress(&self, input: [[u64; 1]; 2]) -> [u64; 1] {
        let a = input[0][0] as u128;
        let b = input[1][0] as u128;
        [((a * 2654435761 + b * 40503 + 12345) % M) as u64]
    }
}

type ToyMmcs = MerkleTreeMmcs<u64, u64, ToyHash, ToyCompress, 2, 1>;
type Rows = Vec<Vec<u64>>;

fn matrix(m: u64, log_height: usize, width: usize) -> RowMajorMatrix<u64> {
    let values = (0..1u64 << log_height)
        .flat_map(|i| (0..width as u64).map(move |j| 1000 * m + 10 * i + j))
        .collect();
    RowMajorMatrix::new(values, width)
}

/// A committed batch, with the single-index opening at every index.
struct Batch {
    mmcs: ToyMmcs,
    log_height: usize,
    dims: Vec<Dimensions>,
    root: u64,
    data: MerkleTree<u64, u64, RowMajorMatrix<u64>, 2, 1>,
    single: Vec<(Rows, Vec<u64>)>,
}

impl Batch {
    /// Commit to matrices of the given `(log_height, width)`. Matrix `m` of the
    /// batch holds `1000 * (m + 1) + 10 * row + column`.
    fn commit(shapes: &[(usize, usize)]) -> Self {
        let mmcs = ToyMmcs::new(ToyHash, ToyCompress, 0);
        let log_height = shapes
            .iter()
            .map(|&(log_height, _)| log_height)
            .max()
            .unwrap();
        let dims = shapes
            .iter()
            .map(|&(log_height, width)| Dimensions {
                width,
                height: 1 << log_height,
            })
            .collect();
        let matrices = shapes
            .iter()
            .enumerate()
            .map(|(m, &(log_height, width))| matrix(m as u64 + 1, log_height, width))
            .collect();
        let (commit, data) = mmcs.commit(matrices);
        let single = (0..1 << log_height)
            .map(|index| {
                let (rows, path) = mmcs.open_batch(index, &data).unpack();
                (rows, path.iter().map(|digest| digest[0]).collect())
            })
            .collect();
        Self {
            mmcs,
            log_height,
            dims,
            root: commit[0][0],
            data,
            single,
        }
    }

    /// Plonky3's pruned proof of the opening at `indices`, after checking that
    /// Plonky3 accepts it and that it opens the rows of the single-index openings.
    fn open(&self, indices: &[usize]) -> Vec<u64> {
        let (rows, proof) = self.mmcs.open_multi_batch(indices, &self.data);
        let proof: Vec<u64> = proof
            .sibling_hashes
            .iter()
            .map(|digest| digest[0])
            .collect();
        assert_eq!(rows, self.rows(indices));
        self.verify(self.root, indices, &rows, &proof).unwrap();
        proof
    }

    /// The rows the single-index openings give at `indices`.
    fn rows(&self, indices: &[usize]) -> Vec<Rows> {
        indices
            .iter()
            .map(|&index| self.single[index].0.clone())
            .collect()
    }

    fn verify(
        &self,
        root: u64,
        indices: &[usize],
        rows: &[Rows],
        proof: &[u64],
    ) -> Result<(), MerkleTreeError> {
        let commit = MerkleCap::new(vec![[root]]);
        let sibling_hashes = proof.iter().map(|&digest| [digest]).collect();
        let proof = PrunedMerklePaths { sibling_hashes };
        self.mmcs
            .verify_multi_batch(&commit, &self.dims, indices, rows, &proof)
    }

    fn rejects(&self, indices: &[usize], rows: &[Rows], proof: &[u64]) -> bool {
        self.verify(self.root, indices, rows, proof).is_err()
    }

    /// Assert that Plonky3 rejects every tampered variant of an opening that
    /// the Lean tests reject.
    fn assert_tampering_rejected(&self, indices: &[usize], proof: &[u64]) {
        let rows = self.rows(indices);
        // A changed opened entry.
        for query in 0..rows.len() {
            for m in 0..rows[query].len() {
                for j in 0..rows[query][m].len() {
                    let mut rows = rows.clone();
                    rows[query][m][j] += 1;
                    assert!(self.rejects(indices, &rows, proof));
                }
            }
        }
        // A changed sibling digest.
        for position in 0..proof.len() {
            let mut proof = proof.to_vec();
            proof[position] += 1;
            assert!(self.rejects(indices, &rows, &proof));
        }
        // A dropped digest.
        for position in 0..proof.len() {
            let mut proof = proof.to_vec();
            proof.remove(position);
            assert!(self.rejects(indices, &rows, &proof));
        }
        // An extra digest.
        for position in 0..=proof.len() {
            let mut proof = proof.to_vec();
            proof.insert(position, 12345);
            assert!(self.rejects(indices, &rows, &proof));
        }
        // A changed index, in the tree or past its last leaf.
        for query in 0..indices.len() {
            for index in 0..2 << self.log_height {
                if index != indices[query] {
                    let mut indices = indices.to_vec();
                    indices[query] = index;
                    assert!(self.rejects(&indices, &rows, proof));
                }
            }
        }
        // A dropped or an extra index, with the rows unchanged.
        for query in 0..indices.len() {
            let mut indices = indices.to_vec();
            indices.remove(query);
            assert!(self.rejects(&indices, &rows, proof));
        }
        for index in 0..1 << self.log_height {
            let mut indices = indices.to_vec();
            indices.push(index);
            assert!(self.rejects(&indices, &rows, proof));
        }
        // Another root. With no query, nothing is compared with the root.
        assert!(indices.is_empty() || self.verify(self.root + 1, indices, &rows, proof).is_err());
    }

    /// Print the batch as a Lean definition, with the pruned proof of the
    /// opening at each of `lists`.
    fn print(&self, name: &str, doc: &str, lists: &[Vec<usize>]) {
        println!("/-- {doc} -/");
        println!("def {name} : Batch where");
        let dims = self
            .dims
            .iter()
            .map(|d| format!("⟨{}, {}⟩", d.width, d.height.ilog2()));
        println!("  dims := #[{}]", dims.collect::<Vec<_>>().join(", "));
        println!("  root := {}", self.root);
        println!("  single := #[");
        let single = self
            .single
            .iter()
            .map(|(rows, path)| pair(array(rows), format!("{path:?}")));
        println!("{}]", single.collect::<Vec<_>>().join(",\n"));
        println!("  multi := [");
        let multi = lists.iter().map(|indices| {
            let proof = self.open(indices);
            self.assert_tampering_rejected(indices, &proof);
            pair(array(indices), array(&proof))
        });
        println!("{}]", multi.collect::<Vec<_>>().join(",\n"));
        println!();
    }
}

/// A Lean array literal, nested ones included.
fn array<T: core::fmt::Debug>(xs: &[T]) -> String {
    format!("{xs:?}").replace('[', "#[")
}

/// A Lean pair on its own line, broken after the first component if too long.
fn pair(first: String, second: String) -> String {
    let line = format!("    ({first}, {second})");
    if line.chars().count() < 100 {
        line
    } else {
        format!("    ({first},\n      {second})")
    }
}

/// The toy hash of a sequence of pruned proofs, each preceded by its length.
fn fingerprint(proofs: impl Iterator<Item = Vec<u64>>) -> u64 {
    ToyHash.hash_iter(proofs.flat_map(|proof| core::iter::once(proof.len() as u64).chain(proof)))[0]
}

#[test]
fn lean_pruned_vectors() {
    // Queries of a domain of 64 points. Every batch is opened at them, reduced
    // to its height.
    let domain = [37, 9, 33, 60, 8, 22];
    let reduced = |log_height: usize| {
        domain
            .iter()
            .map(|&index| index >> (6 - log_height))
            .collect()
    };

    let mixed = Batch::commit(&[(3, 2), (1, 3), (3, 1), (0, 2)]);
    mixed.print(
        "mixed",
        "Two matrices of the tallest height, none of log-height 2, one of log-height 1 and\n\
         one single row: the batch of `CertiFriTest.Merkle`.",
        &[
            vec![5],
            vec![2, 3],
            vec![1, 6],
            (0..8).collect(),
            vec![5, 0, 5, 7],
            vec![6, 1, 4],
            vec![3, 3, 3],
            vec![0, 1, 2],
            vec![4, 5, 6, 7],
            (0..8).rev().collect(),
            reduced(3),
            vec![],
        ],
    );

    let ladder = Batch::commit(&[(4, 1), (3, 2), (2, 1), (4, 2), (1, 3), (0, 1)]);
    ladder.print(
        "ladder",
        "Two matrices of the tallest height and one injected at every level above.",
        &[
            vec![11],
            vec![6, 7],
            vec![2, 13],
            vec![0, 1, 2, 3, 12, 13, 14, 15],
            vec![9, 4, 9, 9, 4],
            vec![15, 0, 8],
            reduced(4),
            (0..16).collect(),
        ],
    );

    let plain = Batch::commit(&[(2, 2)]);
    plain.print(
        "plain",
        "One matrix: nothing is injected.",
        &[
            vec![2],
            vec![0, 1],
            vec![1, 2],
            vec![3, 0, 3],
            (0..4).collect(),
            reduced(2),
        ],
    );

    let pair = Batch::commit(&[(1, 1), (0, 2)]);
    pair.print(
        "pair",
        "Two leaves, and a row injected at the root.",
        &[vec![0], vec![1], vec![0, 1], vec![1, 0, 1], reduced(1)],
    );

    let one_row = Batch::commit(&[(0, 3), (0, 1)]);
    one_row.print(
        "oneRow",
        "The tallest matrix has one row: the tree is one leaf and every path is empty.",
        &[vec![0], vec![0, 0], reduced(0)],
    );

    let subsets = (1..1usize << 8).map(|mask| {
        let indices: Vec<usize> = (0..8).filter(|index| mask >> index & 1 == 1).collect();
        mixed.open(&indices)
    });
    println!("/-- `fingerprint` of the pruned proofs of `mixed` at `subsets 8`. -/");
    println!(
        "def mixedSubsetsFingerprint : Nat := {}",
        fingerprint(subsets)
    );
    println!();

    // 300 lists of 1 to 12 indices, unsorted and with repetitions.
    let mut state: u64 = 1;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 33) % bound) as usize
    };
    let lists = (0..300).map(|_| {
        let length = 1 + next(12);
        let indices: Vec<usize> = (0..length).map(|_| next(16)).collect();
        ladder.open(&indices)
    });
    println!("/-- `fingerprint` of the pruned proofs of `ladder` at `drawnLists`. -/");
    println!("def ladderListsFingerprint : Nat := {}", fingerprint(lists));

    // No matrix: Plonky3 rejects, even with nothing opened.
    assert!(matches!(
        mixed.mmcs.verify_multi_batch(
            &MerkleCap::new(vec![[mixed.root]]),
            &[],
            &[],
            &Vec::<Rows>::new(),
            &PrunedMerklePaths {
                sibling_hashes: vec![]
            }
        ),
        Err(MerkleTreeError::EmptyBatch)
    ));

    // Rows that differ from those of another query at the same index but hash
    // alike: Plonky3 compares the rows and rejects.
    let proof = mixed.open(&[5, 5]);
    let mut rows = mixed.rows(&[5, 5]);
    rows[1][0][0] += M as u64;
    assert!(matches!(
        mixed.verify(mixed.root, &[5, 5], &rows, &proof),
        Err(MerkleTreeError::MalformedPrunedProof(
            PrunedProofError::InconsistentDuplicateOpenings { slot: 0 }
        ))
    ));

    // The same for two queries below one node of the layer where matrix 1 is
    // injected, with different rows of it.
    let proof = mixed.open(&[4, 5]);
    let mut rows = mixed.rows(&[4, 5]);
    rows[1][1][0] += M as u64;
    assert!(matches!(
        mixed.verify(mixed.root, &[4, 5], &rows, &proof),
        Err(MerkleTreeError::MalformedPrunedProof(
            PrunedProofError::InconsistentGroupOpening { slot: 1, matrix: 1 }
        ))
    ));
}
