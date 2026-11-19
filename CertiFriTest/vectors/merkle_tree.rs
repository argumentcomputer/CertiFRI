//! Generator of the Plonky3 vectors pinned in `CertiFriTest/Merkle.lean`.
//!
//! It commits to a small batch of matrices of different heights with Plonky3's
//! `MerkleTreeMmcs` and prints the root and the opening at every index. The
//! hasher is a toy that the Lean tests reimplement.
//!
//! To regenerate, copy this file to `merkle-tree/tests/lean_vectors.rs` in a
//! Plonky3 checkout and run
//!
//!     cargo test -p p3-merkle-tree --test lean_vectors -- --nocapture
//!
//! Revisions 3152b14a89067c83775a8076cc262ffc48a1fd7c and
//! 0d803737b681774186cd283b1fd2d8e493655c82 both print the pinned values.

use p3_commit::Mmcs;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
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

fn matrix(m: u64, log_height: usize, width: usize) -> RowMajorMatrix<u64> {
    let values = (0..1u64 << log_height)
        .flat_map(|i| (0..width as u64).map(move |j| 1000 * m + 10 * i + j))
        .collect();
    RowMajorMatrix::new(values, width)
}

#[test]
fn lean_vectors() {
    let mmcs = MerkleTreeMmcs::<u64, u64, ToyHash, ToyCompress, 2, 1>::new(ToyHash, ToyCompress, 0);
    let (commit, data) = mmcs.commit(vec![
        matrix(1, 3, 2),
        matrix(2, 1, 3),
        matrix(3, 3, 1),
        matrix(4, 0, 2),
    ]);
    println!("ROOT {:?}", commit);
    for index in 0..8 {
        let (rows, path) = mmcs.open_batch(index, &data).unpack();
        println!("OPEN {index} rows={:?} path={:?}", rows, path);
    }
    let (rows, proof) = mmcs.open_multi_batch(&[5, 0, 5, 7], &data);
    println!("MULTI rows={:?} proof={:?}", rows, proof);
}
