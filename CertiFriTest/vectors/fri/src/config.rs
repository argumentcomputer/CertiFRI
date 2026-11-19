//! The Plonky3 configuration the vectors are produced with: Goldilocks and its
//! quadratic extension, BLAKE3 Merkle trees with a single root, a BLAKE3-based
//! challenger, and `TwoAdicFriPcs`.

use p3_blake3::Blake3;
use p3_challenger::{HashChallenger, SerializingChallenger64};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2Dit;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeField64};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::Goldilocks;
use p3_merkle_tree::{MerkleCap, MerkleTreeMmcs};
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher};

use crate::json::Json;

pub const PLONKY3_REV: &str = "3152b14a89067c83775a8076cc262ffc48a1fd7c";

/// The Goldilocks prime, `2^64 - 2^32 + 1`.
pub const P: u64 = 0xFFFF_FFFF_0000_0001;

pub type Val = Goldilocks;
pub type Challenge = BinomialExtensionField<Val, 2>;
pub type ByteHash = Blake3;
pub type FieldHash = SerializingHasher<ByteHash>;
pub type Compress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
pub type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, Compress, 2, 32>;
pub type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
pub type Dft = Radix2Dit<Val>;
pub type Challenger = SerializingChallenger64<Val, HashChallenger<u8, ByteHash, 32>>;
pub type FriPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
pub type Digest = [u8; 32];
pub type Commitment = MerkleCap<Val, Digest>;

/// The numeric FRI parameters, without the commitment-scheme handle.
#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub log_blowup: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_proof_of_work_bits: usize,
    pub query_proof_of_work_bits: usize,
}

/// The commitment scheme of the input batches. Cap height 0: one root.
pub fn val_mmcs() -> ValMmcs {
    ValMmcs::new(FieldHash::new(Blake3), Compress::new(Blake3), 0)
}

/// The commitment scheme of the commit-phase codewords.
pub fn challenge_mmcs() -> ChallengeMmcs {
    ChallengeMmcs::new(val_mmcs())
}

pub fn fri_pcs(params: &Params) -> FriPcs {
    let fri = FriParameters {
        log_blowup: params.log_blowup,
        log_final_poly_len: params.log_final_poly_len,
        max_log_arity: params.max_log_arity,
        num_queries: params.num_queries,
        commit_proof_of_work_bits: params.commit_proof_of_work_bits,
        query_proof_of_work_bits: params.query_proof_of_work_bits,
        mmcs: challenge_mmcs(),
    };
    FriPcs::new(Dft::default(), val_mmcs(), fri)
}

/// A challenger with an empty initial state.
pub fn fresh_challenger() -> Challenger {
    Challenger::new(HashChallenger::new(vec![], Blake3))
}

/// The single root of a commitment.
pub fn root(commitment: &Commitment) -> Digest {
    assert_eq!(commitment.num_roots(), 1, "cap height 0 gives one root");
    commitment.roots()[0]
}

pub fn ext(c0: Val, c1: Val) -> Challenge {
    Challenge::from_basis_coefficients_slice(&[c0, c1]).unwrap()
}

pub fn ext_coeffs(e: Challenge) -> [Val; 2] {
    let coeffs: &[Val] = e.as_basis_coefficients_slice();
    [coeffs[0], coeffs[1]]
}

/// A deterministic source of matrix entries and opening points (SplitMix64).
/// It does not depend on any crate, so the vectors survive dependency updates.
pub struct SplitMix64(u64);

impl SplitMix64 {
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn val(&mut self) -> Val {
        loop {
            let x = self.next_u64();
            if x < P {
                return Val::new(x);
            }
        }
    }

    pub fn ext(&mut self) -> Challenge {
        let c0 = self.val();
        let c1 = self.val();
        ext(c0, c1)
    }
}

// JSON encodings.

pub fn j_val(x: Val) -> Json {
    Json::Num(x.as_canonical_u64())
}

pub fn j_ext(e: Challenge) -> Json {
    let [c0, c1] = ext_coeffs(e);
    Json::Arr(vec![j_val(c0), j_val(c1)])
}

pub fn j_bytes(bytes: &[u8]) -> Json {
    Json::arr(bytes, |b| Json::Num(*b as u64))
}

pub fn j_vals(xs: &[Val]) -> Json {
    Json::arr(xs, |x| j_val(*x))
}

pub fn j_exts(es: &[Challenge]) -> Json {
    Json::arr(es, |e| j_ext(*e))
}

pub fn j_digests(ds: &[Digest]) -> Json {
    Json::arr(ds, |d| j_bytes(d))
}

pub fn j_nums(ns: &[usize]) -> Json {
    Json::arr(ns, |n| Json::num(*n))
}
