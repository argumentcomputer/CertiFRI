//! The configuration the vectors are produced with, multi-stark's
//! `GoldilocksBlake3Config`, and the JSON encodings of its scalars.

use multi_stark::p3_field::{BasedVectorSpace, PrimeField64};
use multi_stark::types::{CommitmentParameters, FriParameters};

use crate::json::Json;

pub use multi_stark::types::{
    Challenger, Commitment, ExtVal, GoldilocksBlake3Config as Config, Val,
};

pub const MULTI_STARK_REV: &str = "3515632f1dc1a5764b60fc0146ea2226bb6fc32d";
pub const PLONKY3_REV: &str = "3152b14a89067c83775a8076cc262ffc48a1fd7c";

/// The degree of `ExtVal` over `Val`.
pub const EXTENSION_DEGREE: usize = 2;

/// The domain-separation tag multi-stark's challenger seed starts with.
const SEED_TAG: &[u8] = b"multi-stark/v0";

pub type Digest = [u8; 32];

/// The seven protocol parameters, in the order of the challenger seed.
#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub log_blowup: usize,
    pub cap_height: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
    pub num_queries: usize,
    pub commit_proof_of_work_bits: usize,
    pub query_proof_of_work_bits: usize,
}

impl Params {
    fn in_seed_order(&self) -> [(&'static str, usize); 7] {
        [
            ("log_blowup", self.log_blowup),
            ("cap_height", self.cap_height),
            ("log_final_poly_len", self.log_final_poly_len),
            ("max_log_arity", self.max_log_arity),
            ("num_queries", self.num_queries),
            ("commit_proof_of_work_bits", self.commit_proof_of_work_bits),
            ("query_proof_of_work_bits", self.query_proof_of_work_bits),
        ]
    }

    pub fn config(&self) -> Config {
        Config::new(
            CommitmentParameters {
                log_blowup: self.log_blowup,
                cap_height: self.cap_height,
            },
            FriParameters {
                log_final_poly_len: self.log_final_poly_len,
                max_log_arity: self.max_log_arity,
                num_queries: self.num_queries,
                commit_proof_of_work_bits: self.commit_proof_of_work_bits,
                query_proof_of_work_bits: self.query_proof_of_work_bits,
            },
        )
    }

    /// The initial state of the challenger, recomputed from the parameters:
    /// the tag, then each parameter as a `u64` in little-endian bytes.
    pub fn seed(&self) -> Vec<u8> {
        let mut seed = SEED_TAG.to_vec();
        for (_, value) in self.in_seed_order() {
            seed.extend_from_slice(&(value as u64).to_le_bytes());
        }
        seed
    }

    pub fn to_json(self) -> Json {
        Json::Obj(
            self.in_seed_order()
                .into_iter()
                .map(|(name, value)| (name, Json::num(value)))
                .collect(),
        )
    }
}

/// The single root of a commitment.
pub fn root(commitment: &Commitment) -> Digest {
    assert_eq!(commitment.num_roots(), 1, "cap height 0 gives one root");
    commitment.roots()[0]
}

pub fn ext_coeffs(e: ExtVal) -> [Val; 2] {
    let coeffs: &[Val] = e.as_basis_coefficients_slice();
    [coeffs[0], coeffs[1]]
}

// JSON encodings.

pub fn j_val(x: Val) -> Json {
    Json::Num(x.as_canonical_u64())
}

pub fn j_ext(e: ExtVal) -> Json {
    let [c0, c1] = ext_coeffs(e);
    Json::Arr(vec![j_val(c0), j_val(c1)])
}

pub fn j_bytes(bytes: &[u8]) -> Json {
    Json::arr(bytes, |b| Json::Num(*b as u64))
}

pub fn j_commitment(commitment: &Commitment) -> Json {
    j_bytes(&root(commitment))
}

pub fn j_vals(xs: &[Val]) -> Json {
    Json::arr(xs, |x| j_val(*x))
}

pub fn j_exts(es: &[ExtVal]) -> Json {
    Json::arr(es, |e| j_ext(*e))
}

pub fn j_digests(ds: &[Digest]) -> Json {
    Json::arr(ds, |d| j_bytes(d))
}

pub fn j_nums(ns: &[usize]) -> Json {
    Json::arr(ns, |n| Json::num(*n))
}

pub fn j_bools(bs: &[bool]) -> Json {
    Json::arr(bs, |b| Json::Bool(*b))
}
