//! The hashing and the challenger written out at the level of bytes.
//!
//! These are the definitions a reimplementation has to match. Each of them is
//! compared against the Plonky3 type it models wherever the generator uses it:
//! the leaf hash and the compression in `primitives.rs` and `merkle.rs`, the
//! challenger in `primitives.rs` and `vector.rs`.

use p3_blake3::Blake3;
use p3_field::PrimeField64;
use p3_symmetric::CryptographicHasher;

use crate::config::{ext, ext_coeffs, Challenge, Digest, Val, P};

/// BLAKE3 with the default 32-byte output.
pub fn blake3(bytes: &[u8]) -> Digest {
    Blake3.hash_iter(bytes.iter().copied())
}

/// A field element as bytes: its canonical value, eight bytes, little-endian.
pub fn val_bytes(x: Val) -> [u8; 8] {
    x.as_canonical_u64().to_le_bytes()
}

/// The leaf hash (`SerializingHasher<Blake3>`): BLAKE3 of the concatenated
/// encodings of the elements.
pub fn hash_vals(values: &[Val]) -> Digest {
    let bytes: Vec<u8> = values.iter().flat_map(|x| val_bytes(*x)).collect();
    blake3(&bytes)
}

/// The compression (`CompressionFunctionFromHasher<Blake3, 2, 32>`): BLAKE3 of
/// the 64 bytes `left ++ right`.
pub fn compress(left: &Digest, right: &Digest) -> Digest {
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(left);
    bytes[32..].copy_from_slice(right);
    blake3(&bytes)
}

/// `SerializingChallenger64<Goldilocks, HashChallenger<u8, Blake3, 32>>`.
///
/// The state is two byte buffers. Observing appends to `input` and discards
/// `output`. Sampling takes bytes from the **end** of `output`; when `output`
/// is empty it is refilled with the BLAKE3 digest of `input`, and `input` is
/// replaced by that same digest.
#[derive(Clone, Debug, Default)]
pub struct ModelChallenger {
    pub input: Vec<u8>,
    pub output: Vec<u8>,
}

impl ModelChallenger {
    /// The challenger with an empty initial state.
    pub fn new() -> Self {
        Self::default()
    }

    fn observe_bytes(&mut self, bytes: &[u8]) {
        self.output.clear();
        self.input.extend_from_slice(bytes);
    }

    pub fn observe_base(&mut self, x: Val) {
        self.observe_bytes(&val_bytes(x));
    }

    /// An extension element is observed as its two coefficients, `c0` first.
    pub fn observe_ext(&mut self, e: Challenge) {
        let [c0, c1] = ext_coeffs(e);
        self.observe_base(c0);
        self.observe_base(c1);
    }

    pub fn observe_digest(&mut self, digest: &Digest) {
        self.observe_bytes(digest);
    }

    fn sample_byte(&mut self) -> u8 {
        if self.output.is_empty() {
            let digest = blake3(&self.input);
            self.input = digest.to_vec();
            self.output = digest.to_vec();
        }
        self.output.pop().unwrap()
    }

    /// Eight sampled bytes read as a little-endian integer. Since bytes come
    /// off the end of the digest, this is the big-endian reading of the last
    /// eight unread digest bytes.
    pub fn sample_u64(&mut self) -> u64 {
        let bytes: [u8; 8] = core::array::from_fn(|_| self.sample_byte());
        u64::from_le_bytes(bytes)
    }

    /// A base-field element: the next 64-bit sample that is below `P`.
    /// Samples at or above `P` are thrown away, not reduced.
    pub fn sample_base(&mut self) -> Val {
        loop {
            let x = self.sample_u64();
            if x < P {
                return Val::new(x);
            }
        }
    }

    /// An extension element: two base-field samples, `c0` first.
    pub fn sample_ext(&mut self) -> Challenge {
        let c0 = self.sample_base();
        let c1 = self.sample_base();
        ext(c0, c1)
    }

    /// The low `bits` bits of one 64-bit sample. No rejection here: the sample
    /// is used even when it is at or above `P`.
    pub fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < 64);
        (self.sample_u64() & ((1u64 << bits) - 1)) as usize
    }

    /// `GrindingChallenger::check_witness`. At zero bits nothing is observed
    /// or sampled.
    pub fn check_witness(&mut self, bits: usize, witness: Val) -> bool {
        if bits == 0 {
            return true;
        }
        self.observe_base(witness);
        self.sample_bits(bits) == 0
    }
}
