//! Search for the constant behind the `rejection` challenger script of
//! `primitives.json`.
//!
//! A base-field sample of the challenger is a 64-bit sample below the modulus;
//! a sample at or above it is thrown away. That happens once in about `2^32`
//! samples, so no ordinary transcript shows it. This program finds the least
//! field element `v` such that a fresh challenger that observes `v` draws such
//! a sample among the four it takes from its first digest.
//!
//! Run it with `cargo run --release --example find_rejection [threads]`. It
//! takes about `2^30` BLAKE3 evaluations. The result is the constant
//! `REJECTION_WITNESS` in `src/primitives.rs`, which the generator re-checks.

use std::sync::atomic::{AtomicU64, Ordering};

use p3_blake3::Blake3;
use p3_symmetric::CryptographicHasher;

const P: u64 = 0xFFFF_FFFF_0000_0001;

/// The position, among the four 64-bit samples of the first digest, of the
/// first one at or above the modulus.
fn rejected_position(v: u64) -> Option<usize> {
    let digest: [u8; 32] = Blake3.hash_iter(v.to_le_bytes());
    (0..4).find(|k| {
        let chunk: [u8; 8] = digest[24 - 8 * k..32 - 8 * k].try_into().unwrap();
        u64::from_be_bytes(chunk) >= P
    })
}

fn main() {
    let threads: u64 = std::env::args()
        .nth(1)
        .map(|s| s.parse().expect("thread count"))
        .unwrap_or(4);
    let best = AtomicU64::new(u64::MAX);
    std::thread::scope(|scope| {
        for t in 0..threads {
            let best = &best;
            scope.spawn(move || {
                let mut v = t;
                while v < best.load(Ordering::Relaxed) {
                    if rejected_position(v).is_some() {
                        best.fetch_min(v, Ordering::Relaxed);
                        break;
                    }
                    v += threads;
                }
            });
        }
    });
    let v = best.load(Ordering::Relaxed);
    println!(
        "v = {v}, rejected sample at position {}",
        rejected_position(v).unwrap()
    );
}
