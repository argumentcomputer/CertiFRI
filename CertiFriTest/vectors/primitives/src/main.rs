//! Known-answer values for the Lean port of the Plonky3 primitives.
//!
//! Prints Lean definitions (data only) to stdout, one section per topic. The
//! sections are pasted into `CertiFriTest/P3/*.lean`.
//!
//! To regenerate: `cargo run --release` in this directory. Plonky3 is pinned
//! by revision in `Cargo.toml`.

use p3_blake3::Blake3;
use p3_challenger::{
    CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger, HashChallenger,
    SerializingChallenger64,
};
use p3_commit::{ExtensionMmcs, Mmcs};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
    CompressionFunctionFromHasher, CryptographicHasher, Hash, MerkleCap,
    PseudoCompressionFunction, SerializingHasher,
};

type F = Goldilocks;
type EF = BinomialExtensionField<F, 2>;
type FieldHash = SerializingHasher<Blake3>;
type Compress = CompressionFunctionFromHasher<Blake3, 2, 32>;
type ValMmcs = MerkleTreeMmcs<F, u8, FieldHash, Compress, 2, 32>;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;

const P: u64 = 0xFFFF_FFFF_0000_0001;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn c(x: F) -> u64 {
    x.as_canonical_u64()
}

fn coords(e: EF) -> (u64, u64) {
    let s: &[F] = e.as_basis_coefficients_slice();
    assert_eq!(s.len(), 2);
    (c(s[0]), c(s[1]))
}

fn ext(a0: u64, a1: u64) -> EF {
    EF::from_basis_coefficients_slice(&[F::new(a0), F::new(a1)]).unwrap()
}

/// SplitMix64, the source of the pseudo-random words below.
struct SplitMix(u64);
impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}

/// Word `i` of the row with seed `seed`: any `u64`, reduced by the field.
fn row_word(seed: u64, i: u64) -> u64 {
    (seed.wrapping_add(i).wrapping_add(1)).wrapping_mul(0x9E37_79B9_7F4A_7C15)
}

fn base_row(seed: u64, len: usize) -> Vec<F> {
    (0..len as u64).map(|i| F::new(row_word(seed, i))).collect()
}

fn ext_row(seed: u64, len: usize) -> Vec<EF> {
    (0..len as u64)
        .map(|j| ext(row_word(seed, 2 * j), row_word(seed, 2 * j + 1)))
        .collect()
}

fn goldilocks() {
    println!("-- ## Goldilocks");
    let edge: Vec<u64> = vec![
        0,
        1,
        2,
        7,
        (1 << 31) - 1,
        1 << 31,
        (1 << 32) - 1,
        1 << 32,
        (1 << 32) + 1,
        1 << 33,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        0xFFFF_FFFE_FFFF_FFFF,
        0xFFFF_FFFF_0000_0000 - 1,
        P - 1,
        P,
        P + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    let mut rng = SplitMix(1);
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    for &a in &edge {
        for &b in &[1u64 << 32, P - 1, u64::MAX] {
            pairs.push((a, b));
        }
    }
    for _ in 0..30 {
        pairs.push((rng.next(), rng.next()));
    }
    println!("/-- `(a, b, a + b, a - b, a * b)`: the operands are any words, the results are");
    println!("canonical. -/");
    println!("def arithmeticVectors : Array (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) := #[");
    let lines: Vec<String> = pairs
        .iter()
        .map(|&(a, b)| {
            let (x, y) = (F::new(a), F::new(b));
            format!(
                "  ({a:#018x}, {b:#018x},\n    {:#018x}, {:#018x}, {:#018x})",
                c(x + y),
                c(x - y),
                c(x * y)
            )
        })
        .collect();
    println!("{}]", lines.join(",\n"));

    let mut unary: Vec<u64> = edge.iter().copied().filter(|&a| a % P != 0).collect();
    for _ in 0..40 {
        unary.push(rng.next());
    }
    println!();
    println!("/-- `(a, -a, a⁻¹)` for nonzero `a`. -/");
    println!("def unaryVectors : Array (UInt64 × UInt64 × UInt64) := #[");
    let lines: Vec<String> = unary
        .iter()
        .map(|&a| {
            let x = F::new(a);
            format!("  ({a:#018x}, {:#018x}, {:#018x})", c(-x), c(x.inverse()))
        })
        .collect();
    println!("{}]", lines.join(",\n"));

    println!();
    println!("/-- `(a, n, a ^ n)`. -/");
    println!("def powerVectors : Array (UInt64 × Nat × UInt64) := #[");
    let mut lines = Vec::new();
    for &e in &[0u64, 1, 2, 3, 64, (1 << 32) - 1, 1 << 32, P - 2, P - 1, u64::MAX] {
        let a = rng.next();
        lines.push(format!("  ({a:#018x}, {e}, {:#018x})", c(F::new(a).exp_u64(e))));
    }
    println!("{}]", lines.join(",\n"));

    println!();
    println!("/-- `Goldilocks::two_adic_generator(k)` for `k = 0, …, 32`. -/");
    println!("def twoAdicGeneratorVectors : Array UInt64 := #[");
    let lines: Vec<String> = (0..=32)
        .map(|k| format!("  {:#018x}", c(F::two_adic_generator(k))))
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();
    println!("/-- `Goldilocks::GENERATOR`. -/");
    println!("def generatorVector : UInt64 := {}", c(F::GENERATOR));
    println!("-- TWO_ADICITY = {}", F::TWO_ADICITY);
    println!("-- ORDER_U64 = {:#x}", F::ORDER_U64);
}

fn extension() {
    println!("-- ## Extension");
    let mut rng = SplitMix(2);
    let edge: Vec<(u64, u64)> = vec![
        (0, 0),
        (1, 0),
        (0, 1),
        (P - 1, P - 1),
        (1 << 32, (1 << 32) - 1),
    ];
    let mut pairs: Vec<((u64, u64), (u64, u64))> = Vec::new();
    for &a in &edge {
        for &b in &edge {
            pairs.push((a, b));
        }
    }
    for _ in 0..25 {
        pairs.push(((rng.next(), rng.next()), (rng.next(), rng.next())));
    }
    println!("/-- `(a, b, a + b, a - b, a * b)`, each element as its coordinates `(c0, c1)`. -/");
    println!("def arithmeticVectors : Array (E × E × E × E × E) := #[");
    let fmt = |e: EF| {
        let (x, y) = coords(e);
        format!("({x:#018x}, {y:#018x})")
    };
    let lines: Vec<String> = pairs
        .iter()
        .map(|&(a, b)| {
            let (x, y) = (ext(a.0, a.1), ext(b.0, b.1));
            format!(
                "  ({}, {},\n    {}, {},\n    {})",
                fmt(x),
                fmt(y),
                fmt(x + y),
                fmt(x - y),
                fmt(x * y)
            )
        })
        .collect();
    println!("{}]", lines.join(",\n"));

    let mut unary: Vec<(u64, u64)> = edge.iter().copied().filter(|&a| a != (0, 0)).collect();
    for _ in 0..20 {
        unary.push((rng.next(), rng.next()));
    }
    println!();
    println!("/-- `(a, -a, a⁻¹)` for nonzero `a`. -/");
    println!("def unaryVectors : Array (E × E × E) := #[");
    let lines: Vec<String> = unary
        .iter()
        .map(|&a| {
            let x = ext(a.0, a.1);
            format!("  ({}, {},\n    {})", fmt(x), fmt(-x), fmt(x.inverse()))
        })
        .collect();
    println!("{}]", lines.join(",\n"));

    println!();
    println!("/-- `(a, n, a ^ n)`. -/");
    println!("def powerVectors : Array (E × Nat × E) := #[");
    let mut lines = Vec::new();
    for &e in &[0u64, 1, 2, 5, (1 << 32) + 1, P, u64::MAX] {
        let x = ext(rng.next(), rng.next());
        lines.push(format!("  ({}, {e},\n    {})", fmt(x), fmt(x.exp_u64(e))));
    }
    println!("{}]", lines.join(",\n"));

    // The embedding of the base field and the basis.
    println!();
    println!("/-- `(a, e, EF::from(a) * e)`: the base element `a` times the extension element");
    println!("`e`. -/");
    println!("def embedVectors : Array (UInt64 × E × E) := #[");
    let mut lines = Vec::new();
    for _ in 0..8 {
        let a = rng.next();
        let e = ext(rng.next(), rng.next());
        lines.push(format!("  ({a:#018x}, {},\n    {})", fmt(e), fmt(EF::from(F::new(a)) * e)));
    }
    println!("{}]", lines.join(",\n"));
    let five = EF::from(F::new(5));
    println!("-- EF::from(5) = {}", fmt(five));
    let x = <EF as BasedVectorSpace<F>>::ith_basis_element(1).unwrap();
    println!("-- ith_basis_element(1) = {}, squared = {}", fmt(x), fmt(x * x));
    println!("-- DIMENSION = {}", <EF as BasedVectorSpace<F>>::DIMENSION);
    let sampled = <EF as BasedVectorSpace<F>>::from_basis_coefficients_fn(|i| F::new(100 + i as u64));
    println!("-- from_basis_coefficients_fn(|i| 100 + i) = {}", fmt(sampled));
    let flat: Vec<F> = <EF as BasedVectorSpace<F>>::flatten_to_base(vec![ext(1, 2), ext(3, 4)]);
    println!("-- flatten_to_base([(1,2),(3,4)]) = {:?}", flat.iter().map(|x| c(*x)).collect::<Vec<_>>());
}

fn blake3_vectors() {
    println!("-- ## BLAKE3");
    println!("/-- `(n, digest)`: the digest of the `n` bytes `i % 251` for `i < n`. -/");
    println!("def vectors : Array (Nat × String) := #[");
    let lens = [
        0usize, 1, 2, 3, 4, 5, 6, 7, 8, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025, 2048, 2049, 3072,
        3073, 4096, 4097, 5120, 5121, 6144, 6145, 7168, 7169, 8192, 8193, 16384, 31744, 102400,
    ];
    let mut lines = Vec::new();
    for &n in &lens {
        let input: Vec<u8> = (0..n).map(|i| (i % 251) as u8).collect();
        let reference = blake3::hash(&input);
        let p3: [u8; 32] = Blake3.hash_iter(input.iter().copied());
        assert_eq!(reference.as_bytes(), &p3);
        lines.push(format!("  ({n}, \"{}\")", hex(&p3)));
    }
    println!("{}]", lines.join(",\n"));

    // Every length up to 300, folded into one digest.
    let mut acc = [0u8; 32];
    for n in 0..=300usize {
        let input: Vec<u8> = (0..n).map(|i| (i % 251) as u8).collect();
        let mut joined = acc.to_vec();
        joined.extend_from_slice(blake3::hash(&input).as_bytes());
        acc = *blake3::hash(&joined).as_bytes();
    }
    println!();
    println!("/-- `(m, digest)`: the digests of the inputs of every length `n ≤ m`, folded from 32");
    println!("zero bytes by `acc ↦ blake3 (acc ++ blake3 (input n))`. -/");
    println!("def sweepVector : Nat × String :=\n  (300, \"{}\")", hex(&acc));
}

fn hashers() {
    println!("-- ## Hashers");
    let field_hash = FieldHash::new(Blake3);
    let compress = Compress::new(Blake3);

    println!("/-- `(seed, n, digest)`: `SerializingHasher<Blake3>` on the row of `n` base elements");
    println!("with seed `seed`. -/");
    println!("def baseRowVectors : Array (UInt64 × Nat × String) := #[");
    let mut lines = Vec::new();
    for (k, &n) in [0usize, 1, 2, 7, 8, 9, 16, 127, 128, 129, 255, 256, 257, 300, 513].iter().enumerate() {
        let seed = 1000 * (k as u64 + 1);
        let row = base_row(seed, n);
        let digest: [u8; 32] = field_hash.hash_iter(row.iter().copied());
        let by_slice: [u8; 32] = field_hash.hash_slice(&row);
        assert_eq!(digest, by_slice);
        // The same bytes through the byte hasher.
        let bytes: Vec<u8> = row.iter().flat_map(|x| c(*x).to_le_bytes()).collect();
        let direct: [u8; 32] = Blake3.hash_iter(bytes.iter().copied());
        assert_eq!(digest, direct);
        lines.push(format!("  ({seed}, {n}, \"{}\")", hex(&digest)));
    }
    println!("{}]", lines.join(",\n"));

    // A row of edge values.
    let edge: Vec<u64> = vec![0, 1, P - 1, (1 << 32) - 1, 1 << 32, 1 << 63, P, u64::MAX, 0x0123_4567_89AB_CDEF];
    let row: Vec<F> = edge.iter().map(|&w| F::new(w)).collect();
    let digest: [u8; 32] = field_hash.hash_slice(&row);
    println!();
    println!("/-- A row of words at the edges of the field, some of them not canonical, and its digest. -/");
    println!(
        "def edgeRowVector : Array UInt64 × String := (#[\n  {}],\n  \"{}\")",
        edge.chunks(4)
            .map(|ws| ws.iter().map(|w| format!("{w:#018x}")).collect::<Vec<_>>().join(", "))
            .collect::<Vec<_>>()
            .join(",\n  "),
        hex(&digest)
    );

    println!();
    println!("/-- `(seed, n, digest)`: the row of `n` extension elements with seed `seed`,");
    println!("flattened as `ExtensionMmcs` does (`flatten_to_base`) and hashed by");
    println!("`SerializingHasher<Blake3>`. -/");
    println!("def extRowVectors : Array (UInt64 × Nat × String) := #[");
    let mut lines = Vec::new();
    for (k, &n) in [0usize, 1, 2, 3, 4, 5, 63, 64, 65, 150].iter().enumerate() {
        let seed = 77 * (k as u64 + 1);
        let row = ext_row(seed, n);
        let flat: Vec<F> = <EF as BasedVectorSpace<F>>::flatten_to_base(row.clone());
        let digest: [u8; 32] = field_hash.hash_slice(&flat);
        lines.push(format!("  ({seed}, {n}, \"{}\")", hex(&digest)));
    }
    println!("{}]", lines.join(",\n"));

    println!();
    println!("/-- `(left, right, compress(left, right))`: `CompressionFunctionFromHasher<Blake3, 2, 32>`. -/");
    println!("def compressVectors : Array (String × String × String) := #[");
    let mut lines = Vec::new();
    let mut rng = SplitMix(3);
    let mut digests: Vec<[u8; 32]> = vec![[0u8; 32], [0xFFu8; 32], core::array::from_fn(|i| i as u8)];
    for _ in 0..4 {
        let mut d = [0u8; 32];
        for chunk in d.chunks_mut(8) {
            chunk.copy_from_slice(&rng.next().to_le_bytes());
        }
        digests.push(d);
    }
    for i in 0..digests.len() {
        let (l, r) = (digests[i], digests[(i + 3) % digests.len()]);
        let out = compress.compress([l, r]);
        // The same through the byte hasher.
        let direct: [u8; 32] = Blake3.hash_iter(l.iter().chain(r.iter()).copied());
        assert_eq!(out, direct);
        lines.push(format!("  (\"{}\",\n    \"{}\",\n    \"{}\")", hex(&l), hex(&r), hex(&out)));
    }
    println!("{}]", lines.join(",\n"));

    // Rows of every length up to 48, folded into one digest.
    let mut acc = [0u8; 32];
    for n in 0..=48usize {
        let d: [u8; 32] = field_hash.hash_slice(&base_row(n as u64, n));
        acc = compress.compress([acc, d]);
        let flat: Vec<F> = <EF as BasedVectorSpace<F>>::flatten_to_base(ext_row(n as u64 + 7, n));
        let d: [u8; 32] = field_hash.hash_slice(&flat);
        acc = compress.compress([acc, d]);
    }
    println!();
    println!("/-- `(m, digest)`: the digests of the base row of length `n` with seed `n` and of the");
    println!("extension row of length `n` with seed `n + 7`, for every `n ≤ m`, folded from the");
    println!("zero digest by the compression, the row digest on the right. -/");
    println!("def rowSweepVector : Nat × String :=\n  (48, \"{}\")", hex(&acc));

    // Roots of trees with two leaves, through the commitment schemes themselves.
    let val_mmcs = ValMmcs::new(field_hash, compress.clone(), 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    println!();
    println!("/-- `(seed, width, root)`: the root `MerkleTreeMmcs` commits to for the matrix of two");
    println!("rows of `width` base elements, the rows having seeds `seed` and `seed + 500`. -/");
    println!("def baseRootVectors : Array (UInt64 × Nat × String) := #[");
    let mut lines = Vec::new();
    for (k, &w) in [1usize, 3, 8, 20, 130].iter().enumerate() {
        let seed = 31 * (k as u64 + 1);
        let mut values = base_row(seed, w);
        values.extend(base_row(seed + 500, w));
        let (commit, _data): (MerkleCap<F, [u8; 32]>, _) = val_mmcs.commit(vec![RowMajorMatrix::new(values, w)]);
        assert_eq!(commit.roots().len(), 1);
        lines.push(format!("  ({seed}, {w}, \"{}\")", hex(&commit.roots()[0])));
    }
    println!("{}]", lines.join(",\n"));
    println!();
    println!("/-- `(seed, width, root)`: the root `ExtensionMmcs` commits to for the matrix of two");
    println!("rows of `width` extension elements, the rows having seeds `seed` and `seed + 500`. -/");
    println!("def extRootVectors : Array (UInt64 × Nat × String) := #[");
    let mut lines = Vec::new();
    for (k, &w) in [1usize, 2, 5, 70].iter().enumerate() {
        let seed = 53 * (k as u64 + 1);
        let mut values = ext_row(seed, w);
        values.extend(ext_row(seed + 500, w));
        let (commit, _data) = challenge_mmcs.commit(vec![RowMajorMatrix::new(values, w)]);
        assert_eq!(commit.roots().len(), 1);
        lines.push(format!("  ({seed}, {w}, \"{}\")", hex(&commit.roots()[0])));
    }
    println!("{}]", lines.join(",\n"));
}

/// One step of a challenger script.
#[derive(Clone, Debug)]
enum Step {
    ObserveBase(u64),
    ObserveExt(u64, u64),
    /// Observed as a `Hash<F, u8, 32>`.
    ObserveDigest([u8; 32]),
    /// Observed as a `MerkleCap` with one root, as the FRI verifier observes a commitment.
    ObserveCap([u8; 32]),
    SampleExt,
    SampleBits(usize),
    /// `check_witness(bits, witness)`.
    CheckWitness(usize, u64),
    /// `grind(bits)`, recorded as the `check_witness` of the witness found.
    Grind(usize),
}

fn run_script<H>(name: &str, doc: &str, initial: Vec<u8>, hasher: H, steps: &[Step])
where
    H: CryptographicHasher<u8, [u8; 32]> + Sync + Send,
{
    let mut ch = SerializingChallenger64::<F, HashChallenger<u8, H, 32>>::from_hasher(initial, hasher);
    let mut lines = Vec::new();
    for step in steps {
        match step.clone() {
            Step::ObserveBase(a) => {
                ch.observe(F::new(a));
                lines.push(format!("  .observeBase {a:#018x}"));
            }
            Step::ObserveExt(a0, a1) => {
                ch.observe_algebra_element(ext(a0, a1));
                lines.push(format!("  .observeExt {a0:#018x} {a1:#018x}"));
            }
            Step::ObserveDigest(d) => {
                ch.observe(Hash::<F, u8, 32>::from(d));
                lines.push(format!("  .observeDigest \"{}\"", hex(&d)));
            }
            Step::ObserveCap(d) => {
                ch.observe(MerkleCap::<F, [u8; 32]>::new(vec![d]));
                lines.push(format!("  .observeDigest \"{}\"", hex(&d)));
            }
            Step::SampleExt => {
                let e: EF = ch.sample_algebra_element();
                let (x, y) = coords(e);
                lines.push(format!("  .sampleExt {x:#018x} {y:#018x}"));
            }
            Step::SampleBits(bits) => {
                let v = ch.sample_bits(bits);
                lines.push(format!("  .sampleBits {bits} {v}"));
            }
            Step::CheckWitness(bits, w) => {
                let ok = ch.check_witness(bits, F::new(w));
                lines.push(format!("  .checkWitness {bits} {w:#018x} {ok}"));
            }
            Step::Grind(bits) => {
                let w = ch.grind(bits);
                lines.push(format!("  .checkWitness {bits} {:#018x} true", c(w)));
            }
        }
    }
    println!();
    println!("/-- {doc} -/");
    println!("def {name} : List Step := [");
    println!("{}]", lines.join(",\n"));
}

/// A byte hash that provokes rejections. See the Lean test for the definition.
#[derive(Clone)]
struct ToyHash;

impl CryptographicHasher<u8, [u8; 32]> for ToyHash {
    fn hash_iter<I: IntoIterator<Item = u8>>(&self, input: I) -> [u8; 32] {
        let mut len: u64 = 0;
        let mut s: u64 = 0;
        for b in input {
            s = s.wrapping_mul(31).wrapping_add(b as u64);
            len += 1;
        }
        s = s.wrapping_add(len);
        let mut out = [0u8; 32];
        for k in 0..4u64 {
            let word = match (s.wrapping_add(k)) % 4 {
                0 => u64::MAX,
                2 => {
                    if (s >> 2) & 1 == 0 {
                        P
                    } else {
                        P - 1
                    }
                }
                _ => (s.wrapping_add(k)).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ (s >> 7),
            };
            out[8 * k as usize..8 * k as usize + 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    }
}

fn challenger() {
    println!("-- ## Challenger");
    let mut rng = SplitMix(4);
    let digest = |rng: &mut SplitMix| -> [u8; 32] {
        let mut d = [0u8; 32];
        for chunk in d.chunks_mut(8) {
            chunk.copy_from_slice(&rng.next().to_le_bytes());
        }
        d
    };

    use Step::*;
    let d1 = digest(&mut rng);
    let d2 = digest(&mut rng);
    let d3 = digest(&mut rng);
    let script1 = vec![
        // A sample from the empty transcript.
        SampleExt,
        // Observe after a sample that left output unread.
        ObserveBase(rng.next()),
        ObserveBase(P - 1),
        ObserveBase(0),
        // Three samples in a row: six words, across one refill.
        SampleExt,
        SampleExt,
        SampleExt,
        ObserveCap(d1),
        // Five words of bits, across one refill.
        SampleBits(10),
        SampleBits(1),
        SampleBits(63),
        SampleBits(20),
        SampleBits(5),
        ObserveExt(rng.next(), rng.next()),
        SampleExt,
        ObserveBase(rng.next()),
        SampleBits(16),
        SampleExt,
        ObserveDigest(d2),
        ObserveExt(P - 1, 1),
        ObserveBase(1 << 32),
        SampleBits(0),
        SampleBits(32),
        SampleExt,
        // An exact buffer: four words, then an observation, then four more.
        SampleExt,
        SampleExt,
        ObserveCap(d3),
        SampleExt,
        SampleExt,
        // Many samples in a row: several refills without observation.
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleExt,
        SampleBits(7),
        SampleBits(7),
        SampleBits(7),
        // Proof of work.
        Grind(12),
        SampleExt,
        CheckWitness(0, 12345),
        SampleBits(8),
        CheckWitness(3, 5),
        CheckWitness(3, 6),
        CheckWitness(1, 7),
        SampleExt,
        Grind(5),
        SampleBits(30),
    ];
    run_script(
        "blake3Script",
        "A transcript of the BLAKE3 challenger from the empty initial state.",
        vec![],
        Blake3,
        &script1,
    );

    let d4 = digest(&mut rng);
    let script2 = vec![
        ObserveCap(d4),
        ObserveBase(rng.next()),
        SampleExt,
        SampleBits(13),
        ObserveExt(rng.next(), rng.next()),
        SampleBits(13),
        SampleBits(13),
        SampleBits(13),
        SampleBits(13),
        SampleBits(13),
        SampleExt,
        Grind(8),
        SampleExt,
    ];
    run_script(
        "blake3InitialScript",
        "A transcript of the BLAKE3 challenger whose initial state is the 41 bytes\n`0, 1, …, 40`.",
        (0u8..=40).collect(),
        Blake3,
        &script2,
    );

    let mut script3 = vec![SampleExt, SampleExt, SampleBits(64 - 1), SampleBits(9), SampleExt];
    for i in 0..12u64 {
        script3.push(ObserveBase(i * 0x0101_0101 + 3));
        script3.push(SampleExt);
        script3.push(SampleBits(11));
        script3.push(SampleExt);
        script3.push(SampleExt);
        if i % 3 == 0 {
            script3.push(ObserveExt(i, i + 1));
            script3.push(SampleBits(40));
        }
    }
    run_script(
        "toyScript",
        "A transcript of the challenger over the toy hash, which makes sampling reject words.",
        vec![1, 2, 3],
        ToyHash,
        &script3,
    );

    // The toy hash itself, for the Lean copy.
    println!();
    println!("/-- `(n, digest)`: the toy hash of the `n` bytes `7 * i + 1` for `i < n`. -/");
    println!("def toyHashVectors : Array (Nat × String) := #[");
    let mut lines = Vec::new();
    for n in 0..12usize {
        let input: Vec<u8> = (0..n).map(|i| (7 * i + 1) as u8).collect();
        lines.push(format!("  ({n}, \"{}\")", hex(&ToyHash.hash_iter(input))));
    }
    println!("{}]", lines.join(",\n"));
}

/// A digest of the digests of many inputs: `acc = blake3(acc || blake3(input(n)))`
/// over all lengths `n` up to 5000 and around the chunk boundaries up to 300 chunks.
/// Also the same for rows of field elements of every length up to 600.
fn sweep() {
    let mut acc = [0u8; 32];
    let mut lens: Vec<usize> = (0..=5000).collect();
    for chunks in 5..=300usize {
        lens.extend([1024 * chunks - 1, 1024 * chunks, 1024 * chunks + 1, 1024 * chunks + 513]);
    }
    for &n in &lens {
        let input: Vec<u8> = (0..n).map(|i| (i % 251) as u8).collect();
        let d = blake3::hash(&input);
        let mut joined = acc.to_vec();
        joined.extend_from_slice(d.as_bytes());
        acc = *blake3::hash(&joined).as_bytes();
    }
    println!("bytes sweep: {}", hex(&acc));

    let field_hash = FieldHash::new(Blake3);
    let compress = Compress::new(Blake3);
    let mut acc = [0u8; 32];
    for n in 0..=600usize {
        let row = base_row(n as u64, n);
        let d: [u8; 32] = field_hash.hash_slice(&row);
        acc = compress.compress([acc, d]);
        let row = ext_row(n as u64 + 7, n);
        let flat: Vec<F> = <EF as BasedVectorSpace<F>>::flatten_to_base(row);
        let d: [u8; 32] = field_hash.hash_slice(&flat);
        acc = compress.compress([acc, d]);
    }
    println!("rows sweep: {}", hex(&acc));

    // A long challenger transcript: observe a digest and an element, sample
    // an extension element and bits, 20000 times.
    let mut ch = SerializingChallenger64::<F, HashChallenger<u8, Blake3, 32>>::from_hasher(vec![], Blake3);
    let mut x: u64 = 1;
    for i in 0..20000u64 {
        ch.observe(F::new(x));
        if i % 3 == 0 {
            ch.observe(Hash::<F, u8, 32>::from(acc));
        }
        let e: EF = ch.sample_algebra_element();
        let (c0, c1) = coords(e);
        let bits = ch.sample_bits((i % 40) as usize);
        if i % 5 == 0 {
            ch.observe_algebra_element(e);
        }
        x = c0 ^ c1.rotate_left(17) ^ (bits as u64);
    }
    println!("challenger sweep: {x:#018x}");
}

fn main() {
    let which = std::env::args().nth(1).unwrap_or_default();
    match which.as_str() {
        "sweep" => sweep(),
        "goldilocks" => goldilocks(),
        "extension" => extension(),
        "blake3" => blake3_vectors(),
        "hashers" => hashers(),
        "challenger" => challenger(),
        _ => {
            goldilocks();
            extension();
            blake3_vectors();
            hashers();
            challenger();
        }
    }
}
