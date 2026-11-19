//! Known-answer values for the primitives, one at a time: Goldilocks, its
//! quadratic extension, BLAKE3, the leaf hash, the compression, and the
//! challenger. Every value is computed by Plonky3; where `model.rs` restates a
//! primitive at the level of bytes, the two are required to agree.

use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_symmetric::{CryptographicHasher, PseudoCompressionFunction};

use crate::config::{
    ext, fresh_challenger, j_bytes, j_ext, j_val, j_vals, Challenge, Challenger, Commitment,
    Compress, Digest, FieldHash, SplitMix64, Val, P, PLONKY3_REV,
};
use crate::json::Json;
use crate::model::{blake3, compress, hash_vals, ModelChallenger};

/// Byte `i` of every BLAKE3 test input is `i mod 251`, as in the official
/// BLAKE3 test vectors.
pub fn pattern_bytes(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

/// Element `i` of every leaf-hash test input: `(i + 1) * 0x0123456789ABCDEF mod p`.
pub fn pattern_vals(len: usize) -> Vec<Val> {
    (0..len)
        .map(|i| Val::new((((i as u128 + 1) * 0x0123_4567_89AB_CDEF) % P as u128) as u64))
        .collect()
}

fn goldilocks(rng: &mut SplitMix64) -> Json {
    let v = Val::new;
    let mut operands: Vec<(Val, Val)> = vec![
        (v(0), v(5)),
        (v(1), v(P - 1)),
        (v(P - 1), v(P - 1)),
        (v(1 << 32), v(1 << 32)),
        (v(1 << 63), v(2)),
        (v(0xFFFF_FFFF), v(0xFFFF_FFFF)),
        (v(P - 2), v(1 << 32)),
    ];
    for _ in 0..5 {
        operands.push((rng.val(), rng.val()));
    }
    let binary = |name: &'static str, f: fn(Val, Val) -> Val| {
        Json::arr(&operands, |(a, b)| {
            Json::Obj(vec![
                ("a", j_val(*a)),
                ("b", j_val(*b)),
                (name, j_val(f(*a, *b))),
            ])
        })
    };

    let mut invertible = vec![v(1), v(2), v(7), v(P - 1), v(1 << 32), v(0xFFFF_FFFF)];
    for _ in 0..4 {
        invertible.push(rng.val());
    }
    let inv = Json::arr(&invertible, |a| {
        let inverse = a.inverse();
        assert_eq!(*a * inverse, Val::ONE);
        Json::Obj(vec![("a", j_val(*a)), ("inverse", j_val(inverse))])
    });

    let powers: Vec<(Val, u64)> = vec![
        (v(7), 0),
        (v(7), 1),
        (v(7), (P - 1) / 2),
        (v(7), P - 1),
        (Val::two_adic_generator(32), 1 << 31),
        (Val::two_adic_generator(5), 19),
        (rng.val(), rng.next_u64()),
        (rng.val(), rng.next_u64()),
    ];
    let exp = Json::arr(&powers, |(base, exponent)| {
        Json::Obj(vec![
            ("base", j_val(*base)),
            ("exponent", Json::Num(*exponent)),
            ("power", j_val(base.exp_u64(*exponent))),
        ])
    });

    let generators: Vec<Val> = (0..=Val::TWO_ADICITY)
        .map(Val::two_adic_generator)
        .collect();
    for k in 0..Val::TWO_ADICITY {
        assert_eq!(generators[k + 1].square(), generators[k]);
    }
    assert_eq!(generators[0], Val::ONE);

    Json::Obj(vec![
        ("modulus", Json::Num(Val::ORDER_U64)),
        ("generator", j_val(Val::GENERATOR)),
        ("two_adicity", Json::num(Val::TWO_ADICITY)),
        ("two_adic_generators", j_vals(&generators)),
        ("add", binary("sum", |a, b| a + b)),
        ("sub", binary("difference", |a, b| a - b)),
        ("mul", binary("product", |a, b| a * b)),
        ("inv", inv),
        ("exp", exp),
    ])
}

fn extension(rng: &mut SplitMix64) -> Json {
    let e = |c0: u64, c1: u64| ext(Val::new(c0), Val::new(c1));
    let mut operands: Vec<(Challenge, Challenge)> = vec![
        (e(0, 1), e(0, 1)),
        (e(1, 0), e(3, 4)),
        (e(0, 0), e(3, 4)),
        (e(P - 1, P - 1), e(P - 1, P - 1)),
        (e(5, 0), e(0, P - 2)),
    ];
    for _ in 0..5 {
        operands.push((rng.ext(), rng.ext()));
    }
    let binary = |name: &'static str, f: fn(Challenge, Challenge) -> Challenge| {
        Json::arr(&operands, |(a, b)| {
            Json::Obj(vec![
                ("a", j_ext(*a)),
                ("b", j_ext(*b)),
                (name, j_ext(f(*a, *b))),
            ])
        })
    };

    let mut invertible = vec![e(1, 0), e(0, 1), e(2, 0), e(P - 1, P - 1), e(3, 4)];
    for _ in 0..5 {
        invertible.push(rng.ext());
    }
    let inv = Json::arr(&invertible, |a| {
        let inverse = a.inverse();
        assert_eq!(*a * inverse, Challenge::ONE);
        Json::Obj(vec![("a", j_ext(*a)), ("inverse", j_ext(inverse))])
    });

    // The basis is `1, X` with `X^2 = 7`.
    assert_eq!(e(0, 1) * e(0, 1), e(7, 0));

    Json::Obj(vec![
        ("non_residue", Json::Num(7)),
        ("add", binary("sum", |a, b| a + b)),
        ("sub", binary("difference", |a, b| a - b)),
        ("mul", binary("product", |a, b| a * b)),
        ("inv", inv),
    ])
}

fn blake3_vectors() -> Json {
    let lengths = [
        0usize, 1, 2, 3, 8, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025, 2048, 2049, 3000, 3072,
        3073, 4096, 4097, 5000, 7168, 8192, 8193,
    ];
    // The first of the official BLAKE3 test vectors.
    assert_eq!(
        blake3(&[])[..8],
        [0xaf, 0x13, 0x49, 0xb9, 0xf5, 0xf9, 0xa1, 0xa6]
    );
    Json::arr(lengths, |len| {
        Json::Obj(vec![
            ("len", Json::num(len)),
            ("digest", j_bytes(&blake3(&pattern_bytes(len)))),
        ])
    })
}

fn leaf_hash_vectors() -> Json {
    let hasher = FieldHash::new(p3_blake3::Blake3);
    let v = Val::new;
    let mut inputs: Vec<Vec<Val>> = [0usize, 1, 2, 3, 4, 8, 16, 127, 128, 129, 300]
        .iter()
        .map(|&len| pattern_vals(len))
        .collect();
    inputs.push(vec![
        v(0),
        v(1),
        v(P - 1),
        v(1 << 32),
        v(0xFFFF_FFFF),
        v(P - (1 << 32)),
    ]);
    Json::arr(&inputs, |values| {
        let digest: Digest = hasher.hash_iter(values.iter().copied());
        assert_eq!(digest, hash_vals(values));
        // Hashing several rows hashes their concatenation.
        let (left, right) = values.split_at(values.len() / 2);
        let split: Digest = hasher.hash_iter_slices([left, right]);
        assert_eq!(split, digest);
        Json::Obj(vec![
            ("values", j_vals(values)),
            ("digest", j_bytes(&digest)),
        ])
    })
}

fn compress_vectors() -> Json {
    let compressor = Compress::new(p3_blake3::Blake3);
    let pattern = pattern_bytes(64);
    let pairs: Vec<(Digest, Digest)> = vec![
        ([0u8; 32], [0u8; 32]),
        ([0xFFu8; 32], [0u8; 32]),
        (
            pattern[..32].try_into().unwrap(),
            pattern[32..].try_into().unwrap(),
        ),
        (blake3(&[]), blake3(&[0])),
        (blake3(&[0]), blake3(&[])),
    ];
    Json::arr(&pairs, |(left, right)| {
        let digest: Digest = compressor.compress([*left, *right]);
        assert_eq!(digest, compress(left, right));
        Json::Obj(vec![
            ("left", j_bytes(left)),
            ("right", j_bytes(right)),
            ("digest", j_bytes(&digest)),
        ])
    })
}

/// The least field element whose observation, from the empty state, puts one
/// of the four 64-bit samples of the first digest (the fourth) at or above the
/// modulus. Found by `examples/find_rejection.rs`.
const REJECTION_WITNESS: u64 = 209_304_950;

/// One step of a challenger script.
enum Step {
    ObserveBase(Val),
    ObserveExt(Challenge),
    ObserveDigest(Digest),
    SampleExt,
    SampleBits(usize),
    CheckWitness(usize, Val),
    /// Search for a witness of that many bits, then check it.
    Grind(usize),
}

/// Run a script from the empty state on Plonky3's challenger and on the model,
/// require every output to agree, and record every step with the buffers of
/// the model after it.
fn run_script(name: &'static str, steps: &[Step]) -> Json {
    let mut p3: Challenger = fresh_challenger();
    let mut model = ModelChallenger::new();
    let mut recorded = vec![];
    for step in steps {
        let mut fields: Vec<(&'static str, Json)> = match step {
            Step::ObserveBase(x) => {
                p3.observe(*x);
                model.observe_base(*x);
                vec![("op", Json::str("observe_base")), ("value", j_val(*x))]
            }
            Step::ObserveExt(e) => {
                p3.observe_algebra_element(*e);
                model.observe_ext(*e);
                vec![("op", Json::str("observe_ext")), ("value", j_ext(*e))]
            }
            Step::ObserveDigest(d) => {
                p3.observe(Commitment::new(vec![*d]));
                model.observe_digest(d);
                vec![("op", Json::str("observe_digest")), ("value", j_bytes(d))]
            }
            Step::SampleExt => {
                let result: Challenge = p3.sample_algebra_element();
                assert_eq!(result, model.sample_ext());
                vec![("op", Json::str("sample_ext")), ("result", j_ext(result))]
            }
            Step::SampleBits(bits) => {
                let result = p3.sample_bits(*bits);
                assert_eq!(result, model.sample_bits(*bits));
                vec![
                    ("op", Json::str("sample_bits")),
                    ("bits", Json::num(*bits)),
                    ("result", Json::num(result)),
                ]
            }
            Step::CheckWitness(bits, witness) => {
                check_witness(&mut p3, &mut model, *bits, *witness)
            }
            Step::Grind(bits) => {
                let witness = p3.clone().grind(*bits);
                let fields = check_witness(&mut p3, &mut model, *bits, witness);
                assert_eq!(fields[3].1, Json::Bool(true));
                fields
            }
        };
        fields.push(("input_buffer", j_bytes(&model.input)));
        fields.push(("output_buffer", j_bytes(&model.output)));
        recorded.push(Json::Obj(fields));
    }
    Json::Obj(vec![
        ("name", Json::str(name)),
        ("steps", Json::Arr(recorded)),
    ])
}

fn check_witness(
    p3: &mut Challenger,
    model: &mut ModelChallenger,
    bits: usize,
    witness: Val,
) -> Vec<(&'static str, Json)> {
    let result = p3.check_witness(bits, witness);
    assert_eq!(result, model.check_witness(bits, witness));
    vec![
        ("op", Json::str("check_witness")),
        ("bits", Json::num(bits)),
        ("witness", j_val(witness)),
        ("result", Json::Bool(result)),
    ]
}

fn challenger_scripts() -> Json {
    let v = Val::new;
    let main = [
        Step::ObserveBase(v(1)),
        Step::ObserveBase(v(P - 1)),
        Step::ObserveBase(v(0x0123_4567_89AB_CDEF)),
        Step::ObserveDigest(blake3(&[])),
        Step::ObserveExt(ext(v(5), v(7))),
        Step::SampleExt,
        Step::ObserveBase(v(42)),
        Step::SampleBits(10),
        // At zero bits a witness check touches nothing.
        Step::CheckWitness(0, v(123)),
        Step::Grind(8),
        Step::CheckWitness(8, v(0)),
        // Three extension samples in a row run past one 32-byte digest.
        Step::SampleExt,
        Step::SampleExt,
        Step::SampleExt,
        Step::SampleBits(1),
        Step::SampleBits(32),
        Step::SampleBits(63),
        Step::SampleBits(0),
        Step::ObserveDigest(blake3(&[0])),
        Step::ObserveExt(ext(v(P - 1), v(0))),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::Grind(12),
        Step::SampleExt,
    ];
    // A sample straight from the empty state hashes the empty input.
    let empty = [Step::SampleExt, Step::SampleBits(20), Step::SampleExt];

    // After observing this element the fourth 64-bit sample is at or above
    // the modulus.
    let mut probe = ModelChallenger::new();
    probe.observe_base(v(REJECTION_WITNESS));
    let samples: [u64; 4] = core::array::from_fn(|_| probe.sample_u64());
    assert!(samples[..3].iter().all(|&s| s < P) && samples[3] >= P);
    // A field sample skips it: the second extension element takes its second
    // coefficient from the next digest.
    let rejection = [
        Step::ObserveBase(v(REJECTION_WITNESS)),
        Step::SampleExt,
        Step::SampleExt,
        Step::SampleExt,
    ];
    // A bit sample does not: the fourth one below masks that very sample.
    let bits_keep = [
        Step::ObserveBase(v(REJECTION_WITNESS)),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::SampleBits(16),
        Step::SampleBits(63),
        Step::SampleBits(16),
    ];
    Json::Arr(vec![
        run_script("main", &main),
        run_script("empty", &empty),
        run_script("rejection", &rejection),
        run_script("bits_keep_large_samples", &bits_keep),
    ])
}

pub fn primitives() -> Json {
    let mut rng = SplitMix64::new(0x7072_696d_6974_6976);
    Json::Obj(vec![
        ("plonky3_rev", Json::str(PLONKY3_REV)),
        ("goldilocks", goldilocks(&mut rng)),
        ("extension", extension(&mut rng)),
        ("blake3", blake3_vectors()),
        ("leaf_hash", leaf_hash_vectors()),
        ("compress", compress_vectors()),
        ("challenger", challenger_scripts()),
    ])
}
