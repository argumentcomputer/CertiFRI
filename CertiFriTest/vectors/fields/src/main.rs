//! Prints, as Lean definitions, values computed by Plonky3 for the BabyBear
//! field, its quartic extension and the scalar field of BN254.
//!
//! Usage: `certifri-field-vectors babybear | babybear-ext | bn254`.
#![allow(deprecated)]

use p3_baby_bear::BabyBear;
use p3_bn254::Bn254;
use p3_field::extension::{BinomialExtensionField, BinomiallyExtendable};
use p3_field::integers::QuotientMap;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField,
};

type EF = BinomialExtensionField<BabyBear, 4>;

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
        z ^ (z >> 31)
    }

    fn word(&mut self) -> u32 {
        (self.next() >> 32) as u32
    }

    fn words(&mut self) -> [u32; 4] {
        [self.word(), self.word(), self.word(), self.word()]
    }

    fn limbs(&mut self) -> [u64; 4] {
        [self.next(), self.next(), self.next(), self.next()]
    }
}

// ---------------------------------------------------------------- BabyBear

const P: u32 = 0x78000001;

fn bb(x: u32) -> BabyBear {
    BabyBear::new(x)
}

fn h(x: BabyBear) -> String {
    let value = x.as_canonical_u32();
    assert!(value < P);
    format!("0x{value:08x}")
}

fn hw(x: u32) -> String {
    format!("0x{x:08x}")
}

fn babybear() {
    assert_eq!(BabyBear::ORDER_U32, P);
    let edges: [u32; 16] = [
        0,
        1,
        2,
        31,
        (1 << 27) - 1,
        1 << 27,
        (1 << 27) + 1,
        1 << 30,
        P - (1 << 27),
        P - 2,
        P - 1,
        P,
        P + 1,
        (1 << 31) - 1,
        1 << 31,
        u32::MAX,
    ];
    let seconds: [u32; 4] = [1, 1 << 27, P - 1, u32::MAX];
    let mut rng = Rng(0xBABE_BEA2);

    let mut pairs: Vec<(u32, u32)> = Vec::new();
    for a in edges {
        for b in seconds {
            pairs.push((a, b));
        }
    }
    for _ in 0..30 {
        pairs.push((rng.word(), rng.word()));
    }
    println!("/-- `(a, b, a + b, a - b, a * b)`: the operands are any words of 32 bits, the");
    println!("results are canonical. -/");
    println!("def arithmeticVectors : Array (Nat × Nat × Nat × Nat × Nat) := #[");
    let lines: Vec<String> = pairs
        .iter()
        .map(|&(a, b)| {
            let (x, y) = (bb(a), bb(b));
            format!("  ({}, {}, {}, {}, {})", hw(a), hw(b), h(x + y), h(x - y), h(x * y))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let mut unary: Vec<u32> = edges.iter().copied().filter(|a| a % P != 0).collect();
    for _ in 0..30 {
        let a = rng.word();
        if a % P != 0 {
            unary.push(a);
        }
    }
    println!("/-- `(a, -a, a⁻¹)` for nonzero `a`. -/");
    println!("def unaryVectors : Array (Nat × Nat × Nat) := #[");
    let lines: Vec<String> = unary
        .iter()
        .map(|&a| {
            let x = bb(a);
            let inverse = x.try_inverse().unwrap();
            assert_eq!(x * inverse, BabyBear::ONE);
            format!("  ({}, {}, {})", hw(a), h(-x), h(inverse))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let exponents: [u64; 11] = [
        0,
        1,
        2,
        3,
        7,
        1 << 27,
        (P - 2) as u64,
        (P - 1) as u64,
        P as u64,
        (1 << 32) + 1,
        u64::MAX,
    ];
    println!("/-- `(a, n, a ^ n)`. -/");
    println!("def powerVectors : Array (Nat × Nat × Nat) := #[");
    let lines: Vec<String> = exponents
        .iter()
        .map(|&n| {
            let a = rng.word();
            format!("  ({}, {}, {})", hw(a), n, h(bb(a).exp_u64(n)))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    println!("/-- `BabyBear::two_adic_generator(k)` for `k = 0, …, 27`. -/");
    println!("def twoAdicGeneratorVectors : Array Nat := #[");
    assert_eq!(BabyBear::TWO_ADICITY, 27);
    let lines: Vec<String> = (0..=BabyBear::TWO_ADICITY)
        .map(|k| format!("  {}", h(BabyBear::two_adic_generator(k))))
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    println!("/-- `BabyBear::GENERATOR`. -/");
    println!("def generatorVector : Nat := {}", BabyBear::GENERATOR.as_canonical_u32());
    println!();

    println!("/-- `<BabyBear as BinomiallyExtendable<4>>::W`. -/");
    println!(
        "def nonResidueVector : Nat := {}",
        <BabyBear as BinomiallyExtendable<4>>::W.as_canonical_u32()
    );
    println!();

    let candidates: [u32; 9] = [0, 1, 31, P - 2, P - 1, P, P + 1, 1 << 31, u32::MAX];
    println!("/-- `(n, BabyBear::from_canonical_checked(n))` for words `n` of 32 bits. -/");
    println!("def canonicalVectors : Array (Nat × Option Nat) := #[");
    let lines: Vec<String> = candidates
        .iter()
        .map(|&n| {
            let checked: Option<BabyBear> = BabyBear::from_canonical_checked(n);
            match checked {
                Some(x) => format!("  ({}, some {})", hw(n), h(x)),
                None => format!("  ({}, none)", hw(n)),
            }
        })
        .collect();
    println!("{}]", lines.join(",\n"));
}

// ------------------------------------------------------------ BabyBearExt

fn ext(words: [u32; 4]) -> EF {
    EF::from_basis_coefficients_slice(&words.map(bb)).unwrap()
}

fn he(x: EF) -> String {
    let coords: &[BabyBear] = x.as_basis_coefficients_slice();
    assert_eq!(coords.len(), 4);
    format!("({}, {}, {}, {})", h(coords[0]), h(coords[1]), h(coords[2]), h(coords[3]))
}

fn hwe(words: [u32; 4]) -> String {
    format!("({}, {}, {}, {})", hw(words[0]), hw(words[1]), hw(words[2]), hw(words[3]))
}

fn words_of(x: EF) -> [u32; 4] {
    let coords: &[BabyBear] = x.as_basis_coefficients_slice();
    [0, 1, 2, 3].map(|i| coords[i].as_canonical_u32())
}

fn babybear_ext() {
    let mut rng = Rng(0xE87_BABE_BEA2);
    let top = P - 1;
    let specials: [[u32; 4]; 5] = [
        [0, 0, 0, 0],
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [top, top, top, top],
        [1 << 27, u32::MAX, P + 5, (1 << 31) - 1],
    ];

    let mut pairs: Vec<([u32; 4], [u32; 4])> = Vec::new();
    for a in specials {
        for b in specials {
            pairs.push((a, b));
        }
    }
    for _ in 0..15 {
        pairs.push((rng.words(), rng.words()));
    }
    println!("/-- `(a, b, a + b, a - b, a * b)`, each element as its coordinates. -/");
    println!("def arithmeticVectors : Array (E × E × E × E × E) := #[");
    let lines: Vec<String> = pairs
        .iter()
        .map(|&(a, b)| {
            let (x, y) = (ext(a), ext(b));
            format!(
                "  ({},\n    {},\n    {},\n    {},\n    {})",
                hwe(a),
                hwe(b),
                he(x + y),
                he(x - y),
                he(x * y)
            )
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let mut unary: Vec<[u32; 4]> = vec![
        [1, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1],
        [top, top, top, top],
        [1 << 27, u32::MAX, P + 5, (1 << 31) - 1],
        [0, 0, 5, 0],
        [3, 0, 0, 7],
        words_of(EF::GENERATOR),
        words_of(EF::two_adic_generator(28)),
        words_of(EF::two_adic_generator(29)),
    ];
    for _ in 0..15 {
        unary.push(rng.words());
    }
    println!("/-- `(a, -a, a⁻¹, a²)` for nonzero `a`. -/");
    println!("def unaryVectors : Array (E × E × E × E) := #[");
    let lines: Vec<String> = unary
        .iter()
        .map(|&a| {
            let x = ext(a);
            let inverse = x.try_inverse().unwrap();
            assert_eq!(x * inverse, EF::ONE);
            format!(
                "  ({},\n    {},\n    {},\n    {})",
                hwe(a),
                he(-x),
                he(inverse),
                he(x.square())
            )
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let exponents: [u64; 8] = [0, 1, 2, 5, P as u64, (1 << 32) + 1, 1 << 63, u64::MAX];
    println!("/-- `(a, n, a ^ n)`. -/");
    println!("def powerVectors : Array (E × Nat × E) := #[");
    let lines: Vec<String> = exponents
        .iter()
        .map(|&n| {
            let a = rng.words();
            format!("  ({}, {},\n    {})", hwe(a), n, he(ext(a).exp_u64(n)))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    println!("/-- `(a, e, EF::from(a) * e)`: the base element `a` times the extension element");
    println!("`e`. -/");
    println!("def embedVectors : Array (Nat × E × E) := #[");
    let lines: Vec<String> = (0..8)
        .map(|_| {
            let a = rng.word();
            let b = rng.words();
            let product = EF::from(bb(a)) * ext(b);
            assert_eq!(product, ext(b) * bb(a));
            format!("  ({}, {},\n    {})", hw(a), hwe(b), he(product))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let mut slices: Vec<[u32; 4]> = vec![
        [0, 0, 0, 0],
        [100, 101, 102, 103],
        [top, 0, top, 0],
        [P, P + 1, u32::MAX, 1 << 31],
    ];
    for _ in 0..4 {
        slices.push(rng.words());
    }
    println!("/-- `(c, EF::from_basis_coefficients_slice(c).as_basis_coefficients_slice())`: the");
    println!("coordinates `c` are any words of 32 bits. -/");
    println!("def basisVectors : Array (E × E) := #[");
    let lines: Vec<String> = slices
        .iter()
        .map(|&c| {
            let x = EF::from_basis_coefficients_slice(&c.map(bb)).unwrap();
            let coords: &[BabyBear] = x.as_basis_coefficients_slice();
            assert_eq!(EF::from_basis_coefficients_slice(coords).unwrap(), x);
            format!("  ({},\n    {})", hwe(c), he(x))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    // A slice of another length is rejected.
    assert!(EF::from_basis_coefficients_slice(&[bb(1), bb(2), bb(3)]).is_none());
    assert!(EF::from_basis_coefficients_slice(&[bb(1), bb(2), bb(3), bb(4), bb(5)]).is_none());
    assert_eq!(<EF as BasedVectorSpace<BabyBear>>::DIMENSION, 4);

    println!("/-- `EF::ith_basis_element(i)` for `i = 0, …, 3`. -/");
    println!("def basisElementVectors : Array E := #[");
    let lines: Vec<String> = (0..4)
        .map(|i| {
            let x: EF = <EF as BasedVectorSpace<BabyBear>>::ith_basis_element(i).unwrap();
            format!("  {}", he(x))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    println!("/-- `EF::from(BabyBear::new(5))`. -/");
    println!("def embedFiveVector : E := {}", he(EF::from(bb(5))));
    println!();

    println!("/-- `EF::GENERATOR`, a generator of the multiplicative group. -/");
    println!("def generatorVector : E := {}", he(EF::GENERATOR));
    println!();

    assert_eq!(<EF as TwoAdicField>::TWO_ADICITY, 29);
    println!("/-- `EF::two_adic_generator(k)` for `k = 27, 28, 29`. -/");
    println!("def twoAdicGeneratorVectors : Array E := #[");
    let lines: Vec<String> =
        (27..=29).map(|k| format!("  {}", he(EF::two_adic_generator(k)))).collect();
    println!("{}]", lines.join(",\n"));
}

// ------------------------------------------------------------------- BN254

fn hb(x: Bn254) -> String {
    let digits = x.as_canonical_biguint().to_str_radix(16);
    assert!(digits.len() <= 64);
    format!("0x{digits:0>64}")
}

fn hl(limbs: [u64; 4]) -> String {
    format!("0x{:016x}{:016x}{:016x}{:016x}", limbs[3], limbs[2], limbs[1], limbs[0])
}

fn bn254() {
    // The order `r`, in little-endian limbs.
    let r: [u64; 4] =
        [0x43e1f593f0000001, 0x2833e84879b97091, 0xb85045b68181585d, 0x30644e72e131a029];
    let r_minus = |k: u64| [r[0] - k, r[1], r[2], r[3]];
    let edges: [[u64; 4]; 12] = [
        [0, 0, 0, 0],
        [1, 0, 0, 0],
        [5, 0, 0, 0],
        [u64::MAX, 0, 0, 0],
        [0, 1, 0, 0],
        [0, 0, 1, 0],
        [0, 0, 0, 1 << 61],
        r_minus(2),
        r_minus(1),
        r,
        [r[0] + 1, r[1], r[2], r[3]],
        [u64::MAX; 4],
    ];
    let seconds: [[u64; 4]; 2] = [r_minus(1), [u64::MAX; 4]];
    let mut rng = Rng(0xB7_254);
    assert_eq!(Bn254::new(r), Bn254::ZERO);

    let mut pairs: Vec<([u64; 4], [u64; 4])> = Vec::new();
    for a in edges {
        for b in seconds {
            pairs.push((a, b));
        }
    }
    for _ in 0..16 {
        pairs.push((rng.limbs(), rng.limbs()));
    }
    println!("/-- `(a, b, a + b, a - b, a * b)`: the operands are any numbers of 256 bits, the");
    println!("results are canonical. -/");
    println!("def arithmeticVectors : Array (Nat × Nat × Nat × Nat × Nat) := #[");
    let lines: Vec<String> = pairs
        .iter()
        .map(|&(a, b)| {
            let (x, y) = (Bn254::new(a), Bn254::new(b));
            format!(
                "  ({},\n    {},\n    {},\n    {},\n    {})",
                hl(a),
                hl(b),
                hb(x + y),
                hb(x - y),
                hb(x * y)
            )
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let mut unary: Vec<[u64; 4]> =
        edges.iter().copied().filter(|&a| Bn254::new(a) != Bn254::ZERO).collect();
    for _ in 0..12 {
        unary.push(rng.limbs());
    }
    println!("/-- `(a, -a, a⁻¹)` for nonzero `a`. -/");
    println!("def unaryVectors : Array (Nat × Nat × Nat) := #[");
    let lines: Vec<String> = unary
        .iter()
        .map(|&a| {
            let x = Bn254::new(a);
            let inverse = x.try_inverse().unwrap();
            assert_eq!(x * inverse, Bn254::ONE);
            format!("  ({},\n    {},\n    {})", hl(a), hb(-x), hb(inverse))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    let exponents: [u64; 7] = [0, 1, 2, 3, 1 << 28, (1 << 32) + 1, u64::MAX];
    println!("/-- `(a, n, a ^ n)`. -/");
    println!("def powerVectors : Array (Nat × Nat × Nat) := #[");
    let lines: Vec<String> = exponents
        .iter()
        .map(|&n| {
            let a = rng.limbs();
            format!("  ({},\n    {},\n    {})", hl(a), n, hb(Bn254::new(a).exp_u64(n)))
        })
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    assert_eq!(Bn254::TWO_ADICITY, 28);
    println!("/-- `Bn254::two_adic_generator(k)` for `k = 0, …, 28`. -/");
    println!("def twoAdicGeneratorVectors : Array Nat := #[");
    let lines: Vec<String> = (0..=Bn254::TWO_ADICITY)
        .map(|k| format!("  {}", hb(Bn254::two_adic_generator(k))))
        .collect();
    println!("{}]", lines.join(",\n"));
    println!();

    println!("/-- `Bn254::GENERATOR`. -/");
    println!("def generatorVector : Nat := {}", Bn254::GENERATOR.as_canonical_biguint());
    println!();

    println!("/-- The order of the field, as Plonky3 prints `Bn254::order()`. -/");
    println!("def orderVector : Nat :=\n  {}", Bn254::order());
}

fn main() {
    match std::env::args().nth(1).as_deref() {
        Some("babybear") => babybear(),
        Some("babybear-ext") => babybear_ext(),
        Some("bn254") => bn254(),
        _ => {
            eprintln!("usage: certifri-field-vectors babybear | babybear-ext | bn254");
            std::process::exit(2);
        }
    }
}
