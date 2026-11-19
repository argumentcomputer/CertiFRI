import CertiFriP3.Goldilocks

/-!
# Tests of the Goldilocks field

Two kinds of checks of `CertiFriP3/Goldilocks.lean`.

* Against natural-number arithmetic. The operations work on machine words; the
  checks compare them with the same operations on natural numbers modulo `p`,
  on words at the edges of the reduction (around `2^32`, `2^63`, `2^64` and
  `p`) and on pseudo-random words.
* Against Plonky3. The vectors of the second part were computed by Plonky3 at
  revision `3152b14a` (`p3_goldilocks::Goldilocks`): sums, differences,
  products, opposites, inverses, powers, the generators of the two-adic
  subgroups and the generator of the multiplicative group.
-/

namespace CertiFriTest.P3.Goldilocks

open CertiFri CertiFri.P3

/-- The order of the field. -/
def p : Nat := Goldilocks.order

/-- The element a word represents. -/
def g (word : UInt64) : Goldilocks := Goldilocks.ofUInt64 word

/-! ## Construction and representation -/

#guard p = 2 ^ 64 - 2 ^ 32 + 1
#guard (Goldilocks.ofNat 0).val = 0 ∧ (Goldilocks.ofNat p).val = 0
#guard (Goldilocks.ofNat (p + 5)).val = 5 ∧ (Goldilocks.ofNat (p - 1)).toNat = p - 1
#guard (Goldilocks.ofNat (2 ^ 200 + 3)).toNat = (2 ^ 200 + 3) % p
#guard (g 0xFFFFFFFF00000000).toNat = p - 1 ∧ (g 0xFFFFFFFF00000001).toNat = 0
#guard (g 0xFFFFFFFFFFFFFFFF).toNat = 2 ^ 64 - 1 - p
#guard (Goldilocks.ofCanonical? 0).map (·.val) = some 0
#guard (Goldilocks.ofCanonical? 0xFFFFFFFF00000000).map (·.val) = some 0xFFFFFFFF00000000
#guard (Goldilocks.ofCanonical? 0xFFFFFFFF00000001).isNone
#guard (Goldilocks.ofCanonical? 0xFFFFFFFFFFFFFFFF).isNone
#guard (0 : Goldilocks).val = 0 ∧ (1 : Goldilocks).val = 1 ∧ (default : Goldilocks).val = 0
#guard g 5 = Goldilocks.ofNat 5 ∧ g 5 ≠ g 6 ∧ g 5 == Goldilocks.ofNat (p + 5) ∧ !(g 5 == g 6)
#guard (Goldilocks.pushBytes ByteArray.empty (g 0x0123456789ABCDEF)).data
  = #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01]
#guard (Goldilocks.pushBytes (ByteArray.mk #[7]) (Goldilocks.ofNat p)).data
  = #[7, 0, 0, 0, 0, 0, 0, 0, 0]

/-! ## Against natural-number arithmetic -/

/-- Representatives at the edges of the word arithmetic. -/
def edges : Array Nat := #[
  0, 1, 2, 3, 7, 2 ^ 16, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 2, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 32 + 1, 2 ^ 33 - 1,
  2 ^ 33, 2 ^ 48, 2 ^ 63 - 1, 2 ^ 63, 2 ^ 63 + 1, 2 ^ 64 - 2 ^ 33, 2 ^ 64 - 2 ^ 33 + 1,
  p - 2 ^ 32 - 1, p - 2 ^ 32, p - 2 ^ 32 + 1, p - 2 ^ 31, p - 3, p - 2, p - 1]

/-- The four operations on the elements `a` and `b` agree with the operations
on natural numbers modulo `p`. -/
def agrees (a b : Nat) : Bool :=
  let x := Goldilocks.ofNat a
  let y := Goldilocks.ofNat b
  (x + y).toNat == (a + b) % p && (x - y).toNat == (a + (p - b % p)) % p
    && (x * y).toNat == a * b % p && (-x).toNat == (p - a % p) % p

#guard edges.all fun a => edges.all fun b => agrees a b

/-- The high word of the product agrees with the product of natural numbers. -/
def highAgrees (a b : Nat) : Bool :=
  (Goldilocks.mulHigh a.toUInt64 b.toUInt64).toNat == a * b / 2 ^ 64

#guard (edges ++ #[p, p + 1, 2 ^ 64 - 2, 2 ^ 64 - 1]).all fun a =>
  (edges ++ #[p, p + 1, 2 ^ 64 - 2, 2 ^ 64 - 1]).all fun b => highAgrees a b

/-- The reduction of `hi * 2^64 + lo` agrees with the remainder modulo `p`. -/
def reduceAgrees (hi lo : Nat) : Bool :=
  (Goldilocks.reduce128 hi.toUInt64 lo.toUInt64).toNat == (hi * 2 ^ 64 + lo) % p

/-- Words at the edges of the reduction: every word is a possible low word, and
the high words of a product of canonical words are below `p - 1`. -/
def words : Array Nat := edges ++ #[p, p + 1, 2 ^ 64 - 2 ^ 32, 2 ^ 64 - 2, 2 ^ 64 - 1]

#guard words.all fun hi => words.all fun lo => reduceAgrees hi lo

/-- One step of the SplitMix64 generator: the next state and the output. -/
def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let state := state + 0x9E3779B97F4A7C15
  let z := (state ^^^ (state >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (state, z ^^^ (z >>> 31))

/-- Whether `check` holds on `count` pairs of pseudo-random words. -/
def onRandomPairs (check : Nat → Nat → Bool) : (count : Nat) → (state : UInt64) → Bool
  | 0, _ => true
  | count + 1, state =>
    let first := splitMix state
    let second := splitMix first.1
    check first.2.toNat second.2.toNat && onRandomPairs check count second.1

#guard onRandomPairs agrees 2000 1
#guard onRandomPairs highAgrees 2000 2
#guard onRandomPairs reduceAgrees 2000 3

/-- The inverse of `a` is the element whose product with `a` is one, and it is
`a ^ (p - 2)`. The inverse of zero is zero. -/
def inverseAgrees (a : Nat) : Bool :=
  let x := Goldilocks.ofNat a
  if a % p = 0 then x⁻¹ == 0 else x * x⁻¹ == 1 && x⁻¹ == fieldPow x (p - 2)

#guard edges.all inverseAgrees
#guard inverseAgrees p
#guard onRandomPairs (fun a b => inverseAgrees a && inverseAgrees b) 150 4

/-! ## The two-adic structure -/

#guard TwoAdicOps.twoAdicity Goldilocks = 32
#guard (TwoAdicOps.cosetShift : Goldilocks).val = 7

/-- The generator of order `2^k` has order exactly `2^k`, and it is the square
of the generator of order `2^(k+1)`. -/
def generatorAgrees (k : Nat) : Bool :=
  let w : Goldilocks := TwoAdicOps.twoAdicGenerator k
  fieldPow w (2 ^ k) == 1 && (k = 0 || fieldPow w (2 ^ (k - 1)) == -1)
    && (k = 32 || (let next : Goldilocks := TwoAdicOps.twoAdicGenerator (k + 1); next * next == w))

#guard (List.range 33).all generatorAgrees

-- The generator of the largest two-adic subgroup is a power of the generator
-- of the multiplicative group, which is not a square.
#guard fieldPow Goldilocks.generator ((p - 1) / 2 ^ 32) = Goldilocks.twoAdicGenerator 32
#guard fieldPow Goldilocks.generator ((p - 1) / 2) = -1
-- Past the two-adicity there is no generator.
#guard (Goldilocks.twoAdicGenerator 33).val = 0 ∧ (Goldilocks.twoAdicGenerator 1000).val = 0

/-! ## Against Plonky3 -/

/-- `(a, b, a + b, a - b, a * b)`: the operands are any words, the results are
canonical. -/
def arithmeticVectors : Array (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) := #[
  (0x0000000000000000, 0x0000000100000000,
    0x0000000100000000, 0xfffffffe00000001, 0x0000000000000000),
  (0x0000000000000000, 0xffffffff00000000,
    0xffffffff00000000, 0x0000000000000001, 0x0000000000000000),
  (0x0000000000000000, 0xffffffffffffffff,
    0x00000000fffffffe, 0xfffffffe00000003, 0x0000000000000000),
  (0x0000000000000001, 0x0000000100000000,
    0x0000000100000001, 0xfffffffe00000002, 0x0000000100000000),
  (0x0000000000000001, 0xffffffff00000000,
    0x0000000000000000, 0x0000000000000002, 0xffffffff00000000),
  (0x0000000000000001, 0xffffffffffffffff,
    0x00000000ffffffff, 0xfffffffe00000004, 0x00000000fffffffe),
  (0x0000000000000002, 0x0000000100000000,
    0x0000000100000002, 0xfffffffe00000003, 0x0000000200000000),
  (0x0000000000000002, 0xffffffff00000000,
    0x0000000000000001, 0x0000000000000003, 0xfffffffeffffffff),
  (0x0000000000000002, 0xffffffffffffffff,
    0x0000000100000000, 0xfffffffe00000005, 0x00000001fffffffc),
  (0x0000000000000007, 0x0000000100000000,
    0x0000000100000007, 0xfffffffe00000008, 0x0000000700000000),
  (0x0000000000000007, 0xffffffff00000000,
    0x0000000000000006, 0x0000000000000008, 0xfffffffefffffffa),
  (0x0000000000000007, 0xffffffffffffffff,
    0x0000000100000005, 0xfffffffe0000000a, 0x00000006fffffff2),
  (0x000000007fffffff, 0x0000000100000000,
    0x000000017fffffff, 0xfffffffe80000000, 0x7fffffff00000000),
  (0x000000007fffffff, 0xffffffff00000000,
    0x000000007ffffffe, 0x0000000080000000, 0xfffffffe80000002),
  (0x000000007fffffff, 0xffffffffffffffff,
    0x000000017ffffffd, 0xfffffffe80000002, 0x7ffffffe00000002),
  (0x0000000080000000, 0x0000000100000000,
    0x0000000180000000, 0xfffffffe80000001, 0x8000000000000000),
  (0x0000000080000000, 0xffffffff00000000,
    0x000000007fffffff, 0x0000000080000001, 0xfffffffe80000001),
  (0x0000000080000000, 0xffffffffffffffff,
    0x000000017ffffffe, 0xfffffffe80000003, 0x7fffffff00000000),
  (0x00000000ffffffff, 0x0000000100000000,
    0x00000001ffffffff, 0xffffffff00000000, 0xffffffff00000000),
  (0x00000000ffffffff, 0xffffffff00000000,
    0x00000000fffffffe, 0x0000000100000000, 0xfffffffe00000002),
  (0x00000000ffffffff, 0xffffffffffffffff,
    0x00000001fffffffd, 0x0000000000000001, 0xfffffffd00000002),
  (0x0000000100000000, 0x0000000100000000,
    0x0000000200000000, 0x0000000000000000, 0x00000000ffffffff),
  (0x0000000100000000, 0xffffffff00000000,
    0x00000000ffffffff, 0x0000000100000001, 0xfffffffe00000001),
  (0x0000000100000000, 0xffffffffffffffff,
    0x00000001fffffffe, 0x0000000000000002, 0xfffffffe00000000),
  (0x0000000100000001, 0x0000000100000000,
    0x0000000200000001, 0x0000000000000001, 0x00000001ffffffff),
  (0x0000000100000001, 0xffffffff00000000,
    0x0000000100000000, 0x0000000100000002, 0xfffffffe00000000),
  (0x0000000100000001, 0xffffffffffffffff,
    0x00000001ffffffff, 0x0000000000000003, 0xfffffffefffffffe),
  (0x0000000200000000, 0x0000000100000000,
    0x0000000300000000, 0x0000000100000000, 0x00000001fffffffe),
  (0x0000000200000000, 0xffffffff00000000,
    0x00000001ffffffff, 0x0000000200000001, 0xfffffffd00000001),
  (0x0000000200000000, 0xffffffffffffffff,
    0x00000002fffffffe, 0x0000000100000002, 0xfffffffcffffffff),
  (0x7fffffffffffffff, 0x0000000100000000,
    0x80000000ffffffff, 0x7ffffffeffffffff, 0x7ffffffe80000000),
  (0x7fffffffffffffff, 0xffffffff00000000,
    0x7ffffffffffffffe, 0x8000000000000000, 0x7fffffff00000002),
  (0x7fffffffffffffff, 0xffffffffffffffff,
    0x80000000fffffffd, 0x7fffffff00000001, 0x7ffffffd80000003),
  (0x8000000000000000, 0x0000000100000000,
    0x8000000100000000, 0x7fffffff00000000, 0x7fffffff80000000),
  (0x8000000000000000, 0xffffffff00000000,
    0x7fffffffffffffff, 0x8000000000000001, 0x7fffffff00000001),
  (0x8000000000000000, 0xffffffffffffffff,
    0x80000000fffffffe, 0x7fffffff00000002, 0x7ffffffe80000001),
  (0x8000000000000001, 0x0000000100000000,
    0x8000000100000001, 0x7fffffff00000001, 0x8000000080000000),
  (0x8000000000000001, 0xffffffff00000000,
    0x8000000000000000, 0x8000000000000002, 0x7fffffff00000000),
  (0x8000000000000001, 0xffffffffffffffff,
    0x80000000ffffffff, 0x7fffffff00000003, 0x7fffffff7fffffff),
  (0xfffffffeffffffff, 0x0000000100000000,
    0x00000000fffffffe, 0xfffffffdffffffff, 0xfffffffd00000001),
  (0xfffffffeffffffff, 0xffffffff00000000,
    0xfffffffefffffffe, 0xffffffff00000000, 0x0000000000000002),
  (0xfffffffeffffffff, 0xffffffffffffffff,
    0x00000000fffffffc, 0xfffffffe00000001, 0xfffffffd00000005),
  (0xfffffffeffffffff, 0x0000000100000000,
    0x00000000fffffffe, 0xfffffffdffffffff, 0xfffffffd00000001),
  (0xfffffffeffffffff, 0xffffffff00000000,
    0xfffffffefffffffe, 0xffffffff00000000, 0x0000000000000002),
  (0xfffffffeffffffff, 0xffffffffffffffff,
    0x00000000fffffffc, 0xfffffffe00000001, 0xfffffffd00000005),
  (0xffffffff00000000, 0x0000000100000000,
    0x00000000ffffffff, 0xfffffffe00000000, 0xfffffffe00000001),
  (0xffffffff00000000, 0xffffffff00000000,
    0xfffffffeffffffff, 0x0000000000000000, 0x0000000000000001),
  (0xffffffff00000000, 0xffffffffffffffff,
    0x00000000fffffffd, 0xfffffffe00000002, 0xfffffffe00000003),
  (0xffffffff00000001, 0x0000000100000000,
    0x0000000100000000, 0xfffffffe00000001, 0x0000000000000000),
  (0xffffffff00000001, 0xffffffff00000000,
    0xffffffff00000000, 0x0000000000000001, 0x0000000000000000),
  (0xffffffff00000001, 0xffffffffffffffff,
    0x00000000fffffffe, 0xfffffffe00000003, 0x0000000000000000),
  (0xffffffff00000002, 0x0000000100000000,
    0x0000000100000001, 0xfffffffe00000002, 0x0000000100000000),
  (0xffffffff00000002, 0xffffffff00000000,
    0x0000000000000000, 0x0000000000000002, 0xffffffff00000000),
  (0xffffffff00000002, 0xffffffffffffffff,
    0x00000000ffffffff, 0xfffffffe00000004, 0x00000000fffffffe),
  (0xfffffffffffffffe, 0x0000000100000000,
    0x00000001fffffffd, 0xfffffffefffffffe, 0xfffffffd00000000),
  (0xfffffffffffffffe, 0xffffffff00000000,
    0x00000000fffffffc, 0x00000000fffffffe, 0xfffffffe00000004),
  (0xfffffffffffffffe, 0xffffffffffffffff,
    0x00000001fffffffb, 0xffffffff00000000, 0xfffffffb00000006),
  (0xffffffffffffffff, 0x0000000100000000,
    0x00000001fffffffe, 0xfffffffeffffffff, 0xfffffffe00000000),
  (0xffffffffffffffff, 0xffffffff00000000,
    0x00000000fffffffd, 0x00000000ffffffff, 0xfffffffe00000003),
  (0xffffffffffffffff, 0xffffffffffffffff,
    0x00000001fffffffc, 0x0000000000000000, 0xfffffffc00000004),
  (0x910a2dec89025cc1, 0xbeeb8da1658eec67,
    0x4ff5bb8eee914927, 0xd21ea04a2373705b, 0x257bc5afb74a8e0d),
  (0xf893a2eefb32555e, 0x71c18690ee42c90b,
    0x6a552980e9751e68, 0x86d21c5e0cef8c53, 0x9c03dc00f33bf2dc),
  (0x71bb54d8d101b5b9, 0xc34d0bff90150280,
    0x350860d96116b838, 0xae6e48d840ecb33a, 0x5982e4c3e302ad1b),
  (0xe099ec6cd7363ca5, 0x85e7bb0f12278575,
    0x6681a77ce95dc219, 0x5ab2315dc50eb730, 0x80ec81ef6047ef62),
  (0x491718de357e3da8, 0xcb435c8e74616796,
    0x145a756da9dfa53d, 0x7dd3bc4ec11cd613, 0x4fad0dafb5d9243e),
  (0x6775dc7701564f61, 0x9afcd44d14cf8bfe,
    0x0272b0c51625db5e, 0xcc790828ec86c364, 0xf18a92ae58262916),
  (0x7476cf8a4baa5dc0, 0x87b341d690d7a28a,
    0xfc2a1160dc82004a, 0xecc38db2bad2bb37, 0x32112c98442b8c2e),
  (0x6f9b6dae6f4c57a8, 0x2ac2ce17a5794a3b,
    0x9a5e3bc614c5a1e3, 0x44d89f96c9d30d6d, 0x753ab8083de2311b),
  (0xa534a6a6b7fd0b63, 0xd0bad0da572baaf1,
    0x75ef77820f28b653, 0xd479d5cb60d16073, 0x598b5b2a0d976667),
  (0xae84379630af89ee, 0xe263183773ef6508,
    0x90e74fcea49eeef5, 0xcc211f5dbcc024e7, 0xa18ba7a2930e85f7),
  (0x10e2c46865e98746, 0x14d7973c5c2a449c,
    0x25ba5ba4c213cbe2, 0xfc0b2d2b09bf42ab, 0xd223c89ba1a15c4d),
  (0x7ef1fd0ed1548fcd, 0x1f8410633ef306ac,
    0x9e760d7210479679, 0x5f6decab92618921, 0x95460e5b188b8c11),
  (0x497305c5d1aab99f, 0x0c43407dc177b6f7,
    0x55b6464393227096, 0x3d2fc548103302a8, 0x2c33fa91315d3bd4),
  (0x83f91ca7864a7135, 0xb6b9aeef0d2df7ab,
    0x3ab2cb97937868df, 0xcd3f6db7791c798b, 0xdf6ecea863b1fef4),
  (0x0b331645445bcd27, 0xff6c67e81909778a,
    0x0a9f7e2e5d6544b0, 0x0bc6ae5c2b52559e, 0xb6dbeb4666615a30),
  (0x990cd70b12c5d084, 0x962b1967c90789ba,
    0x2f37f073dbcd5a3d, 0x02e1bda349be46ca, 0xcbca088c94ee9956),
  (0x65ace2685a072c6d, 0x70616f2f48dce01c,
    0xd60e5197a2e40c89, 0xf54b7338112a4c52, 0xa7ab497699eb7c99),
  (0x40d6824e2ef3fc17, 0x879e2e2256feff0c,
    0xc874b07085f2fb23, 0xb938542ad7f4fd0c, 0xf30bcacc0d0fe6be),
  (0x8b2e02445e4be0f5, 0xbf8c59bb003553c1,
    0x4aba5c005e8134b5, 0xcba1a8885e168d35, 0x4d727ee7f278ccf4),
  (0xd16aa4b296eb9d18, 0xab27a171be5b133c,
    0x7c9246255546b053, 0x26430340d89089dc, 0x588dd9727803e7d9),
  (0xdca0c749607e2c86, 0xb54b3c40881e2907,
    0x91ec038ae89c558c, 0x27558b08d860037f, 0x2957fadf141b4242),
  (0x3c821fbf59108163, 0xa7ff0d388687ffb2,
    0xe4812cf7df988115, 0x94831285d28881b2, 0xc9ff03bed948017d),
  (0xde70d1019fc66081, 0xd6de6acd12c87e38,
    0xb54f3bcfb28edeb8, 0x079266348cfde249, 0xb3e88db8d0cc7735),
  (0x530e0e6118e9685e, 0x28bff9ea304d9f96,
    0x7bce084b493707f4, 0x2a4e1476e89bc8c8, 0xd3e14730facb9822),
  (0xe4d9303221373073, 0xe9a6100461edd57a,
    0xce7f4037832505ec, 0xfb33202cbf495afa, 0xcdbed7acfd8616e2),
  (0x4d4673ef77ba0574, 0x21af8cfd4c4cbee5,
    0x6ef600ecc406c459, 0x2b96e6f22b6d468f, 0xc504798311867525),
  (0x536000f4bd6ae8f8, 0xf0af3ce429ca1790,
    0x440f3dd9e7350087, 0x62b0c40f93a0d169, 0xe51bd7a97c2621b6),
  (0x64c70b0b0c5b4a8f, 0x167587272751ecaf,
    0x7b3c923233ad373e, 0x4e5183e3e5095de0, 0x52f0e52292ced978),
  (0x9b679c859acd7aaf, 0x27cd5f9ec8c694cc,
    0xc334fc2463940f7b, 0x739a3ce6d206e5e3, 0x684bd5a0215f88b5),
  (0xf55540b2bff06252, 0xe02852925a4dc852,
    0xd57d93461a3e2aa3, 0x152cee2065a29a00, 0x2441f236c3e552d4)]

/-- `(a, -a, a⁻¹)` for nonzero `a`. -/
def unaryVectors : Array (UInt64 × UInt64 × UInt64) := #[
  (0x0000000000000001, 0xffffffff00000000, 0x0000000000000001),
  (0x0000000000000002, 0xfffffffeffffffff, 0x7fffffff80000001),
  (0x0000000000000007, 0xfffffffefffffffa, 0x249249246db6db6e),
  (0x000000007fffffff, 0xfffffffe80000002, 0x5555555455555555),
  (0x0000000080000000, 0xfffffffe80000001, 0xfffffffd00000003),
  (0x00000000ffffffff, 0xfffffffe00000002, 0xfffffffe00000001),
  (0x0000000100000000, 0xfffffffe00000001, 0xfffffffe00000002),
  (0x0000000100000001, 0xfffffffe00000000, 0xaaaaaaa9aaaaaaac),
  (0x0000000200000000, 0xfffffffd00000001, 0x7fffffff00000001),
  (0x7fffffffffffffff, 0x7fffffff00000002, 0x4924924892492492),
  (0x8000000000000000, 0x7fffffff00000001, 0xfffffffd00000001),
  (0x8000000000000001, 0x7fffffff00000000, 0x5555555455555557),
  (0xfffffffeffffffff, 0x0000000000000002, 0x7fffffff80000000),
  (0xfffffffeffffffff, 0x0000000000000002, 0x7fffffff80000000),
  (0xffffffff00000000, 0x0000000000000001, 0xffffffff00000000),
  (0xffffffff00000002, 0xffffffff00000000, 0x0000000000000001),
  (0xfffffffffffffffe, 0xfffffffe00000004, 0x2492492449249249),
  (0xffffffffffffffff, 0xfffffffe00000003, 0xaaaaaaa9aaaaaaab),
  (0x86c5d1b05ce2ce14, 0x793a2e4ea31d31ed, 0xfd4c0a7066d03a77),
  (0x1180b23a1075b77f, 0xee7f4dc4ef8a4882, 0xde81a47c384a55af),
  (0xc09a1a817914ffbc, 0x3f65e57d86eb0045, 0x2aa3df2f47631dd9),
  (0x88b894e1401ed25b, 0x77476b1dbfe12da6, 0x012d03087dab57ad),
  (0xb86c9a98359e0b62, 0x47936566ca61f49f, 0x23649f627ddad025),
  (0x47a9dc6739325fac, 0xb8562397c6cda055, 0x3ad255664d5edd28),
  (0x099545b4ca73e0f3, 0xf66aba4a358c1f0e, 0x94303e67073e2b3e),
  (0x05a2e18941c3936b, 0xfa5d1e75be3c6c96, 0xceb093fee2fd713f),
  (0x91866d4d0cde66a9, 0x6e7992b1f3219958, 0x78a7acbbf22fa2bd),
  (0x1eb967d7929813bb, 0xe14698276d67ec46, 0x7ff42fdd42500c38),
  (0x29663e9ea0ec2561, 0xd699c1605f13daa0, 0x1f9c34bbf1ede023),
  (0xd2c61eeb27a21187, 0x2d39e113d85dee7a, 0x2d70b3af4051b1ff),
  (0xf902155aa328d575, 0x06fdeaa45cd72a8c, 0xd7920c41399a3f3f),
  (0xb0eb094e6f1dcf73, 0x4f14f6b090e2308e, 0x800332f61b8c4fa1),
  (0x90ccb6a06cd2330e, 0x6f33495e932dccf3, 0x55cbc796d66e1dfa),
  (0x7878834768668743, 0x87877cb7979978be, 0x94a5fe6be4a1a53f),
  (0x9fbd96359554aa53, 0x604269c96aab55ae, 0x5e272c8ba9563c74),
  (0xdc3320bb97ca63be, 0x23ccdf4368359c43, 0x00695898ca8be5f0),
  (0xce45a342c10ffb55, 0x31ba5cbc3ef004ac, 0x6d693d6ba364e4f6),
  (0x1bea994d2e7d779d, 0xe41566b1d1828864, 0x3b4ff207d686c565),
  (0xa64b31c22cc57f39, 0x59b4ce3cd33a80c8, 0xd8433eedcc2ffdda),
  (0x388495061eb06ce1, 0xc77b6af8e14f9320, 0xfae9a3cc51ea5eae),
  (0x6c38537a931e49d7, 0x93c7ac846ce1b62a, 0x3ecb3fcfbc420b2e),
  (0xe31d5ce0684b83f2, 0x1ce2a31e97b47c0f, 0x819d24df0ffe147c),
  (0xaf60baae69576109, 0x509f455096a89ef8, 0x681bc9ff7dfc7184),
  (0xf0dad8272e600eb1, 0x0f2527d7d19ff150, 0xf2b6e2da41c74407),
  (0xc0257e403811c379, 0x3fda81bec7ee3c88, 0xc33f9c341ca159bc),
  (0x2072b26dfe81f26e, 0xdf8d4d91017e0d93, 0xfd0fcafa421d16fe),
  (0x2d4de979b560315c, 0xd2b216854a9fcea5, 0x2fa8905743de30b6),
  (0xbcf35b6db5f3ba40, 0x430ca4914a0c45c1, 0x700cd7d73a1d68d9),
  (0xc7c9572ddea951a8, 0x3836a8d12156ae59, 0xf5e338016be14ba5),
  (0x635b0b7e74f0c83e, 0x9ca4f4808b0f37c3, 0x8310bdaeb2fc4d51),
  (0x18c80a5e762810c2, 0xe737f5a089d7ef3f, 0xc88a94c136d0dc2b),
  (0xf3f0a4b172d1294b, 0x0c0f5b4d8d2ed6b6, 0x427bb4a392babbd3),
  (0x98d0ff43e17386ae, 0x672f00bb1e8c7953, 0x5641cf16b6a965d0),
  (0x180a2bd6343d01f8, 0xe7f5d428cbc2fe09, 0xec4bf1784ae3318a),
  (0xdb20290ac13e4a81, 0x24dfd6f43ec1b580, 0x147f1236609c1e00),
  (0xd80391ffb30d1390, 0x27fc6dff4cf2ec71, 0xb4811d151791570b),
  (0x00077ba99ea524f2, 0xfff88455615adb0f, 0x05084fd926060328),
  (0x4f05f03735c3b951, 0xb0fa0fc7ca3c46b0, 0xb906bd65f2001b3b)]

/-- `(a, n, a ^ n)`. -/
def powerVectors : Array (UInt64 × Nat × UInt64) := #[
  (0xbc73014050141d01, 0, 0x0000000000000001),
  (0x96bf5d405151ec53, 1, 0x96bf5d405151ec53),
  (0xaa3de53fbde4ae5b, 2, 0xcc9564a83fc240c4),
  (0x7bc42e82782acb92, 3, 0x6def24f2dc456e14),
  (0x764176e3c9cf4b25, 64, 0x37104c4b90dad742),
  (0xfd845ef300ce2d0b, 4294967295, 0x316190a779209546),
  (0xa3e9bfbbf6c43e6f, 4294967296, 0xbd9e099cae44d8cc),
  (0x0781577a0f53e5d6, 18446744069414584319, 0x9a83467ee5e9a57f),
  (0xd909c315b21d8f6c, 18446744069414584320, 0x0000000000000001),
  (0xe8e6022a79eb517b, 18446744073709551615, 0x24b383cea70853a7)]

/-- `Goldilocks::two_adic_generator(k)` for `k = 0, …, 32`. -/
def twoAdicGeneratorVectors : Array UInt64 := #[
  0x0000000000000001,
  0xffffffff00000000,
  0x0001000000000000,
  0xfffffffeff000001,
  0xefffffff00000001,
  0x00003fffffffc000,
  0x0000008000000000,
  0xf80007ff08000001,
  0xbf79143ce60ca966,
  0x1905d02a5c411f4e,
  0x9d8f2ad78bfed972,
  0x0653b4801da1c8cf,
  0xf2c35199959dfcb6,
  0x1544ef2335d17997,
  0xe0ee099310bba1e2,
  0xf6b2cffe2306baac,
  0x54df9630bf79450e,
  0xabd0a6e8aa3d8a0e,
  0x81281a7b05f9beac,
  0xfbd41c6b8caa3302,
  0x30ba2ecd5e93e76d,
  0xf502aef532322654,
  0x4b2a18ade67246b5,
  0xea9d5a1336fbc98b,
  0x86cdcc31c307e171,
  0x4bbaf5976ecfefd8,
  0xed41d05b78d6e286,
  0x10d78dd8915a171d,
  0x59049500004a4485,
  0xdfa8c93ba46d2666,
  0x7e9bd009b86a0845,
  0x400a7f755588e659,
  0x185629dcda58878c]

/-- `Goldilocks::GENERATOR`. -/
def generatorVector : UInt64 := 7

#guard arithmeticVectors.size = 90
#guard arithmeticVectors.all fun (a, b, sum, difference, product) =>
  (g a + g b).val == sum && (g a - g b).val == difference && (g a * g b).val == product

#guard unaryVectors.size = 58
#guard unaryVectors.all fun (a, opposite, inverse) =>
  (-g a).val == opposite && (g a)⁻¹.val == inverse

#guard powerVectors.size = 10
#guard powerVectors.all fun (a, n, power) => (fieldPow (g a) n).val == power

#guard twoAdicGeneratorVectors.size = 33
#guard (List.range 33).all fun k =>
  some (TwoAdicOps.twoAdicGenerator k : Goldilocks).val == twoAdicGeneratorVectors[k]?

#guard (TwoAdicOps.cosetShift : Goldilocks).val = generatorVector
#guard Goldilocks.generator.val = generatorVector

end CertiFriTest.P3.Goldilocks
