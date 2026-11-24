import CertiFriP3.BabyBear

/-!
# Tests of the BabyBear field and its quartic extension

Checks of `CertiFriP3/BabyBear.lean`, and through it of the prime field of
`CertiFriP3/PrimeField.lean` and of the extension of `CertiFriP3/Quartic.lean`.

* Against natural-number arithmetic. The operations of the base field are
  compared with the same operations on natural numbers and on integers modulo
  `p`, on numbers at the edges of the reduction (around `2^27`, `2^31`, `2^32`,
  `2^64` and `p`) and on pseudo-random numbers. The operations of the extension
  are compared with the arithmetic of polynomials with natural coefficients,
  reduced modulo `X^4 - 11` and modulo `p`.
* Algebraic identities. The laws of a field, the embedding and the basis of
  the extension on pseudo-random elements, and the consistency of the table of
  generators of the two-adic subgroups.
* Against Plonky3. The vectors of the two sections named so were computed by
  Plonky3 at revision `0d803737`, by a program linked with its crates
  `p3-baby-bear` and `p3-field` (`CertiFriTest/vectors/fields`; `BabyBear` and
  `BinomialExtensionField<BabyBear, 4>`): sums, differences, products,
  opposites, inverses, squares, powers, the generators of the two-adic
  subgroups and of the multiplicative groups, the constant `W`, the
  construction that rejects numbers that are not canonical, and the passage
  between an extension element and its coordinates.

In the vectors of the extension an element is the tuple of its coordinates, as
Plonky3's `as_basis_coefficients_slice` lists them. The operands of a vector
may be words of 32 bits that are not canonical (Plonky3's `BabyBear::new`
reduces a word); the results are canonical.
-/

namespace CertiFriTest.P3.BabyBear

open CertiFri CertiFri.P3

/-- The order of the field. -/
def p : Nat := BabyBear.order

/-- The element a natural number represents. -/
def b (n : Nat) : BabyBear := Fp.ofNat n

/-! ## Construction and representation -/

#guard p = 2 ^ 31 - 2 ^ 27 + 1
#guard (b 0).val = 0 ∧ (b p).val = 0 ∧ (b (p + 5)).val = 5 ∧ (b (p - 1)).val = p - 1
#guard (b (2 ^ 200 + 3)).val = (2 ^ 200 + 3) % p
#guard (Fp.ofCanonical? 0 : Option BabyBear).map (·.val) = some 0
#guard (Fp.ofCanonical? (p - 1) : Option BabyBear).map (·.val) = some (p - 1)
#guard (Fp.ofCanonical? p : Option BabyBear).isNone
#guard (Fp.ofCanonical? (p + 1) : Option BabyBear).isNone
#guard (Fp.ofCanonical? (2 ^ 64) : Option BabyBear).isNone
#guard (0 : BabyBear).val = 0 ∧ (1 : BabyBear).val = 1 ∧ (default : BabyBear).val = 0
#guard b 5 = b (p + 5) ∧ b 5 ≠ b 6 ∧ b 5 == b (p + 5) ∧ !(b 5 == b 6)
#guard reprStr (b (p + 5)) = "5"

/-! ## Against natural-number arithmetic -/

/-- Numbers at the edges of the reduction. -/
def edges : Array Nat := #[
  0, 1, 2, 3, 31, 2 ^ 15, 2 ^ 16, 2 ^ 27 - 1, 2 ^ 27, 2 ^ 27 + 1, 2 ^ 30 - 1, 2 ^ 30, 2 ^ 30 + 1,
  (p - 1) / 2, (p + 1) / 2, p - 2 ^ 27 - 1, p - 2 ^ 27, p - 2 ^ 27 + 1, p - 3, p - 2, p - 1, p,
  p + 1, 2 ^ 31 - 1, 2 ^ 31, 2 ^ 32 - 1, 2 ^ 32, 2 * p - 1, 2 ^ 62, 2 ^ 63 - 1, 2 ^ 64 - 1, 2 ^ 64,
  p * p - 1, p * p]

/-- The four operations on the elements `m` and `n` represent agree with the
operations on natural numbers and on integers, reduced modulo `p`. -/
def agrees (m n : Nat) : Bool :=
  let x := b m
  let y := b n
  (x + y).val == (m + n) % p && (x - y).val == (((m : Int) - n) % p).toNat
    && (x * y).val == m * n % p && (-x).val == ((-(m : Int)) % p).toNat

#guard edges.all fun m => edges.all fun n => agrees m n

-- A number is canonical exactly when it is below `p`.
#guard edges.all fun n =>
  (Fp.ofCanonical? n : Option BabyBear) == if n < p then some (b n) else none

/-- One step of the SplitMix64 generator: the next state and the output. -/
def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let state := state + 0x9E3779B97F4A7C15
  let z := (state ^^^ (state >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (state, z ^^^ (z >>> 31))

/-- Whether `check` holds on `count` pairs of pseudo-random words of 64 bits. -/
def onRandomPairs (check : Nat → Nat → Bool) : (count : Nat) → (state : UInt64) → Bool
  | 0, _ => true
  | count + 1, state =>
    let first := splitMix state
    let second := splitMix first.1
    check first.2.toNat second.2.toNat && onRandomPairs check count second.1

#guard onRandomPairs agrees 2000 1
-- Words of 31 bits: about half of them are canonical.
#guard onRandomPairs (fun m n => agrees (m % 2 ^ 31) (n % 2 ^ 31)) 2000 2

/-- The identities that tie the difference and the opposite to the sum. -/
def differenceAgrees (m n : Nat) : Bool :=
  let x := b m
  let y := b n
  x - y + y == x && x + -x == 0 && x - y == x + -y && x - x == 0 && -(-x) == x

#guard edges.all fun m => edges.all fun n => differenceAgrees m n
#guard onRandomPairs differenceAgrees 2000 3

/-- The inverse of the element `n` represents is the element whose product
with it is one, in the field and on natural numbers, and it is the power
`p - 2`. The inverse of zero is zero. -/
def inverseAgrees (n : Nat) : Bool :=
  let x := b n
  if n % p = 0 then x⁻¹ == 0
  else
    x * x⁻¹ == 1 && x⁻¹.val * n % p == 1 && x⁻¹ == fieldPow x (p - 2) && x⁻¹⁻¹ == x

#guard edges.all inverseAgrees
#guard onRandomPairs (fun m n => inverseAgrees m && inverseAgrees n) 500 4
-- The inverses of the numbers below 2000, among them `0⁻¹ = 0`.
#guard (List.range 2000).all inverseAgrees
#guard (0 : BabyBear)⁻¹ = 0 ∧ (1 : BabyBear)⁻¹ = 1 ∧ (-1 : BabyBear)⁻¹ = -1

/-- The power `k` of the element `n` represents agrees with the power of
natural numbers. -/
def powerAgrees (n k : Nat) : Bool :=
  (fieldPow (b n) k).val == n ^ k % p

#guard edges.all fun n => (List.range 40).all fun k => powerAgrees n k
#guard onRandomPairs (fun n k => powerAgrees n (k % 512)) 300 5

/-- `Fp.powBits` on an exponent below `2 ^ bits` agrees with the power of
natural numbers. -/
def powBitsAgrees (n k : Nat) : Bool :=
  (Fp.powBits 1 (b n) 9 (k % 512)).val == n ^ (k % 512) % p
    && Fp.powBits 1 (b n) (Nat.log2 k + 1) k == fieldPow (b n) k

#guard onRandomPairs powBitsAgrees 300 6

/-- The laws of exponents, on exponents of 64 bits, and the theorem of
Fermat: the power `p` of an element is the element. -/
def powerLaws (m n : Nat) : Bool :=
  let x := b (m + 3 * n)
  fieldPow x (m + n) == fieldPow x m * fieldPow x n
    && fieldPow x (m * n) == fieldPow (fieldPow x m) n
    && fieldPow x p == x && (x == 0 || fieldPow x (p - 1) == 1)

#guard onRandomPairs powerLaws 300 7
#guard edges.all fun m => edges.all fun n => powerLaws m n

/-! ## The two-adic structure -/

#guard TwoAdicOps.twoAdicity BabyBear = 27
#guard (TwoAdicOps.cosetShift : BabyBear).val = 31
#guard (p - 1) % 2 ^ 27 = 0 ∧ (p - 1) % 2 ^ 28 ≠ 0
#guard BabyBear.twoAdicGenerators.size = 28 ∧ BabyBear.twoAdicGenerators.all (· < p)

/-- The generator of order `2^k` has order exactly `2^k`, and it is the square
of the generator of order `2^(k+1)`. -/
def generatorAgrees (k : Nat) : Bool :=
  let w : BabyBear := TwoAdicOps.twoAdicGenerator k
  fieldPow w (2 ^ k) == 1 && (k = 0 || fieldPow w (2 ^ (k - 1)) == -1)
    && (k = 27 || (let next : BabyBear := TwoAdicOps.twoAdicGenerator (k + 1); next * next == w))

#guard (List.range 28).all generatorAgrees
#guard (TwoAdicOps.twoAdicGenerator 0 : BabyBear) = 1
#guard (TwoAdicOps.twoAdicGenerator 1 : BabyBear) = -1
#guard (List.range 28).all fun k =>
  some (TwoAdicOps.twoAdicGenerator k : BabyBear).val == BabyBear.twoAdicGenerators[k]?

-- The generator of the largest two-adic subgroup is a power of the generator
-- of the multiplicative group.
#guard fieldPow BabyBear.generator ((p - 1) / 2 ^ 27) = BabyBear.twoAdicGenerator 27
-- The generator of the multiplicative group has order `p - 1 = 2^27 * 3 * 5`:
-- no power `(p - 1) / q` of it is one, for `q` a prime factor of `p - 1`.
#guard p - 1 = 2 ^ 27 * 3 * 5
#guard fieldPow BabyBear.generator (p - 1) = 1
#guard fieldPow BabyBear.generator ((p - 1) / 2) = -1
#guard [2, 3, 5].all fun q => fieldPow BabyBear.generator ((p - 1) / q) != 1
-- Past the two-adicity there is no generator.
#guard (BabyBear.twoAdicGenerator 28).val = 0 ∧ (BabyBear.twoAdicGenerator 1000).val = 0

/-! ## Against Plonky3 -/

/-- `(a, b, a + b, a - b, a * b)`: the operands are any words of 32 bits, the
results are canonical. -/
def arithmeticVectors : Array (Nat × Nat × Nat × Nat × Nat) := #[
  (0x00000000, 0x00000001, 0x00000001, 0x78000000, 0x00000000),
  (0x00000000, 0x08000000, 0x08000000, 0x70000001, 0x00000000),
  (0x00000000, 0x78000000, 0x78000000, 0x00000001, 0x00000000),
  (0x00000000, 0xffffffff, 0x0ffffffd, 0x68000004, 0x00000000),
  (0x00000001, 0x00000001, 0x00000002, 0x00000000, 0x00000001),
  (0x00000001, 0x08000000, 0x08000001, 0x70000002, 0x08000000),
  (0x00000001, 0x78000000, 0x00000000, 0x00000002, 0x78000000),
  (0x00000001, 0xffffffff, 0x0ffffffe, 0x68000005, 0x0ffffffd),
  (0x00000002, 0x00000001, 0x00000003, 0x00000001, 0x00000002),
  (0x00000002, 0x08000000, 0x08000002, 0x70000003, 0x10000000),
  (0x00000002, 0x78000000, 0x00000001, 0x00000003, 0x77ffffff),
  (0x00000002, 0xffffffff, 0x0fffffff, 0x68000006, 0x1ffffffa),
  (0x0000001f, 0x00000001, 0x00000020, 0x0000001e, 0x0000001f),
  (0x0000001f, 0x08000000, 0x0800001f, 0x70000020, 0x07fffffe),
  (0x0000001f, 0x78000000, 0x0000001e, 0x00000020, 0x77ffffe2),
  (0x0000001f, 0xffffffff, 0x1000001c, 0x68000023, 0x0fffff9f),
  (0x07ffffff, 0x00000001, 0x08000000, 0x07fffffe, 0x07ffffff),
  (0x07ffffff, 0x08000000, 0x0fffffff, 0x78000000, 0x37777778),
  (0x07ffffff, 0x78000000, 0x07fffffe, 0x08000000, 0x70000002),
  (0x07ffffff, 0xffffffff, 0x17fffffc, 0x70000003, 0x56eeeef3),
  (0x08000000, 0x00000001, 0x08000001, 0x07ffffff, 0x08000000),
  (0x08000000, 0x08000000, 0x10000000, 0x00000000, 0x3f777778),
  (0x08000000, 0x78000000, 0x07ffffff, 0x08000001, 0x70000001),
  (0x08000000, 0xffffffff, 0x17fffffd, 0x70000004, 0x66eeeef0),
  (0x08000001, 0x00000001, 0x08000002, 0x08000000, 0x08000001),
  (0x08000001, 0x08000000, 0x10000001, 0x00000001, 0x47777778),
  (0x08000001, 0x78000000, 0x08000000, 0x08000002, 0x70000000),
  (0x08000001, 0xffffffff, 0x17fffffe, 0x70000005, 0x76eeeeed),
  (0x40000000, 0x00000001, 0x40000001, 0x3fffffff, 0x40000000),
  (0x40000000, 0x08000000, 0x48000000, 0x38000000, 0x1bbbbbbc),
  (0x40000000, 0x78000000, 0x3fffffff, 0x40000001, 0x38000001),
  (0x40000000, 0xffffffff, 0x4ffffffd, 0x30000003, 0x6777777a),
  (0x70000001, 0x00000001, 0x70000002, 0x70000000, 0x70000001),
  (0x70000001, 0x08000000, 0x00000000, 0x68000001, 0x38888889),
  (0x70000001, 0x78000000, 0x70000000, 0x70000002, 0x08000000),
  (0x70000001, 0xffffffff, 0x07fffffd, 0x60000004, 0x11111111),
  (0x77ffffff, 0x00000001, 0x78000000, 0x77fffffe, 0x77ffffff),
  (0x77ffffff, 0x08000000, 0x07fffffe, 0x6fffffff, 0x68000001),
  (0x77ffffff, 0x78000000, 0x77fffffe, 0x78000000, 0x00000002),
  (0x77ffffff, 0xffffffff, 0x0ffffffb, 0x68000002, 0x58000007),
  (0x78000000, 0x00000001, 0x00000000, 0x77ffffff, 0x78000000),
  (0x78000000, 0x08000000, 0x07ffffff, 0x70000000, 0x70000001),
  (0x78000000, 0x78000000, 0x77ffffff, 0x00000000, 0x00000001),
  (0x78000000, 0xffffffff, 0x0ffffffc, 0x68000003, 0x68000004),
  (0x78000001, 0x00000001, 0x00000001, 0x78000000, 0x00000000),
  (0x78000001, 0x08000000, 0x08000000, 0x70000001, 0x00000000),
  (0x78000001, 0x78000000, 0x78000000, 0x00000001, 0x00000000),
  (0x78000001, 0xffffffff, 0x0ffffffd, 0x68000004, 0x00000000),
  (0x78000002, 0x00000001, 0x00000002, 0x00000000, 0x00000001),
  (0x78000002, 0x08000000, 0x08000001, 0x70000002, 0x08000000),
  (0x78000002, 0x78000000, 0x00000000, 0x00000002, 0x78000000),
  (0x78000002, 0xffffffff, 0x0ffffffe, 0x68000005, 0x0ffffffd),
  (0x7fffffff, 0x00000001, 0x07ffffff, 0x07fffffd, 0x07fffffe),
  (0x7fffffff, 0x08000000, 0x0ffffffe, 0x77ffffff, 0x2f777778),
  (0x7fffffff, 0x78000000, 0x07fffffd, 0x07ffffff, 0x70000003),
  (0x7fffffff, 0xffffffff, 0x17fffffb, 0x70000002, 0x46eeeef6),
  (0x80000000, 0x00000001, 0x08000000, 0x07fffffe, 0x07ffffff),
  (0x80000000, 0x08000000, 0x0fffffff, 0x78000000, 0x37777778),
  (0x80000000, 0x78000000, 0x07fffffe, 0x08000000, 0x70000002),
  (0x80000000, 0xffffffff, 0x17fffffc, 0x70000003, 0x56eeeef3),
  (0xffffffff, 0x00000001, 0x0ffffffe, 0x0ffffffc, 0x0ffffffd),
  (0xffffffff, 0x08000000, 0x17fffffd, 0x07fffffd, 0x66eeeef0),
  (0xffffffff, 0x78000000, 0x0ffffffc, 0x0ffffffe, 0x68000004),
  (0xffffffff, 0xffffffff, 0x1ffffffa, 0x00000000, 0x25dddde8),
  (0xaf98ffa1, 0x9213d4ac, 0x51acd44b, 0x1d852af5, 0x1bae3ecd),
  (0x0c38d2ec, 0xde1cd5ef, 0x7255a8da, 0x1e1bfcff, 0x23bc037a),
  (0x5d01dfae, 0xa2a41e71, 0x0fa5fe1d, 0x325dc13e, 0x1f7397b0),
  (0xc35b619d, 0xcb56dfb0, 0x26b2414a, 0x700481ee, 0x0f90db1b),
  (0x0863da36, 0x08bc7435, 0x11204e6b, 0x77a76602, 0x1a984768),
  (0x756b54b0, 0x606d8761, 0x5dd8dc10, 0x14fdcd4f, 0x37e94362),
  (0x096ee9f9, 0x2d733775, 0x36e2216e, 0x53fbb285, 0x203dc769),
  (0x8858957b, 0xe758ab48, 0x07b140c0, 0x18ffea34, 0x552f2159),
  (0xfb2aa307, 0xbc9a1f8e, 0x4fc4c292, 0x3e908379, 0x1ed92853),
  (0x2156f4b8, 0x2f0f223b, 0x506616f3, 0x6a47d27e, 0x753fc673),
  (0xba692946, 0xd59543a5, 0x27fe6ce8, 0x5cd3e5a2, 0x2b89fd9d),
  (0x12e343ef, 0xf238d22a, 0x151c1617, 0x10aa71c7, 0x1b2b2358),
  (0xea4823c3, 0x899e8906, 0x0be6acc6, 0x60a99abd, 0x217feb0d),
  (0x89792601, 0xf869317f, 0x19e2577d, 0x090ff483, 0x5534070f),
  (0x01905db4, 0x42f80521, 0x448862d5, 0x36985894, 0x62f1292e),
  (0x665a3787, 0xc95111f5, 0x3fab497a, 0x15092593, 0x27083ec9),
  (0xe840c46c, 0x7e49496c, 0x768a0dd6, 0x69f77b00, 0x09b636e4),
  (0x9bdba357, 0x4451418a, 0x682ce4e0, 0x578a61cd, 0x2aaacf08),
  (0xcbb8aac6, 0x6a022788, 0x45bad24c, 0x61b6833e, 0x19b30a6c),
  (0x7bd5d2d5, 0x613a1a9e, 0x650fed72, 0x1a9bb837, 0x024e276d),
  (0x6692f8ca, 0xc15e097b, 0x37f10243, 0x1d34ef50, 0x723f136e),
  (0xa2313d60, 0x6d1a8837, 0x1f4bc595, 0x3516b529, 0x417832f9),
  (0x72b00422, 0xfa78aa4b, 0x0528ae6a, 0x683759d9, 0x00ddc3ec),
  (0x1d2da9d9, 0xd219dcb8, 0x77478690, 0x3b13cd23, 0x3be35ce4),
  (0xf51c082c, 0xc3a42ed8, 0x50c03701, 0x3177d954, 0x41b1e489),
  (0xd593d9dc, 0xe0dbf15a, 0x4e6fcb33, 0x6cb7e883, 0x3d11a7b3),
  (0x045e69ae, 0xc73c9bc8, 0x539b0575, 0x2d21cde8, 0x3b46018b),
  (0x48eed780, 0xf503142a, 0x4df1eba8, 0x43ebc358, 0x619bd956),
  (0x3370592d, 0xcb8275fb, 0x0ef2cf26, 0x57ede334, 0x68869f1f),
  (0xb030e9d8, 0xd0595ecd, 0x188a48a2, 0x57d78b0c, 0x57378062)]

/-- `(a, -a, a⁻¹)` for nonzero `a`. -/
def unaryVectors : Array (Nat × Nat × Nat) := #[
  (0x00000001, 0x78000000, 0x00000001),
  (0x00000002, 0x77ffffff, 0x3c000001),
  (0x0000001f, 0x77ffffe2, 0x03def7be),
  (0x07ffffff, 0x70000002, 0x70800000),
  (0x08000000, 0x70000001, 0x77fffff2),
  (0x08000001, 0x70000000, 0x19b6db6f),
  (0x40000000, 0x38000001, 0x68ffffff),
  (0x70000001, 0x08000000, 0x0000000f),
  (0x77ffffff, 0x00000002, 0x3c000000),
  (0x78000000, 0x00000001, 0x78000000),
  (0x78000002, 0x78000000, 0x00000001),
  (0x7fffffff, 0x70000003, 0x3def7bdf),
  (0x80000000, 0x70000002, 0x70800000),
  (0xffffffff, 0x68000004, 0x42620ae5),
  (0x4eebf55e, 0x29140aa3, 0x09a6a994),
  (0x7f0fa662, 0x70f059a0, 0x5376658c),
  (0xf0ed9c20, 0x771263e3, 0x46247cc7),
  (0xc2ad4b5f, 0x2d52b4a3, 0x09dcdd7e),
  (0xc8200d11, 0x27dff2f1, 0x3181c64f),
  (0xbf7cd2bc, 0x30832d46, 0x67d0e7dd),
  (0xed7b629b, 0x02849d67, 0x63858cc2),
  (0x354aee54, 0x42b511ad, 0x40422420),
  (0x156e4696, 0x6291b96b, 0x11d2f60a),
  (0x175b731c, 0x60a48ce5, 0x3e0235ee),
  (0xee4bfe29, 0x01b401d9, 0x2bf033c4),
  (0x174b44ae, 0x60b4bb53, 0x5c5bc560),
  (0x5ecbb975, 0x1934468c, 0x14d48a02),
  (0x01e418fd, 0x761be704, 0x502c3eba),
  (0xa3c3fe32, 0x4c3c01d0, 0x0a11502f),
  (0x4407a854, 0x33f857ad, 0x24d227b2),
  (0xa400c132, 0x4bff3ed0, 0x7799ccd3),
  (0x8f78719f, 0x60878e63, 0x332c8724),
  (0x94504e0a, 0x5bafb1f8, 0x71a0bead),
  (0x01b360e9, 0x764c9f18, 0x6af13bbf),
  (0x603a4f0e, 0x17c5b0f3, 0x6eab6308),
  (0x03da0f78, 0x7425f089, 0x59842366),
  (0x27acbb8e, 0x50534473, 0x65239473),
  (0xc95eee06, 0x26a111fc, 0x3d1d795a),
  (0x65270f2e, 0x12d8f0d3, 0x11bb34da),
  (0x4ec93f48, 0x2936c0b9, 0x432ec8dd),
  (0xc13ae2bb, 0x2ec51d47, 0x19d41ff9),
  (0x33c10152, 0x443efeaf, 0x4500fef2),
  (0x3ae11b27, 0x3d1ee4da, 0x4a33fae7),
  (0x0e1b708c, 0x69e48f75, 0x693a954c)]

/-- `(a, n, a ^ n)`. -/
def powerVectors : Array (Nat × Nat × Nat) := #[
  (0x3131f06d, 0, 0x00000001),
  (0xb0daee9a, 1, 0x38daee99),
  (0x980cec69, 2, 0x3b807bd8),
  (0x90608baf, 3, 0x03bc2c0b),
  (0x0dd0472a, 7, 0x195d5f63),
  (0x5cb41f1d, 134217728, 0x24553874),
  (0xa165d259, 2013265919, 0x48eb0cd7),
  (0x5b362a82, 2013265920, 0x00000001),
  (0x3d78c770, 2013265921, 0x3d78c770),
  (0x71415267, 4294967297, 0x18199d28),
  (0x60ee81cd, 18446744073709551615, 0x7549dbc0)]

/-- `BabyBear::two_adic_generator(k)` for `k = 0, …, 27`. -/
def twoAdicGeneratorVectors : Array Nat := #[
  0x00000001,
  0x78000000,
  0x67055c21,
  0x5ee99486,
  0x0bb4c4e4,
  0x2d4cc4da,
  0x669d6090,
  0x17b56c64,
  0x67456167,
  0x688442f9,
  0x145e952d,
  0x4fe61226,
  0x4c734715,
  0x11c33e2a,
  0x62c3d2b1,
  0x77cad399,
  0x54c131f4,
  0x4cabd6a6,
  0x5cf5713f,
  0x3e9430e8,
  0x0ba067a3,
  0x18adc27d,
  0x21fd55bc,
  0x4b859b3d,
  0x3bd57996,
  0x4483d85a,
  0x3a26eef8,
  0x1a427a41]

/-- `BabyBear::GENERATOR`. -/
def generatorVector : Nat := 31

/-- `<BabyBear as BinomiallyExtendable<4>>::W`. -/
def nonResidueVector : Nat := 11

/-- `(n, BabyBear::from_canonical_checked(n))` for words `n` of 32 bits. -/
def canonicalVectors : Array (Nat × Option Nat) := #[
  (0x00000000, some 0x00000000),
  (0x00000001, some 0x00000001),
  (0x0000001f, some 0x0000001f),
  (0x77ffffff, some 0x77ffffff),
  (0x78000000, some 0x78000000),
  (0x78000001, none),
  (0x78000002, none),
  (0x80000000, none),
  (0xffffffff, none)]

#guard arithmeticVectors.size = 94
#guard arithmeticVectors.all fun (m, n, sum, difference, product) =>
  (b m + b n).val == sum && (b m - b n).val == difference && (b m * b n).val == product

#guard unaryVectors.size = 44
#guard unaryVectors.all fun (n, opposite, inverse) =>
  (-b n).val == opposite && (b n)⁻¹.val == inverse

#guard powerVectors.size = 11
#guard powerVectors.all fun (n, k, power) => (fieldPow (b n) k).val == power

#guard twoAdicGeneratorVectors.size = 28
#guard (List.range 28).all fun k =>
  some (TwoAdicOps.twoAdicGenerator k : BabyBear).val == twoAdicGeneratorVectors[k]?
#guard BabyBear.twoAdicGenerators = twoAdicGeneratorVectors

#guard (TwoAdicOps.cosetShift : BabyBear).val = generatorVector
#guard BabyBear.generator.val = generatorVector
#guard (QuarticParams.nonResidue : BabyBear).val = nonResidueVector

-- Plonky3's `from_canonical_checked` is `Fp.ofCanonical?`.
#guard canonicalVectors.size = 9
#guard canonicalVectors.all fun (n, checked) =>
  (Fp.ofCanonical? n : Option BabyBear).map (·.val) == checked

end CertiFriTest.P3.BabyBear

namespace CertiFriTest.P3.BabyBearExt

open CertiFri CertiFri.P3
open CertiFriTest.P3.BabyBear (p b splitMix)

/-- The coordinates of an element, as natural numbers. -/
abbrev E := Nat × Nat × Nat × Nat

/-- The element with the given coordinates, each reduced modulo `p`. -/
def e (coords : E) : BabyBearExt :=
  ⟨b coords.1, b coords.2.1, b coords.2.2.1, b coords.2.2.2⟩

/-- The coordinates of an element. -/
def coords (x : BabyBearExt) : E := (x.c0.val, x.c1.val, x.c2.val, x.c3.val)

/-- The embedding of the base field. -/
def embed (a : BabyBear) : BabyBearExt := ExtensionOps.embed a

/-- The basis element `X`. -/
def X : BabyBearExt := e (0, 1, 0, 0)

/-! ## The embedding and the basis -/

#guard ExtensionOps.degree BabyBear BabyBearExt = 4
#guard coords (0 : BabyBearExt) = (0, 0, 0, 0) ∧ coords (1 : BabyBearExt) = (1, 0, 0, 0)
#guard coords (default : BabyBearExt) = (0, 0, 0, 0)
#guard coords (embed (b 5)) = (5, 0, 0, 0)
#guard coords (X * X) = (0, 0, 1, 0) ∧ coords (X * X * X) = (0, 0, 0, 1)
#guard coords (X * X * X * X) = (11, 0, 0, 0)
#guard X * X * X * X = embed QuarticParams.nonResidue
-- `11` is not a square of the base field and `-1` is one, which makes
-- `X^4 - 11` irreducible.
#guard fieldPow (b 11) ((p - 1) / 2) = -1 ∧ fieldPow (-1 : BabyBear) ((p - 1) / 2) = 1
#guard coords (ExtensionOps.ofBasis #[b 100, b 101, b 102, b 103]) = (100, 101, 102, 103)
#guard ExtensionOps.toBasis (F := BabyBear) (e (100, 101, 102, 103))
  = #[b 100, b 101, b 102, b 103]
#guard e (3, 4, 5, 6)
  = embed (b 3) + embed (b 4) * X + embed (b 5) * X * X + embed (b 6) * X * X * X
-- Missing coordinates are zero; coordinates past the fourth are ignored.
#guard coords (ExtensionOps.ofBasis (#[] : Array BabyBear)) = (0, 0, 0, 0)
#guard coords (ExtensionOps.ofBasis #[b 9]) = (9, 0, 0, 0)
#guard coords (ExtensionOps.ofBasis #[b 9, b 8, b 7]) = (9, 8, 7, 0)
#guard coords (ExtensionOps.ofBasis #[b 9, b 8, b 7, b 6, b 5]) = (9, 8, 7, 6)
#guard e (1, 2, 3, 4) ≠ e (1, 2, 3, 5) ∧ e (1, 2, 3, 4) = e (p + 1, 2, 3, 4)
-- Equality as the verifier tests it: two elements that differ in one
-- coordinate are different.
#guard e (1, 2, 3, 4) == e (p + 1, 2, 3, 4) ∧ Quartic.beq (e (1, 2, 3, 4)) (e (p + 1, 2, 3, 4))
#guard #[(2, 2, 3, 4), (1, 3, 3, 4), (1, 2, 4, 4), (1, 2, 3, 5)].all fun c =>
  !(e (1, 2, 3, 4) == e c) && !Quartic.beq (e (1, 2, 3, 4)) (e c)
#guard (0 : BabyBearExt)⁻¹ = 0

/-! ## Against polynomial arithmetic on natural numbers -/

/-- The coefficient of `X^k` in the product of the polynomials with
coefficients `a` and `c`. -/
def productCoefficient (a c : Array Nat) (k : Nat) : Nat :=
  (List.range (k + 1)).foldl (fun sum i => sum + a[i]?.getD 0 * c[k - i]?.getD 0) 0

/-- The product of two elements, on natural numbers: the product of the two
polynomials, with `X^(k + 4)` replaced by `11 * X^k`, reduced modulo `p`. -/
def schoolbook (a c : E) : E :=
  let coefficient (k : Nat) : Nat :=
    productCoefficient #[a.1, a.2.1, a.2.2.1, a.2.2.2] #[c.1, c.2.1, c.2.2.1, c.2.2.2] k
  let reduced (k : Nat) : Nat := (coefficient k + 11 * coefficient (k + 4)) % p
  (reduced 0, reduced 1, reduced 2, reduced 3)

/-- The operation `f` on each pair of coordinates. -/
def zipCoords (f : Nat → Nat → Nat) (a c : E) : E :=
  (f a.1 c.1, f a.2.1 c.2.1, f a.2.2.1 c.2.2.1, f a.2.2.2 c.2.2.2)

/-- The four operations on the elements with coordinates `a` and `c` agree
with the arithmetic of polynomials with natural and integer coefficients. -/
def agrees (a c : E) : Bool :=
  coords (e a * e c) == schoolbook a c
    && coords (e a + e c) == zipCoords (fun m n => (m + n) % p) a c
    && coords (e a - e c) == zipCoords (fun m n => (((m : Int) - n) % p).toNat) a c
    && coords (-e a) == zipCoords (fun m _ => ((-(m : Int)) % p).toNat) a a

/-- Coordinates of elements at the edges: the basis, elements with coordinates
`p - 1`, and coordinates that are not canonical. -/
def samples : Array E := #[
  (0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1), (11, 0, 0, 0),
  (p - 1, 0, 0, 0), (0, p - 1, 0, 0), (0, 0, p - 1, 0), (0, 0, 0, p - 1),
  (p - 1, p - 1, p - 1, p - 1), (1, 1, 1, 1), (2 ^ 27, 2 ^ 31 - 1, 2 ^ 32 - 1, p + 5),
  (p, 2 ^ 64 - 1, 2 ^ 30, 3), (0x12345678, 0x9ABCDEF0, 0x0FEDCBA9, 0x87654321)]

#guard samples.all fun a => samples.all fun c => agrees a c

/-- Pseudo-random coordinates, each a word of 64 bits, with the next state. -/
def randomCoords (state : UInt64) : UInt64 × E :=
  let first := splitMix state
  let second := splitMix first.1
  let third := splitMix second.1
  let fourth := splitMix third.1
  (fourth.1, (first.2.toNat, second.2.toNat, third.2.toNat, fourth.2.toNat))

/-- Whether `check` holds on `count` triples of pseudo-random coordinates. -/
def onRandomTriples (check : E → E → E → Bool) : (count : Nat) → (state : UInt64) → Bool
  | 0, _ => true
  | count + 1, state =>
    let first := randomCoords state
    let second := randomCoords first.1
    let third := randomCoords second.1
    check first.2 second.2 third.2 && onRandomTriples check count third.1

#guard onRandomTriples (fun a c d => agrees a c && agrees c d && agrees d a) 500 11

/-! ## Algebraic identities -/

/-- The laws of a field on three elements. -/
def laws (x y z : BabyBearExt) : Bool :=
  x + y == y + x && x * y == y * x && x + (y + z) == x + y + z && x * (y * z) == x * y * z
    && x * (y + z) == x * y + x * z && (x + y) * z == x * z + y * z
    && x - y == x + -y && x - y + y == x && x + -x == 0 && x - x == 0 && -(-x) == x
    && x + 0 == x && x * 1 == x && x * 0 == 0
    && (x == 0 || (x * x⁻¹ == 1 && x⁻¹ * x == 1 && x⁻¹⁻¹ == x))
    && (x * y)⁻¹ == x⁻¹ * y⁻¹ && (-x)⁻¹ == -x⁻¹

#guard samples.all fun a => samples.all fun c => samples.all fun d => laws (e a) (e c) (e d)
#guard onRandomTriples (fun a c d => laws (e a) (e c) (e d)) 500 12

/-- The embedding respects the operations, and the product by an embedded
element is the product of each coordinate. -/
def embedLaws (s t : Nat) (a : E) : Bool :=
  let x := e a
  embed (b s * b t) == embed (b s) * embed (b t) && embed (b s + b t) == embed (b s) + embed (b t)
    && embed (b s - b t) == embed (b s) - embed (b t) && embed (-b s) == -embed (b s)
    && embed (b s)⁻¹ == (embed (b s))⁻¹ && coords (embed (b s)) == (s % p, 0, 0, 0)
    && embed (b s) * x == ⟨b s * x.c0, b s * x.c1, b s * x.c2, b s * x.c3⟩
    && x * embed (b s) == embed (b s) * x

#guard embed 0 = (0 : BabyBearExt) ∧ embed 1 = (1 : BabyBearExt)
#guard samples.all fun a => samples.all fun c => embedLaws a.1 c.2.1 a && embedLaws c.2.2.2 a.1 c
#guard onRandomTriples (fun a c d => embedLaws a.1 c.1 d && embedLaws c.2.1 d.2.1 a) 500 13

/-- An element is the one its coordinates give, and the coordinates of the
element given by four coordinates are those. -/
def basisLaws (a : E) : Bool :=
  let x := e a
  let basis : Array BabyBear := ExtensionOps.toBasis x
  basis == #[x.c0, x.c1, x.c2, x.c3] && (ExtensionOps.ofBasis basis : BabyBearExt) == x
    && ExtensionOps.toBasis (ExtensionOps.ofBasis basis : BabyBearExt) == basis
    && basis.map (·.val) == #[a.1 % p, a.2.1 % p, a.2.2.1 % p, a.2.2.2 % p]

#guard samples.all basisLaws
#guard onRandomTriples (fun a c d => basisLaws a && basisLaws c && basisLaws d) 500 14

/-- The powers of an element agree with repeated products, and the
multiplicative group has order `p^4 - 1`. -/
def powerLaws (a : E) : Bool :=
  let x := e a
  ((List.range 20).foldl
      (fun (state : Bool × BabyBearExt) k => (state.1 && fieldPow x k == state.2, state.2 * x))
      (true, 1)).1
    && (x == 0 || fieldPow x (p ^ 4 - 1) == 1)
    && fieldPow x (p ^ 4) == x

#guard samples.all powerLaws
#guard onRandomTriples (fun a c d => powerLaws a && powerLaws c && powerLaws d) 20 15

/-! ## Against Plonky3 -/

/-- `(a, b, a + b, a - b, a * b)`, each element as its coordinates. -/
def arithmeticVectors : Array (E × E × E × E × E) := #[
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x78000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x78000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000001, 0x00000001, 0x00000001, 0x00000001),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x08000000, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x70000001, 0x68000004, 0x77fffffc, 0x70000003),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000002, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000001, 0x00000001, 0x00000000, 0x00000000),
    (0x00000001, 0x78000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000)),
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000002, 0x00000001, 0x00000001, 0x00000001),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000)),
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x08000001, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x70000002, 0x68000004, 0x77fffffc, 0x70000003),
    (0x08000000, 0x0ffffffd, 0x00000005, 0x07fffffe)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000001, 0x00000000, 0x00000000),
    (0x78000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x00000002, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000001, 0x00000000)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x78000000, 0x00000000, 0x78000000, 0x78000000),
    (0x00000001, 0x00000002, 0x00000001, 0x00000001),
    (0x77fffff6, 0x78000000, 0x78000000, 0x78000000)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x08000000, 0x0ffffffe, 0x00000005, 0x07fffffe),
    (0x70000001, 0x68000005, 0x77fffffc, 0x70000003),
    (0x57ffffea, 0x08000000, 0x0ffffffd, 0x00000005)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x78000000, 0x78000000, 0x78000000),
    (0x77ffffff, 0x78000000, 0x78000000, 0x78000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x78000000, 0x00000000, 0x78000000, 0x78000000),
    (0x78000000, 0x77ffffff, 0x78000000, 0x78000000),
    (0x77fffff6, 0x78000000, 0x78000000, 0x78000000)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x77ffffff, 0x77ffffff, 0x77ffffff, 0x77ffffff),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000022, 0x00000018, 0x0000000e, 0x00000004)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x07ffffff, 0x0ffffffc, 0x00000004, 0x07fffffd),
    (0x70000000, 0x68000003, 0x77fffffb, 0x70000002),
    (0x58000003, 0x07ffffe3, 0x08000015, 0x58000001)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x08000000, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x08000000, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x08000001, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x07ffffff, 0x0ffffffd, 0x00000005, 0x07fffffe),
    (0x08000000, 0x0ffffffd, 0x00000005, 0x07fffffe)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x08000000, 0x0ffffffe, 0x00000005, 0x07fffffe),
    (0x08000000, 0x0ffffffc, 0x00000005, 0x07fffffe),
    (0x57ffffea, 0x08000000, 0x0ffffffd, 0x00000005)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x07ffffff, 0x0ffffffc, 0x00000004, 0x07fffffd),
    (0x08000001, 0x0ffffffe, 0x00000006, 0x07ffffff),
    (0x58000003, 0x07ffffe3, 0x08000015, 0x58000001)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x10000000, 0x1ffffffa, 0x0000000a, 0x0ffffffc),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x400001a2, 0x05dddcfb, 0x68000039, 0x0eeeeed0)),
  ((0x8066bb2f, 0x8768c03b, 0x3cc5a317, 0x13fc23af),
    (0x05d238eb, 0xbc3efea9, 0x206513f1, 0x92d61d7a),
    (0x0e38f419, 0x53a7bee2, 0x5d2ab708, 0x2ed24128),
    (0x02948243, 0x4329c193, 0x1c608f26, 0x71260637),
    (0x5b0c8a4f, 0x2397c3a1, 0x46aa313b, 0x634edc70)),
  ((0x5bb42924, 0x3e03042f, 0x093ce3ec, 0xa165aec2),
    (0x4a917b22, 0x84ae84bb, 0x2ca42532, 0x7fa95b19),
    (0x2e45a445, 0x4ab188e9, 0x35e1091e, 0x310f09d9),
    (0x1122ae02, 0x31547f75, 0x5498bebb, 0x21bc53a9),
    (0x7675ad3b, 0x429a34e7, 0x38f69b77, 0x04e99d2a)),
  ((0x711b5ec4, 0xeec60b8e, 0xe1ae35a9, 0x0f3557dd),
    (0x705e01bf, 0xba65dc41, 0x0b79a0f1, 0x7b69d693),
    (0x69796082, 0x412be7cc, 0x7527d699, 0x129f2e6f),
    (0x00bd5d05, 0x34602f4d, 0x5e3494b7, 0x0bcb814b),
    (0x42809d52, 0x440cec43, 0x68fd32db, 0x30779fd0)),
  ((0x67722e0a, 0x4fdad7ed, 0x72fd7a07, 0xa9606f63),
    (0x8fc95d85, 0x5642264f, 0x83c169f0, 0xfb435e9d),
    (0x073b8b8d, 0x2e1cfe3b, 0x06bee3f5, 0x3ca3cdfd),
    (0x4fa8d086, 0x7198b19f, 0x673c1018, 0x261d10c7),
    (0x2ef7359c, 0x08b2ded3, 0x01362ef9, 0x607ff908)),
  ((0x234a0635, 0x9e6f2246, 0xd63a8e97, 0xa2527b3f),
    (0x4e3810fc, 0x7c07e91c, 0xdd505e76, 0x3742fe55),
    (0x71821731, 0x2a770b60, 0x4b8aed0a, 0x61957993),
    (0x4d11f53a, 0x2267392a, 0x70ea3022, 0x6b0f7cea),
    (0x2c2195b3, 0x18f160f0, 0x75180785, 0x11659b73)),
  ((0x1be9c6e8, 0x9df22a2f, 0x09396767, 0x5ed31617),
    (0x6e306352, 0x4a6e5755, 0xb455c89e, 0x28e2f050),
    (0x121a2a39, 0x70608183, 0x458f3004, 0x0fb60666),
    (0x25b96397, 0x5383d2da, 0x44e39ecb, 0x35f025c7),
    (0x09e4458c, 0x39f85142, 0x0e5136cc, 0x18a0c4be)),
  ((0x978fdcb0, 0xf86d4200, 0xbd2c0b2d, 0x4236daf4),
    (0x76d0c870, 0xef9eecc0, 0xa625fcfc, 0x5ea227ef),
    (0x1e60a51e, 0x080c2ebc, 0x73520827, 0x28d902e2),
    (0x20bf1440, 0x08ce5540, 0x17060e31, 0x5b94b306),
    (0x51331792, 0x2543c77d, 0x5ec0a916, 0x66719dbf)),
  ((0x1a3d1f4f, 0xf9799d19, 0x0a1db564, 0x2c3fc702),
    (0x97235653, 0x445d18e7, 0xd0efb1a6, 0x43de9567),
    (0x396075a1, 0x4dd6b5fe, 0x630d6709, 0x701e5c69),
    (0x7319c8fe, 0x3d1c8431, 0x292e03c0, 0x6061319c),
    (0x6a2761c3, 0x498c922d, 0x76708c7c, 0x5b61b3f0)),
  ((0x55e71265, 0x8530a6d9, 0xc3565614, 0xf14aeea3),
    (0x3af442e1, 0xca362e38, 0xad2af770, 0x8917f39b),
    (0x18db5545, 0x5f66d50f, 0x08814d81, 0x1262e23b),
    (0x1af2cf84, 0x32fa78a2, 0x162b5ea4, 0x6832fb08),
    (0x65ba1047, 0x1e9f898e, 0x4b2050e9, 0x4a939d1c)),
  ((0xc332194b, 0x2f785549, 0xb02472f1, 0x4eb53d29),
    (0x6e3b8c3d, 0x80d9bd95, 0xb2e87784, 0xc7f8d748),
    (0x416da586, 0x385212dd, 0x730cea73, 0x26ae146f),
    (0x54f68d0e, 0x269e97b5, 0x753bfb6e, 0x76bc65e3),
    (0x1c8ffa01, 0x14e92364, 0x359551c0, 0x1cc9a416)),
  ((0x527223cb, 0x0f0de319, 0x2b0b6806, 0x32c3f2fd),
    (0xb18bc6d3, 0x88142bfe, 0xeba83013, 0x428133ce),
    (0x13fdea9c, 0x1f220f16, 0x26b39817, 0x754526cb),
    (0x18e65cf9, 0x76f9b71d, 0x2f6337f5, 0x6842bf30),
    (0x3674443d, 0x35a3c9da, 0x448fb1bc, 0x132e7760)),
  ((0xba1d6cdb, 0x548ce534, 0x3dcde35a, 0x73df0cc0),
    (0xcfae763d, 0x681f0ffe, 0x4bda0b40, 0x2b3ae48e),
    (0x21cbe315, 0x44abf531, 0x11a7ee99, 0x2719f14d),
    (0x626ef69f, 0x646dd537, 0x69f3d81b, 0x48a42832),
    (0x4c04ac06, 0x260c379c, 0x544c2cfb, 0x719cda83)),
  ((0x89eb46e8, 0x0bcc0dce, 0x29d0dd81, 0xcf6ac2b2),
    (0xf0a35625, 0x78c65ab6, 0xe78c5927, 0xc3da7d78),
    (0x128e9d0a, 0x0c926883, 0x215d36a6, 0x2b454027),
    (0x1147f0c4, 0x0b05b319, 0x3244845c, 0x0b90453a),
    (0x459107bc, 0x6a8b0a65, 0x4f446f6b, 0x2c6f54a2)),
  ((0x13f0b633, 0x9bd22bb0, 0x74ecb39b, 0xe50547ce),
    (0xee5a3924, 0x6338292e, 0xb1d9cdb8, 0x9214c3e3),
    (0x124aef55, 0x0f0a54dc, 0x36c68151, 0x0f1a0bae),
    (0x15967d11, 0x389a0282, 0x3b12e5e4, 0x52f083eb),
    (0x43a651f9, 0x243a493d, 0x44f5801c, 0x33030115)),
  ((0x17b847ce, 0x1bfa8120, 0x074afff8, 0x5c3184b2),
    (0xc5a5e7f3, 0xf996a105, 0x94bafdfa, 0x1620d229),
    (0x655e2fc0, 0x25912223, 0x2405fdf1, 0x725256db),
    (0x42125fdd, 0x1263e01d, 0x62900200, 0x4610b289),
    (0x5eb141e4, 0x142d7eca, 0x6932c8c3, 0x51d130ca))]

/-- `(a, -a, a⁻¹, a²)` for nonzero `a`. -/
def unaryVectors : Array (E × E × E × E) := #[
  ((0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x78000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000),
    (0x00000001, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000001, 0x00000000, 0x00000000),
    (0x00000000, 0x78000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x20ba2e8c),
    (0x00000000, 0x00000000, 0x00000001, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000001, 0x00000000),
    (0x00000000, 0x00000000, 0x78000000, 0x00000000),
    (0x00000000, 0x00000000, 0x20ba2e8c, 0x00000000),
    (0x0000000b, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x00000001),
    (0x00000000, 0x00000000, 0x00000000, 0x78000000),
    (0x00000000, 0x20ba2e8c, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x0000000b, 0x00000000)),
  ((0x78000000, 0x78000000, 0x78000000, 0x78000000),
    (0x00000001, 0x00000001, 0x00000001, 0x00000001),
    (0x6c000001, 0x0c000000, 0x00000000, 0x00000000),
    (0x00000022, 0x00000018, 0x0000000e, 0x00000004)),
  ((0x08000000, 0xffffffff, 0x78000006, 0x7fffffff),
    (0x70000001, 0x68000004, 0x77fffffc, 0x70000003),
    (0x5fea118b, 0x132f6509, 0x6280e762, 0x4bdfff04),
    (0x400001a2, 0x05dddcfb, 0x68000039, 0x0eeeeed0)),
  ((0x00000000, 0x00000000, 0x00000005, 0x00000000),
    (0x00000000, 0x00000000, 0x77fffffc, 0x00000000),
    (0x00000000, 0x00000000, 0x1e8ba2e9, 0x00000000),
    (0x00000113, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000003, 0x00000000, 0x00000000, 0x00000007),
    (0x77fffffe, 0x00000000, 0x00000000, 0x77fffffa),
    (0x24df6d4b, 0x31fdf1c5, 0x72ef74ec, 0x71f6aba8),
    (0x00000009, 0x00000000, 0x0000021b, 0x0000002a)),
  ((0x00000008, 0x00000001, 0x00000000, 0x00000000),
    (0x77fffff9, 0x78000000, 0x00000000, 0x00000000),
    (0x652408c7, 0x5c5b7ee8, 0x6c749024, 0x2e716dfc),
    (0x00000040, 0x00000010, 0x00000001, 0x00000000)),
  ((0x00000000, 0x00000000, 0x76fb2832, 0x00000000),
    (0x00000000, 0x00000000, 0x0104d7cf, 0x00000000),
    (0x00000000, 0x00000000, 0x4903b637, 0x00000000),
    (0x1a427a41, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000000, 0x00000000, 0x00000000, 0x0771f1c8),
    (0x00000000, 0x00000000, 0x00000000, 0x708e0e39),
    (0x00000000, 0x3e09fb40, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x76fb2832, 0x00000000)),
  ((0xa50c516e, 0xc3916d14, 0xd634539d, 0xf63e80a0),
    (0x4af3ae94, 0x2c6e92ee, 0x19cbac65, 0x71c17f63),
    (0x14c100d3, 0x04214897, 0x7481ab36, 0x6f837af4),
    (0x3e5ea573, 0x5d7427cb, 0x3ad948f4, 0x4fc6de2f)),
  ((0x6d5c96ee, 0xebb04a29, 0x5fa7fce0, 0x8c3791e4),
    (0x0aa36913, 0x044fb5d9, 0x18580321, 0x63c86e1e),
    (0x055e111a, 0x2c88e664, 0x069fe5ac, 0x73beece1),
    (0x1d6367a4, 0x18e9c78a, 0x40403c12, 0x70d7f355)),
  ((0x271ed8de, 0x7a2d85eb, 0x60abaf40, 0x128c0a5a),
    (0x50e12723, 0x75d27a17, 0x175450c1, 0x6573f5a7),
    (0x2db3c9fe, 0x74faf579, 0x22cb64dc, 0x2bc69968),
    (0x439cc68f, 0x1220c86c, 0x37a175a5, 0x004cad58)),
  ((0x1f9627aa, 0x79b519e3, 0x02517128, 0x3fddc8dd),
    (0x5869d857, 0x764ae61f, 0x75ae8ed9, 0x38223724),
    (0x68db4726, 0x4c72d978, 0x16dc0ac8, 0x4b82b184),
    (0x0bca657f, 0x3c89330c, 0x6575f881, 0x67839ab7)),
  ((0xcd2c2ab2, 0x9c0b0436, 0xde7c40d2, 0xcedcafb2),
    (0x22d3d550, 0x53f4fbcc, 0x1183bf30, 0x21235050),
    (0x69b21f1e, 0x1e8054bd, 0x00274ac6, 0x0edae496),
    (0x5f48a8b1, 0x0dcf6c33, 0x205cce52, 0x6839ea0c)),
  ((0x9fa6f1a1, 0x7105e02b, 0x507e5388, 0x2f855e12),
    (0x50590e61, 0x06fa1fd6, 0x2781ac79, 0x487aa1ef),
    (0x4923368b, 0x1b90d9eb, 0x4997be10, 0x202c1d10),
    (0x0db67cc5, 0x73d58c47, 0x42da1ea2, 0x1e115d73)),
  ((0x44b89e80, 0xc0b103fb, 0x0fe8df75, 0xd4937d48),
    (0x33476181, 0x2f4efc07, 0x6817208c, 0x1b6c82ba),
    (0x16351e54, 0x3c8a878a, 0x356a0943, 0x60094129),
    (0x0f133cf2, 0x4f5cf925, 0x3215689d, 0x12bd701b)),
  ((0xf26a3283, 0x9afadc02, 0xf7ebcba4, 0x4cb12e91),
    (0x7595cd80, 0x55052400, 0x7014345f, 0x2b4ed170),
    (0x5da85979, 0x28c4b421, 0x6f8ed0ae, 0x3a84e739),
    (0x656b7901, 0x2a325074, 0x6d7390a3, 0x3b5f375b)),
  ((0xbb92465a, 0x79283a6e, 0x8d723e08, 0x6bfb52cd),
    (0x346db9a8, 0x76d7c594, 0x628dc1fa, 0x0c04ad34),
    (0x1fbc3214, 0x2cfb43d2, 0x655cf1ab, 0x23b55e11),
    (0x6f374d60, 0x571a4a32, 0x743dab29, 0x5b6a29ad)),
  ((0x4fe3a887, 0x22d282c7, 0x23dc20f6, 0x8c74f80f),
    (0x281c577a, 0x552d7d3a, 0x5423df0b, 0x638b07f3),
    (0x66b06395, 0x25e57fdd, 0x5b6304a1, 0x3c6ee315),
    (0x108f4a72, 0x3f5c9ea5, 0x224035bd, 0x23043b9a)),
  ((0x40469e0c, 0x0337e98a, 0xfb06d22b, 0x948cb5d0),
    (0x37b961f5, 0x74c81677, 0x6cf92dd8, 0x5b734a32),
    (0x228dd474, 0x034f1161, 0x41127693, 0x228c6a6c),
    (0x023cb4ab, 0x596af895, 0x14fb7714, 0x652acbd7)),
  ((0xc6d171c7, 0x3503e852, 0x9121f3f9, 0x78fdb39f),
    (0x292e8e3b, 0x42fc17af, 0x5ede0c09, 0x77024c63),
    (0x02a96c14, 0x00ba8316, 0x02e0d571, 0x0e9a5694),
    (0x4b0f12d1, 0x5ed3d39a, 0x6499d364, 0x153ee386)),
  ((0x28204d9d, 0xab78acdb, 0x8da9e423, 0xd68a6f6d),
    (0x4fdfb264, 0x44875327, 0x62561bdf, 0x19759095),
    (0x29d39c1f, 0x72cc04cb, 0x0504a89d, 0x031e0bc8),
    (0x02818265, 0x5cc8ab32, 0x75964f55, 0x19ca6d11)),
  ((0x9d906004, 0xf022b20a, 0xdf1c87ef, 0xfa4007c8),
    (0x526f9ffe, 0x77dd4df9, 0x10e37813, 0x6dbff83b),
    (0x3af986f4, 0x2c922118, 0x05e2fdb5, 0x24251f84),
    (0x2ed9b1d7, 0x6dba7f10, 0x77b5f73f, 0x5175b488)),
  ((0x06272132, 0xf03c44e1, 0xd12ed6e3, 0x11e948fa),
    (0x71d8decf, 0x77c3bb22, 0x1ed1291f, 0x6616b707),
    (0x29313dfc, 0x4ef7243b, 0x0fb5e91d, 0x4db6e88a),
    (0x0d0d1018, 0x2590d624, 0x0dc10205, 0x599f988b))]

/-- `(a, n, a ^ n)`. -/
def powerVectors : Array (E × Nat × E) := #[
  ((0xea2eb0f9, 0x4aae0581, 0x7a669e44, 0xd257b41d), 0,
    (0x00000001, 0x00000000, 0x00000000, 0x00000000)),
  ((0xc6c2ddb9, 0x98d92f1f, 0xe4cb51a4, 0xd4ca613a), 1,
    (0x4ec2ddb8, 0x20d92f1e, 0x6ccb51a3, 0x5cca6139)),
  ((0x2fbea106, 0xfd462b5f, 0x23f8b1d0, 0x5294613a), 2,
    (0x753d82fc, 0x1e0b3096, 0x28ef543b, 0x41d8f5cc)),
  ((0xc6b440f7, 0x88a30ce6, 0x50a981d2, 0x2490d05e), 5,
    (0x0bde51a3, 0x1f666a31, 0x4c532a48, 0x131598c9)),
  ((0xe6783c84, 0x8d073600, 0xd587be3e, 0x62617887), 2013265921,
    (0x6e783c83, 0x7243128d, 0x1a7841c4, 0x6af1defa)),
  ((0xbc0e7387, 0x31a6e669, 0x8eb6cf22, 0x61f493ee), 4294967297,
    (0x4d134fc6, 0x40abecf8, 0x6b35f715, 0x49e2b06d)),
  ((0xea610489, 0xa6c5ae52, 0x94a53e20, 0x472b7cf6), 9223372036854775808,
    (0x22cb1b39, 0x204e19ee, 0x5da2d96e, 0x5c274df0)),
  ((0x54b1a50b, 0x494b500c, 0xb7e36a86, 0x6271059d), 18446744073709551615,
    (0x74bc2665, 0x6ecfccc9, 0x6d8e9c08, 0x317b9ee4))]

/-- `(a, e, EF::from(a) * e)`: the base element `a` times the extension element
`e`. -/
def embedVectors : Array (Nat × E × E) := #[
  (0x73b1689d, (0x9c65e6df, 0xb0056fc4, 0xfa4fec84, 0x94c0647e),
    (0x4eaf4e9a, 0x598d0fb3, 0x3d09af88, 0x08853162)),
  (0x38f5380e, (0x3b44e600, 0x79d3b981, 0x4ccd9542, 0x1d644eb8),
    (0x19f2c6b7, 0x40ca23b6, 0x479a3f8d, 0x64d92646)),
  (0x36f1b9cc, (0x1c0ac0eb, 0x47bce560, 0xd4dd8ece, 0x95e78053),
    (0x085fa11b, 0x1ad07294, 0x1737c57d, 0x63b64c81)),
  (0xcbf74105, (0x74f45654, 0xe1948148, 0xbeeeb1ed, 0x7452d54d),
    (0x32f2f70c, 0x11c5c9f4, 0x13f9c904, 0x6c5a2db0)),
  (0x4c83f0ad, (0x6c95116c, 0x70ef27a7, 0x514489e6, 0x969d97a1),
    (0x7619d3c8, 0x2d3cca19, 0x5179409e, 0x29fffeb9)),
  (0xb1648b95, (0x89720627, 0xc5c74e27, 0x977ba1d0, 0xe01bde2b),
    (0x4bc23579, 0x0e4cc607, 0x71223c70, 0x225a602c)),
  (0x7dc3f2f0, (0xe975893b, 0x12e83f7b, 0xf5dbc032, 0xc9f2bc36),
    (0x142e7169, 0x5b9dfcd8, 0x601dbe85, 0x00f6e1f6)),
  (0x5adb0b3b, (0x3e1cc8ee, 0x91ebaa3a, 0x229ae3f9, 0xd51c8212),
    (0x6dd7916a, 0x1ec39df5, 0x1f4de7b2, 0x3f345d08))]

/-- `(c, EF::from_basis_coefficients_slice(c).as_basis_coefficients_slice())`: the
coordinates `c` are any words of 32 bits. -/
def basisVectors : Array (E × E) := #[
  ((0x00000000, 0x00000000, 0x00000000, 0x00000000),
    (0x00000000, 0x00000000, 0x00000000, 0x00000000)),
  ((0x00000064, 0x00000065, 0x00000066, 0x00000067),
    (0x00000064, 0x00000065, 0x00000066, 0x00000067)),
  ((0x78000000, 0x00000000, 0x78000000, 0x00000000),
    (0x78000000, 0x00000000, 0x78000000, 0x00000000)),
  ((0x78000001, 0x78000002, 0xffffffff, 0x80000000),
    (0x00000000, 0x00000001, 0x0ffffffd, 0x07ffffff)),
  ((0x5f17085e, 0xf4512182, 0xd95ac400, 0xf89a0c6e),
    (0x5f17085e, 0x04512180, 0x615ac3ff, 0x089a0c6c)),
  ((0xae4ff2cc, 0x8bc7659a, 0xc6b4cd17, 0x22d6dd25),
    (0x364ff2cb, 0x13c76599, 0x4eb4cd16, 0x22d6dd25)),
  ((0x71947f00, 0x920c15f1, 0x7ffb8c20, 0x22fabbde),
    (0x71947f00, 0x1a0c15f0, 0x07fb8c1f, 0x22fabbde)),
  ((0x543c678d, 0x2b89ec9e, 0xc6507323, 0x7559a92b),
    (0x543c678d, 0x2b89ec9e, 0x4e507322, 0x7559a92b))]

/-- `EF::ith_basis_element(i)` for `i = 0, …, 3`. -/
def basisElementVectors : Array E := #[
  (0x00000001, 0x00000000, 0x00000000, 0x00000000),
  (0x00000000, 0x00000001, 0x00000000, 0x00000000),
  (0x00000000, 0x00000000, 0x00000001, 0x00000000),
  (0x00000000, 0x00000000, 0x00000000, 0x00000001)]

/-- `EF::from(BabyBear::new(5))`. -/
def embedFiveVector : E := (0x00000005, 0x00000000, 0x00000000, 0x00000000)

/-- `EF::GENERATOR`, a generator of the multiplicative group. -/
def generatorVector : E := (0x00000008, 0x00000001, 0x00000000, 0x00000000)

/-- `EF::two_adic_generator(k)` for `k = 27, 28, 29`. -/
def twoAdicGeneratorVectors : Array E := #[
  (0x1a427a41, 0x00000000, 0x00000000, 0x00000000),
  (0x00000000, 0x00000000, 0x76fb2832, 0x00000000),
  (0x00000000, 0x00000000, 0x00000000, 0x0771f1c8)]

#guard arithmeticVectors.size = 40
#guard arithmeticVectors.all fun (a, c, sum, difference, product) =>
  coords (e a + e c) == sum && coords (e a - e c) == difference && coords (e a * e c) == product

#guard unaryVectors.size = 26
#guard unaryVectors.all fun (a, opposite, inverse, square) =>
  coords (-e a) == opposite && coords (e a)⁻¹ == inverse && coords (e a * e a) == square

#guard powerVectors.size = 8
#guard powerVectors.all fun (a, n, power) => coords (fieldPow (e a) n) == power

#guard embedVectors.size = 8
#guard embedVectors.all fun (s, a, product) => coords (embed (b s) * e a) == product

-- Plonky3's `from_basis_coefficients_slice` is `ofBasis` on four coordinates
-- (it rejects any other number of coordinates, where `ofBasis` pads or
-- truncates), and its `as_basis_coefficients_slice` is `toBasis`.
#guard basisVectors.size = 8
#guard basisVectors.all fun (c, canonical) =>
  let x : BabyBearExt := ExtensionOps.ofBasis #[b c.1, b c.2.1, b c.2.2.1, b c.2.2.2]
  let basis : Array BabyBear := ExtensionOps.toBasis x
  coords x == canonical
    && basis.map (·.val) == #[canonical.1, canonical.2.1, canonical.2.2.1, canonical.2.2.2]
    && (ExtensionOps.ofBasis basis : BabyBearExt) == x

#guard basisElementVectors = #[coords 1, coords X, coords (X * X), coords (X * X * X)]
#guard coords (embed (b 5)) = embedFiveVector

-- Plonky3's generator of the multiplicative group of the extension is not a
-- square.
#guard fieldPow (e generatorVector) ((p ^ 4 - 1) / 2) = -1
-- Plonky3's generators of the subgroups of order `2^28` and `2^29` of the
-- extension: each is a square root of the one before, starting from the
-- generator of order `2^27` of the base field.
#guard twoAdicGeneratorVectors.size = 3
#guard twoAdicGeneratorVectors[0]? = some (coords (embed (TwoAdicOps.twoAdicGenerator 27)))
#guard (List.range 2).all fun k =>
  let w := e (twoAdicGeneratorVectors[k]?.getD default)
  let next := e (twoAdicGeneratorVectors[k + 1]?.getD default)
  next * next == w && fieldPow next (2 ^ (27 + k)) == -1

end CertiFriTest.P3.BabyBearExt
