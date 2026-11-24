import CertiFri.Field

/-!
# The Goldilocks field

The prime field of order `p = 2^64 - 2^32 + 1`, as Plonky3's `Goldilocks`
(`goldilocks/src/goldilocks.rs`), with the instances the verifier is written
against: `FieldOps` and `TwoAdicOps`.

An element is stored as its representative below `p` in a machine word, and the
type carries the proof that the word is below `p`. Two elements are therefore
equal exactly when their words are, and every function of this file returns a
canonical word by construction. Plonky3 keeps a word that may exceed `p` and
reduces it when it serializes or compares; the values are the same.

Arithmetic stays in machine words: no natural number is allocated by an
operation of the field. The product is computed as a 128-bit value in two
words and reduced with `2^64 = 2^32 - 1` and `2^96 = -1` modulo `p`, as in
Plonky3's `reduce128`. The inverse is computed by the extended Euclidean
algorithm on words; Plonky3 uses a different algorithm for the same value.

That each word is canonical is proved here. That the order is prime, that the
operations compute the field operations and that the generators are primitive
roots of unity is proved in the proofs package
(`Proofs/CertiFriProofs/P3/GoldilocksWord.lean`, `GoldilocksModel.lean`). The
operations are also tested, against natural-number arithmetic and against
values computed by Plonky3 (`CertiFriTest/P3/Goldilocks.lean`).

Not covered: square roots, Plonky3's vectorized arithmetic, and encodings other
than the eight little-endian bytes of the canonical word.
-/

namespace CertiFri.P3

/-- The order `p = 2^64 - 2^32 + 1` of the Goldilocks field. -/
def Goldilocks.order : Nat := 0xFFFFFFFF00000001

/-- An element of the Goldilocks field: its representative below the order, in
a machine word. -/
structure Goldilocks where
  /-- The representative of the element in `[0, p)`. -/
  val : UInt64
  /-- The representative is below the order. -/
  canonical : val < 0xFFFFFFFF00000001

namespace Goldilocks

/-- The order as a machine word. -/
local notation "P64" => (0xFFFFFFFF00000001 : UInt64)

/-- `2^64 - p = 2^32 - 1`, which is `2^64` modulo `p`. It is also the mask of
the low 32 bits of a word. -/
local notation "EPS" => (0xFFFFFFFF : UInt64)

/-- Elements with the same word are equal. -/
theorem ext {a b : Goldilocks} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq Goldilocks := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse fun heq => h (heq ▸ rfl)

/-- A word at least `p` is below `2 * p`: one subtraction makes it canonical. -/
theorem sub_order_lt {x : UInt64} (h : ¬ x < P64) : x - P64 < P64 := by
  have hle : P64 ≤ x := UInt64.not_lt.mp h
  have hx := x.toNat_lt
  have hp : UInt64.toNat P64 = 0xFFFFFFFF00000001 := rfl
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ hle]
  omega

/-- The element a machine word represents: the word reduced modulo `p`. -/
@[inline] def ofUInt64 (x : UInt64) : Goldilocks :=
  if h : x < P64 then ⟨x, h⟩ else ⟨x - P64, sub_order_lt h⟩

/-- The element a natural number represents: the number reduced modulo `p`. -/
def ofNat (n : Nat) : Goldilocks :=
  ofUInt64 (n % order).toUInt64

/-- The element with canonical word `x`, if `x` is below `p`. This is how
Plonky3 deserializes an element: a word of `p` or more is rejected, not
reduced. -/
def ofCanonical? (x : UInt64) : Option Goldilocks :=
  if h : x < P64 then some ⟨x, h⟩ else none

/-- The representative of the element in `[0, p)`, as a natural number. -/
def toNat (a : Goldilocks) : Nat :=
  a.val.toNat

/-- The representative is below the order. -/
theorem toNat_lt_order (a : Goldilocks) : a.toNat < order :=
  UInt64.lt_iff_toNat_lt.mp a.canonical

/-- Append the eight bytes of the element: its canonical word, least significant
byte first. This is the encoding Plonky3 hashes and absorbs
(`into_bytes`, `to_unique_u64().to_le_bytes()`). -/
def pushBytes (bytes : ByteArray) (a : Goldilocks) : ByteArray :=
  let w := a.val
  ((((((((bytes.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push
    (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push
    (w >>> 48).toUInt8).push (w >>> 56).toUInt8)

/-- The zero of the field. -/
protected def zero : Goldilocks := ofUInt64 0

/-- The one of the field. -/
protected def one : Goldilocks := ofUInt64 1

instance : Inhabited Goldilocks := ⟨Goldilocks.zero⟩

instance : Repr Goldilocks := ⟨fun a prec => reprPrec a.val prec⟩

/-- Sum. With `nb = p - b`, the sum is `a - nb` when that does not underflow
and `a + b` otherwise; neither overflows a word. -/
protected def add (a b : Goldilocks) : Goldilocks :=
  let nb := P64 - b.val
  if nb ≤ a.val then ofUInt64 (a.val - nb) else ofUInt64 (a.val + b.val)

/-- Difference: `a - b` when that does not underflow, `a + (p - b)` otherwise. -/
protected def sub (a b : Goldilocks) : Goldilocks :=
  if b.val ≤ a.val then ofUInt64 (a.val - b.val) else ofUInt64 (a.val + (P64 - b.val))

/-- Opposite: `p - a`, which the reduction sends to zero when `a` is zero. -/
protected def neg (a : Goldilocks) : Goldilocks :=
  ofUInt64 (P64 - a.val)

/-- The high word of the 128-bit product of two words. The low word is the
wrapping product. The operands are split in halves of 32 bits; no partial sum
overflows a word. -/
@[inline] def mulHigh (a b : UInt64) : UInt64 :=
  let a0 := a &&& EPS
  let a1 := a >>> 32
  let b0 := b &&& EPS
  let b1 := b >>> 32
  let mid := a0 * b1 + ((a0 * b0) >>> 32)
  let mid2 := a1 * b0 + (mid &&& EPS)
  a1 * b1 + (mid >>> 32) + (mid2 >>> 32)

/-- The element represented by the 128-bit value `hi * 2^64 + lo`. With
`hi = hh * 2^32 + hl`, the value is `lo - hh + hl * (2^32 - 1)` modulo `p`,
because `2^64 = 2^32 - 1` and `2^96 = -1` modulo `p`. A borrow or a carry out
of a word is `2^64`, and is corrected by subtracting or adding `2^32 - 1`. -/
@[inline] def reduce128 (hi lo : UInt64) : Goldilocks :=
  let hh := hi >>> 32
  let hl := hi &&& EPS
  let t0 := if lo < hh then lo - hh - EPS else lo - hh
  let t1 := hl * EPS
  let t2 := t0 + t1
  ofUInt64 (if t2 < t1 then t2 + EPS else t2)

/-- Product. -/
protected def mul (a b : Goldilocks) : Goldilocks :=
  reduce128 (mulHigh a.val b.val) (a.val * b.val)

/-- The extended Euclidean algorithm on `(p, a)`, on words.

The remainders start at `r0 = p`, `r1 = a` and the cofactors at `t0 = 0`,
`t1 = 1`. A step replaces `(r0, r1)` by `(r1, r0 mod r1)` and `(t0, t1)` by
`(t1, t0 + q * t1)` for the quotient `q`. The cofactors are kept as absolute
values, since their signs alternate: after an even number of steps
`r1 = t1 * a` modulo `p`, after an odd number `r1 = -t1 * a`, and `odd` records
which. Since `t1 * r0 + t0 * r1 = p` throughout, no cofactor overflows a word.

When the remainder reaches one, the signed cofactor is the inverse. A remainder
of zero is reached only from `a = 0`, and gives zero. -/
def invLoop (r0 r1 t0 t1 : UInt64) (odd : Bool) : Goldilocks :=
  if h : r1 ≤ 1 then
    if r1 = 1 then (if odd then ofUInt64 (P64 - t1) else ofUInt64 t1) else Goldilocks.zero
  else
    have : (r0 % r1).toNat < r1.toNat := by
      have h1 : (1 : UInt64).toNat = 1 := rfl
      have hlt := mt UInt64.le_iff_toNat_le.mpr h
      rw [UInt64.toNat_mod]
      exact Nat.mod_lt _ (by omega)
    invLoop r1 (r0 % r1) t1 (t0 + r0 / r1 * t1) (!odd)
termination_by r1.toNat

/-- Inverse, with the inverse of zero being zero. -/
protected def inv (a : Goldilocks) : Goldilocks :=
  invLoop P64 a.val 0 1 false

instance : FieldOps Goldilocks where
  zero := Goldilocks.zero
  one := Goldilocks.one
  add := Goldilocks.add
  sub := Goldilocks.sub
  mul := Goldilocks.mul
  neg := Goldilocks.neg
  inv := Goldilocks.inv
  beq a b := decide (a = b)

/-- The words of Plonky3's `Goldilocks::TWO_ADIC_GENERATORS`: entry `k` is a
generator of the subgroup of order `2^k`, and each entry is the square of the
next. -/
def twoAdicGenerators : Array UInt64 := #[
  0x0000000000000001, 0xffffffff00000000, 0x0001000000000000, 0xfffffffeff000001,
  0xefffffff00000001, 0x00003fffffffc000, 0x0000008000000000, 0xf80007ff08000001,
  0xbf79143ce60ca966, 0x1905d02a5c411f4e, 0x9d8f2ad78bfed972, 0x0653b4801da1c8cf,
  0xf2c35199959dfcb6, 0x1544ef2335d17997, 0xe0ee099310bba1e2, 0xf6b2cffe2306baac,
  0x54df9630bf79450e, 0xabd0a6e8aa3d8a0e, 0x81281a7b05f9beac, 0xfbd41c6b8caa3302,
  0x30ba2ecd5e93e76d, 0xf502aef532322654, 0x4b2a18ade67246b5, 0xea9d5a1336fbc98b,
  0x86cdcc31c307e171, 0x4bbaf5976ecfefd8, 0xed41d05b78d6e286, 0x10d78dd8915a171d,
  0x59049500004a4485, 0xdfa8c93ba46d2666, 0x7e9bd009b86a0845, 0x400a7f755588e659,
  0x185629dcda58878c]

/-- Plonky3's `Goldilocks::two_adic_generator(bits)` for `bits ≤ 32`. Plonky3
panics above 32; this function returns zero there. -/
def twoAdicGenerator (bits : Nat) : Goldilocks :=
  match twoAdicGenerators[bits]? with
  | some word => ofUInt64 word
  | none => Goldilocks.zero

/-- Plonky3's `Goldilocks::GENERATOR`: the generator `7` of the multiplicative
group. -/
def generator : Goldilocks := ofUInt64 7

instance : TwoAdicOps Goldilocks where
  twoAdicity := 32
  twoAdicGenerator := twoAdicGenerator
  cosetShift := generator

end Goldilocks

end CertiFri.P3
