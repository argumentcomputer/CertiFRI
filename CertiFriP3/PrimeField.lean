import CertiFri.Field

/-!
# Prime fields with representatives in natural numbers

The prime field of order `p`, for any `p`, with the `FieldOps` instance the
verifier is written against. An element is stored as its representative below
`p`, and the type carries the proof that it is below `p`: two elements are
equal exactly when their representatives are.

The operations are those of the natural numbers followed by a reduction modulo
`p`. A representative of a field of at most 63 bits is an unboxed machine
integer in compiled code, and so is the product of two representatives of a
field of at most 31 bits; larger fields use arbitrary-precision arithmetic.
The inverse is the power `p - 2`, by squaring (Fermat's little theorem), with
the inverse of zero being zero.

The fields of Plonky3 that this file is instantiated at (`BabyBear.lean`,
`Bn254.lean`) keep their elements in Montgomery form; the values are the same.
The Goldilocks field has its own implementation on machine words
(`Goldilocks.lean`).

Nothing about the operations is proved in this package. That they are the
operations of a field when `p` is prime is proved in the proofs package
(`Proofs/CertiFriProofs/P3/FpLaws.lean`).

Not covered: encodings of an element as bytes, and square roots.
-/

namespace CertiFri.P3

/-- An element of the prime field of order `p`: its representative below `p`. -/
structure Fp (p : Nat) where
  /-- The representative of the element in `[0, p)`. -/
  val : Nat
  /-- The representative is below the order. -/
  lt : val < p

namespace Fp

variable {p : Nat}

/-- Elements with the same representative are equal. -/
theorem ext {a b : Fp p} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (Fp p) := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse fun heq => h (heq ▸ rfl)

instance : Repr (Fp p) := ⟨fun a prec => reprPrec a.val prec⟩

/-- The element a natural number represents: the number reduced modulo `p`. -/
def ofNat [NeZero p] (n : Nat) : Fp p :=
  ⟨n % p, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))⟩

/-- The element with representative `n`, if `n` is below `p`. A number of `p`
or more is rejected, not reduced. -/
def ofCanonical? (n : Nat) : Option (Fp p) :=
  if h : n < p then some ⟨n, h⟩ else none

instance [NeZero p] : Inhabited (Fp p) := ⟨ofNat 0⟩

/-- Sum. -/
protected def add (a b : Fp p) : Fp p :=
  ⟨(a.val + b.val) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt a.lt)⟩

/-- Difference: `a + (p - b)`, reduced. -/
protected def sub (a b : Fp p) : Fp p :=
  ⟨(a.val + (p - b.val)) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt a.lt)⟩

/-- Opposite: `p - a`, which the reduction sends to zero when `a` is zero. -/
protected def neg (a : Fp p) : Fp p :=
  ⟨(p - a.val) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt a.lt)⟩

/-- Product. -/
protected def mul (a b : Fp p) : Fp p :=
  ⟨(a.val * b.val) % p, Nat.mod_lt _ (Nat.zero_lt_of_lt a.lt)⟩

/-- `x ^ n` for an exponent below `2 ^ bits`, by squaring: the exponent is read
from its lowest bit, and `x ^ n = (x ^ (n / 2)) ^ 2 * x ^ (n % 2)`. The power
zero is `one`. -/
def powBits (one x : Fp p) : (bits n : Nat) → Fp p
  | 0, _ => one
  | bits + 1, n =>
    let half := powBits one x bits (n / 2)
    if n % 2 = 0 then half.mul half else (half.mul half).mul x

/-- Inverse, with the inverse of zero being zero: the power `p - 2`. -/
protected def inv [NeZero p] (a : Fp p) : Fp p :=
  if a.val = 0 then a else powBits (ofNat 1) a (Nat.log2 p + 1) (p - 2)

instance [NeZero p] : FieldOps (Fp p) where
  zero := ofNat 0
  one := ofNat 1
  add := Fp.add
  sub := Fp.sub
  mul := Fp.mul
  neg := Fp.neg
  inv := Fp.inv
  beq a b := decide (a = b)

end Fp

end CertiFri.P3
