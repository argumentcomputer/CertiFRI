/-!
# Executable field interfaces

The verifier is generic over the base field `F` and the extension field `EF`
its challenges live in. These classes carry operations only. They state no
laws: a law about machine arithmetic is a theorem, and theorems about field
structure need Mathlib. The proofs package relates an instance to a
mathematical field through an abstraction map (`CertiFri.Refines`) and proves
the laws there.
-/

namespace CertiFri

/-- The operations of a field, as executable functions.

`inv` is total. An instance is expected to send zero to zero, matching the
convention of the mathematical model. -/
class FieldOps (F : Type) extends Zero F, One F, Add F, Sub F, Mul F, Neg F, Inv F, BEq F

/-- The two-adic structure the evaluation domains are built from. -/
class TwoAdicOps (F : Type) [FieldOps F] where
  /-- The largest `k` such that the field has a subgroup of order `2 ^ k`. -/
  twoAdicity : Nat
  /-- A generator of the subgroup of order `2 ^ bits`, for `bits ≤ twoAdicity`.
  Generators of different orders are compatible: squaring the generator of
  order `2 ^ (bits + 1)` gives the generator of order `2 ^ bits`. -/
  twoAdicGenerator : (bits : Nat) → F
  /-- The shift of the coset the committed codewords are evaluated on
  (Plonky3's `Val::GENERATOR`). -/
  cosetShift : F

/-- `EF` as an extension of `F` with a fixed basis. -/
class ExtensionOps (F EF : Type) [FieldOps F] [FieldOps EF] where
  /-- Degree of the extension. -/
  degree : Nat
  /-- The embedding of the base field. -/
  embed : F → EF
  /-- Coordinates in the fixed basis. This is the order in which an extension
  element is absorbed into the transcript. -/
  toBasis : EF → Array F
  /-- The element with the given coordinates. This is how a challenge is
  assembled from sampled base-field elements. -/
  ofBasis : Array F → EF

/-- `x ^ n` for an exponent below `2 ^ bits`, by squaring: the exponent is read
from its lowest bit, and `x ^ n = (x ^ (n / 2)) ^ 2 * x ^ (n % 2)`. -/
def fieldPowBits {F : Type} [FieldOps F] (x : F) : (bits n : Nat) → F
  | 0, _ => 1
  | bits + 1, n =>
    let half := fieldPowBits x bits (n / 2)
    if n % 2 = 0 then half * half else half * half * x

/-- `x ^ n`, by squaring. -/
def fieldPow {F : Type} [FieldOps F] (x : F) (n : Nat) : F :=
  fieldPowBits x (Nat.log2 n + 1) n


/-- The image in the field of a natural number below `2 ^ bits`, by doubling:
`n = 2 * (n / 2) + n % 2`. -/
def fieldOfNatBits {F : Type} [FieldOps F] : (bits n : Nat) → F
  | 0, _ => 0
  | bits + 1, n =>
    let half := fieldOfNatBits bits (n / 2)
    if n % 2 = 0 then half + half else half + half + 1

/-- The image of a natural number in the field: `1 + ⋯ + 1`, `n` times
(Plonky3's `from_usize`). -/
def fieldOfNat {F : Type} [FieldOps F] (n : Nat) : F :=
  fieldOfNatBits (Nat.log2 n + 1) n

/-- `x ^ (2 ^ k)`, by squaring `k` times (Plonky3's `exp_power_of_2`). -/
def fieldPowTwo {F : Type} [FieldOps F] (x : F) : (k : Nat) → F
  | 0 => x
  | k + 1 =>
    let y := fieldPowTwo x k
    y * y

end CertiFri
