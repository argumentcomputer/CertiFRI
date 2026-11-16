/-!
# Executable field interfaces

The verifier is generic over the base field `F` and the extension field `EF`
its challenges live in. These classes carry operations only. They state no
laws: a law about machine arithmetic is a theorem, and theorems about field
structure need Mathlib. The proofs package relates an instance to a
mathematical field through an abstraction map (`CertiFri.Refines`). A concrete
instance must supply proofs that its operations and equality test refine the
model; no concrete machine-field instance is certified here yet.
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

end CertiFri
