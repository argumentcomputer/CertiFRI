import CertiFriProofs.Exec.Setup
import CertiFriProofs.Theory.Stark.Check
import CertiFri.Stark.Verifier

/-!
# The fields of the STARK verifier and their model

The STARK verifier (`CertiFri/Stark/Verifier.lean`) uses more of its two
executable fields than the opening proof does: the coordinates of an extension
element in the basis of the extension, and the generator of every trace
domain. `StarkModel` extends `FieldModel` (`Exec/Setup.lean`) with what the
security proof needs of them.

## Contents

* `StarkModel F EF K`: the executable fields implement the field `K`, with
  * an extension structure `extData` (`Theory/Stark/Check.lean`) whose degree
    is the executable one, and whose coordinates and basis are what `toBasis`
    and `ofBasis` compute;
  * the generator of order `2 ^ k` a primitive root of that order, for every
    `k` up to the two-adicity, the generators being compatible (the square of
    the generator of order `2 ^ (k + 1)` is the generator of order `2 ^ k`);
  * a coset shift that is not zero.
* `StarkModel.gen`, `StarkModel.shift`: the generators and the shift, in `K`.
* `StarkModel.wellFormed`: the conditions `WellFormed` of the opening proof,
  for any shape whose first domain exists in the field.

## Assumptions

These are laws of the field implementation, to be proved of a concrete one
(for Goldilocks and its quadratic extension they are not proved here).
Linear independence of the basis is not among them: the proofs use only that
an element is the combination of the basis with its coordinates.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri

/-- The executable fields `F` and `EF` implement the field `K`, with the
extension structure and the two-adic structure the STARK verifier uses. -/
structure StarkModel (F EF K : Type) [FieldOps F] [FieldOps EF] [TwoAdicOps F]
    [ExtensionOps F EF] [Field K] extends FieldModel F EF K where
  /-- The degree, a basis and the coordinates of the extension. -/
  extData : ExtData K
  /-- The degree is the executable one. -/
  degree_eq : extData.d = ExtensionOps.degree (F := F) (EF := EF)
  /-- `toBasis` returns one coordinate per basis element. -/
  toBasis_size : ∀ x : EF, (ExtensionOps.toBasis (F := F) x).size = extData.d
  /-- `toBasis` computes the coordinates. -/
  toBasis : ∀ (x : EF) (k : ℕ), k < extData.d →
    base.toModel ((ExtensionOps.toBasis x).getD k 0) = extData.coord (ext.toModel x) k
  /-- `ofBasis` combines the basis with the given coordinates. -/
  ofBasis : ∀ a : Array F, a.size = extData.d →
    ext.toModel (ExtensionOps.ofBasis a) =
      ∑ k ∈ Finset.range extData.d, base.toModel (a.getD k 0) * extData.basis k
  /-- The generator of order `2 ^ k` is a primitive root of that order. -/
  generator : ∀ k ≤ TwoAdicOps.twoAdicity (F := F),
    IsPrimitiveRoot (base.toModel (TwoAdicOps.twoAdicGenerator k)) (2 ^ k)
  /-- The generators are compatible. -/
  generator_sq : ∀ k < TwoAdicOps.twoAdicity (F := F),
    base.toModel (TwoAdicOps.twoAdicGenerator (k + 1)) ^ 2 =
      base.toModel (TwoAdicOps.twoAdicGenerator k)
  /-- The coset shift is not zero. -/
  shift_ne : base.toModel TwoAdicOps.cosetShift ≠ 0

namespace StarkModel

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (M : StarkModel F EF K)

/-- The generator of the subgroup of order `2 ^ k`, in `K`. -/
def gen (k : ℕ) : K := M.base.toModel (TwoAdicOps.twoAdicGenerator k)

/-- The coset shift, in `K`. -/
def shift : K := M.base.toModel TwoAdicOps.cosetShift

/-- The conditions of the opening proof on the two-adic structure, for a shape
whose first domain exists in the field. -/
theorem wellFormed (params : FriParams) (shape : ClaimShape)
    (h : logMaxHeight params.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F)) :
    WellFormed M.toFieldModel params shape :=
  ⟨M.generator _ h, M.shift_ne⟩

end StarkModel

end CertiFri.Exec.Stark
