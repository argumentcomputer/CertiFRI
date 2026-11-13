import Mathlib.Algebra.Field.Defs
import CertiFri.Field

/-!
# Refinement of executable fields

The executable verifier computes over a type `F` with operations and no laws.
A `Refines F K` relates it to a mathematical field `K` through an abstraction
map that carries each executable operation to the field operation. Every
theorem about the verifier is stated on the images under this map.

The map need not be injective: a field implementation may keep elements in a
redundant representation. Equality tests are what must agree with the model.
-/

namespace CertiFri

/-- `F` implements the field `K`. -/
structure Refines (F K : Type) [FieldOps F] [Field K] where
  /-- The mathematical value an executable value stands for. -/
  toModel : F → K
  map_zero : toModel 0 = 0
  map_one : toModel 1 = 1
  map_add : ∀ a b, toModel (a + b) = toModel a + toModel b
  map_sub : ∀ a b, toModel (a - b) = toModel a - toModel b
  map_mul : ∀ a b, toModel (a * b) = toModel a * toModel b
  map_neg : ∀ a, toModel (-a) = -toModel a
  map_inv : ∀ a, toModel a⁻¹ = (toModel a)⁻¹
  /-- The executable equality test decides equality of the modelled values. -/
  beq_iff : ∀ a b, (a == b) = true ↔ toModel a = toModel b

end CertiFri
