import CertiFri.Field

/-!
# Quartic binomial extensions

Plonky3's `BinomialExtensionField<F, 4>`: the ring `F[X] / (X^4 - W)` for a
base field `F` and a constant `W` of it
(`field/src/extension/binomial_extension.rs`), with the instances the verifier
is written against: `FieldOps` and `ExtensionOps F (Quartic F)`. It is a field
when `X^4 - W` is irreducible; the constant is a parameter of the base field
(`QuarticParams`), as Plonky3's `BinomiallyExtendable<4>::W`.

An element is `c0 + c1 * X + c2 * X^2 + c3 * X^3`. The basis is
`(1, X, X^2, X^3)`, in the order of Plonky3's `as_basis_coefficients_slice`.

The inverse follows Plonky3's `quartic_inv`. With `Y = X^2`, the product of
`a` and its conjugate `a' = c0 - c1 * X + c2 * X^2 - c3 * X^3` lies in
`F[Y] / (Y^2 - W)`, where an inverse is the conjugate divided by the norm.

Nothing is proved in this package. That the operations are those of the field
`F[X] / (X^4 - W)` is proved in the proofs package
(`Proofs/CertiFriProofs/P3/QuarticLaws.lean`).

Not covered: the Frobenius map, and the two-adic structure of the extension,
which the verifier does not use.
-/

namespace CertiFri.P3

/-- The constant `W` of the quartic extension `F[X] / (X^4 - W)` of `F`. -/
class QuarticParams (F : Type) where
  /-- The fourth power of the adjoined element `X`. -/
  nonResidue : F

/-- An element `c0 + c1 * X + c2 * X^2 + c3 * X^3` of `F[X] / (X^4 - W)`. -/
structure Quartic (F : Type) where
  /-- The coordinate of `1`. -/
  c0 : F
  /-- The coordinate of `X`. -/
  c1 : F
  /-- The coordinate of `X^2`. -/
  c2 : F
  /-- The coordinate of `X^3`. -/
  c3 : F
  deriving DecidableEq, Repr, Inhabited

namespace Quartic

variable {F : Type} [FieldOps F] [QuarticParams F]

/-- The zero of the field. -/
protected def zero : Quartic F := ⟨0, 0, 0, 0⟩

/-- The one of the field. -/
protected def one : Quartic F := ⟨1, 0, 0, 0⟩

/-- Sum, coordinate by coordinate. -/
protected def add (a b : Quartic F) : Quartic F :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3⟩

/-- Difference, coordinate by coordinate. -/
protected def sub (a b : Quartic F) : Quartic F :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3⟩

/-- Opposite, coordinate by coordinate. -/
protected def neg (a : Quartic F) : Quartic F :=
  ⟨-a.c0, -a.c1, -a.c2, -a.c3⟩

/-- Product: the product of the two polynomials, with `X^4` replaced by `W`. -/
protected def mul (a b : Quartic F) : Quartic F :=
  let w : F := QuarticParams.nonResidue
  ⟨a.c0 * b.c0 + w * (a.c1 * b.c3 + a.c2 * b.c2 + a.c3 * b.c1),
    a.c0 * b.c1 + a.c1 * b.c0 + w * (a.c2 * b.c3 + a.c3 * b.c2),
    a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 + w * (a.c3 * b.c3),
    a.c0 * b.c3 + a.c1 * b.c2 + a.c2 * b.c1 + a.c3 * b.c0⟩

/-- Inverse, with the inverse of zero being zero. With `Y = X^2`, the product
of `a` and its conjugate `c0 - c1 * X + c2 * X^2 - c3 * X^3` is `n0 + n1 * Y`,
whose inverse is `(n0 - n1 * Y) / (n0^2 - W * n1^2)`; the inverse of `a` is the
conjugate times that. -/
protected def inv (a : Quartic F) : Quartic F :=
  let w : F := QuarticParams.nonResidue
  let n0 := a.c0 * a.c0 + w * (a.c2 * a.c2) - w * (a.c1 * a.c3 + a.c1 * a.c3)
  let n1 := a.c0 * a.c2 + a.c0 * a.c2 - a.c1 * a.c1 - w * (a.c3 * a.c3)
  let scalar := (n0 * n0 - w * (n1 * n1))⁻¹
  let i0 := n0 * scalar
  let i1 := -(n1 * scalar)
  ⟨a.c0 * i0 + w * (a.c2 * i1),
    -(a.c1 * i0) - w * (a.c3 * i1),
    a.c2 * i0 + a.c0 * i1,
    -(a.c3 * i0) - a.c1 * i1⟩

/-- Equality, coordinate by coordinate. -/
protected def beq (a b : Quartic F) : Bool :=
  a.c0 == b.c0 && a.c1 == b.c1 && a.c2 == b.c2 && a.c3 == b.c3

instance : FieldOps (Quartic F) where
  zero := Quartic.zero
  one := Quartic.one
  add := Quartic.add
  sub := Quartic.sub
  mul := Quartic.mul
  neg := Quartic.neg
  inv := Quartic.inv
  beq := Quartic.beq

/-- The embedding of the base field. -/
def embed (a : F) : Quartic F :=
  ⟨a, 0, 0, 0⟩

/-- The coordinates `c0, c1, c2, c3`, in the order of Plonky3's
`as_basis_coefficients_slice`. -/
def toBasis (a : Quartic F) : Array F :=
  #[a.c0, a.c1, a.c2, a.c3]

/-- The element with coordinates `coords[0], …, coords[3]`. A missing
coordinate is zero and coordinates past the fourth are ignored. -/
def ofBasis (coords : Array F) : Quartic F :=
  ⟨coords[0]?.getD 0, coords[1]?.getD 0, coords[2]?.getD 0, coords[3]?.getD 0⟩

instance : ExtensionOps F (Quartic F) where
  degree := 4
  embed := embed
  toBasis := toBasis
  ofBasis := ofBasis

end Quartic

end CertiFri.P3
