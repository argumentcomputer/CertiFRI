import CertiFriP3.Goldilocks

/-!
# The quadratic extension of Goldilocks

Plonky3's `BinomialExtensionField<Goldilocks, 2>`: the field
`Goldilocks[X] / (X^2 - 7)` (`field/src/extension/binomial_extension.rs`, with
the non-residue `W = 7` of `goldilocks/src/extension.rs`), and the instances
the verifier is written against: `FieldOps` and
`ExtensionOps Goldilocks GoldilocksExt`.

An element is `c0 + c1 * X`. The basis is `(1, X)`: `c0` is the coordinate
Plonky3's `as_basis_coefficients_slice` lists first.

Nothing is proved in this package. That `X^2 - 7` is irreducible and that the
operations are those of the field `Goldilocks[X] / (X^2 - 7)` is proved in the
proofs package (`Proofs/CertiFriProofs/P3/GoldilocksModel.lean`). The
operations are also tested against values computed by Plonky3
(`CertiFriTest/P3/GoldilocksExt.lean`).

Not covered: the other extensions of Goldilocks that Plonky3 defines, and the
two-adic structure of the extension, which the verifier does not use.
-/

namespace CertiFri.P3

/-- An element `c0 + c1 * X` of the quadratic extension `Goldilocks[X] / (X^2 - 7)`. -/
structure GoldilocksExt where
  /-- The coordinate of `1`. -/
  c0 : Goldilocks
  /-- The coordinate of `X`. -/
  c1 : Goldilocks
  deriving DecidableEq, Repr, Inhabited

namespace GoldilocksExt

/-- The non-residue `W = 7`: the square of `X`. -/
def nonResidue : Goldilocks := Goldilocks.ofUInt64 7

/-- The zero of the field. -/
protected def zero : GoldilocksExt := ⟨Goldilocks.zero, Goldilocks.zero⟩

/-- The one of the field. -/
protected def one : GoldilocksExt := ⟨Goldilocks.one, Goldilocks.zero⟩

/-- Sum, coordinate by coordinate. -/
protected def add (a b : GoldilocksExt) : GoldilocksExt :=
  ⟨a.c0.add b.c0, a.c1.add b.c1⟩

/-- Difference, coordinate by coordinate. -/
protected def sub (a b : GoldilocksExt) : GoldilocksExt :=
  ⟨a.c0.sub b.c0, a.c1.sub b.c1⟩

/-- Opposite, coordinate by coordinate. -/
protected def neg (a : GoldilocksExt) : GoldilocksExt :=
  ⟨a.c0.neg, a.c1.neg⟩

/-- Product: `(a0 + a1 X) (b0 + b1 X) = (a0 b0 + W a1 b1) + (a0 b1 + a1 b0) X`. -/
protected def mul (a b : GoldilocksExt) : GoldilocksExt :=
  ⟨(a.c0.mul b.c0).add (nonResidue.mul (a.c1.mul b.c1)),
    (a.c0.mul b.c1).add (a.c1.mul b.c0)⟩

/-- Inverse, with the inverse of zero being zero: the conjugate `a0 - a1 X`
divided by the norm `a0^2 - W a1^2`. The norm of a nonzero element is nonzero,
since `W` is not a square. -/
protected def inv (a : GoldilocksExt) : GoldilocksExt :=
  let scalar := ((a.c0.mul a.c0).sub (nonResidue.mul (a.c1.mul a.c1))).inv
  ⟨a.c0.mul scalar, (a.c1.mul scalar).neg⟩

instance : FieldOps GoldilocksExt where
  zero := GoldilocksExt.zero
  one := GoldilocksExt.one
  add := GoldilocksExt.add
  sub := GoldilocksExt.sub
  mul := GoldilocksExt.mul
  neg := GoldilocksExt.neg
  inv := GoldilocksExt.inv
  beq a b := decide (a = b)

/-- The embedding of the base field. -/
def embed (a : Goldilocks) : GoldilocksExt :=
  ⟨a, Goldilocks.zero⟩

/-- The coordinates `c0, c1`, in the order of Plonky3's
`as_basis_coefficients_slice`. -/
def toBasis (a : GoldilocksExt) : Array Goldilocks :=
  #[a.c0, a.c1]

/-- The element with coordinates `coords[0], coords[1]`. A missing coordinate
is zero and coordinates past the second are ignored. -/
def ofBasis (coords : Array Goldilocks) : GoldilocksExt :=
  ⟨coords[0]?.getD Goldilocks.zero, coords[1]?.getD Goldilocks.zero⟩

instance : ExtensionOps Goldilocks GoldilocksExt where
  degree := 2
  embed := embed
  toBasis := toBasis
  ofBasis := ofBasis

end GoldilocksExt

end CertiFri.P3
