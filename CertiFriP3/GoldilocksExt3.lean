import CertiFriP3.Goldilocks

/-!
# The cubic trinomial extension of Goldilocks (`X^3 - X - 1`)

Stock Plonky3's `CubicTrinomialExtensionField<Goldilocks>`: the cubic extension
`Goldilocks[X] / (X^3 - X - 1)` of order `p^3 = (2^64 - 2^32 + 1)^3 ≈ 2^192`,
together with the `FieldOps` and `ExtensionOps Goldilocks GoldilocksExt3`
instances required by `CertiFri.Fri.verify`.

An element is `c0 + c1 * X + c2 * X^2` in the basis `(1, X, X^2)`, matching
Plonky3's `as_basis_coefficients_slice` order. Since `X^3 = X + 1` and
`X^4 = X^2 + X`:

* **Multiplication** uses Karatsuba with 6 base-field multiplications and zero
  non-residue multiplications.
* **Inversion** computes the exact adjugate and norm of the `3 × 3`
  multiplication matrix (`GoldilocksExt3.inv?`), failing closed with `none`
  when `norm a = 0` (which occurs iff `a = 0`, proved in
  `Proofs/CertiFriProofs/P3/GoldilocksExt3.lean` from the irreducibility of
  `X^3 - X - 1` over `GF(p)`). `FieldOps.inv` maps `0` to `0` as required by
  `CertiFri.Refines`.
* **Serialization** emits `c0`, `c1`, `c2` as 24 little-endian bytes (`pushBytes`)
  and deserializes strictly canonically (`ofCanonical?`, rejecting any word `≥ p`).

The irreducibility of `X^3 - X - 1`, the `Field` instance, `Refines`,
`Exec.FieldModel`, `Exec.WellFormed`, and the unconditional executable verifier
soundness theorem over `GoldilocksExt3` are proved in
`Proofs/CertiFriProofs/P3/GoldilocksExt3.lean`.
-/

namespace CertiFri.P3

/-- An element `c0 + c1 * X + c2 * X^2` of the cubic trinomial extension
`Goldilocks[X] / (X^3 - X - 1)`. -/
structure GoldilocksExt3 where
  /-- The coordinate of `1`. -/
  c0 : Goldilocks
  /-- The coordinate of `X`. -/
  c1 : Goldilocks
  /-- The coordinate of `X^2`. -/
  c2 : Goldilocks
  deriving DecidableEq, Repr, Inhabited

namespace GoldilocksExt3

/-- The zero of the field. -/
protected def zero : GoldilocksExt3 :=
  ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

/-- The one of the field. -/
protected def one : GoldilocksExt3 :=
  ⟨Goldilocks.one, Goldilocks.zero, Goldilocks.zero⟩

/-- Sum, coordinate by coordinate. -/
protected def add (a b : GoldilocksExt3) : GoldilocksExt3 :=
  ⟨a.c0.add b.c0, a.c1.add b.c1, a.c2.add b.c2⟩

/-- Difference, coordinate by coordinate. -/
protected def sub (a b : GoldilocksExt3) : GoldilocksExt3 :=
  ⟨a.c0.sub b.c0, a.c1.sub b.c1, a.c2.sub b.c2⟩

/-- Opposite, coordinate by coordinate. -/
protected def neg (a : GoldilocksExt3) : GoldilocksExt3 :=
  ⟨a.c0.neg, a.c1.neg, a.c2.neg⟩

/-- Karatsuba product modulo `X^3 - X - 1` (6 base multiplications, 0
non-residue multiplications).

Using `X^3 = X + 1` and `X^4 = X^2 + X`:
* `c0 = a0*b0 + (a1*b2 + a2*b1)`
* `c1 = (a0*b1 + a1*b0) + (a1*b2 + a2*b1) + a2*b2`
* `c2 = (a0*b2 + a2*b0) + a1*b1 + a2*b2` -/
protected def mul (a b : GoldilocksExt3) : GoldilocksExt3 :=
  let p0 := a.c0.mul b.c0
  let p1 := a.c1.mul b.c1
  let p2 := a.c2.mul b.c2
  let p01 := ((a.c0.add a.c1).mul (b.c0.add b.c1)).sub (p0.add p1)
  let p02 := ((a.c0.add a.c2).mul (b.c0.add b.c2)).sub (p0.add p2)
  let p12 := ((a.c1.add a.c2).mul (b.c1.add b.c2)).sub (p1.add p2)
  ⟨p0.add p12, (p01.add p12).add p2, (p02.add p1).add p2⟩

/-- First column of the adjugate of the `3 × 3` multiplication matrix
`M_a = [[a0, a2, a1], [a1, a0 + a2, a1 + a2], [a2, a1, a0 + a2]]`, satisfying
`a * adjugate a = embed (norm a)`. -/
def adjugate (a : GoldilocksExt3) : GoldilocksExt3 :=
  let a02 := a.c0.add a.c2
  let s0 := (a02.mul a02).sub (a.c1.mul (a.c1.add a.c2))
  let s1 := (a.c2.mul a.c2).sub (a.c0.mul a.c1)
  let s2 := (a.c1.mul a.c1).sub (a.c2.mul a02)
  ⟨s0, s1, s2⟩

/-- Field norm `N(a) = det M_a = a0*s0 + a2*s1 + a1*s2`. -/
def norm (a : GoldilocksExt3) : Goldilocks :=
  let adj := adjugate a
  ((a.c0.mul adj.c0).add (a.c2.mul adj.c1)).add (a.c1.mul adj.c2)

/-- Exact inverse via the adjugate and norm, failing closed with `none` when
`norm a = 0` (i.e. `a = 0`). -/
def inv? (a : GoldilocksExt3) : Option GoldilocksExt3 :=
  let adj := adjugate a
  let n := ((a.c0.mul adj.c0).add (a.c2.mul adj.c1)).add (a.c1.mul adj.c2)
  if n == Goldilocks.zero then
    none
  else
    let invN := n.inv
    some ⟨adj.c0.mul invN, adj.c1.mul invN, adj.c2.mul invN⟩

/-- Inverse, mapping zero to zero (`(inv? a).getD 0`). -/
protected def inv (a : GoldilocksExt3) : GoldilocksExt3 :=
  (inv? a).getD GoldilocksExt3.zero

/-- Append the 24 canonical little-endian bytes of the element: `c0`, `c1`,
`c2` in order. -/
def pushBytes (bytes : ByteArray) (a : GoldilocksExt3) : ByteArray :=
  a.c2.pushBytes (a.c1.pushBytes (a.c0.pushBytes bytes))

/-- Deserialize from three canonical `UInt64` words, rejecting any word `≥ p`. -/
def ofCanonical? (w0 w1 w2 : UInt64) : Option GoldilocksExt3 :=
  match Goldilocks.ofCanonical? w0, Goldilocks.ofCanonical? w1, Goldilocks.ofCanonical? w2 with
  | some c0, some c1, some c2 => some ⟨c0, c1, c2⟩
  | _, _, _ => none

/-- Deserialize from 24 canonical little-endian bytes at byte offset `off`,
failing closed if fewer than 24 bytes remain or any word is `≥ p`. -/
def ofBytesAt? (bytes : ByteArray) (off : Nat) : Option GoldilocksExt3 :=
  if off + 24 ≤ bytes.size then
    let word64 (base : Nat) : UInt64 :=
      let b (k : Nat) : UInt64 := (bytes.get! (base + k)).toUInt64
      b 0 ||| (b 1 <<< 8) ||| (b 2 <<< 16) ||| (b 3 <<< 24) |||
        (b 4 <<< 32) ||| (b 5 <<< 40) ||| (b 6 <<< 48) ||| (b 7 <<< 56)
    ofCanonical? (word64 off) (word64 (off + 8)) (word64 (off + 16))
  else
    none

instance : FieldOps GoldilocksExt3 where
  zero := GoldilocksExt3.zero
  one := GoldilocksExt3.one
  add := GoldilocksExt3.add
  sub := GoldilocksExt3.sub
  mul := GoldilocksExt3.mul
  neg := GoldilocksExt3.neg
  inv := GoldilocksExt3.inv
  beq a b := decide (a = b)

/-- The embedding of the base field into the cubic extension. -/
def embed (a : Goldilocks) : GoldilocksExt3 :=
  ⟨a, Goldilocks.zero, Goldilocks.zero⟩

/-- The coordinates `c0, c1, c2`, in Plonky3's `as_basis_coefficients_slice`
order. -/
def toBasis (a : GoldilocksExt3) : Array Goldilocks :=
  #[a.c0, a.c1, a.c2]

/-- The element with coordinates `coords[0], coords[1], coords[2]`. Missing
coordinates are zero and coordinates past the third are ignored. -/
def ofBasis (coords : Array Goldilocks) : GoldilocksExt3 :=
  ⟨coords[0]?.getD Goldilocks.zero, coords[1]?.getD Goldilocks.zero,
    coords[2]?.getD Goldilocks.zero⟩

instance : ExtensionOps Goldilocks GoldilocksExt3 where
  degree := 3
  embed := embed
  toBasis := toBasis
  ofBasis := ofBasis

end GoldilocksExt3

end CertiFri.P3
