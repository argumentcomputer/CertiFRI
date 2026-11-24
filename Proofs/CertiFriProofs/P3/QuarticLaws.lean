import Mathlib
import CertiFriP3.Quartic
import CertiFriProofs.P3.Model

/-!
# The quartic extensions are fields

`Quartic F` (`CertiFriP3/Quartic.lean`) is `F[X] / (X^4 - W)` in coordinates.
When `F` implements a prime field and `X^4 - W` is irreducible over it,
`Quartic F` implements the binomial extension `(ZMod p)[X] / (X^4 - w)` in the
sense of `BinomialRep`, where `w` is the value of `W`.

## Contents

* `Quartic.coord`: the coordinates of an element.
* `Quartic.binomialRep`: the `BinomialRep`, whose abstraction map is
  `c0 + c1 * X + c2 * X^2 + c3 * X^3` on the values of the coordinates.

The identities behind the product and the inverse of the code are proved
first, in any commutative ring with a root of `X^4 - ω`.

## Assumptions

`F` is a `PrimeRep` for a prime `p`, and `X^4 - w` is irreducible over
`ZMod p`. The inverse of the code divides by the norm of the element, which is
not zero for an element other than zero because the model is a field.
-/

open Polynomial

namespace CertiFri.P3.Quartic

variable {F : Type} [FieldOps F] [QuarticParams F] {p : ℕ} [Fact p.Prime]

/-- The coordinates of an element; zero from the fourth on. -/
def coord (x : Quartic F) (i : ℕ) : F :=
  match i with
  | 0 => x.c0
  | 1 => x.c1
  | 2 => x.c2
  | 3 => x.c3
  | _ => 0

/-! ## Identities in a ring with a root of `X^4 - ω` -/

section Algebra

variable {A : Type} [CommRing A] {r ω : A}

/-- The product of the code is the product of the polynomials in a root `r` of
`X^4 - ω`. -/
private theorem mul_identity (hr : r ^ 4 = ω) (a0 a1 a2 a3 b0 b1 b2 b3 : A) :
    a0 * b0 + ω * (a1 * b3 + a2 * b2 + a3 * b1)
        + (a0 * b1 + a1 * b0 + ω * (a2 * b3 + a3 * b2)) * r
        + (a0 * b2 + a1 * b1 + a2 * b0 + ω * (a3 * b3)) * r ^ 2
        + (a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0) * r ^ 3 =
      (a0 + a1 * r + a2 * r ^ 2 + a3 * r ^ 3) * (b0 + b1 * r + b2 * r ^ 2 + b3 * r ^ 3) := by
  linear_combination
    (-(a1 * b3 + a2 * b2 + a3 * b1) - (a2 * b3 + a3 * b2) * r - a3 * b3 * r ^ 2) * hr

/-- The product of an element and its conjugate `a0 - a1 * r + a2 * r^2 - a3 * r^3`
is `n0 + n1 * r^2`, with `n0` and `n1` as the code computes them. -/
private theorem conj_identity (hr : r ^ 4 = ω) (a0 a1 a2 a3 : A) :
    (a0 + a1 * r + a2 * r ^ 2 + a3 * r ^ 3) * (a0 - a1 * r + a2 * r ^ 2 - a3 * r ^ 3) =
      a0 * a0 + ω * (a2 * a2) - ω * (a1 * a3 + a1 * a3)
        + (a0 * a2 + a0 * a2 - a1 * a1 - ω * (a3 * a3)) * r ^ 2 := by
  linear_combination (a2 * a2 - 2 * a1 * a3 - a3 * a3 * r ^ 2) * hr

/-- The product of `n0 + n1 * r^2` and its conjugate `n0 - n1 * r^2` is the norm
`n0^2 - ω * n1^2`. -/
private theorem norm_identity (hr : r ^ 4 = ω) (n0 n1 : A) :
    (n0 + n1 * r ^ 2) * (n0 - n1 * r ^ 2) = n0 * n0 - ω * (n1 * n1) := by
  linear_combination (-(n1 * n1)) * hr

/-- The inverse of the code, with the scalar `s` it multiplies by, is the
conjugate times `n0 - n1 * r^2` times `s`. -/
private theorem inv_identity (hr : r ^ 4 = ω) (a0 a1 a2 a3 n0 n1 s : A) :
    a0 * (n0 * s) + ω * (a2 * -(n1 * s)) + (-(a1 * (n0 * s)) - ω * (a3 * -(n1 * s))) * r
        + (a2 * (n0 * s) + a0 * -(n1 * s)) * r ^ 2
        + (-(a3 * (n0 * s)) - a1 * -(n1 * s)) * r ^ 3 =
      (a0 - a1 * r + a2 * r ^ 2 - a3 * r ^ 3) * (n0 - n1 * r ^ 2) * s := by
  linear_combination (a2 * n1 * s - a3 * n1 * s * r) * hr

end Algebra

/-! ## The base field and the binomial field -/

section Base

omit [QuarticParams F]

variable (R : PrimeRep F p) (w : ZMod p) [Fact (Irreducible (X ^ 4 - C w : (ZMod p)[X]))]

/-- The value of zero. -/
private theorem toZMod_zero : R.toZMod (0 : F) = 0 :=
  R.refines.map_zero

/-- The value of one. -/
private theorem toZMod_one : R.toZMod (1 : F) = 1 :=
  R.refines.map_one

/-- The value of a sum. -/
private theorem toZMod_add (a b : F) : R.toZMod (a + b) = R.toZMod a + R.toZMod b :=
  R.refines.map_add a b

/-- The value of a difference. -/
private theorem toZMod_sub (a b : F) : R.toZMod (a - b) = R.toZMod a - R.toZMod b :=
  R.refines.map_sub a b

/-- The value of a product. -/
private theorem toZMod_mul (a b : F) : R.toZMod (a * b) = R.toZMod a * R.toZMod b :=
  R.refines.map_mul a b

/-- The value of an opposite. -/
private theorem toZMod_neg (a : F) : R.toZMod (-a) = -R.toZMod a :=
  R.refines.map_neg a

/-- The value of an inverse. -/
private theorem toZMod_inv (a : F) : R.toZMod a⁻¹ = (R.toZMod a)⁻¹ :=
  R.refines.map_inv a

/-- The value of an element in the binomial field: the abstraction map of
`binomialRep`. -/
private noncomputable def value (x : Quartic F) : Binomial (ZMod p) 4 w :=
  Binomial.ofCoords fun i => R.toZMod (coord x i)

/-- The value of an element is `c0 + c1 * X + c2 * X^2 + c3 * X^3`. -/
private theorem value_eq (x : Quartic F) :
    value R w x = Binomial.of (R.toZMod x.c0) + Binomial.of (R.toZMod x.c1) * Binomial.root
      + Binomial.of (R.toZMod x.c2) * Binomial.root ^ 2
      + Binomial.of (R.toZMod x.c3) * Binomial.root ^ 3 := by
  simp [value, Binomial.ofCoords, Finset.sum_range_succ, coord]

/-- A combination of `1, X, X^2, X^3` that is zero has coefficients zero. -/
private theorem eq_zero_of_combination (c0 c1 c2 c3 : ZMod p)
    (h : (Binomial.of c0 + Binomial.of c1 * Binomial.root + Binomial.of c2 * Binomial.root ^ 2
      + Binomial.of c3 * Binomial.root ^ 3 : Binomial (ZMod p) 4 w) = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 := by
  have key : (Binomial.ofCoords (fun i =>
      if i = 0 then c0 else if i = 1 then c1 else if i = 2 then c2 else c3) :
      Binomial (ZMod p) 4 w) = Binomial.ofCoords fun _ => 0 := by
    simp [Binomial.ofCoords, Finset.sum_range_succ, h]
  rw [Binomial.ofCoords_eq_iff] at key
  exact ⟨by simpa using key 0 (by norm_num), by simpa using key 1 (by norm_num),
    by simpa using key 2 (by norm_num), by simpa using key 3 (by norm_num)⟩

/-- The inverse of the code, on values, is the inverse of the binomial field.
`n0 + n1 * X^2` is the product of the element and its conjugate, and `s` the
inverse of its norm `n0^2 - w * n1^2`, which is not zero for an element other
than zero. -/
private theorem inv_eq (a0 a1 a2 a3 n0 n1 s : ZMod p)
    (hn0 : n0 = a0 * a0 + w * (a2 * a2) - w * (a1 * a3 + a1 * a3))
    (hn1 : n1 = a0 * a2 + a0 * a2 - a1 * a1 - w * (a3 * a3))
    (hs : s = (n0 * n0 - w * (n1 * n1))⁻¹) :
    (Binomial.of (a0 * (n0 * s) + w * (a2 * -(n1 * s)))
        + Binomial.of (-(a1 * (n0 * s)) - w * (a3 * -(n1 * s))) * Binomial.root
        + Binomial.of (a2 * (n0 * s) + a0 * -(n1 * s)) * Binomial.root ^ 2
        + Binomial.of (-(a3 * (n0 * s)) - a1 * -(n1 * s)) * Binomial.root ^ 3 :
        Binomial (ZMod p) 4 w) =
      (Binomial.of a0 + Binomial.of a1 * Binomial.root + Binomial.of a2 * Binomial.root ^ 2
        + Binomial.of a3 * Binomial.root ^ 3)⁻¹ := by
  have hr : (Binomial.root : Binomial (ZMod p) 4 w) ^ 4 = Binomial.of w := Binomial.root_pow
  have hinv := inv_identity hr (Binomial.of a0) (Binomial.of a1) (Binomial.of a2)
    (Binomial.of a3) (Binomial.of n0) (Binomial.of n1) (Binomial.of s)
  have hconj := conj_identity hr (Binomial.of a0) (Binomial.of a1) (Binomial.of a2)
    (Binomial.of a3)
  have hnorm := norm_identity hr (Binomial.of n0) (Binomial.of n1)
  simp only [← map_mul, ← map_add, ← map_sub, ← map_neg, ← hn0, ← hn1] at hinv hconj hnorm
  rw [hinv]
  by_cases hx : (Binomial.of a0 + Binomial.of a1 * Binomial.root
      + Binomial.of a2 * Binomial.root ^ 2 + Binomial.of a3 * Binomial.root ^ 3 :
      Binomial (ZMod p) 4 w) = 0
  · obtain ⟨h0, h1, h2, h3⟩ := eq_zero_of_combination w a0 a1 a2 a3 hx
    rw [hx, inv_zero, h0, h1, h2, h3]
    simp
  · have hN : n0 * n0 - w * (n1 * n1) ≠ 0 := by
      intro hN
      rw [hN, map_zero] at hnorm
      have hc : (Binomial.of a0 - Binomial.of a1 * Binomial.root
          + Binomial.of a2 * Binomial.root ^ 2 - Binomial.of a3 * Binomial.root ^ 3 :
          Binomial (ZMod p) 4 w) ≠ 0 := by
        intro hc
        obtain ⟨h0, h1, h2, h3⟩ := eq_zero_of_combination w a0 (-a1) a2 (-a3)
          (by simpa [sub_eq_add_neg] using hc)
        apply hx
        rw [h0, neg_eq_zero.1 h1, h2, neg_eq_zero.1 h3]
        simp
      have hsum : (Binomial.of n0 + Binomial.of n1 * Binomial.root ^ 2 :
          Binomial (ZMod p) 4 w) ≠ 0 := by
        rw [← hconj]
        exact mul_ne_zero hx hc
      rcases mul_eq_zero.1 hnorm with h | h
      · exact hsum h
      · obtain ⟨h0, -, h2, -⟩ := eq_zero_of_combination w n0 0 (-n1) 0
          (by simpa [sub_eq_add_neg] using h)
        apply hsum
        rw [h0, neg_eq_zero.1 h2]
        simp
    apply eq_inv_of_mul_eq_one_right
    rw [← mul_assoc, ← mul_assoc, hconj, hnorm, ← map_mul, hs, mul_inv_cancel₀ hN, map_one]

end Base

/-! ## The operations of the code, on values -/

section Model

variable (R : PrimeRep F p) (w : ZMod p) [Fact (Irreducible (X ^ 4 - C w : (ZMod p)[X]))]

/-- The value of zero is zero. -/
private theorem value_zero : value R w 0 = 0 := by
  rw [value_eq]
  show Binomial.of (R.toZMod 0) + Binomial.of (R.toZMod 0) * Binomial.root
    + Binomial.of (R.toZMod 0) * Binomial.root ^ 2
    + Binomial.of (R.toZMod 0) * Binomial.root ^ 3 = 0
  simp [toZMod_zero]

/-- The value of one is one. -/
private theorem value_one : value R w 1 = 1 := by
  rw [value_eq]
  show Binomial.of (R.toZMod 1) + Binomial.of (R.toZMod 0) * Binomial.root
    + Binomial.of (R.toZMod 0) * Binomial.root ^ 2
    + Binomial.of (R.toZMod 0) * Binomial.root ^ 3 = 1
  simp [toZMod_zero, toZMod_one]

/-- The value of a sum is the sum of the values. -/
private theorem value_add (a b : Quartic F) :
    value R w (a + b) = value R w a + value R w b := by
  rw [value_eq, value_eq, value_eq]
  show Binomial.of (R.toZMod (a.c0 + b.c0))
    + Binomial.of (R.toZMod (a.c1 + b.c1)) * Binomial.root
    + Binomial.of (R.toZMod (a.c2 + b.c2)) * Binomial.root ^ 2
    + Binomial.of (R.toZMod (a.c3 + b.c3)) * Binomial.root ^ 3 = _
  simp only [toZMod_add, map_add]
  ring

/-- The value of a difference is the difference of the values. -/
private theorem value_sub (a b : Quartic F) :
    value R w (a - b) = value R w a - value R w b := by
  rw [value_eq, value_eq, value_eq]
  show Binomial.of (R.toZMod (a.c0 - b.c0))
    + Binomial.of (R.toZMod (a.c1 - b.c1)) * Binomial.root
    + Binomial.of (R.toZMod (a.c2 - b.c2)) * Binomial.root ^ 2
    + Binomial.of (R.toZMod (a.c3 - b.c3)) * Binomial.root ^ 3 = _
  simp only [toZMod_sub, map_sub]
  ring

/-- The value of an opposite is the opposite of the value. -/
private theorem value_neg (a : Quartic F) : value R w (-a) = -value R w a := by
  rw [value_eq, value_eq]
  show Binomial.of (R.toZMod (-a.c0)) + Binomial.of (R.toZMod (-a.c1)) * Binomial.root
    + Binomial.of (R.toZMod (-a.c2)) * Binomial.root ^ 2
    + Binomial.of (R.toZMod (-a.c3)) * Binomial.root ^ 3 = _
  simp only [toZMod_neg, map_neg]
  ring

/-- The equality test decides equality of the values. -/
private theorem value_beq (a b : Quartic F) :
    (a == b) = true ↔ value R w a = value R w b := by
  rw [value, value, Binomial.ofCoords_eq_iff]
  show (a.c0 == b.c0 && a.c1 == b.c1 && a.c2 == b.c2 && a.c3 == b.c3) = true ↔ _
  simp only [Bool.and_eq_true, R.beq]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ i hi
    interval_cases i
    · exact congrArg R.toZMod h0
    · exact congrArg R.toZMod h1
    · exact congrArg R.toZMod h2
    · exact congrArg R.toZMod h3
  · intro h
    exact ⟨⟨⟨R.toZMod_injective (h 0 (by norm_num)), R.toZMod_injective (h 1 (by norm_num))⟩,
      R.toZMod_injective (h 2 (by norm_num))⟩, R.toZMod_injective (h 3 (by norm_num))⟩

variable {w}

/-- The value of a product is the product of the values. -/
private theorem value_mul (hw : R.toZMod (QuarticParams.nonResidue : F) = w) (a b : Quartic F) :
    value R w (a * b) = value R w a * value R w b := by
  rw [value_eq, value_eq, value_eq, ← mul_identity Binomial.root_pow]
  show Binomial.of (R.toZMod (Quartic.mul a b).c0)
    + Binomial.of (R.toZMod (Quartic.mul a b).c1) * Binomial.root
    + Binomial.of (R.toZMod (Quartic.mul a b).c2) * Binomial.root ^ 2
    + Binomial.of (R.toZMod (Quartic.mul a b).c3) * Binomial.root ^ 3 = _
  simp only [Quartic.mul, toZMod_add, toZMod_mul, hw, map_add, map_mul]

/-- The value of an inverse is the inverse of the value. -/
private theorem value_inv (hw : R.toZMod (QuarticParams.nonResidue : F) = w) (a : Quartic F) :
    value R w a⁻¹ = (value R w a)⁻¹ := by
  rw [value_eq, value_eq]
  show Binomial.of (R.toZMod (Quartic.inv a).c0)
    + Binomial.of (R.toZMod (Quartic.inv a).c1) * Binomial.root
    + Binomial.of (R.toZMod (Quartic.inv a).c2) * Binomial.root ^ 2
    + Binomial.of (R.toZMod (Quartic.inv a).c3) * Binomial.root ^ 3 = _
  simp only [Quartic.inv, toZMod_add, toZMod_sub, toZMod_mul, toZMod_neg, toZMod_inv, hw]
  exact inv_eq w _ _ _ _ _ _ _ rfl rfl rfl

end Model

/-- **The quartic extension implements the binomial field.** `w` is the value
of the constant `W` of the code. -/
noncomputable def binomialRep (R : PrimeRep F p) (w : ZMod p)
    (hw : R.toZMod (QuarticParams.nonResidue : F) = w)
    [Fact (Irreducible (X ^ 4 - C w : (ZMod p)[X]))] :
    BinomialRep F (Quartic F) R 4 w where
  coord := coord
  ext :=
    { toModel := fun x => Binomial.ofCoords fun i => R.toZMod (coord x i)
      map_zero := value_zero R w
      map_one := value_one R w
      map_add := value_add R w
      map_sub := value_sub R w
      map_mul := value_mul R hw
      map_neg := value_neg R w
      map_inv := value_inv R hw
      beq_iff := value_beq R w }
  toModel_eq := fun _ => rfl
  surj := fun c => ⟨⟨c 0, c 1, c 2, c 3⟩, fun i hi => by interval_cases i <;> rfl⟩
  degree_eq := rfl
  embed := fun a i hi => by interval_cases i <;> rfl
  toBasis_size := fun _ => rfl
  toBasis := fun x i hi => by interval_cases i <;> rfl
  ofBasis := fun a _ i hi => by
    interval_cases i <;> exact (Array.getD_eq_getD_getElem? ..).symm

end CertiFri.P3.Quartic
