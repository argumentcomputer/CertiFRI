import Mathlib
import CertiFriProofs.Theory.Stark.Check

/-!
# Binomial extensions

The field `k[X] / (X^d - w)`, for a field `k` and a constant `w` such that
`X^d - w` is irreducible. It is the model of the extension fields of
`CertiFriP3`: the quadratic extension of Goldilocks (`d = 2`, `w = 7`) and the
quartic extension of BabyBear (`d = 4`, `w = 11`).

## Contents

* `Binomial k d w`: the field, with `Binomial.of` the embedding of `k` and
  `Binomial.root` the class of `X`.
* `Binomial.ofCoords`, `Binomial.coords`: an element is `∑ i < d, c i * X^i`
  for exactly one choice of the coordinates `c i` with `i < d`.
* `Binomial.extData`: the degree, the basis `1, X, …, X^(d-1)` and the
  coordinates, as the STARK verifier's checks use them.
* `Binomial.card`: a finite `k` gives a field of `|k| ^ d` elements.
* `Binomial.irreducible_two`, `Binomial.irreducible_four`: `X^2 - w` is
  irreducible when `w` is not a square, and `X^4 - w` when neither `w` nor
  `-w` is.

## Assumptions

`X^d - w` is irreducible, as a `Fact`. The two criteria discharge it.
-/

open Polynomial

namespace CertiFri.P3

/-- The field `k[X] / (X^d - w)`. -/
def Binomial (k : Type) [Field k] (d : ℕ) (w : k) : Type :=
  AdjoinRoot (X ^ d - C w : k[X])

namespace Binomial

variable {k : Type} [Field k] {d : ℕ} {w : k}

/-- `X^2 - w` is irreducible when `w` is not a square. -/
theorem irreducible_two (hw : ¬ IsSquare w) : Irreducible (X ^ 2 - C w : k[X]) := by
  refine irreducible_of_degree_le_three_of_not_isRoot ?_ fun x hx => hw ⟨x, ?_⟩
  · rw [natDegree_X_pow_sub_C]
    decide
  · have h : x ^ 2 - w = 0 := by simpa using hx
    rw [← sq]
    exact (sub_eq_zero.mp h).symm

/-- `X^4 - w` is irreducible when neither `w` nor `-w` is a square. -/
theorem irreducible_four (hw : ¬ IsSquare w) (hw' : ¬ IsSquare (-w)) :
    Irreducible (X ^ 4 - C w : k[X]) := by
  refine X_pow_mul_sub_C_irreducible (n := 2) (m := 2) (irreducible_two hw) fun E _ _ x hx => ?_
  have hx' : IsIntegral k x := not_not.mp fun h => by
    simpa only [degree_zero, degree_X_pow_sub_C two_pos,
      WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dite_eq_right h))
  refine irreducible_two fun ⟨b, hb⟩ => hw' ⟨Algebra.norm k b, ?_⟩
  rw [← map_mul, ← hb, ← IntermediateField.adjoin.powerBasis_gen hx',
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  simp [IntermediateField.minpoly_gen, hx]

/-- The degree of an irreducible binomial is positive. -/
theorem degree_pos (h : Irreducible (X ^ d - C w : k[X])) : 0 < d := by
  refine Nat.pos_of_ne_zero fun hd => ?_
  subst hd
  rw [pow_zero, ← C_1, ← C_sub] at h
  exact not_irreducible_C _ h

/-- The polynomial `∑ i < d, c i * X^i`. -/
private noncomputable def poly (d : ℕ) (c : ℕ → k) : k[X] :=
  ∑ i ∈ Finset.range d, C (c i) * X ^ i

/-- The coefficients of `poly d c` are the `c i` below `d`, and zero from `d`. -/
private theorem coeff_poly (c : ℕ → k) (i : ℕ) :
    (poly d c).coeff i = if i < d then c i else 0 := by
  simp [poly]

/-- The degree of `poly d c` is below `d`. -/
private theorem degree_poly_lt (c : ℕ → k) : (poly d c).degree < d :=
  (degree_lt_iff_coeff_zero _ _).mpr fun i hi => by
    rw [coeff_poly, ite_eq_right (not_lt.mpr hi)]

/-- Two polynomials `poly d c` have the same class modulo `X^d - w` exactly
when their coefficients agree below `d`. -/
private theorem mk_poly_eq_iff (hd : 0 < d) (c c' : ℕ → k) :
    AdjoinRoot.mk (X ^ d - C w : k[X]) (poly d c) = AdjoinRoot.mk (X ^ d - C w) (poly d c') ↔
      ∀ i < d, c i = c' i := by
  rw [AdjoinRoot.mk_eq_mk]
  constructor
  · intro h i hi
    have hlt : (poly d c - poly d c').degree < (X ^ d - C w : k[X]).degree := by
      rw [degree_X_pow_sub_C hd]
      exact (degree_sub_le _ _).trans_lt (max_lt (degree_poly_lt c) (degree_poly_lt c'))
    have h0 := congrArg (fun f => f.coeff i) (eq_zero_of_dvd_of_degree_lt h hlt)
    simp only [coeff_sub, coeff_poly, ite_eq_left hi, coeff_zero] at h0
    exact sub_eq_zero.mp h0
  · intro h
    have hcc : poly d c = poly d c' :=
      Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]
    rw [hcc, sub_self]
    exact dvd_zero _

/-- Every class modulo `X^d - w` is the class of a polynomial `poly d c`: the
remainder of a representative in the division by `X^d - w`. -/
private theorem exists_mk_poly (hd : 0 < d) (y : AdjoinRoot (X ^ d - C w : k[X])) :
    ∃ c : ℕ → k, AdjoinRoot.mk (X ^ d - C w : k[X]) (poly d c) = y := by
  have hm : (X ^ d - C w : k[X]).Monic := monic_X_pow_sub_C w hd.ne'
  have h1 : (X ^ d - C w : k[X]) ≠ 1 := fun h => by
    have h' := congrArg natDegree h
    rw [natDegree_X_pow_sub_C, natDegree_one] at h'
    exact hd.ne' h'
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective y
  refine ⟨(f %ₘ (X ^ d - C w)).coeff, ?_⟩
  have hf : poly d (f %ₘ (X ^ d - C w)).coeff = f %ₘ (X ^ d - C w) := by
    refine (as_sum_range_C_mul_X_pow' _ ?_).symm
    have h := natDegree_modByMonic_lt f hm h1
    rwa [natDegree_X_pow_sub_C] at h
  rw [hf, AdjoinRoot.mk_eq_mk, modByMonic_eq_sub_mul_div, sub_sub_cancel_left, dvd_neg]
  exact dvd_mul_right _ _

variable [Fact (Irreducible (X ^ d - C w : k[X]))]

/-- The quotient by an irreducible polynomial is a field. -/
noncomputable instance instField : Field (Binomial k d w) :=
  inferInstanceAs (Field (AdjoinRoot (X ^ d - C w : k[X])))

/-- Equality in the field is decidable, classically. -/
noncomputable instance instDecidableEq : DecidableEq (Binomial k d w) :=
  Classical.decEq _

/-- The embedding of the base field. -/
noncomputable def of : k →+* Binomial k d w :=
  AdjoinRoot.of (X ^ d - C w : k[X])

/-- The class of `X`. -/
noncomputable def root : Binomial k d w :=
  AdjoinRoot.root (X ^ d - C w : k[X])

/-- The power `d` of the class of `X` is `w`. -/
theorem root_pow : (root : Binomial k d w) ^ d = of w := by
  have h := AdjoinRoot.eval₂_root (X ^ d - C w : k[X])
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The element `∑ i < d, c i * X^i`. -/
noncomputable def ofCoords (c : ℕ → k) : Binomial k d w :=
  ∑ i ∈ Finset.range d, of (c i) * root ^ i

/-- The combination `ofCoords c` is the class of the polynomial `poly d c`. -/
private theorem ofCoords_eq_mk (c : ℕ → k) :
    (ofCoords c : Binomial k d w) = AdjoinRoot.mk (X ^ d - C w : k[X]) (poly d c) := by
  rw [poly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
  rfl

/-- Two families of coordinates give the same element exactly when they agree
below `d`. -/
theorem ofCoords_eq_iff (c c' : ℕ → k) :
    (ofCoords c : Binomial k d w) = ofCoords c' ↔ ∀ i < d, c i = c' i := by
  rw [ofCoords_eq_mk, ofCoords_eq_mk]
  exact mk_poly_eq_iff (degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))) c c'

/-- Every element has coordinates. -/
theorem exists_ofCoords (y : Binomial k d w) : ∃ c : ℕ → k, ofCoords c = y := by
  obtain ⟨c, hc⟩ := exists_mk_poly (degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))) y
  exact ⟨c, (ofCoords_eq_mk c).trans hc⟩

/-- The coordinates of an element. -/
noncomputable def coords (y : Binomial k d w) : ℕ → k :=
  Classical.choose (exists_ofCoords y)

/-- An element is the combination of the powers of `X` with its coordinates. -/
theorem ofCoords_coords (y : Binomial k d w) : ofCoords (coords y) = y :=
  Classical.choose_spec (exists_ofCoords y)

/-- The coordinates of a combination, below `d`. -/
theorem coords_ofCoords (c : ℕ → k) (i : ℕ) (hi : i < d) :
    coords (ofCoords c : Binomial k d w) i = c i :=
  (ofCoords_eq_iff _ _).mp (ofCoords_coords (ofCoords c)) i hi

/-- The embedding of the base field, in coordinates. -/
theorem of_eq_ofCoords (a : k) :
    (of a : Binomial k d w) = ofCoords fun i => if i = 0 then a else 0 := by
  have hd := degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))
  rw [ofCoords, Finset.sum_eq_single 0, ite_eq_left rfl, pow_zero, mul_one]
  · intro i _ hi
    rw [ite_eq_right hi, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hd) h

/-- The extension structure the checks of the STARK verifier use: the degree
`d`, the basis `1, X, …, X^(d-1)` and the coordinates in it. -/
noncomputable def extData : CertiFri.Stark.Model.ExtData (Binomial k d w) where
  d := d
  basis := fun i => root ^ i
  coord := fun y i => of (coords y i)
  d_pos := degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))
  basis_zero := pow_zero _
  sum_coord := ofCoords_coords

/-- The extension of a finite field is finite. -/
instance instFinite [Finite k] : Finite (Binomial k d w) := by
  have hd := degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))
  have := (monic_X_pow_sub_C w hd.ne').finite_adjoinRoot
  exact Module.finite_of_finite k (M := AdjoinRoot (X ^ d - C w : k[X]))

/-- The extension of a finite field, as a finite type. -/
noncomputable instance instFintype [Finite k] : Fintype (Binomial k d w) :=
  Fintype.ofFinite _

/-- A finite base field of `q` elements gives a field of `q ^ d` elements. -/
theorem card [Fintype k] : Fintype.card (Binomial k d w) = Fintype.card k ^ d := by
  have hd := degree_pos (Fact.out : Irreducible (X ^ d - C w : k[X]))
  have hm : (X ^ d - C w : k[X]).Monic := monic_X_pow_sub_C w hd.ne'
  have := hm.finite_adjoinRoot
  have h := Module.natCard_eq_pow_finrank (K := k) (V := AdjoinRoot (X ^ d - C w : k[X]))
  rw [(AdjoinRoot.powerBasis' hm).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_X_pow_sub_C] at h
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact h

/-- Natural numbers below the characteristic are different in the extension. -/
theorem natCast_injOn (p : ℕ) [CharP k p] {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : Binomial k d w) = b) : a = b := by
  have h' : (of (a : k) : Binomial k d w) = of (b : k) := by
    rw [map_natCast, map_natCast, h]
  exact ((CharP.natCast_eq_natCast k p).mp (of.injective h')).eq_of_lt_of_lt ha hb

end Binomial

end CertiFri.P3
