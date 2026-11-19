import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Basic
import CertiFriProofs.Theory.ProximityGap.CorrelatedAgreement
import CertiFriProofs.Theory.ProximityGap.LinearCode

/-!
# Correlated agreement for Reed–Solomon curves at the unique-decoding radius

`curveCA_udThreshold` proves `CurveCA F udThreshold` for every field `F`. Let
`D` be a set of `n` points, let `2 * e + d ≤ n`, and let `u 0, …, u (m - 1)` be
words on `D`. If the point `∑ k, β ^ k * u k` of the curve through them is
within `e` errors of a polynomial of degree below `d` for more than
`(m - 1) * (n * (e + 1) + 1)` values of `β`, then there are polynomials `v k`
of degree below `d` such that all the `u k` agree with the `v k` outside one
common set of at most `e` points.

Nothing is assumed. The field need not be finite: the statement is about the
finite set `D` and a finite set of parameters.

## The proof

For each close parameter `β` fix a close polynomial `p β`; its error set is
`errSet D u β (p β)`. Let `z₀` be a parameter whose error set `S` is largest,
with `t ≤ e` points. All close parameters except at most
`(t + d) * (t + 1) * (m - 1)` have the error set `S`
(`card_filter_errSet_ne_le`). So `m` of them do; interpolating their close
polynomials (`exists_interpolant_poly`) gives the `v k`, which agree with the
`u k` outside `S`.

The count is the Berlekamp–Welch decoder with the parameter of the curve as an
indeterminate. Take a subdomain `D₂ ⊇ S` of `2 * t + d` points and a point `y`.
In the coefficients of a polynomial `A` of degree at most `t` and a polynomial
`B` of degree below `t + d`, the equations

* `w x * A x = B x` for `x ∈ D₂`, where `w` is the point of the curve at the
  parameter,
* `A y = 0`

form a square linear system (`bwMatrix`). When `w` is within `t` errors of `p`
on `D₂`, its solutions are the pairs `(A, A * p)` with `A` vanishing at the
errors and at `y` (`eq_mul_of_agree`), so it has a nonzero solution exactly
when the errors and `y` together are at most `t` points. The determinant of
the system is a polynomial in the parameter, `testPoly`, of degree at most
`(t + 1) * (m - 1)` (`natDegree_testPoly_le`), and it vanishes at a close
parameter exactly when the errors on `D₂` and `y` together are at most `t`
points (`eval_testPoly_eq_zero_iff_card`). For `y ∈ D₂ \ S` it does not vanish
at `z₀`, so it is not zero; and a close parameter whose error set is not `S` is
a root of it for some `y ∈ D₂ \ S`.

## Not covered

* Larger radii, `2 * e + d > n`, where the close polynomial is not unique.
* A smaller threshold. The count is a union bound over the points `y`, each
  costing the degree of its determinant; this is where the factor `n * (e + 1)`
  comes from, and it makes the threshold quadratic in the size of the domain.
  Whether a threshold linear in `n` can be had is not addressed here.
-/

namespace CertiFri

namespace UniqueDecoding

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## Polynomials with prescribed roots, and the decoding identity -/

/-- A set of at most `t` points is contained in the roots of a nonzero
polynomial of degree at most `t`. -/
theorem exists_vanishing {T : Finset F} {t : ℕ} (hT : T.card ≤ t) :
    ∃ A : F[X], A ≠ 0 ∧ A.degree < (t + 1 : ℕ) ∧ ∀ x ∈ T, A.eval x = 0 := by
  have hmonic : (∏ x ∈ T, (X - C x)).Monic :=
    monic_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  refine ⟨∏ x ∈ T, (X - C x), hmonic.ne_zero, ?_, fun x hx => ?_⟩
  · rw [← natDegree_lt_iff_degree_lt hmonic.ne_zero,
      natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C x]
    simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
    omega
  · rw [eval_prod]
    exact prod_eq_zero hx (by simp)

/-- A nonzero polynomial of degree at most `t` vanishes on at most `t`
points. -/
theorem card_le_of_vanishing {T : Finset F} {t : ℕ} {A : F[X]} (hA : A ≠ 0)
    (hdeg : A.degree < (t + 1 : ℕ)) (h : ∀ x ∈ T, A.eval x = 0) : T.card ≤ t := by
  by_contra hlt
  have hnat := (natDegree_lt_iff_degree_lt hA).mpr hdeg
  exact hA (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' A T h (by omega))

/-- The product of a polynomial of degree at most `t` and one of degree below
`d` has degree below `t + d`. -/
theorem degree_mul_lt {A p : F[X]} {t d : ℕ} (hA : A.degree < (t + 1 : ℕ))
    (hp : p.degree < d) : (A * p).degree < (t + d : ℕ) := by
  by_cases hA0 : A = 0
  · simp [hA0]
  by_cases hp0 : p = 0
  · simp [hp0]
  have h1 := (natDegree_lt_iff_degree_lt hA0).mpr hA
  have h2 := (natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [← natDegree_lt_iff_degree_lt (mul_ne_zero hA0 hp0), natDegree_mul hA0 hp0]
  omega

/-- The decoding identity. On a domain `D₂` of at least `2 * t + d` points, let
the word `w` differ from the polynomial `p` of degree below `d` at no more than
`t` points. If `A` of degree at most `t` and `B` of degree below `t + d`
satisfy `w x * A x = B x` on `D₂`, then `B = A * p`, and `A` vanishes wherever
`w` differs from `p`. -/
theorem eq_mul_of_agree [DecidableEq F] {D₂ : Finset F} {t d : ℕ}
    (hcard : 2 * t + d ≤ D₂.card) {w : F → F} {p A B : F[X]} (hp : p.degree < d)
    (hE : (D₂.filter fun x => w x ≠ p.eval x).card ≤ t)
    (hA : A.degree < (t + 1 : ℕ)) (hB : B.degree < (t + d : ℕ))
    (h : ∀ x ∈ D₂, w x * A.eval x = B.eval x) :
    B = A * p ∧ ∀ x ∈ D₂, w x ≠ p.eval x → A.eval x = 0 := by
  have hBA : B = A * p := by
    have hle : t + d ≤ (D₂.filter fun x => w x = p.eval x).card := by
      have hsplit := card_filter_add_card_filter_not (s := D₂) fun x => w x = p.eval x
      have hE' : (D₂.filter fun x => ¬w x = p.eval x).card ≤ t := hE
      omega
    refine eq_of_degrees_lt_of_eval_finset_eq (D₂.filter fun x => w x = p.eval x)
      (hB.trans_le (Nat.cast_le.mpr hle)) ((degree_mul_lt hA hp).trans_le (Nat.cast_le.mpr hle))
      fun x hx => ?_
    rw [mem_filter] at hx
    rw [← h x hx.1, hx.2, eval_mul, mul_comm]
  refine ⟨hBA, fun x hx hne => ?_⟩
  have hx' := h x hx
  rw [hBA, eval_mul, mul_comm (A.eval x), ← sub_eq_zero, ← sub_mul] at hx'
  exact (mul_eq_zero.mp hx').resolve_left (sub_ne_zero.mpr hne)

/-! ## Polynomials and their coefficient vectors -/

/-- A vector of `n` coefficients is a polynomial of degree below `n`. -/
theorem exists_poly_of_coeffs {n : ℕ} (f : Fin n → F) :
    ∃ A : F[X], A.degree < n ∧ (A = 0 ↔ f = 0) ∧
      ∀ x, A.eval x = ∑ i : Fin n, f i * x ^ (i : ℕ) := by
  refine ⟨((degreeLTEquiv F n).symm f : F[X]), mem_degreeLT.mp (Subtype.property _), ?_,
    fun x => ?_⟩
  · rw [← degreeLTEquiv_eq_zero_iff_eq_zero (Subtype.property _)]
    simp
  · rw [eval_eq_sum_degreeLTEquiv (Subtype.property _)]
    simp

/-- A polynomial of degree below `n` is a vector of `n` coefficients. -/
theorem exists_coeffs_of_poly {n : ℕ} {A : F[X]} (hA : A.degree < n) :
    ∃ f : Fin n → F, (f = 0 ↔ A = 0) ∧ ∀ x, A.eval x = ∑ i : Fin n, f i * x ^ (i : ℕ) :=
  ⟨degreeLTEquiv F n ⟨A, mem_degreeLT.mpr hA⟩, degreeLTEquiv_eq_zero_iff_eq_zero _,
    eval_eq_sum_degreeLTEquiv _⟩

/-! ## The linear system -/

section System

variable {R : Type*} [CommRing R] {a s : ℕ}

/-- The matrix of a linear system in the coefficients of two polynomials, `A`
with `a` coefficients and `B` with `s` coefficients. Row `r` is the equation
`c r * A (pt r) - b r * B (pt r) = 0`. -/
def bwMatrix (pt c b : Fin a ⊕ Fin s → R) : Matrix (Fin a ⊕ Fin s) (Fin a ⊕ Fin s) R :=
  Matrix.of fun r => Sum.elim (fun i => c r * pt r ^ (i : ℕ)) fun j => -(b r * pt r ^ (j : ℕ))

/-- Row `r` of the system applied to a vector `v` of coefficients: the
left-hand side of equation `r` for the polynomials with coefficients `v`. -/
theorem bwMatrix_mulVec (pt c b v : Fin a ⊕ Fin s → R) (r : Fin a ⊕ Fin s) :
    (bwMatrix pt c b).mulVec v r =
      c r * ∑ i : Fin a, v (Sum.inl i) * pt r ^ (i : ℕ) -
        b r * ∑ j : Fin s, v (Sum.inr j) * pt r ^ (j : ℕ) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, bwMatrix, Matrix.of_apply,
    Sum.elim_inl, Sum.elim_inr, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring)
    (congrArg Neg.neg (Finset.sum_congr rfl fun _ _ => by ring))

/-- A ring homomorphism maps the matrix of a system to the matrix of the image
system. -/
theorem map_bwMatrix {R' : Type*} [CommRing R'] (f : R →+* R') (pt c b : Fin a ⊕ Fin s → R) :
    f.mapMatrix (bwMatrix pt c b) =
      bwMatrix (fun r => f (pt r)) (fun r => f (c r)) fun r => f (b r) := by
  ext r (i | j) <;> simp [bwMatrix]

/-- Over a field, the determinant of the system vanishes exactly when the
system has a nonzero solution `(A, B)`. -/
theorem det_bwMatrix_eq_zero_iff (pt c b : Fin a ⊕ Fin s → F) :
    (bwMatrix pt c b).det = 0 ↔
      ∃ A B : F[X], A.degree < a ∧ B.degree < s ∧ (A ≠ 0 ∨ B ≠ 0) ∧
        ∀ r, c r * A.eval (pt r) = b r * B.eval (pt r) := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hMv⟩
    obtain ⟨A, hA, hA0, hAe⟩ := exists_poly_of_coeffs fun i => v (Sum.inl i)
    obtain ⟨B, hB, hB0, hBe⟩ := exists_poly_of_coeffs fun j => v (Sum.inr j)
    refine ⟨A, B, hA, hB, ?_, fun r => ?_⟩
    · by_contra hn
      rw [not_or, not_not, not_not] at hn
      refine hv (funext fun r => ?_)
      rcases r with i | j
      · exact congrFun (hA0.mp hn.1) i
      · exact congrFun (hB0.mp hn.2) j
    · have h := congrFun hMv r
      rw [bwMatrix_mulVec, Pi.zero_apply, sub_eq_zero] at h
      rw [hAe, hBe]
      exact h
  · rintro ⟨A, B, hA, hB, hne, h⟩
    obtain ⟨f, hf0, hfe⟩ := exists_coeffs_of_poly hA
    obtain ⟨g, hg0, hge⟩ := exists_coeffs_of_poly hB
    refine ⟨Sum.elim f g, fun h0 => ?_, funext fun r => ?_⟩
    · have hf : f = 0 := funext fun i => congrFun h0 (Sum.inl i)
      have hg : g = 0 := funext fun j => congrFun h0 (Sum.inr j)
      exact hne.elim (fun hA0 => hA0 (hf0.mp hf)) fun hB0 => hB0 (hg0.mp hg)
    · rw [bwMatrix_mulVec, Pi.zero_apply, sub_eq_zero]
      simp only [Sum.elim_inl, Sum.elim_inr, ← hfe, ← hge]
      exact h r

/-- The determinant of a matrix of polynomials whose column `j` has entries of
degree at most `c j` has degree at most `∑ j, c j`. -/
theorem natDegree_det_le {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F[X])
    (c : n → ℕ) (h : ∀ i j, (M i j).natDegree ≤ c j) : M.det.natDegree ≤ ∑ j, c j := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  calc natDegree (Equiv.Perm.sign σ • ∏ i, M (σ i) i)
      ≤ natDegree (∏ i, M (σ i) i) := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
    _ ≤ ∑ i, natDegree (M (σ i) i) := natDegree_prod_le _ _
    _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ => h _ _

/-- When the points and the coefficients `b` of a system are constants, and
the coefficients `c` are polynomials of degree at most `k`, the determinant has
degree at most `a * k`: only the `a` columns of the first polynomial are not
constant. -/
theorem natDegree_det_bwMatrix_le (pt b : Fin a ⊕ Fin s → F) (c : Fin a ⊕ Fin s → F[X]) {k : ℕ}
    (hc : ∀ r, (c r).natDegree ≤ k) :
    (bwMatrix (fun r => C (pt r)) c fun r => C (b r)).det.natDegree ≤ a * k := by
  refine (natDegree_det_le _ (Sum.elim (fun _ => k) fun _ => 0) ?_).trans (by simp)
  rintro r (i | j)
  · simp only [bwMatrix, Matrix.of_apply, Sum.elim_inl, ← C_pow]
    exact (natDegree_mul_C_le _ _).trans (hc r)
  · simp only [bwMatrix, Matrix.of_apply, Sum.elim_inr, ← C_pow, ← C_mul, ← C_neg, natDegree_C,
      le_refl]

end System

/-! ## The test polynomial -/

section Test

variable {m t s : ℕ} {D₂ : Finset F}

/-- The value at the point `x` of the curve through the words `u k`, as a
polynomial in the parameter of the curve: `∑ k, u k x * Z ^ k`. -/
noncomputable def curvePoly (u : Fin m → F → F) (x : F) : F[X] :=
  ∑ k : Fin m, C (u k x) * X ^ (k : ℕ)

/-- At the parameter `β` it is the point of the curve: `∑ k, β ^ k * u k x`. -/
theorem eval_curvePoly (u : Fin m → F → F) (x β : F) :
    (curvePoly u x).eval β = ∑ k : Fin m, β ^ (k : ℕ) * u k x := by
  rw [curvePoly, eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

/-- As a polynomial in the parameter, a curve of `m` terms has degree at most
`m - 1`. -/
theorem natDegree_curvePoly_le (u : Fin m → F → F) (x : F) :
    (curvePoly u x).natDegree ≤ m - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun k _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)

/-- The test polynomial at the point `y`, in the parameter `Z` of the curve:
the determinant of the system with one equation
`(∑ k, u k x * Z ^ k) * A x - B x = 0` for each point `x` of `D₂`, and the
equation `A y = 0`. The unknowns are the `t + 1` coefficients of `A` and the
`s` coefficients of `B`; the equivalence `σ` enumerates the equations. -/
noncomputable def testPoly (σ : Fin (t + 1) ⊕ Fin s ≃ Option D₂) (u : Fin m → F → F) (y : F) :
    F[X] :=
  (bwMatrix (fun r => C ((σ r).elim y fun x => (x : F)))
    (fun r => (σ r).elim 1 fun x => curvePoly u x) fun r => C ((σ r).elim 0 fun _ => 1)).det

/-- The test polynomial has degree at most `(t + 1) * (m - 1)`. -/
theorem natDegree_testPoly_le (σ : Fin (t + 1) ⊕ Fin s ≃ Option D₂) (u : Fin m → F → F)
    (y : F) : (testPoly σ u y).natDegree ≤ (t + 1) * (m - 1) := by
  refine natDegree_det_bwMatrix_le _ _ _ fun r => ?_
  cases σ r <;> simp [natDegree_curvePoly_le]

/-- The test polynomial vanishes at `β` exactly when the system at `β` has a
nonzero solution. -/
theorem eval_testPoly_eq_zero_iff (σ : Fin (t + 1) ⊕ Fin s ≃ Option D₂) (u : Fin m → F → F)
    (y β : F) :
    (testPoly σ u y).eval β = 0 ↔
      ∃ A B : F[X], A.degree < (t + 1 : ℕ) ∧ B.degree < s ∧ (A ≠ 0 ∨ B ≠ 0) ∧ A.eval y = 0 ∧
        ∀ x ∈ D₂, (∑ k : Fin m, β ^ (k : ℕ) * u k x) * A.eval x = B.eval x := by
  rw [testPoly, ← coe_evalRingHom, RingHom.map_det, map_bwMatrix, det_bwMatrix_eq_zero_iff]
  refine exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    refine ⟨by simpa using h (σ.symm none), fun x hx => ?_⟩
    simpa [eval_curvePoly] using h (σ.symm (some ⟨x, hx⟩))
  · rintro ⟨hy, hx⟩ r
    rcases σ r with _ | x
    · simpa using hy
    · simpa [eval_curvePoly] using hx x x.2

end Test

/-! ## Interpolation -/

/-- Through `m` polynomials of degree below `d` placed at `m` distinct
parameters passes a curve with `m` coefficients `v k` of degree below `d`; and
at every point where the curve through words `u k` takes the values of these
polynomials at the `m` parameters, each `u k` takes the value of `v k`. -/
theorem exists_interpolant_poly {m d : ℕ} {b : Fin m → F} (hb : Function.Injective b)
    (p : Fin m → F[X]) (hp : ∀ i, (p i).degree < d) :
    ∃ v : Fin m → F[X], (∀ k, (v k).degree < d) ∧ ∀ (u : Fin m → F → F) (x : F),
      (∀ i, ∑ k : Fin m, b i ^ (k : ℕ) * u k x = (p i).eval x) → ∀ k, u k x = (v k).eval x := by
  obtain ⟨w, hw, hwc⟩ := ProximityGap.exists_interpolant
    (L := (degreeLT F d).map (LinearMap.pi fun x : F => leval x)) hb
    (c := fun i x => (p i).eval x) fun i => ⟨p i, mem_degreeLT.mpr (hp i), rfl⟩
  choose v hv hvw using hw
  refine ⟨v, fun k => mem_degreeLT.mp (hv k), fun u x h k => ?_⟩
  have h0 : (fun k => u k x - w k x) = 0 :=
    Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hb fun i => by
      rw [← ProximityGap.curve_sub_curve, hwc i, sub_eq_zero]
      exact h i
  have hvx : (v k).eval x = w k x := congrFun (hvw k) x
  rw [hvx]
  exact sub_eq_zero.mp (congrFun h0 k)

/-! ## What the test polynomial tests -/

variable [DecidableEq F] {m : ℕ}

/-- The points of `D` at which the point with parameter `β` of the curve
through the words `u k` differs from the polynomial `p`. -/
def errSet (D : Finset F) (u : Fin m → F → F) (β : F) (p : F[X]) : Finset F :=
  D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x ≠ p.eval x

/-- The error set is a subset of the domain. -/
theorem errSet_subset (D : Finset F) (u : Fin m → F → F) (β : F) (p : F[X]) :
    errSet D u β p ⊆ D :=
  filter_subset _ _

/-- The error set on a subdomain is a subset of the error set on the domain. -/
theorem errSet_mono {D₂ D : Finset F} (h : D₂ ⊆ D) (u : Fin m → F → F) (β : F) (p : F[X]) :
    errSet D₂ u β p ⊆ errSet D u β p :=
  filter_subset_filter _ h

/-- Let `D₂` have `2 * t + d` points, as the enumeration `σ` of the equations
forces, and let the point with parameter `β` of the curve differ on `D₂` from
the polynomial `p` of degree below `d` at no more than `t` points. Then the
test polynomial at `y` vanishes at `β` exactly when these points and `y`
together number at most `t`. -/
theorem eval_testPoly_eq_zero_iff_card {t d : ℕ} {D₂ : Finset F}
    (σ : Fin (t + 1) ⊕ Fin (t + d) ≃ Option D₂) (u : Fin m → F → F) (y β : F) {p : F[X]}
    (hp : p.degree < d) (hE : (errSet D₂ u β p).card ≤ t) :
    (testPoly σ u y).eval β = 0 ↔ (insert y (errSet D₂ u β p)).card ≤ t := by
  have hcard : 2 * t + d ≤ D₂.card := by
    have h := Fintype.card_congr σ
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_option, Fintype.card_coe] at h
    omega
  rw [eval_testPoly_eq_zero_iff]
  constructor
  · rintro ⟨A, B, hA, hB, hne, hy, h⟩
    obtain ⟨hBA, hvan⟩ := eq_mul_of_agree hcard hp hE hA hB h
    have hA0 : A ≠ 0 := fun hA0 =>
      hne.elim (fun h => h hA0) fun h => h (by rw [hBA, hA0, zero_mul])
    refine card_le_of_vanishing hA0 hA fun x hx => ?_
    rcases mem_insert.mp hx with rfl | hx
    · exact hy
    · exact hvan x (mem_filter.mp hx).1 (mem_filter.mp hx).2
  · intro hcard'
    obtain ⟨A, hA0, hA, hvan⟩ := exists_vanishing hcard'
    refine ⟨A, A * p, hA, degree_mul_lt hA hp, Or.inl hA0, hvan y (mem_insert_self _ _),
      fun x hx => ?_⟩
    by_cases hx' : ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x
    · rw [hx', eval_mul, mul_comm]
    · rw [eval_mul, hvan x (mem_insert_of_mem (mem_filter.mpr ⟨hx, hx'⟩)), mul_zero, zero_mul]

/-! ## Counting the parameters with another error set -/

/-- On a domain of at least `2 * t + d` points, let the point of the curve at
each parameter `β ∈ G` differ from a polynomial `p β` of degree below `d` at no
more than `t` points, and at exactly `t` points for the parameter `z₀ ∈ G`.
Then at most `(t + d) * ((t + 1) * (m - 1))` parameters in `G` have an error
set other than that of `z₀`. -/
theorem card_filter_errSet_ne_le {D : Finset F} {d t : ℕ} (u : Fin m → F → F) {G : Finset F}
    (p : F → F[X]) (hp : ∀ β ∈ G, (p β).degree < d) (hD : 2 * t + d ≤ D.card)
    (hE : ∀ β ∈ G, (errSet D u β (p β)).card ≤ t) {z₀ : F} (hz₀ : z₀ ∈ G)
    (hz₀t : (errSet D u z₀ (p z₀)).card = t) :
    (G.filter fun β => errSet D u β (p β) ≠ errSet D u z₀ (p z₀)).card ≤
      (t + d) * ((t + 1) * (m - 1)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- No errors anywhere: every error set is empty.
    have hempty : ∀ β ∈ G, errSet D u β (p β) = ∅ := fun β hβ =>
      card_eq_zero.mp (Nat.le_zero.mp (hE β hβ))
    rw [filter_eq_empty_iff.mpr fun β hβ =>
      not_not.mpr ((hempty β hβ).trans (hempty z₀ hz₀).symm)]
    simp
  -- A subdomain of exactly `2 * t + d` points containing the error set at `z₀`.
  obtain ⟨D₂, hSD₂, hD₂D, hD₂card⟩ :=
    exists_subsuperset_card_eq (errSet_subset D u z₀ (p z₀))
      (by omega : (errSet D u z₀ (p z₀)).card ≤ 2 * t + d) hD
  have hcardeq : Fintype.card (Fin (t + 1) ⊕ Fin (t + d)) = Fintype.card (Option D₂) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_option, Fintype.card_coe, hD₂card]
    omega
  let σ := Fintype.equivOfCardEq hcardeq
  have hS₂ : errSet D₂ u z₀ (p z₀) = errSet D u z₀ (p z₀) :=
    subset_antisymm (errSet_mono hD₂D _ _ _) fun x hx =>
      mem_filter.mpr ⟨hSD₂ hx, (mem_filter.mp hx).2⟩
  have hE₂ : ∀ β ∈ G, (errSet D₂ u β (p β)).card ≤ t := fun β hβ =>
    (card_le_card (errSet_mono hD₂D _ _ _)).trans (hE β hβ)
  have hZ : ∀ β ∈ G, ∀ y, (testPoly σ u y).eval β = 0 ↔
      (insert y (errSet D₂ u β (p β))).card ≤ t := fun β hβ y =>
    eval_testPoly_eq_zero_iff_card σ u y β (hp β hβ) (hE₂ β hβ)
  -- The test polynomials at the points outside the error set of `z₀` are not zero.
  have hne : ∀ y ∈ D₂ \ errSet D u z₀ (p z₀), testPoly σ u y ≠ 0 := by
    intro y hy h0
    have h := (hZ z₀ hz₀ y).mp (by rw [h0, eval_zero])
    rw [hS₂, card_insert_of_notMem (mem_sdiff.mp hy).2, hz₀t] at h
    omega
  -- Every parameter with another error set is a root of one of them.
  have hsub : (G.filter fun β => errSet D u β (p β) ≠ errSet D u z₀ (p z₀)) ⊆
      (D₂ \ errSet D u z₀ (p z₀)).biUnion fun y => (testPoly σ u y).roots.toFinset := by
    intro β hβ
    obtain ⟨hβG, hβS⟩ := mem_filter.mp hβ
    obtain ⟨y, hy, hycard⟩ : ∃ y ∈ D₂ \ errSet D u z₀ (p z₀),
        (insert y (errSet D₂ u β (p β))).card ≤ t := by
      rcases (hE₂ β hβG).lt_or_eq with hlt | heq
      · have hpos : 0 < (D₂ \ errSet D u z₀ (p z₀)).card := by
          rw [card_sdiff_of_subset hSD₂]
          omega
        obtain ⟨y, hy⟩ := card_pos.mp hpos
        exact ⟨y, hy, (card_insert_le _ _).trans hlt⟩
      · have hEβ : errSet D₂ u β (p β) = errSet D u β (p β) :=
          eq_of_subset_of_card_le (errSet_mono hD₂D _ _ _) (by rw [heq]; exact hE β hβG)
        have hnsub : ¬errSet D u β (p β) ⊆ errSet D u z₀ (p z₀) := fun hsub =>
          hβS (eq_of_subset_of_card_le hsub (by rw [hz₀t, ← hEβ, heq]))
        obtain ⟨y, hyE, hyS⟩ := not_subset.mp hnsub
        rw [← hEβ] at hyE
        exact ⟨y, mem_sdiff.mpr ⟨(mem_filter.mp hyE).1, hyS⟩,
          by rw [insert_eq_of_mem hyE, heq]⟩
    refine mem_biUnion.mpr ⟨y, hy, ?_⟩
    rw [Multiset.mem_toFinset, mem_roots (hne y hy), IsRoot.def]
    exact (hZ β hβG y).mpr hycard
  calc (G.filter fun β => errSet D u β (p β) ≠ errSet D u z₀ (p z₀)).card
      ≤ ((D₂ \ errSet D u z₀ (p z₀)).biUnion fun y => (testPoly σ u y).roots.toFinset).card :=
        card_le_card hsub
    _ ≤ ∑ y ∈ D₂ \ errSet D u z₀ (p z₀), (testPoly σ u y).roots.toFinset.card :=
        card_biUnion_le
    _ ≤ ∑ _y ∈ D₂ \ errSet D u z₀ (p z₀), (t + 1) * (m - 1) := sum_le_sum fun y _ =>
        (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_testPoly_le σ u y))
    _ = (t + d) * ((t + 1) * (m - 1)) := by
        rw [sum_const, card_sdiff_of_subset hSD₂, hD₂card, hz₀t, smul_eq_mul]
        congr 1
        omega

end UniqueDecoding

open UniqueDecoding Finset Polynomial

/-- **Correlated agreement for curves over Reed–Solomon codes holds in the
unique-decoding regime**, with threshold `udThreshold`.

Let `2 * e + d ≤ D.card`. If for more than `(m - 1) * (D.card * (e + 1) + 1)`
values of `β` the word `∑ k, β ^ k * u k` differs from some polynomial of
degree below `d` at no more than `e` points of `D`, then there are polynomials
`v k` of degree below `d` such that the points of `D` where some `u k` differs
from `v k` number at most `e`. The field may be infinite. -/
theorem curveCA_udThreshold (F : Type*) [Field F] [DecidableEq F] : CurveCA F udThreshold := by
  intro D d e m hD u G hG hgood
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun k => k.elim0, fun k => k.elim0, by simp⟩
  unfold udThreshold at hG
  choose! p hp hpE using hgood
  change ∀ β ∈ G, (errSet D u β (p β)).card ≤ e at hpE
  -- A parameter `z₀` whose error set is largest, with `t` points.
  obtain ⟨z₀, hz₀, hmax⟩ := exists_max_image G (fun β => (errSet D u β (p β)).card)
    (card_pos.mp (by omega))
  obtain ⟨t, ht⟩ : ∃ t, (errSet D u z₀ (p z₀)).card = t := ⟨_, rfl⟩
  have hte : t ≤ e := ht ▸ hpE z₀ hz₀
  -- Few parameters have another error set, so at least `m` have that of `z₀`.
  have hbad : (G.filter fun β => ¬errSet D u β (p β) = errSet D u z₀ (p z₀)).card ≤
      (t + d) * ((t + 1) * (m - 1)) :=
    card_filter_errSet_ne_le u p hp (by omega) (fun β hβ => (hmax β hβ).trans_eq ht) hz₀ ht
  have hsplit := card_filter_add_card_filter_not (s := G)
    fun β => errSet D u β (p β) = errSet D u z₀ (p z₀)
  have hm_le : m ≤ (G.filter fun β => errSet D u β (p β) = errSet D u z₀ (p z₀)).card := by
    have h1 : (t + d) * ((t + 1) * (m - 1)) ≤ D.card * ((e + 1) * (m - 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega))
    have h2 : (m - 1) * (D.card * (e + 1) + 1) = D.card * ((e + 1) * (m - 1)) + (m - 1) := by
      ring
    omega
  -- Interpolate through `m` of them: the `u k` agree with the result outside
  -- the error set of `z₀`.
  obtain ⟨b, hb, hbmem⟩ := ProximityGap.exists_injective_of_le_card hm_le
  obtain ⟨v, hv, hvu⟩ := exists_interpolant_poly hb (fun i => p (b i))
    fun i => hp _ (mem_filter.mp (hbmem i)).1
  refine ⟨v, hv, (card_le_card fun x hx => ?_).trans (ht.le.trans hte)⟩
  obtain ⟨hxD, k, hk⟩ := mem_filter.mp hx
  by_contra hxS
  refine hk (hvu u x (fun i => ?_) k)
  by_contra hne
  exact hxS ((mem_filter.mp (hbmem i)).2 ▸ mem_filter.mpr ⟨hxD, hne⟩)

end CertiFri
