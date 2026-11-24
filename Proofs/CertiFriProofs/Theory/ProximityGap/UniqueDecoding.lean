import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Polynomial.Basic
import CertiFriProofs.Theory.ProximityGap.CorrelatedAgreement
import CertiFriProofs.Theory.ProximityGap.LinearCode

/-!
# Correlated agreement for Reed–Solomon curves at the unique-decoding radius

`curveCA_udThreshold` proves `CurveCA F udThreshold` for every field `F`, with the
linear threshold `udThreshold n e m = (m - 1) * (n + e)`.

Let `D` be a set of `n` points, let `2 * e + d ≤ n`, and let `u 0, …, u (m - 1)` be
words on `D`. If the point `∑ k, β ^ k * u k` of the curve through them is within
`e` errors of a polynomial of degree below `d` for more than `(m - 1) * (n + e)`
values of `β`, then there are polynomials `v k` of degree below `d` such that all
the `u k` agree with the `v k` outside one common set of at most `e` points.

Nothing is assumed. The field need not be finite: the statement is about the finite
set `D` and a finite set of parameters.

## The proof (linear-threshold parametric Berlekamp–Welch)

Let `z₀ ∈ G` maximize the error count `t := |errSet D u z₀ (p z₀)| ≤ e`, with
`S := errSet D u z₀ (p z₀)`. Take a subdomain `D₂ ⊇ S` of `2 * t + d` points and
form the square `(2 * t + d) × (2 * t + d)` Berlekamp–Welch system `M₀(Z)` over
`F[Z]` for monic `A` of degree `t` (`a_t = 1`) and `B` of degree below `t + d`.

1. At `Z = z₀`, `M₀(z₀)` is nonsingular (since any nonzero `A` of degree `< t`
   vanishing on `S` is impossible), so `Δ(Z) := det M₀(Z) ≠ 0` has degree at most
   `t * (m - 1)`. Cramer's rule (`M₀.cramer rhs`) yields polynomials `A(Z, X)` of
   `X`-degree `t` (leading `X`-coefficient `Δ(Z)`) and `B(Z, X)` of `X`-degree below
   `t + d`, with `Z`-degree of every `X`-coefficient of `A` at most `t * (m - 1)`,
   satisfying `w(Z)(x) * A(Z, x) = B(Z, x)` for all `x ∈ D₂`.
2. For each `y ∈ D \ D₂`, augmenting `M₀(Z)` by row `y` and column `a_t` gives a
   `(2 * t + d + 1) × (2 * t + d + 1)` matrix `M_y(Z)` whose determinant has
   `Z`-degree at most `(t + 1) * (m - 1)` and vanishes on all of `G`. Since
   `|G| > (t + 1) * (m - 1)`, `det M_y(Z) = 0`. Multiplying by `M_y.adjugate` and
   cancelling its `(none, none)` cofactor `Δ(Z) ≠ 0` shows
   `w(Z)(y) * A(Z, y) = B(Z, y)` for *every* `y ∈ D`.
3. Let `S* := {x ∈ D | A(Z, x) = 0 in F[Z]}` (`s := |S*|`). Evaluating at `z₀`
   gives `S* ⊆ S`, so `s ≤ t`.
   * If `s = t`, then `S* = S`: for every `β ∈ G` with `Δ(β) ≠ 0`, `A(β, X)` has
     exact roots `S` and vanishes on `errSet D u β (p β)`, so
     `errSet D u β (p β) ⊆ S`. Since `|G| - t * (m - 1) ≥ m`, interpolating `p β`
     through `m` such parameters yields `v k` agreeing with `u k` outside `S`.
   * If `s < t` (`t' := t - s ≥ 1`), divide `A(Z, X)` and `B(Z, X)` in `(F[Z])[X]`
     by the monic constant polynomial `A₀(X) := ∏ x ∈ S*, (X - x)` to obtain
     `(Ã, B̃)` satisfying `w(Z)(x) * Ã(Z, x) = B̃(Z, x)` and `Ã(Z, x) ≠ 0` on
     `D' := D \ S*`. Solving the smaller `(2 * t' + d) × (2 * t' + d)` system
     `M'₀(Z)` on a subdomain `D'₂ ⊆ D'` containing `S \ S*` gives `A'(Z, X)` of
     `Z`-degree at most `t' * (m - 1)` with `Δ'(Z) * Ã(Z, X) = Δ(Z) * A'(Z, X)`.
     Hence `A'(Z, x) ≠ 0` for all `x ∈ D'`, while for every `β ∈ G'` (`Δ(β) ≠ 0`),
     `|errSet D u β (p β)| = t`, `S* ⊆ errSet D u β (p β)`, and `A'(β, x) = 0` on
     all `t'` points of `errSet D u β (p β) \ S*`. Double-counting pairs
     `(x, β) ∈ D' × G'` with `A'(β, x) = 0` gives
     `t' * |G'| ≤ |D'| * t' * (m - 1)`, so `|G'| ≤ (n - s) * (m - 1)` and
     `|G| ≤ (n - s + t) * (m - 1) ≤ (n + e) * (m - 1)`, contradiction!
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

/-! ## Curves and interpolation -/

/-- The value at the point `x` of the curve through the words `u k`, as a
polynomial in the parameter of the curve: `∑ k, u k x * Z ^ k`. -/
noncomputable def curvePoly {m : ℕ} (u : Fin m → F → F) (x : F) : F[X] :=
  ∑ k : Fin m, C (u k x) * X ^ (k : ℕ)

/-- At the parameter `β` it is the point of the curve: `∑ k, β ^ k * u k x`. -/
theorem eval_curvePoly {m : ℕ} (u : Fin m → F → F) (x β : F) :
    (curvePoly u x).eval β = ∑ k : Fin m, β ^ (k : ℕ) * u k x := by
  rw [curvePoly, eval_finsetSum]
  exact Finset.sum_congr rfl fun k _ => by rw [eval_mul, eval_C, eval_pow, eval_X, mul_comm]

/-- As a polynomial in the parameter, a curve of `m` terms has degree at most
`m - 1`. -/
theorem natDegree_curvePoly_le {m : ℕ} (u : Fin m → F → F) (x : F) :
    (curvePoly u x).natDegree ≤ m - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun k _ =>
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)

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

/-! ## Parametric monic Berlekamp–Welch system over `F[Z]` -/

section MonicSystem

variable {m t d : ℕ} {D₂ : Finset F}

/-- The `(2 * t + d) × (2 * t + d)` square matrix `M₀(Z)` of the monic
Berlekamp–Welch system on `D₂` enumerated by `σ : Fin t ⊕ Fin (t + d) ≃ D₂`. -/
noncomputable def bwMonicMatrix (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    Matrix (Fin t ⊕ Fin (t + d)) (Fin t ⊕ Fin (t + d)) F[X] :=
  bwMatrix (fun r => C ((σ r : F))) (fun r => curvePoly u (σ r)) (fun _ => 1)

/-- The right-hand side vector for the monic term `X ^ t` of `A`. -/
noncomputable def bwMonicRhs (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    Fin t ⊕ Fin (t + d) → F[X] :=
  fun r => -(curvePoly u (σ r) * C ((σ r : F) ^ t))

/-- Determinant `Δ(Z) = det M₀(Z)`. -/
noncomputable def bwDelta (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) : F[X] :=
  (bwMonicMatrix σ u).det

/-- Cramer's rule solution vector for `(a₀, …, a_{t-1}, b₀, …, b_{t+d-1})` over `F[Z]`. -/
noncomputable def bwSol (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    Fin t ⊕ Fin (t + d) → F[X] :=
  (bwMonicMatrix σ u).cramer (bwMonicRhs σ u)

/-- The `X`-coefficients of `A(Z, X)` in `F[Z]`: the leading `X ^ t` coefficient is `Δ(Z)`. -/
noncomputable def bwCoeffA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    Fin (t + 1) → F[X] :=
  Fin.lastCases (bwDelta σ u) (fun i => bwSol σ u (Sum.inl i))

/-- The `X`-coefficients of `B(Z, X)` in `F[Z]`. -/
noncomputable def bwCoeffB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    Fin (t + d) → F[X] :=
  fun j => bwSol σ u (Sum.inr j)

/-- `A(Z, x)` as a polynomial in `Z`. -/
noncomputable def bwEvalXA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x : F) : F[X] :=
  ∑ i : Fin (t + 1), bwCoeffA σ u i * C (x ^ (i : ℕ))

/-- `B(Z, x)` as a polynomial in `Z`. -/
noncomputable def bwEvalXB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x : F) : F[X] :=
  ∑ j : Fin (t + d), bwCoeffB σ u j * C (x ^ (j : ℕ))

/-- `A(β, X)` as a polynomial in `X`. -/
noncomputable def bwEvalZA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) : F[X] :=
  ∑ i : Fin (t + 1), C ((bwCoeffA σ u i).eval β) * X ^ (i : ℕ)

/-- `B(β, X)` as a polynomial in `X`. -/
noncomputable def bwEvalZB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) : F[X] :=
  ∑ j : Fin (t + d), C ((bwCoeffB σ u j).eval β) * X ^ (j : ℕ)

/-- `A(Z, X)` as a polynomial in `X` over `F[Z]`. -/
noncomputable def bwPolyA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) : (F[X])[X] :=
  ∑ i : Fin (t + 1), C (bwCoeffA σ u i) * X ^ (i : ℕ)

/-- `B(Z, X)` as a polynomial in `X` over `F[Z]`. -/
noncomputable def bwPolyB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) : (F[X])[X] :=
  ∑ j : Fin (t + d), C (bwCoeffB σ u j) * X ^ (j : ℕ)

theorem natDegree_bwDelta_le (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) :
    (bwDelta σ u).natDegree ≤ t * (m - 1) := by
  simpa [bwDelta, bwMonicMatrix] using
    natDegree_det_bwMatrix_le (fun r => (σ r : F)) (fun _ => (1 : F))
      (fun r => curvePoly u (σ r)) fun r => natDegree_curvePoly_le u (σ r)

theorem natDegree_bwSol_inl_le (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (i : Fin t) :
    (bwSol σ u (Sum.inl i)).natDegree ≤ t * (m - 1) := by
  rw [bwSol, Matrix.cramer_apply]
  refine (natDegree_det_le _ (Sum.elim (fun _ => m - 1) fun _ => 0) ?_).trans (by simp)
  intro r col
  rw [Matrix.updateCol_apply]
  split
  · next h =>
    subst h
    simp only [Sum.elim_inl, bwMonicRhs, natDegree_neg]
    exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u (σ r))
  · rcases col with i' | j'
    · simp only [bwMonicMatrix, bwMatrix, Matrix.of_apply, Sum.elim_inl, ← C_pow]
      exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u (σ r))
    · simp only [bwMonicMatrix, bwMatrix, Matrix.of_apply, Sum.elim_inr, one_mul, ← C_pow,
        ← C_neg, natDegree_C, le_refl]

theorem natDegree_bwCoeffA_le (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (i : Fin (t + 1)) :
    (bwCoeffA σ u i).natDegree ≤ t * (m - 1) := by
  refine Fin.lastCases ?_ ?_ i
  · simp [bwCoeffA, natDegree_bwDelta_le]
  · intro i'
    simp [bwCoeffA, natDegree_bwSol_inl_le]

theorem natDegree_bwEvalXA_le (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x : F) :
    (bwEvalXA σ u x).natDegree ≤ t * (m - 1) :=
  natDegree_sum_le_of_forall_le _ _ fun i _ =>
    (natDegree_mul_C_le _ _).trans (natDegree_bwCoeffA_le σ u i)

theorem eval_bwEvalXA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x β : F) :
    (bwEvalXA σ u x).eval β = (bwEvalZA σ u β).eval x := by
  simp only [bwEvalXA, bwEvalZA, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem eval_bwEvalXB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x β : F) :
    (bwEvalXB σ u x).eval β = (bwEvalZB σ u β).eval x := by
  simp only [bwEvalXB, bwEvalZB, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem eval_bwPolyA (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x : F) :
    (bwPolyA σ u).eval (C x) = bwEvalXA σ u x := by
  simp only [bwPolyA, bwEvalXA, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, C_pow]

theorem eval_bwPolyB (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (x : F) :
    (bwPolyB σ u).eval (C x) = bwEvalXB σ u x := by
  simp only [bwPolyB, bwEvalXB, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, C_pow]

theorem degree_bwEvalZA_lt (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) :
    (bwEvalZA σ u β).degree < (t + 1 : ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i _
  exact (degree_C_mul_X_pow_le _ _).trans_lt (Nat.cast_lt.mpr i.2)

theorem degree_bwEvalZB_lt (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) :
    (bwEvalZB σ u β).degree < (t + d : ℕ) := by
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro j _
  exact (degree_C_mul_X_pow_le _ _).trans_lt (Nat.cast_lt.mpr j.2)

theorem coeff_bwEvalZA_last (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) :
    (bwEvalZA σ u β).coeff t = (bwDelta σ u).eval β := by
  rw [bwEvalZA, finsetSum_coeff]
  rw [Finset.sum_eq_single (Fin.last t)]
  · simp [bwCoeffA]
  · intro i _ hne
    have hlt : (i : ℕ) ≠ t := fun h => hne (Fin.ext h)
    simp [hlt.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bwEvalZA_ne_zero_of_delta_ne (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) {β : F}
    (hβ : (bwDelta σ u).eval β ≠ 0) : bwEvalZA σ u β ≠ 0 := by
  intro h0
  have := coeff_bwEvalZA_last σ u β
  rw [h0, coeff_zero] at this
  exact hβ this.symm

/-- On every point `x ∈ D₂`, the Cramer solution satisfies `w(Z)(x) * A(Z, x) = B(Z, x)`. -/
theorem bwSol_eq_on_domain (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) {x : F}
    (hx : x ∈ D₂) : curvePoly u x * bwEvalXA σ u x = bwEvalXB σ u x := by
  let r := σ.symm ⟨x, hx⟩
  have hσr : (σ r : F) = x := congrArg Subtype.val (σ.apply_symm_apply ⟨x, hx⟩)
  have hmul := congrFun ((bwMonicMatrix σ u).mulVec_cramer (bwMonicRhs σ u)) r
  rw [bwMonicMatrix, bwMatrix_mulVec, Pi.smul_apply, smul_eq_mul, bwMonicRhs, hσr] at hmul
  have hA : bwEvalXA σ u x =
      (∑ i : Fin t, bwSol σ u (Sum.inl i) * C (x ^ (i : ℕ))) + bwDelta σ u * C (x ^ t) := by
    rw [bwEvalXA, Fin.sum_univ_castSucc]
    simp [bwCoeffA, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hB : bwEvalXB σ u x = ∑ j : Fin (t + d), bwSol σ u (Sum.inr j) * C (x ^ (j : ℕ)) := rfl
  simp only [one_mul, ← C_pow] at hmul
  rw [hA, hB, mul_add]
  have hmul' : curvePoly u x * ∑ i : Fin t, bwSol σ u (Sum.inl i) * C (x ^ (i : ℕ)) -
      ∑ j : Fin (t + d), bwSol σ u (Sum.inr j) * C (x ^ (j : ℕ)) =
      -(bwDelta σ u * (curvePoly u x * C (x ^ t))) := by
    simpa [bwDelta, bwMonicMatrix, bwSol, mul_neg] using hmul
  linear_combination hmul'

/-- Determinant of `M₀(β)` vanishes iff there is a nonzero solution `(A, B)` on `D₂`
with `deg A < t` and `deg B < t + d`. -/
theorem eval_bwDelta_eq_zero_iff (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (β : F) :
    (bwDelta σ u).eval β = 0 ↔
      ∃ A B : F[X], A.degree < t ∧ B.degree < (t + d : ℕ) ∧ (A ≠ 0 ∨ B ≠ 0) ∧
        ∀ x ∈ D₂, (∑ k : Fin m, β ^ (k : ℕ) * u k x) * A.eval x = B.eval x := by
  rw [bwDelta, bwMonicMatrix, ← coe_evalRingHom, RingHom.map_det, map_bwMatrix,
    det_bwMatrix_eq_zero_iff]
  refine exists_congr fun A => exists_congr fun B => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    have hr := h (σ.symm ⟨x, hx⟩)
    have hσ : (σ (σ.symm ⟨x, hx⟩) : F) = x := congrArg Subtype.val (σ.apply_symm_apply ⟨x, hx⟩)
    simpa [hσ, eval_curvePoly] using hr
  · intro h r
    simpa [eval_curvePoly] using h (σ r) (σ r).2

/-- The `(1 + (2 * t + d)) × (1 + (2 * t + d))` augmented matrix obtained by adding
row `y` (top) and column `a_t` (left) to `M₀(Z)`. -/
noncomputable def bwAugMatrix (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (y : F) :
    Matrix (Unit ⊕ (Fin t ⊕ Fin (t + d))) (Unit ⊕ (Fin t ⊕ Fin (t + d))) F[X] :=
  Matrix.fromBlocks
    (Matrix.of fun _ _ => curvePoly u y * C (y ^ t))
    (Matrix.of fun _ => Sum.elim (fun i => curvePoly u y * C (y ^ (i : ℕ))) fun j => -C (y ^ (j : ℕ)))
    (Matrix.of fun r _ => curvePoly u (σ r) * C ((σ r : F) ^ t))
    (bwMonicMatrix σ u)

theorem natDegree_det_bwAugMatrix_le (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (y : F) :
    (bwAugMatrix σ u y).det.natDegree ≤ (t + 1) * (m - 1) := by
  let c : Unit ⊕ (Fin t ⊕ Fin (t + d)) → ℕ :=
    Sum.elim (fun _ => m - 1) (Sum.elim (fun _ => m - 1) (fun _ => 0))
  have hsum : ∑ j, c j = (t + 1) * (m - 1) := by
    simp only [c, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, Fintype.card_unit, Fintype.card_fin, smul_eq_mul,
      one_mul, mul_zero, add_zero]
    ring
  rw [← hsum]
  refine natDegree_det_le _ c ?_
  rintro (_ | r) (_ | (i | j))
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₁₁, Matrix.of_apply, c, Sum.elim_inl]
    exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u y)
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inl, c,
      Sum.elim_inr]
    exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u y)
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inr, c,
      ← C_neg, natDegree_C, le_refl]
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, c, Sum.elim_inl]
    exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u (σ r))
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₂₂, bwMonicMatrix, bwMatrix, Matrix.of_apply,
      Sum.elim_inl, c, Sum.elim_inr, ← C_pow]
    exact (natDegree_mul_C_le _ _).trans (natDegree_curvePoly_le u (σ r))
  · simp only [bwAugMatrix, Matrix.fromBlocks_apply₂₂, bwMonicMatrix, bwMatrix, Matrix.of_apply,
      Sum.elim_inr, one_mul, ← C_pow, ← C_neg, natDegree_C, c, le_refl]

/-- Evaluating `det (bwAugMatrix σ u y)` at `β` vanishes whenever there is a nonzero
solution `(A, B)` of `w(β)(x) * A(x) = B(x)` on `insert y D₂`. -/
theorem eval_det_bwAugMatrix_eq_zero (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (y β : F)
    {A B : F[X]} (hA : A.degree < (t + 1 : ℕ)) (hB : B.degree < (t + d : ℕ)) (hne : A ≠ 0 ∨ B ≠ 0)
    (hy : (∑ k : Fin m, β ^ (k : ℕ) * u k y) * A.eval y = B.eval y)
    (hD₂ : ∀ x ∈ D₂, (∑ k : Fin m, β ^ (k : ℕ) * u k x) * A.eval x = B.eval x) :
    (bwAugMatrix σ u y).det.eval β = 0 := by
  rw [← coe_evalRingHom, RingHom.map_det, ← Matrix.exists_mulVec_eq_zero_iff]
  obtain ⟨f, hf0, hfe⟩ := exists_coeffs_of_poly hA
  obtain ⟨g, hg0, hge⟩ := exists_coeffs_of_poly hB
  let v : Unit ⊕ (Fin t ⊕ Fin (t + d)) → F :=
    Sum.elim (fun _ => f (Fin.last t)) (Sum.elim (fun i => f i.castSucc) g)
  refine ⟨v, fun hv => ?_, funext fun row => ?_⟩
  · have hf : f = 0 := funext fun i => by
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · exact congrFun hv (Sum.inl ())
      · exact congrFun hv (Sum.inr (Sum.inl i'))
    have hg : g = 0 := funext fun j => congrFun hv (Sum.inr (Sum.inr j))
    exact hne.elim (fun hA0 => hA0 (hf0.mp hf)) fun hB0 => hB0 (hg0.mp hg)
  · rcases row with ⟨⟩ | r
    · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
        RingHom.mapMatrix_apply, Matrix.map_apply, bwAugMatrix, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, v,
        coe_evalRingHom, eval_mul, eval_C, eval_neg, eval_curvePoly, Pi.zero_apply]
      have hAsum : A.eval y =
          (∑ i : Fin t, f i.castSucc * y ^ (i : ℕ)) + f (Fin.last t) * y ^ t := by
        rw [hfe, Fin.sum_univ_castSucc]
        rfl
      have hBsum : B.eval y = ∑ j : Fin (t + d), g j * y ^ (j : ℕ) := hge y
      have hsum1 : ∑ i : Fin t, (∑ k : Fin m, β ^ (k : ℕ) * u k y) * y ^ (i : ℕ) * f i.castSucc =
          (∑ k : Fin m, β ^ (k : ℕ) * u k y) * ∑ i : Fin t, f i.castSucc * y ^ (i : ℕ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      have hsum2 : ∑ j : Fin (t + d), -(y ^ (j : ℕ)) * g j = -B.eval y := by
        rw [hBsum, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum1, hsum2]
      linear_combination hy - (∑ k : Fin m, β ^ (k : ℕ) * u k y) * hAsum
    · simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique,
        RingHom.mapMatrix_apply, Matrix.map_apply, bwAugMatrix, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, bwMonicMatrix, bwMatrix, Matrix.of_apply, Sum.elim_inl,
        Sum.elim_inr, v, coe_evalRingHom, eval_mul, eval_C, eval_neg, eval_pow,
        eval_curvePoly, one_mul, Pi.zero_apply]
      have hAsum : A.eval (σ r : F) =
          (∑ i : Fin t, f i.castSucc * (σ r : F) ^ (i : ℕ)) + f (Fin.last t) * (σ r : F) ^ t := by
        rw [hfe, Fin.sum_univ_castSucc]
        rfl
      have hBsum : B.eval (σ r : F) = ∑ j : Fin (t + d), g j * (σ r : F) ^ (j : ℕ) := hge (σ r : F)
      have hsum1 : ∑ i : Fin t,
          (∑ k : Fin m, β ^ (k : ℕ) * u k (σ r)) * (σ r : F) ^ (i : ℕ) * f i.castSucc =
          (∑ k : Fin m, β ^ (k : ℕ) * u k (σ r)) *
            ∑ i : Fin t, f i.castSucc * (σ r : F) ^ (i : ℕ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      have hsum2 : ∑ j : Fin (t + d), -((σ r : F) ^ (j : ℕ)) * g j = -B.eval (σ r : F) := by
        rw [hBsum, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum1, hsum2]
      linear_combination hD₂ (σ r) (σ r).2 - (∑ k : Fin m, β ^ (k : ℕ) * u k (σ r)) * hAsum

/-- If `det (bwAugMatrix σ u y) = 0` and `bwDelta σ u ≠ 0`, then the Cramer solution
from `D₂` also satisfies the Berlekamp–Welch equation at `y`. -/
theorem bwSol_eq_at_of_det_aug_eq_zero (σ : Fin t ⊕ Fin (t + d) ≃ D₂) (u : Fin m → F → F) (y : F)
    (hΔ : bwDelta σ u ≠ 0) (haug : (bwAugMatrix σ u y).det = 0) :
    curvePoly u y * bwEvalXA σ u y = bwEvalXB σ u y := by
  let v : Unit ⊕ (Fin t ⊕ Fin (t + d)) → F[X] :=
    Sum.elim (fun _ => bwDelta σ u) (bwSol σ u)
  let h_y : F[X] := curvePoly u y * bwEvalXA σ u y - bwEvalXB σ u y
  -- `bwAugMatrix σ u y * v` vanishes on all `D₂` rows and equals `h_y` on the top row `inl ()`.
  have hMv : (bwAugMatrix σ u y).mulVec v = Pi.single (Sum.inl ()) h_y := by
    funext row
    rcases row with ⟨⟩ | r
    · simp only [Pi.single_eq_same, h_y, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Fintype.sum_unique, bwAugMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, v]
      have hA : bwEvalXA σ u y =
          (∑ i : Fin t, bwSol σ u (Sum.inl i) * C (y ^ (i : ℕ))) + bwDelta σ u * C (y ^ t) := by
        rw [bwEvalXA, Fin.sum_univ_castSucc]
        simp [bwCoeffA, Fin.lastCases_castSucc, Fin.lastCases_last]
      have hB : bwEvalXB σ u y = ∑ j : Fin (t + d), bwSol σ u (Sum.inr j) * C (y ^ (j : ℕ)) := rfl
      have hsum1 : ∑ i : Fin t, curvePoly u y * C (y ^ (i : ℕ)) * bwSol σ u (Sum.inl i) =
          curvePoly u y * ∑ i : Fin t, bwSol σ u (Sum.inl i) * C (y ^ (i : ℕ)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      have hsum2 : ∑ j : Fin (t + d), -C (y ^ (j : ℕ)) * bwSol σ u (Sum.inr j) = -bwEvalXB σ u y := by
        rw [hB, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum1, hsum2, hA]
      ring
    · rw [Pi.single_eq_of_ne (Sum.inr_ne_inl), Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
      simp only [Fintype.sum_unique, bwAugMatrix, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, v]
      have hmul := congrFun ((bwMonicMatrix σ u).mulVec_cramer (bwMonicRhs σ u)) r
      have hmul' : ∑ x : Fin t ⊕ Fin (t + d), bwMonicMatrix σ u r x * bwSol σ u x =
          bwDelta σ u * bwMonicRhs σ u r := hmul
      rw [hmul']
      simp only [bwMonicRhs]
      ring
  -- Left-multiply by `adjugate`: `0 = adj * (M * v) = adj * Pi.single (inl ()) h_y`.
  have hadj0 : (bwAugMatrix σ u y).adjugate (Sum.inl ()) (Sum.inl ()) * h_y = 0 := by
    have h1 : (bwAugMatrix σ u y).adjugate.mulVec ((bwAugMatrix σ u y).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, haug, zero_smul, Matrix.zero_mulVec]
    rw [hMv] at h1
    have h2 := congrFun h1 (Sum.inl ())
    simpa [Matrix.mulVec_single] using h2
  -- The `(inl (), inl ())` entry of `adjugate (bwAugMatrix σ u y)` is `bwDelta σ u`.
  have hadj_eq : (bwAugMatrix σ u y).adjugate (Sum.inl ()) (Sum.inl ()) = bwDelta σ u := by
    rw [Matrix.adjugate_apply]
    have hupd : (bwAugMatrix σ u y).updateRow (Sum.inl ()) (Pi.single (Sum.inl ()) 1) =
        Matrix.fromBlocks (1 : Matrix Unit Unit F[X]) 0
          (Matrix.of fun r _ => curvePoly u (σ r) * C ((σ r : F) ^ t))
          (bwMonicMatrix σ u) := by
      ext (⟨⟩ | r) (⟨⟩ | col) <;> simp [bwAugMatrix, Matrix.updateRow_apply]
    rw [hupd, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, bwDelta]
  rw [hadj_eq] at hadj0
  exact sub_eq_zero.mp ((mul_eq_zero.mp hadj0).resolve_left hΔ)

end MonicSystem

/-! ## Factoring out constant roots in `(F[Z])[X]` -/

section FactorRoots

/-- The monic polynomial `∏ x ∈ S, (X - C (C x))` over `F[Z]`. -/
noncomputable def vanishingOverPoly (S : Finset F) : (F[X])[X] :=
  ∏ x ∈ S, (X - C (C x))

theorem monic_vanishingOverPoly (S : Finset F) : (vanishingOverPoly S).Monic :=
  monic_prod_of_monic _ _ fun x _ => monic_X_sub_C (C x)

theorem natDegree_vanishingOverPoly (S : Finset F) :
    (vanishingOverPoly S).natDegree = S.card := by
  rw [vanishingOverPoly, natDegree_prod_of_monic _ _ fun x _ => monic_X_sub_C (C x)]
  simp

theorem eval_vanishingOverPoly (S : Finset F) (x : F) :
    (vanishingOverPoly S).eval (C x) = C (∏ y ∈ S, (x - y)) := by
  rw [vanishingOverPoly, eval_prod, map_prod]
  refine Finset.prod_congr rfl fun y _ => ?_
  simp

/-- If `P : (F[Z])[X]` vanishes at `C x` for every `x ∈ S`, then `vanishingOverPoly S ∣ P`. -/
theorem vanishingOverPoly_dvd [DecidableEq F] {S : Finset F} {P : (F[X])[X]}
    (h : ∀ x ∈ S, P.eval (C x) = 0) : vanishingOverPoly S ∣ P := by
  induction S using Finset.induction_on generalizing P with
  | empty => simp [vanishingOverPoly]
  | @insert a S ha ih =>
    have hdvd_a : X - C (C a) ∣ P := dvd_iff_isRoot.mpr (h a (mem_insert_self a S))
    obtain ⟨Q, rfl⟩ := hdvd_a
    have hQ : ∀ x ∈ S, Q.eval (C x) = 0 := by
      intro x hx
      have h0 := h x (mem_insert_of_mem hx)
      rw [eval_mul, eval_sub, eval_X, eval_C, ← C_sub] at h0
      have hne : (C (x - a) : F[X]) ≠ 0 := by
        rw [ne_eq, C_eq_zero, sub_eq_zero]
        exact fun hxa => ha (hxa ▸ hx)
      exact (mul_eq_zero.mp h0).resolve_left hne
    obtain ⟨R, rfl⟩ := ih hQ
    refine ⟨R, ?_⟩
    simp only [vanishingOverPoly, prod_insert ha]
    ring

end FactorRoots

/-! ## Error sets and the linear-threshold correlated agreement theorem -/

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

end UniqueDecoding

open UniqueDecoding Finset Polynomial

/-- **Correlated agreement for curves over Reed–Solomon codes holds in the
unique-decoding regime**, with linear threshold `udThreshold n e m = (m - 1) * (n + e)`.

Let `2 * e + d ≤ D.card`. If for more than `(m - 1) * (D.card + e)` values of `β`
the word `∑ k, β ^ k * u k` differs from some polynomial of degree below `d` at
no more than `e` points of `D`, then there are polynomials `v k` of degree below
`d` such that the points of `D` where some `u k` differs from `v k` number at
most `e`. The field may be infinite. -/
theorem curveCA_udThreshold (F : Type*) [Field F] [DecidableEq F] : CurveCA F udThreshold := by
  intro D d e m hD u G hG hgood
  -- Handle `m = 0`, `m = 1`, and `D = ∅` directly.
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨fun k => k.elim0, fun k => k.elim0, by simp⟩
  rcases Nat.eq_zero_or_pos D.card with hD0 | hDpos
  · rw [card_eq_zero.mp hD0]
    exact ⟨fun _ => 0, fun _ => by simp, by simp⟩
  unfold udThreshold at hG
  by_cases hm1 : m = 1
  · subst hm1
    have hGpos : 0 < G.card := by omega
    obtain ⟨β, hβ⟩ := card_pos.mp hGpos
    obtain ⟨p, hp, hpE⟩ := hgood β hβ
    refine ⟨fun _ => p, fun _ => hp, ?_⟩
    refine (card_le_card fun x hx => ?_).trans hpE
    obtain ⟨hxD, k, hk⟩ := mem_filter.mp hx
    fin_cases k
    exact mem_filter.mpr ⟨hxD, by simpa using hk⟩
  have hm2 : 2 ≤ m := by omega
  choose! p hp hpE using hgood
  change ∀ β ∈ G, (errSet D u β (p β)).card ≤ e at hpE
  -- A parameter `z₀ ∈ G` whose error set `S` is largest, with `t := S.card ≤ e`.
  obtain ⟨z₀, hz₀, hmax⟩ := exists_max_image G (fun β => (errSet D u β (p β)).card)
    (card_pos.mp (by omega))
  set S : Finset F := errSet D u z₀ (p z₀)
  set t : ℕ := S.card
  have hte : t ≤ e := hpE z₀ hz₀
  have hE : ∀ β ∈ G, (errSet D u β (p β)).card ≤ t := hmax
  -- Case `t = 0`: every `β ∈ G` has no errors, so interpolate through `m` of them.
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · have hm_le : m ≤ G.card := by
      have : m - 1 ≤ (m - 1) * (D.card + e) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    obtain ⟨b, hb, hbmem⟩ := ProximityGap.exists_injective_of_le_card hm_le
    obtain ⟨v, hv, hvu⟩ := exists_interpolant_poly hb (fun i => p (b i))
      fun i => hp _ (hbmem i)
    refine ⟨v, hv, ?_⟩
    have hempty : (D.filter fun x => ∃ k, u k x ≠ (v k).eval x) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hxD hne
      obtain ⟨k, hk⟩ := hne
      refine hk (hvu u x (fun i => ?_) k)
      have h0 : errSet D u (b i) (p (b i)) = ∅ :=
        card_eq_zero.mp (Nat.le_zero.mp (ht0 ▸ hE _ (hbmem i)))
      by_contra hne'
      have hmem : x ∈ errSet D u (b i) (p (b i)) := mem_filter.mpr ⟨hxD, hne'⟩
      rw [h0] at hmem
      exact notMem_empty x hmem
    rw [hempty, card_empty]
    exact Nat.zero_le e
  -- Case `t ≥ 1`: pick `D₂ ⊇ S` of size `2 * t + d` and form the monic system `M₀(Z)`.
  obtain ⟨D₂, hSD₂, hD₂D, hD₂card⟩ :=
    exists_subsuperset_card_eq (errSet_subset D u z₀ (p z₀)) (by omega : S.card ≤ 2 * t + d)
      (by omega : 2 * t + d ≤ D.card)
  have hcardeq : Fintype.card (Fin t ⊕ Fin (t + d)) = Fintype.card D₂ := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hD₂card]
    omega
  let σ := Fintype.equivOfCardEq hcardeq
  have hS₂ : errSet D₂ u z₀ (p z₀) = S :=
    subset_antisymm (errSet_mono hD₂D _ _ _) fun x hx =>
      mem_filter.mpr ⟨hSD₂ hx, (mem_filter.mp hx).2⟩
  -- Step 1: `bwDelta σ u` does not vanish at `z₀`, hence is nonzero.
  have hΔz₀ : (bwDelta σ u).eval z₀ ≠ 0 := by
    intro h0
    obtain ⟨A, B, hA, hB, hne, h⟩ := (eval_bwDelta_eq_zero_iff σ u z₀).mp h0
    have hA' : A.degree < (t + 1 : ℕ) := hA.trans (Nat.cast_lt.mpr (Nat.lt_succ_self t))
    obtain ⟨hBA, hvan⟩ := eq_mul_of_agree (by omega : 2 * t + d ≤ D₂.card) (hp z₀ hz₀)
      (show (errSet D₂ u z₀ (p z₀)).card ≤ t by rw [hS₂]) hA' hB h
    have hA0 : A ≠ 0 := fun hA0 =>
      hne.elim (fun h => h hA0) fun h => h (by rw [hBA, hA0, zero_mul])
    have hle : S.card ≤ t - 1 := by
      have hdeg' : A.degree < ((t - 1) + 1 : ℕ) := by
        rwa [Nat.sub_add_cancel htpos]
      exact card_le_of_vanishing hA0 hdeg' fun x hx =>
        hvan x (hSD₂ hx) (mem_filter.mp hx).2
    omega
  have hΔne : bwDelta σ u ≠ 0 := fun h0 => hΔz₀ (by rw [h0, eval_zero])
  -- Step 2: `curvePoly u x * bwEvalXA σ u x = bwEvalXB σ u x` for ALL `x ∈ D`.
  have hEqD : ∀ x ∈ D, curvePoly u x * bwEvalXA σ u x = bwEvalXB σ u x := by
    intro y hyD
    by_cases hyD₂ : y ∈ D₂
    · exact bwSol_eq_on_domain σ u hyD₂
    · have haug0 : (bwAugMatrix σ u y).det = 0 := by
        refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ G (fun β hβ => ?_) ?_
        · obtain ⟨Eβ, hEβ0, hEβdeg, hEβvan⟩ := exists_vanishing (hE β hβ)
          refine eval_det_bwAugMatrix_eq_zero σ u y β hEβdeg (degree_mul_lt hEβdeg (hp β hβ))
            (Or.inl hEβ0) ?_ fun x hx => ?_
          · by_cases hye : ∑ k : Fin m, β ^ (k : ℕ) * u k y = (p β).eval y
            · rw [hye, eval_mul, mul_comm]
            · rw [eval_mul, hEβvan y (mem_filter.mpr ⟨hyD, hye⟩), mul_zero, zero_mul]
          · by_cases hxe : ∑ k : Fin m, β ^ (k : ℕ) * u k x = (p β).eval x
            · rw [hxe, eval_mul, mul_comm]
            · rw [eval_mul, hEβvan x (mem_filter.mpr ⟨hD₂D hx, hxe⟩), mul_zero, zero_mul]
        · have hdeg := natDegree_det_bwAugMatrix_le σ u y
          have hle1 : (t + 1) * (m - 1) ≤ (m - 1) * (D.card + e) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left _ (by omega)
          omega
      exact bwSol_eq_at_of_det_aug_eq_zero σ u y hΔne haug0
  -- For every `β ∈ G` with `Δ(β) ≠ 0`, `bwEvalZA σ u β` vanishes on `errSet D u β (p β)`
  -- and `|errSet D u β (p β)| = t`.
  have hβ_props : ∀ β ∈ G, (bwDelta σ u).eval β ≠ 0 →
      (errSet D u β (p β)).card = t ∧
      ∀ x ∈ errSet D u β (p β), (bwEvalZA σ u β).eval x = 0 := by
    intro β hβ hΔβ
    have hEqβ : ∀ x ∈ D, (∑ k : Fin m, β ^ (k : ℕ) * u k x) * (bwEvalZA σ u β).eval x =
        (bwEvalZB σ u β).eval x := by
      intro x hxD
      have h := congrArg (Polynomial.eval β) (hEqD x hxD)
      simpa only [eval_mul, eval_curvePoly, eval_bwEvalXA, eval_bwEvalXB] using h
    obtain ⟨_, hvan⟩ := eq_mul_of_agree (by omega : 2 * t + d ≤ D.card) (hp β hβ) (hE β hβ)
      (degree_bwEvalZA_lt σ u β) (degree_bwEvalZB_lt σ u β) hEqβ
    refine ⟨?_, fun x hx => hvan x (mem_filter.mp hx).1 (mem_filter.mp hx).2⟩
    by_contra hne_card
    have hlt : (errSet D u β (p β)).card ≤ t - 1 := by
      have := hE β hβ
      omega
    obtain ⟨Eβ, hEβ0, hEβdeg, hEβvan⟩ := exists_vanishing hlt
    have hEβdeg' : Eβ.degree < t := by
      rwa [Nat.sub_add_cancel htpos] at hEβdeg
    have hEpdeg : (Eβ * p β).degree < (t + d : ℕ) :=
      degree_mul_lt (hEβdeg'.trans (Nat.cast_lt.mpr (Nat.lt_succ_self t))) (hp β hβ)
    refine hΔβ ((eval_bwDelta_eq_zero_iff σ u β).mpr
      ⟨Eβ, Eβ * p β, hEβdeg', hEpdeg, Or.inl hEβ0, fun x hxD₂ => ?_⟩)
    by_cases hxe : ∑ k : Fin m, β ^ (k : ℕ) * u k x = (p β).eval x
    · rw [hxe, eval_mul, mul_comm]
    · rw [eval_mul, hEβvan x (mem_filter.mpr ⟨hD₂D hxD₂, hxe⟩), mul_zero, zero_mul]
  -- Step 3: Let `S* = {x ∈ D | bwEvalXA σ u x = 0}`, with `s = S*.card`.
  set Sstar : Finset F := D.filter fun x => bwEvalXA σ u x = 0
  set s : ℕ := Sstar.card
  -- `S* ⊆ S`, so `s ≤ t`.
  have hSstar_sub_S : Sstar ⊆ S := by
    intro x hx
    obtain ⟨hxD, hx0⟩ := mem_filter.mp hx
    by_contra hxS
    have hA0 := bwEvalZA_ne_zero_of_delta_ne σ u hΔz₀
    have hvan : ∀ y ∈ insert x S, (bwEvalZA σ u z₀).eval y = 0 := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hyS
      · rw [← eval_bwEvalXA, hx0, eval_zero]
      · exact (hβ_props z₀ hz₀ hΔz₀).2 y hyS
    have hle := card_le_of_vanishing hA0 (degree_bwEvalZA_lt σ u z₀) hvan
    rw [card_insert_of_notMem hxS] at hle
    omega
  have hst : s ≤ t := card_le_card hSstar_sub_S
  -- Filter `G' = {β ∈ G | Δ(β) ≠ 0}`.
  set G' : Finset F := G.filter fun β => (bwDelta σ u).eval β ≠ 0
  have hGbad : (G.filter fun β => ¬ (bwDelta σ u).eval β ≠ 0).card ≤ t * (m - 1) := by
    have hsub : (G.filter fun β => ¬ (bwDelta σ u).eval β ≠ 0) ⊆ (bwDelta σ u).roots.toFinset := by
      intro β hβ
      rw [mem_filter, not_not] at hβ
      rw [Multiset.mem_toFinset, mem_roots hΔne, IsRoot.def]
      exact hβ.2
    exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (natDegree_bwDelta_le σ u)))
  have hGsplit := card_filter_add_card_filter_not (s := G) fun β => (bwDelta σ u).eval β ≠ 0
  -- For every `β ∈ G'`, `S* ⊆ errSet D u β (p β)`.
  have hSstar_sub_E : ∀ β ∈ G', Sstar ⊆ errSet D u β (p β) := by
    intro β hβ x hx
    obtain ⟨hβG, hΔβ⟩ := mem_filter.mp hβ
    obtain ⟨hcardβ, hvanβ⟩ := hβ_props β hβG hΔβ
    by_contra hxE
    have hA0 := bwEvalZA_ne_zero_of_delta_ne σ u hΔβ
    have hvan : ∀ y ∈ insert x (errSet D u β (p β)), (bwEvalZA σ u β).eval y = 0 := by
      intro y hy
      rcases mem_insert.mp hy with rfl | hyE
      · rw [← eval_bwEvalXA, (mem_filter.mp hx).2, eval_zero]
      · exact hvanβ y hyE
    have hle := card_le_of_vanishing hA0 (degree_bwEvalZA_lt σ u β) hvan
    rw [card_insert_of_notMem hxE, hcardβ] at hle
    omega
  -- Split on `s = t` vs `s < t`.
  rcases hst.eq_or_lt with hst_eq | hst_lt
  · -- Case `s = t`: `S* = S`, so every `β ∈ G'` has `errSet D u β (p β) = S`, and `|G'| ≥ m`.
    have hSstar_eq : Sstar = S := eq_of_subset_of_card_le hSstar_sub_S hst_eq.ge
    have hm_le : m ≤ G'.card := by
      have h1 : (t + 1) * (m - 1) ≤ (m - 1) * (D.card + e) := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      have h2 : (t + 1) * (m - 1) = t * (m - 1) + (m - 1) := by ring
      have hGsplit' : G'.card + (G.filter fun β => ¬ (bwDelta σ u).eval β ≠ 0).card = G.card :=
        hGsplit
      omega
    obtain ⟨b, hb, hbmem⟩ := ProximityGap.exists_injective_of_le_card hm_le
    obtain ⟨v, hv, hvu⟩ := exists_interpolant_poly hb (fun i => p (b i))
      fun i => hp _ (mem_filter.mp (hbmem i)).1
    refine ⟨v, hv, (card_le_card fun x hx => ?_).trans hte⟩
    obtain ⟨hxD, k, hk⟩ := mem_filter.mp hx
    by_contra hxS
    refine hk (hvu u x (fun i => ?_) k)
    by_contra hne
    have hEeq : errSet D u (b i) (p (b i)) = S := by
      have hsub := hSstar_eq ▸ hSstar_sub_E (b i) (hbmem i)
      have hbi := mem_filter.mp (hbmem i)
      exact (eq_of_subset_of_card_le hsub (hβ_props _ hbi.1 hbi.2).1.le).symm
    exact hxS (hEeq ▸ mem_filter.mpr ⟨hxD, hne⟩)
  · -- Case `s < t`: factor out `vanishingOverPoly S*`, reduce to `D' = D \ S*` and `t' = t - s`,
    -- and derive a contradiction by double counting pairs `(x, β) ∈ D' × G'`.
    exfalso
    set t' : ℕ := t - s
    have ht'pos : 0 < t' := by omega
    set D' : Finset F := D \ Sstar
    set S' : Finset F := S \ Sstar
    have hD'card : D'.card = D.card - s := card_sdiff_of_subset (filter_subset _ _)
    have hS'card : S'.card = t' := card_sdiff_of_subset hSstar_sub_S
    have hS'subD' : S' ⊆ D' := sdiff_subset_sdiff (errSet_subset D u z₀ (p z₀)) (Subset.refl _)
    -- Divide `bwPolyA` and `bwPolyB` by `A₀ = vanishingOverPoly S*` in `(F[Z])[X]`.
    let A₀ : (F[X])[X] := vanishingOverPoly Sstar
    have hA₀monic : A₀.Monic := monic_vanishingOverPoly Sstar
    have hA₀deg : A₀.natDegree = s := natDegree_vanishingOverPoly Sstar
    obtain ⟨Atilde, hAtilde⟩ := vanishingOverPoly_dvd (S := Sstar) (P := bwPolyA σ u) fun x hx => by
      rw [eval_bwPolyA]
      exact (mem_filter.mp hx).2
    obtain ⟨Btilde, hBtilde⟩ := vanishingOverPoly_dvd (S := Sstar) (P := bwPolyB σ u) fun x hx => by
      rw [eval_bwPolyB, ← hEqD x (mem_filter.mp hx).1, (mem_filter.mp hx).2, mul_zero]
    -- Degree bounds and leading coefficient of `Atilde`, `Btilde`.
    have hPolyA_coeff : (bwPolyA σ u).coeff t = bwDelta σ u := by
      rw [bwPolyA, finsetSum_coeff, Finset.sum_eq_single (Fin.last t)]
      · simp [bwCoeffA]
      · intro i _ hne
        have hlt : (i : ℕ) ≠ t := fun h => hne (Fin.ext h)
        simp [hlt.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hPolyA_deg : (bwPolyA σ u).natDegree = t := by
      have hle : (bwPolyA σ u).natDegree ≤ t :=
        natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_X_pow_le _ _).trans (by omega)
      exact le_antisymm hle (le_natDegree_of_ne_zero (hPolyA_coeff.symm ▸ hΔne))
    have hAtilde_ne : Atilde ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hAtilde
      have : (bwPolyA σ u).coeff t = 0 := by rw [hAtilde, coeff_zero]
      exact hΔne (hPolyA_coeff ▸ this)
    have hAtilde_deg : Atilde.natDegree = t' := by
      have hmul := hA₀monic.natDegree_mul' hAtilde_ne
      rw [← hAtilde, hPolyA_deg, hA₀deg] at hmul
      omega
    have hAtilde_lc : Atilde.coeff t' = bwDelta σ u := by
      have hlc : (A₀ * Atilde).leadingCoeff = Atilde.leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, hA₀monic.leadingCoeff, one_mul]
      rw [← hAtilde, leadingCoeff, leadingCoeff, hPolyA_deg, hAtilde_deg] at hlc
      exact hlc.symm.trans hPolyA_coeff
    have hBtilde_deg : Btilde.degree < (t' + d : ℕ) := by
      have hBdeg : (bwPolyB σ u).degree < (t + d : ℕ) := by
        refine (degree_sum_le _ _).trans_lt ?_
        rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
        intro j _
        exact (degree_C_mul_X_pow_le _ _).trans_lt (Nat.cast_lt.mpr j.2)
      by_cases hB0 : Btilde = 0
      · simp [hB0]
      · have hmul := hA₀monic.natDegree_mul' hB0
        have hBne : bwPolyB σ u ≠ 0 := by
          rw [hBtilde]
          exact mul_ne_zero hA₀monic.ne_zero hB0
        have hBnat := (natDegree_lt_iff_degree_lt hBne).mpr hBdeg
        rw [← hBtilde, hA₀deg] at hmul
        rw [← natDegree_lt_iff_degree_lt hB0]
        omega
    -- On `D'`, `A₀(x) ≠ 0`, so `curvePoly u x * Atilde(x) = Btilde(x)` and `Atilde(x) ≠ 0`.
    have hA₀_ne : ∀ x ∈ D', A₀.eval (C x) ≠ 0 := by
      intro x hx
      rw [eval_vanishingOverPoly, ne_eq, C_eq_zero]
      exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr fun hxy =>
        (mem_sdiff.mp hx).2 (hxy ▸ hy)
    have hTildeEq : ∀ x ∈ D', curvePoly u x * Atilde.eval (C x) = Btilde.eval (C x) := by
      intro x hx
      have h := hEqD x (mem_sdiff.mp hx).1
      rw [← eval_bwPolyA, ← eval_bwPolyB, hAtilde, hBtilde, eval_mul, eval_mul] at h
      have h' : A₀.eval (C x) * (curvePoly u x * Atilde.eval (C x) - Btilde.eval (C x)) = 0 := by
        rw [mul_sub, ← mul_assoc, mul_comm (A₀.eval (C x)), mul_assoc, h, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (hA₀_ne x hx))
    have hTildeNe : ∀ x ∈ D', Atilde.eval (C x) ≠ 0 := by
      intro x hx h0
      have hx0 : bwEvalXA σ u x = 0 := by
        rw [← eval_bwPolyA, hAtilde, eval_mul, h0, mul_zero]
      exact (mem_sdiff.mp hx).2 (mem_filter.mpr ⟨(mem_sdiff.mp hx).1, hx0⟩)
    -- Pick a subdomain `D'₂ ⊆ D'` of size `2 * t' + d` containing `S'`, and solve `M'₀(Z)`.
    obtain ⟨D'₂, hS'D'₂, hD'₂D', hD'₂card⟩ :=
      exists_subsuperset_card_eq hS'subD' (by omega : S'.card ≤ 2 * t' + d)
        (by omega : 2 * t' + d ≤ D'.card)
    have hcardeq' : Fintype.card (Fin t' ⊕ Fin (t' + d)) = Fintype.card D'₂ := by
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, hD'₂card]
      omega
    let σ' := Fintype.equivOfCardEq hcardeq'
    have hD'₂D : D'₂ ⊆ D := hD'₂D'.trans sdiff_subset
    have hS'₂ : errSet D'₂ u z₀ (p z₀) = S' := by
      refine subset_antisymm ?_ fun x hx => mem_filter.mpr ⟨hS'D'₂ hx, (mem_filter.mp (mem_sdiff.mp hx).1).2⟩
      intro x hx
      have hxD'₂ := (mem_filter.mp hx).1
      have hxe := (mem_filter.mp hx).2
      exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hD'₂D hxD'₂, hxe⟩, (mem_sdiff.mp (hD'₂D' hxD'₂)).2⟩
    have hΔ'z₀ : (bwDelta σ' u).eval z₀ ≠ 0 := by
      intro h0
      obtain ⟨A, B, hA, hB, hne, h⟩ := (eval_bwDelta_eq_zero_iff σ' u z₀).mp h0
      have hA' : A.degree < (t' + 1 : ℕ) := hA.trans (Nat.cast_lt.mpr (Nat.lt_succ_self t'))
      obtain ⟨hBA, hvan⟩ := eq_mul_of_agree (by omega : 2 * t' + d ≤ D'₂.card) (hp z₀ hz₀)
        (show (errSet D'₂ u z₀ (p z₀)).card ≤ t' by rw [hS'₂, hS'card]) hA' hB h
      have hA0 : A ≠ 0 := fun hA0 =>
        hne.elim (fun h => h hA0) fun h => h (by rw [hBA, hA0, zero_mul])
      have hle : S'.card ≤ t' - 1 := by
        have hdeg' : A.degree < ((t' - 1) + 1 : ℕ) := by rwa [Nat.sub_add_cancel ht'pos]
        exact card_le_of_vanishing hA0 hdeg' fun x hx =>
          hvan x (hS'D'₂ hx) (mem_filter.mp (mem_sdiff.mp hx).1).2
      omega
    have hΔ'ne : bwDelta σ' u ≠ 0 := fun h0 => hΔ'z₀ (by rw [h0, eval_zero])
    -- Show `bwDelta σ' u * Atilde.eval (C x) = bwDelta σ u * bwEvalXA σ' u x` for all `x ∈ F`.
    let tildeVec : Fin t' ⊕ Fin (t' + d) → F[X] :=
      Sum.elim (fun i => Atilde.coeff (i : ℕ)) (fun j => Btilde.coeff (j : ℕ))
    have hAtilde_eval : ∀ x : F,
        Atilde.eval (C x) =
          (∑ i : Fin t', tildeVec (Sum.inl i) * C (x ^ (i : ℕ))) + bwDelta σ u * C (x ^ t') := by
      intro x
      rw [eval_eq_sum_range' (by omega : Atilde.natDegree < t' + 1), Finset.sum_range_succ,
        ← Fin.sum_univ_eq_sum_range, hAtilde_lc]
      simp [tildeVec, C_pow]
    have hBtilde_eval : ∀ x : F,
        Btilde.eval (C x) = ∑ j : Fin (t' + d), tildeVec (Sum.inr j) * C (x ^ (j : ℕ)) := by
      intro x
      have hlt : Btilde.natDegree < t' + d ∨ Btilde = 0 := by
        by_cases h0 : Btilde = 0
        · exact Or.inr h0
        · exact Or.inl ((natDegree_lt_iff_degree_lt h0).mpr hBtilde_deg)
      rcases hlt with hnat | rfl
      · rw [eval_eq_sum_range' hnat, ← Fin.sum_univ_eq_sum_range]
        simp [tildeVec, C_pow]
      · simp [tildeVec]
    have hM'tilde : (bwMonicMatrix σ' u).mulVec tildeVec = bwDelta σ u • bwMonicRhs σ' u := by
      funext r
      rw [bwMonicMatrix, bwMatrix_mulVec, Pi.smul_apply, smul_eq_mul, bwMonicRhs]
      have hx := hTildeEq (σ' r) (hD'₂D' (σ' r).2)
      rw [hAtilde_eval (σ' r), hBtilde_eval (σ' r)] at hx
      simp only [one_mul, ← C_pow]
      linear_combination hx
    have hprop : bwDelta σ' u • tildeVec = bwDelta σ u • bwSol σ' u := by
      have hdiff : (bwMonicMatrix σ' u).mulVec
          (bwDelta σ' u • tildeVec - bwDelta σ u • bwSol σ' u) = 0 := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hM'tilde,
          bwSol, (bwMonicMatrix σ' u).mulVec_cramer (bwMonicRhs σ' u)]
        change bwDelta σ' u • (bwDelta σ u • bwMonicRhs σ' u) -
          bwDelta σ u • (bwDelta σ' u • bwMonicRhs σ' u) = 0
        rw [smul_comm, sub_self]
      have hadj := congrArg (bwMonicMatrix σ' u).adjugate.mulVec hdiff
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero, Matrix.smul_mulVec,
        Matrix.one_mulVec] at hadj
      funext k
      have hk := congrFun hadj k
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, smul_eq_mul] at hk
      exact sub_eq_zero.mp ((mul_eq_zero.mp hk).resolve_left hΔ'ne)
    have hAtilde_prop : ∀ x : F,
        bwDelta σ' u * Atilde.eval (C x) = bwDelta σ u * bwEvalXA σ' u x := by
      intro x
      rw [hAtilde_eval x, bwEvalXA, Fin.sum_univ_castSucc]
      simp only [bwCoeffA, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc,
        Fin.val_last, mul_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => ?_) (by ring)
      have hi := congrFun hprop (Sum.inl i)
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [← mul_assoc, hi, mul_assoc]
    -- Consequently `bwEvalXA σ' u x ≠ 0` for every `x ∈ D'`.
    have hA'ne : ∀ x ∈ D', bwEvalXA σ' u x ≠ 0 := by
      intro x hx h0
      have h := hAtilde_prop x
      rw [h0, mul_zero] at h
      exact (mul_eq_zero.mp h).elim hΔ'ne (hTildeNe x hx)
    -- And for every `β ∈ G'` and every `x ∈ errSet D u β (p β) \ S*`, `(bwEvalXA σ' u x).eval β = 0`.
    have hA'van : ∀ β ∈ G', ∀ x ∈ errSet D u β (p β) \ Sstar, (bwEvalXA σ' u x).eval β = 0 := by
      intro β hβ x hx
      obtain ⟨hβG, hΔβ⟩ := mem_filter.mp hβ
      obtain ⟨hxE, hxSstar⟩ := mem_sdiff.mp hx
      have hAβx : (bwEvalXA σ u x).eval β = 0 := by
        rw [eval_bwEvalXA]
        exact (hβ_props β hβG hΔβ).2 x hxE
      have hA₀x : (A₀.eval (C x)).eval β ≠ 0 := by
        rw [eval_vanishingOverPoly, eval_C]
        exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr fun hxy =>
          hxSstar (hxy ▸ hy)
      have hTildeβ : (Atilde.eval (C x)).eval β = 0 := by
        rw [← eval_bwPolyA, hAtilde, eval_mul, eval_mul] at hAβx
        exact (mul_eq_zero.mp hAβx).resolve_left hA₀x
      have hpropβ := congrArg (Polynomial.eval β) (hAtilde_prop x)
      rw [eval_mul, eval_mul, hTildeβ, mul_zero] at hpropβ
      exact (mul_eq_zero.mp hpropβ.symm).resolve_left hΔβ
    -- Double count pairs `(x, β) ∈ D' × G'` with `(bwEvalXA σ' u x).eval β = 0`.
    have hlower : t' * G'.card ≤
        ∑ β ∈ G', (D'.filter fun x => (bwEvalXA σ' u x).eval β = 0).card := by
      rw [Nat.mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun β hβ => ?_
      have hsub : errSet D u β (p β) \ Sstar ⊆
          D'.filter fun x => (bwEvalXA σ' u x).eval β = 0 := by
        intro x hx
        refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨errSet_subset D u β (p β) (mem_sdiff.mp hx).1,
          (mem_sdiff.mp hx).2⟩, hA'van β hβ x hx⟩
      have hbi := mem_filter.mp hβ
      have hcard_sdiff : (errSet D u β (p β) \ Sstar).card = t' := by
        rw [card_sdiff_of_subset (hSstar_sub_E β hβ), (hβ_props β hbi.1 hbi.2).1]
      exact hcard_sdiff.ge.trans (card_le_card hsub)
    have hswap : ∑ β ∈ G', (D'.filter fun x => (bwEvalXA σ' u x).eval β = 0).card =
        ∑ x ∈ D', (G'.filter fun β => (bwEvalXA σ' u x).eval β = 0).card := by
      simp only [card_filter]
      exact Finset.sum_comm
    have hupper : ∑ x ∈ D', (G'.filter fun β => (bwEvalXA σ' u x).eval β = 0).card ≤
        D'.card * (t' * (m - 1)) := by
      calc ∑ x ∈ D', (G'.filter fun β => (bwEvalXA σ' u x).eval β = 0).card
          ≤ ∑ _x ∈ D', t' * (m - 1) := sum_le_sum fun x hx => by
            have hsub : (G'.filter fun β => (bwEvalXA σ' u x).eval β = 0) ⊆
                (bwEvalXA σ' u x).roots.toFinset := by
              intro β hβ
              rw [Multiset.mem_toFinset, mem_roots (hA'ne x hx), IsRoot.def]
              exact (mem_filter.mp hβ).2
            exact (card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
              ((card_roots' _).trans (natDegree_bwEvalXA_le σ' u x)))
        _ = D'.card * (t' * (m - 1)) := by rw [sum_const, smul_eq_mul]
    have hG'le : G'.card ≤ D'.card * (m - 1) := by
      have hcomb : t' * G'.card ≤ t' * (D'.card * (m - 1)) := by
        have := (hlower.trans_eq hswap).trans hupper
        linarith
      exact Nat.le_of_mul_le_mul_left hcomb ht'pos
    have hGle : G.card ≤ (m - 1) * (D.card + e) := by
      have hGsplit' : G'.card + (G.filter fun β => ¬ (bwDelta σ u).eval β ≠ 0).card = G.card :=
        hGsplit
      rw [hD'card] at hG'le
      have h1 : G.card ≤ (D.card - s) * (m - 1) + t * (m - 1) := by omega
      have h2 : (D.card - s) * (m - 1) + t * (m - 1) = (D.card - s + t) * (m - 1) := by ring
      have h3 : (D.card - s + t) * (m - 1) ≤ (D.card + e) * (m - 1) :=
        Nat.mul_le_mul_right _ (by omega)
      have h4 : (D.card + e) * (m - 1) = (m - 1) * (D.card + e) := Nat.mul_comm _ _
      omega
    omega

end CertiFri
