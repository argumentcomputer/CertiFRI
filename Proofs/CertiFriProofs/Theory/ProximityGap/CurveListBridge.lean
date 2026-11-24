import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.Separable
import CertiFriProofs.Theory.ProximityGap.GuruswamiSudan

/-!
# Algebraic Bridge Toward Unconditional `CurveListCA` (`CurveListBridge`)

Discharges Steps 1 and 2 of the remaining algebraic bridge from
`GuruswamiSudan.exists_gs_poly_curve` to unconditional `CurveListCA`
(`ProximityGap/GuruswamiSudan.lean`):

1. **Denominator Clearing & Pole-Free Specialization (`exists_gs_poly_curve_int`,
   `evalZBiv_vanishesMult`, `card_evalZBiv_eq_zero_le`, `eval_specialized_eq_zero_of_agree_ge`):**
   Clears all `Z`-denominators of the parametric Guruswami–Sudan annihilator
   `Q_Z : ((RatFunc F)[X])[X]` to obtain a nonzero trivariate polynomial
   `Q_poly : ((F[X])[X])[X]` (coefficients in `F[Z]`, inner `X`, outer `Y`)
   such that:
   * `Q_poly ≠ 0`, with at most `maxZDeg Q_poly` parameters `β ∈ F` where
     the specialization `evalZBiv β Q_poly` vanishes identically;
   * for **every** `β ∈ F` (pole-free!) and **every** `x ∈ D`, the specialized
     bivariate polynomial `evalZBiv β Q_poly : (F[X])[X]` has `(1, d - 1)`-weighted
     degree at most `D_X` and vanishes to multiplicity at least `r` at
     `(x, ∑ k, β ^ k * u k x)`;
   * consequently, for every `β ∈ F` and every degree-`< d` polynomial `p : F[X]`
     agreeing with `∑ k, β ^ k * u k` on at least `A` points of `D`,
     `(evalZBiv β Q_poly).eval p = 0` and `(Y - C p) ∣ evalZBiv β Q_poly`.

2. **Characteristic-`p` Separability (`derivative_ne_zero_of_natDegree_lt_char`,
   `separable_of_irreducible_natDegree_lt_char`):**
   Over any field `K` of prime characteristic `p` (in particular `K = RatFunc (RatFunc F)`
   over Goldilocks `Fp3` where `p = 2^64 - 2^32 + 1`), every irreducible polynomial
   `f : K[Y]` with `f.natDegree < p` has nonzero derivative (`f.derivative ≠ 0`) and is
   automatically separable (`IsCoprime f f.derivative`, i.e. `f.Separable`), eliminating
   Frobenius `p`-th power stripping whenever `deg_Y(Q) < p`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace CertiFri

namespace CurveListBridge

open Polynomial Finset GuruswamiSudan

/-! ## 1. Polynomial Ring Maps on Bivariate Polynomials -/

section BivMap

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Lift a ring homomorphism `φ : R →+* S` to bivariate polynomials `(R[X])[X] →+* (S[X])[X]`
(mapping inner `X`-coefficients via `Polynomial.mapRingHom φ`). -/
noncomputable def mapBivHom (φ : R →+* S) : (R[X])[X] →+* (S[X])[X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

@[simp] theorem coeff_coeff_mapBivHom (φ : R →+* S) (Q : (R[X])[X]) (j i : ℕ) :
    ((mapBivHom φ Q).coeff j).coeff i = φ ((Q.coeff j).coeff i) := by
  simp [mapBivHom, Polynomial.coeff_map]

theorem mapBivHom_injective {φ : R →+* S} (hφ : Function.Injective φ) :
    Function.Injective (mapBivHom φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ hφ)

/-- Ring homomorphism shifting the inner indeterminate `X ↦ X + C x` over any commutative ring. -/
noncomputable def shiftXRingHom {A : Type*} [CommRing A] (x : A) : A[X] →+* A[X] :=
  eval₂RingHom C (X + C x)

/-- Shifted bivariate polynomial `Q(X + x, Y + y)` over any commutative ring `A`. -/
noncomputable def shiftBivRing {A : Type*} [CommRing A] (x y : A) (Q : (A[X])[X]) : (A[X])[X] :=
  (Q.map (shiftXRingHom x)).comp (X + C (C y))

theorem shiftBivRing_eq_shiftBiv {K : Type*} [Field K] (x y : K) (Q : (K[X])[X]) :
    shiftBivRing x y Q = shiftBiv x y Q := rfl

/-- `mapBivHom φ` commutes with `shiftXRingHom` on inner univariate polynomials. -/
theorem map_shiftXRingHom {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (x : A) (p : A[X]) :
    (shiftXRingHom x p).map φ = shiftXRingHom (φ x) (p.map φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n a =>
    change (eval₂ C (X + C x) (monomial n a)).map φ =
      eval₂ C (X + C (φ x)) ((monomial n a).map φ)
    rw [Polynomial.map_monomial, eval₂_monomial, eval₂_monomial]
    simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_X]

/-- `mapBivHom φ` commutes with the Hasse bivariate shift `shiftBivRing`. -/
theorem mapBivHom_shiftBivRing {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (x y : A) (Q : (A[X])[X]) :
    mapBivHom φ (shiftBivRing x y Q) = shiftBivRing (φ x) (φ y) (mapBivHom φ Q) := by
  have hcomp : ∀ (P : (A[X])[X]) (g : (A[X])[X]),
      mapBivHom φ (P.comp g) = (mapBivHom φ P).comp (mapBivHom φ g) := by
    intro P g
    exact Polynomial.map_comp (Polynomial.mapRingHom φ) P g
  have hmap : mapBivHom φ (Q.map (shiftXRingHom x)) =
      (mapBivHom φ Q).map (shiftXRingHom (φ x)) := by
    change (Q.map (shiftXRingHom x)).map (Polynomial.mapRingHom φ) =
      (Q.map (Polynomial.mapRingHom φ)).map (shiftXRingHom (φ x))
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact RingHom.ext fun p => map_shiftXRingHom φ x p
  have harg : mapBivHom φ (X + C (C y) : (A[X])[X]) = X + C (C (φ y)) := by
    simp [mapBivHom]
  unfold shiftBivRing
  rw [hcomp, hmap, harg]

end BivMap

/-! ## 2. Denominator Clearing for Parametric Guruswami–Sudan Annihilators -/

section DenomClearing

variable {F : Type*} [Field F]

/-- Canonical embedding `F[Z] →+* RatFunc F` lifted to bivariate polynomials
`((F[Z])[X])[Y] →+* ((RatFunc F)[X])[Y]`. -/
noncomputable def embedBiv : ((F[X])[X])[X] →+* ((RatFunc F)[X])[X] :=
  mapBivHom (algebraMap F[X] (RatFunc F))

theorem embedBiv_injective : Function.Injective (embedBiv (F := F)) :=
  mapBivHom_injective (IsFractionRing.injective F[X] (RatFunc F))

/-- Evaluation of the parameter `Z ↦ β` lifted to bivariate polynomials
`((F[Z])[X])[Y] →+* (F[X])[Y]`. -/
noncomputable def evalZBiv (β : F) : ((F[X])[X])[X] →+* (F[X])[X] :=
  mapBivHom (Polynomial.evalRingHom β)

/-- Maximum `Z`-degree appearing among all coefficients of `Q_poly : ((F[Z])[X])[Y]`. -/
noncomputable def maxZDeg (Q_poly : ((F[X])[X])[X]) : ℕ :=
  Q_poly.support.sup fun j => (Q_poly.coeff j).support.sup fun i =>
    ((Q_poly.coeff j).coeff i).natDegree

/-- Product of all `RatFunc.denom` denominators occurring in `Q : ((RatFunc F)[X])[Y]`. -/
noncomputable def commonDenom (Q : ((RatFunc F)[X])[X]) : F[X] :=
  ∏ j ∈ Q.support, ∏ i ∈ (Q.coeff j).support, ((Q.coeff j).coeff i).denom

theorem commonDenom_ne_zero (Q : ((RatFunc F)[X])[X]) : commonDenom Q ≠ 0 := by
  classical
  unfold commonDenom
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  exact Finset.prod_ne_zero_iff.mpr fun i _ => RatFunc.denom_ne_zero _

theorem denom_dvd_commonDenom (Q : ((RatFunc F)[X])[X]) (j i : ℕ) :
    ((Q.coeff j).coeff i).denom ∣ commonDenom Q := by
  classical
  by_cases hj : j ∈ Q.support
  · by_cases hi : i ∈ (Q.coeff j).support
    · have h1 : ((Q.coeff j).coeff i).denom ∣ ∏ i' ∈ (Q.coeff j).support, ((Q.coeff j).coeff i').denom :=
        Finset.dvd_prod_of_mem _ hi
      have h2 : (∏ i' ∈ (Q.coeff j).support, ((Q.coeff j).coeff i').denom) ∣ commonDenom Q :=
        Finset.dvd_prod_of_mem _ hj
      exact dvd_trans h1 h2
    · have hzero : (Q.coeff j).coeff i = 0 := by
        simpa [Polynomial.mem_support_iff] using hi
      rw [hzero, RatFunc.denom_zero]
      exact one_dvd _
  · have hzero : Q.coeff j = 0 := by
      simpa [Polynomial.mem_support_iff] using hj
    rw [hzero, coeff_zero, RatFunc.denom_zero]
    exact one_dvd _

/-- Clear all `Z`-denominators of `Q : ((RatFunc F)[X])[Y]` by multiplying by `commonDenom Q`. -/
noncomputable def clearDenomBiv (Q : ((RatFunc F)[X])[X]) : ((F[X])[X])[X] :=
  ∑ j ∈ Q.support,
    Polynomial.monomial j
      (∑ i ∈ (Q.coeff j).support,
        Polynomial.monomial i
          (((Q.coeff j).coeff i).num * (commonDenom Q / ((Q.coeff j).coeff i).denom)))

theorem coeff_coeff_clearDenomBiv (Q : ((RatFunc F)[X])[X]) (j i : ℕ) :
    ((clearDenomBiv Q).coeff j).coeff i =
      ((Q.coeff j).coeff i).num * (commonDenom Q / ((Q.coeff j).coeff i).denom) := by
  classical
  unfold clearDenomBiv
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hj : j ∈ Q.support
  · rw [Finset.sum_ite_eq' Q.support j, ite_eq_left hj, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    by_cases hi : i ∈ (Q.coeff j).support
    · rw [Finset.sum_ite_eq' (Q.coeff j).support i, ite_eq_left hi]
    · rw [Finset.sum_ite_eq' (Q.coeff j).support i, ite_eq_right hi]
      have hzero : (Q.coeff j).coeff i = 0 := by
        simpa [Polynomial.mem_support_iff] using hi
      rw [hzero, RatFunc.num_zero, zero_mul]
  · rw [Finset.sum_ite_eq' Q.support j, ite_eq_right hj, coeff_zero]
    have hzero : Q.coeff j = 0 := by
      simpa [Polynomial.mem_support_iff] using hj
    rw [hzero, coeff_zero, RatFunc.num_zero, zero_mul]

/-- Exact clearing identity in `((RatFunc F)[X])[Y]`:
`embedBiv (clearDenomBiv Q) = C (C (algebraMap (commonDenom Q))) * Q`. -/
theorem embedBiv_clearDenomBiv (Q : ((RatFunc F)[X])[X]) :
    embedBiv (clearDenomBiv Q) =
      C (C (algebraMap F[X] (RatFunc F) (commonDenom Q))) * Q := by
  ext j i
  rw [embedBiv, coeff_coeff_mapBivHom, coeff_coeff_clearDenomBiv,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  set q := (Q.coeff j).coeff i
  have hdvd : q.denom ∣ commonDenom Q := denom_dvd_commonDenom Q j i
  have hmul : q.denom * (commonDenom Q / q.denom) = commonDenom Q :=
    EuclideanDomain.mul_div_cancel' (RatFunc.denom_ne_zero q) hdvd
  have hdenom_ne : algebraMap F[X] (RatFunc F) q.denom ≠ 0 := by
    intro h0
    exact RatFunc.denom_ne_zero q
      ((IsFractionRing.injective F[X] (RatFunc F)) (h0.trans (map_zero _).symm))
  have hq : q = algebraMap F[X] (RatFunc F) q.num / algebraMap F[X] (RatFunc F) q.denom :=
    (RatFunc.num_div_denom q).symm
  have hmul' : algebraMap F[X] (RatFunc F) (commonDenom Q) =
      algebraMap F[X] (RatFunc F) q.denom *
        algebraMap F[X] (RatFunc F) (commonDenom Q / q.denom) := by
    rw [← map_mul, hmul]
  calc algebraMap F[X] (RatFunc F) (q.num * (commonDenom Q / q.denom))
      = algebraMap F[X] (RatFunc F) q.num *
          algebraMap F[X] (RatFunc F) (commonDenom Q / q.denom) := map_mul _ _ _
    _ = (algebraMap F[X] (RatFunc F) q.denom *
          algebraMap F[X] (RatFunc F) (commonDenom Q / q.denom)) *
        (algebraMap F[X] (RatFunc F) q.num / algebraMap F[X] (RatFunc F) q.denom) := by
        field_simp [hdenom_ne]
    _ = algebraMap F[X] (RatFunc F) (commonDenom Q) * q := by
        rw [← hmul', ← hq]

theorem clearDenomBiv_ne_zero {Q : ((RatFunc F)[X])[X]} (hQ : Q ≠ 0) :
    clearDenomBiv Q ≠ 0 := by
  intro h0
  have h1 := embedBiv_clearDenomBiv Q
  rw [h0, map_zero] at h1
  have hcd : algebraMap F[X] (RatFunc F) (commonDenom Q) ≠ 0 := by
    intro hc
    exact commonDenom_ne_zero Q
      ((IsFractionRing.injective F[X] (RatFunc F)) (hc.trans (map_zero _).symm))
  have hCC : (C (C (algebraMap F[X] (RatFunc F) (commonDenom Q))) : ((RatFunc F)[X])[X]) ≠ 0 := by
    intro hc
    apply hcd
    have := congrArg (fun P : ((RatFunc F)[X])[X] => (P.coeff 0).coeff 0) hc
    simpa using this
  exact mul_ne_zero hCC hQ h1.symm

/-- Weighted degree is preserved by `clearDenomBiv` and EVERY specialization `evalZBiv β`. -/
theorem evalZBiv_hasWeightedDegLE {k D_X : ℕ} {Q : ((RatFunc F)[X])[X]}
    (hQ : HasWeightedDegLE k D_X Q) (β : F) :
    HasWeightedDegLE k D_X (evalZBiv β (clearDenomBiv Q)) := by
  intro j i hij
  rw [evalZBiv, coeff_coeff_mapBivHom, coeff_coeff_clearDenomBiv,
      hQ j i hij, RatFunc.num_zero, zero_mul, map_zero]

/-- Pole-free multiplicity vanishing: if `Q : ((RatFunc F)[X])[Y]` vanishes to
multiplicity `r` at `(RatFunc.C x, ∑ k, RatFunc.X ^ k * RatFunc.C (u k x))`, then
for **every** `β ∈ F`, the specialized bivariate polynomial `evalZBiv β (clearDenomBiv Q)`
vanishes to multiplicity `r` at `(x, ∑ k, β ^ k * u k x)`. -/
theorem evalZBiv_vanishesMult {r m : ℕ} {u : Fin m → F → F} {x : F}
    {Q : ((RatFunc F)[X])[X]}
    (hvan : VanishesMult r (RatFunc.C x)
      (∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k x)) Q)
    (β : F) :
    VanishesMult r x (∑ k : Fin m, β ^ (k : ℕ) * u k x)
      (evalZBiv β (clearDenomBiv Q)) := by
  let xZ : F[X] := C x
  let yZ : F[X] := ∑ k : Fin m, X ^ (k : ℕ) * C (u k x)
  have hxZ_emb : algebraMap F[X] (RatFunc F) xZ = RatFunc.C x := by
    simp [xZ, RatFunc.algebraMap_C]
  have hyZ_emb : algebraMap F[X] (RatFunc F) yZ =
      ∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k x) := by
    simp only [yZ, map_sum, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hxZ_eval : (Polynomial.evalRingHom β) xZ = x := by
    simp [xZ]
  have hyZ_eval : (Polynomial.evalRingHom β) yZ = ∑ k : Fin m, β ^ (k : ℕ) * u k x := by
    simp only [yZ, map_sum, map_mul, map_pow, coe_evalRingHom, eval_X, eval_C]
  intro a b hab
  have hshift_zero : ((shiftBivRing xZ yZ (clearDenomBiv Q)).coeff b).coeff a = 0 := by
    apply IsFractionRing.injective F[X] (RatFunc F)
    rw [map_zero]
    have h1 : algebraMap F[X] (RatFunc F) (((shiftBivRing xZ yZ (clearDenomBiv Q)).coeff b).coeff a) =
        ((embedBiv (shiftBivRing xZ yZ (clearDenomBiv Q))).coeff b).coeff a :=
      (coeff_coeff_mapBivHom (algebraMap F[X] (RatFunc F)) _ b a).symm
    rw [h1, embedBiv, mapBivHom_shiftBivRing, hxZ_emb, hyZ_emb]
    change ((shiftBiv (RatFunc.C x)
        (∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k x))
        (embedBiv (clearDenomBiv Q))).coeff b).coeff a = 0
    rw [embedBiv_clearDenomBiv, shiftBiv_C_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        hvan a b hab, mul_zero]
  rw [← shiftBivRing_eq_shiftBiv, ← hyZ_eval, ← hxZ_eval]
  rw [evalZBiv, ← mapBivHom_shiftBivRing, coeff_coeff_mapBivHom, hshift_zero, map_zero]

/-- Cardinality bound on vanishing specializations: if `Q_poly ≠ 0`, then at most
`maxZDeg Q_poly` parameters `β ∈ S` satisfy `evalZBiv β Q_poly = 0`. -/
theorem card_evalZBiv_eq_zero_le [DecidableEq F] {Q_poly : ((F[X])[X])[X]}
    (hQ : Q_poly ≠ 0) (S : Finset F) :
    (S.filter fun β => evalZBiv β Q_poly = 0).card ≤ maxZDeg Q_poly := by
  classical
  have hex : ∃ j ∈ Q_poly.support, ∃ i ∈ (Q_poly.coeff j).support,
      ((Q_poly.coeff j).coeff i) ≠ 0 := by
    have hsupp : Q_poly.support.Nonempty := Polynomial.support_nonempty.mpr hQ
    obtain ⟨j, hj⟩ := hsupp
    have hcj : Q_poly.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
    have hisupp : (Q_poly.coeff j).support.Nonempty := Polynomial.support_nonempty.mpr hcj
    obtain ⟨i, hi⟩ := hisupp
    exact ⟨j, hj, i, hi, Polynomial.mem_support_iff.mp hi⟩
  obtain ⟨j, hj, i, hi, hne⟩ := hex
  set f : F[X] := (Q_poly.coeff j).coeff i
  have hsub : (S.filter fun β => evalZBiv β Q_poly = 0) ⊆ f.roots.toFinset := by
    intro β hβ
    have h0 : evalZBiv β Q_poly = 0 := (Finset.mem_filter.mp hβ).2
    have hval : f.eval β = 0 := by
      have := congrArg (fun P : (F[X])[X] => (P.coeff j).coeff i) h0
      simpa [evalZBiv, f] using this
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr hval)
  have hcard1 : (S.filter fun β => evalZBiv β Q_poly = 0).card ≤ f.roots.toFinset.card :=
    Finset.card_le_card hsub
  have hcard2 : f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
  have hcard3 : f.roots.card ≤ f.natDegree := Polynomial.card_roots' f
  have hdeg : f.natDegree ≤ maxZDeg Q_poly := by
    unfold maxZDeg
    have h1 : f.natDegree ≤ (Q_poly.coeff j).support.sup (fun i' => ((Q_poly.coeff j).coeff i').natDegree) :=
      Finset.le_sup (f := fun i' => ((Q_poly.coeff j).coeff i').natDegree) hi
    have h2 : (Q_poly.coeff j).support.sup (fun i' => ((Q_poly.coeff j).coeff i').natDegree) ≤
        Q_poly.support.sup (fun j' => (Q_poly.coeff j').support.sup (fun i' => ((Q_poly.coeff j').coeff i').natDegree)) :=
      Finset.le_sup (f := fun j' => (Q_poly.coeff j').support.sup (fun i' => ((Q_poly.coeff j').coeff i').natDegree)) hj
    exact le_trans h1 h2
  exact le_trans hcard1 (le_trans hcard2 (le_trans hcard3 hdeg))

/-- **Integral Parametric Guruswami–Sudan Annihilator (`exists_gs_poly_curve_int`):**
Clears all `Z`-denominators from `exists_gs_poly_curve` to produce a nonzero trivariate
polynomial `Q_poly : ((F[Z])[X])[Y]` whose specialization at **every** `β ∈ F` vanishes
to multiplicity `r` at `(x, ∑ k, β^k * u k x)` for all `x ∈ D`, has `(1, d-1)`-weighted
degree `≤ D_X < r * A`, and therefore annihilates every degree-`< d` polynomial agreeing
with `∑ k, β^k * u k` on at least `A` points of `D`. -/
theorem exists_gs_poly_curve_int [DecidableEq F] (D : Finset F) (d A m : ℕ)
    (u : Fin m → F → F) (hD : 0 < D.card) (hJ : D.card * (d - 1) < A ^ 2) :
    ∃ (r D_X : ℕ) (Q_poly : ((F[X])[X])[X]),
      1 ≤ r ∧ D_X < r * A ∧ Q_poly ≠ 0 ∧
      (∀ β : F, HasWeightedDegLE (d - 1) D_X (evalZBiv β Q_poly)) ∧
      (∀ β : F, ∀ x ∈ D,
        VanishesMult r x (∑ k : Fin m, β ^ (k : ℕ) * u k x) (evalZBiv β Q_poly)) ∧
      (∀ (β : F) (p : F[X]),
        p.degree < d →
        A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x).card →
        (evalZBiv β Q_poly).eval p = 0 ∧ X - C p ∣ evalZBiv β Q_poly) := by
  obtain ⟨r, D_X, Q, hr, hDX, hQne, hQdeg, hQvan⟩ :=
    exists_gs_poly_curve D d A m u hD hJ
  refine ⟨r, D_X, clearDenomBiv Q, hr, hDX, clearDenomBiv_ne_zero hQne,
    fun β => evalZBiv_hasWeightedDegLE hQdeg β,
    fun β x hx => evalZBiv_vanishesMult (hQvan x hx) β, ?_⟩
  intro β p hp hagree
  have hdeg := evalZBiv_hasWeightedDegLE hQdeg β
  have hvan : ∀ x ∈ D, VanishesMult r x (∑ k : Fin m, β ^ (k : ℕ) * u k x)
      (evalZBiv β (clearDenomBiv Q)) :=
    fun x hx => evalZBiv_vanishesMult (hQvan x hx) β
  exact ⟨eval_eq_zero_of_agree_ge hdeg hvan hp hagree hDX,
         X_sub_C_dvd_of_agree_ge hdeg hvan hp hagree hDX⟩

end DenomClearing

/-! ## 3. Characteristic-`p` Separability for Low-`Y`-Degree Irreducible Factors -/

section CharPSeparability

/-- Over any field `K` of prime characteristic `p`, any polynomial `f : K[Y]` with
`0 < f.natDegree < p` has nonzero formal derivative `f.derivative ≠ 0`. -/
theorem derivative_ne_zero_of_natDegree_lt_char {K : Type*} [Field K] {p : ℕ}
    [CharP K p] {f : K[X]} (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) :
    f.derivative ≠ 0 := by
  intro h0
  have hcoeff : f.derivative.coeff (f.natDegree - 1) = 0 := by
    rw [h0, coeff_zero]
  rw [Polynomial.coeff_derivative] at hcoeff
  have hsucc : f.natDegree - 1 + 1 = f.natDegree := Nat.sub_add_cancel hpos
  have hcast : ((f.natDegree - 1 : ℕ) : K) + 1 = (f.natDegree : K) := by
    rw [← Nat.cast_succ]
    exact congrArg (Nat.cast : ℕ → K) hsucc
  rw [hsucc, hcast] at hcoeff
  have hlc : f.coeff f.natDegree ≠ 0 := by
    have hfne : f ≠ 0 := by
      intro hf0
      rw [hf0, natDegree_zero] at hpos
      exact Nat.lt_irrefl 0 hpos
    exact Polynomial.leadingCoeff_ne_zero.mpr hfne
  have hnat_ne : (f.natDegree : K) ≠ 0 := by
    intro hc
    have hdvd : p ∣ f.natDegree := (CharP.cast_eq_zero_iff K p f.natDegree).mp hc
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le_of_gt hlt)
  exact mul_ne_zero hlc hnat_ne hcoeff

/-- Over any field `K` of prime characteristic `p`, every irreducible polynomial
`f : K[Y]` with `f.natDegree < p` is automatically separable (`IsCoprime f f.derivative`
and `f.Separable`). In particular, over Goldilocks (`p = 2^64 - 2^32 + 1`), every
Guruswami–Sudan irreducible factor with `deg_Y < p` requires NO Frobenius `p`-th power
stripping before Hensel lifting. -/
theorem separable_of_irreducible_natDegree_lt_char {K : Type*} [Field K] {p : ℕ}
    [CharP K p] {f : K[X]} (hirr : Irreducible f) (hlt : f.natDegree < p) :
    f.Separable := by
  have hpos : 0 < f.natDegree := by
    by_contra hle
    have h0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hle
    have hfne : f ≠ 0 := hirr.ne_zero
    have hfc : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have hcne : f.coeff 0 ≠ 0 := by
      intro hc
      apply hfne
      rw [hfc, hc, map_zero]
    have hunit : IsUnit f := by
      rw [hfc]
      exact (isUnit_iff_ne_zero.mpr hcne).map C
    exact hirr.not_isUnit hunit
  have hder_ne : f.derivative ≠ 0 := derivative_ne_zero_of_natDegree_lt_char hpos hlt
  have hdeg_lt : f.derivative.natDegree < f.natDegree :=
    Polynomial.natDegree_derivative_lt (Nat.ne_of_gt hpos)
  have hnot_dvd : ¬ (f ∣ f.derivative) := by
    intro hdvd
    exact not_le_of_gt hdeg_lt (Polynomial.natDegree_le_of_dvd hdvd hder_ne)
  exact (hirr.isRelPrime_iff_not_dvd.mpr hnot_dvd).isCoprime

end CharPSeparability

end CurveListBridge

end CertiFri
