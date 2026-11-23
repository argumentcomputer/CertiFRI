import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import CertiFriProofs.Theory.ProximityGap.CurveListBridge
import CertiFriProofs.Theory.ProximityGap.HenselLift
import CertiFriProofs.Theory.ProximityGap.JohnsonMCA

/-!
# Unconditional Discharge of `CurveListCA` in the Johnson Regime (`CurveListCA`)

Discharges `CertiFri.CurveListCA F curveListThreshold` unconditionally over any
finite field `F` of characteristic `p ≥ 2` and extension degree at most `4`
(`Fintype.card F ≤ p ^ 4`, in particular Goldilocks `Fp3Model` with
`p = 2^64 - 2^32 + 1` and `|Fp3Model| = p^3`), as well as over any field of
characteristic `0` or large prime characteristic `p > gsDegY |D| d A`.

## Proof Architecture (5 Steps, Zero `sorry`, Standard Axioms Only)

1. **Direct `F`-linear low-`Z`-degree Guruswami–Sudan interpolation
   (`exists_gs_poly_curve_lowZDeg`):**
   For `d ≥ 2`, `m ≥ 2`, `n * (d - 1) < A ^ 2`, sets sharp multiplicity
   `r = (2 * (d - 1) * n) / (A^2 - n * (d - 1)) + 1`, `D_X = r * A - 1`,
   `L_Y = D_X / (d - 1)`, `D_Z = (r + 1) * (m - 1) * L_Y`, and solves Hasse
   vanishing directly over `F` to obtain nonzero `Q ∈ ((F[Z])[X])[Y]` of
   `Y`-degree `≤ L_Y`, `X`-degree `≤ D_X`, and `Z`-degree `≤ D_Z` (independent
   of `|D|`!).
2. **UFD factorization, characteristic-`p` separability, and weighted pigeonhole:**
   Factors `Q` in the UFD `((F[Z])[X])[Y]`. Since `L_Y < p`, every irreducible
   factor `R` with `ℓ = deg_Y(R) ≥ 1` is separable over `FractionRing (F[Z][X])`
   (`CurveListBridge.separable_of_irreducible_natDegree_lt_char`), so its
   Sylvester discriminant `Δ_R(Z, X)` is nonzero (`Sylvester.sylvesterDet_ne_zero_of_isCoprime`).
   Picks one `x₀ ∈ G` avoiding all `lc_Y(R)(Z, x₀) = 0` and `Δ_R(Z, x₀) = 0`,
   shifts `X ↦ X + x₀`, factors each `R(Z, x₀, T)` in the UFD `(F[Z])[T]`, and
   applies `H.natDegree`-weighted pigeonhole over all pairs `(R, H)` (total
   weight `≤ L_Y`) to isolate a single pair `(R, H)` capturing `|G_H| > t * B`.
3. **Cleared-denominator Hensel lifting into `E = AdjoinRoot H_K`:**
   Runs `HenselLift.henselCoeff` with `W = pseudoRem H ℓ V_bez`, proves every
   `HenselLift.henselResidualCoeff` vanishes identically via `Sylvester.sylvesterDet`
   coprimality over `RatFunc F`, and lifts to a degree-`< d` root `P_orig ∈ E[X]`
   of `R_E(X, Y) = 0` over the field `E = (RatFunc F)[T] / (H_K)`.
4. **Hasse-multiplicity double counting (`|S_P| ≥ A`):**
   For every `x ∈ D` where `P_orig(x) ≠ u_Z(x)` in `E`, writes
   `R(Z, x, Y) = (Y - u_Z(x))^μ * S_x(Z, Y)` with `S_x(Z, u_Z(x)) ≠ 0` of
   `Z`-degree `≤ D_Z + ℓ * (m - 1)` (independent of `d`!), deduces
   `S_x(β, p_β(x)) = 0` for all `β ∈ G'_H`, and double-counts incidences on
   `G'_H × D` to prove `A ≤ |S_P|`.
5. **Lagrange interpolation on `S₀ ⊆ S_P` (`|S₀| = d`) → `v ∉ L`:**
   Interpolates `v k = Lagrange.interpolate S₀ id (u k)` (`deg < d`), proves
   `P_orig = ∑ Z^k • v k` in `E[X]`, concludes `S_P ⊆ tupleAgreeSet D u v` and
   `p_β = ∑ β^k • v k` for any `β ∈ G'_H`, hence `v ∉ L`.

Zero `sorry`, zero custom `axiom`, zero `native_decide`, zero `bv_decide`.
-/

namespace CertiFri

namespace CurveListCAProof

open Polynomial Finset GuruswamiSudan CurveListBridge Sylvester HenselLift

/-! ## 1. Sharp Guruswami–Sudan Parameters and Threshold Formula -/

/-- Sharp multiplicity `r` for Johnson parameters `(n, d, A)` with `n * (d - 1) < A^2`. -/
def gsMult (n d A : ℕ) : ℕ :=
  (2 * (d - 1) * n) / (A ^ 2 - n * (d - 1)) + 1

/-- Weighted-degree bound `D_X = r * A - 1 < r * A`. -/
def gsDegX (n d A : ℕ) : ℕ :=
  gsMult n d A * A - 1

/-- `Y`-degree bound `L_Y = D_X / (d - 1)` (for `d ≥ 2`). -/
def gsDegY (n d A : ℕ) : ℕ :=
  if d ≤ 1 then 0 else gsDegX n d A / (d - 1)

/-- Per-curve-coordinate threshold coefficient `curveListCoeff n d A` (independent of `m`),
so `curveListThreshold n d A m ≤ (m - 1) * curveListCoeff n d A` for all `m ≥ 2`. -/
def curveListCoeff (n d A : ℕ) : ℕ :=
  if d = 0 then n
  else if d = 1 then n * (n / A + 1)
  else
    let r := gsMult n d A
    let D_X := gsDegX n d A
    let L_Y := gsDegY n d A
    let D_Z1 := (r + 1) * L_Y
    let B3 := ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z1
    let B4 := (4 * L_Y + 2) * D_Z1 + n * (D_Z1 + L_Y)
    max ((2 * L_Y + 1) * D_X) (2 * D_Z1 + L_Y * max B3 B4)

/-- Explicit unconditional `CurveListCA` threshold `T n d A m`. -/
def curveListThreshold (n d A m : ℕ) : ℕ :=
  if m ≤ 1 then 0
  else if d = 0 then n * (m - 1)
  else if d = 1 then n * (m - 1) * (n / A + 1)
  else
    let r := gsMult n d A
    let D_X := gsDegX n d A
    let L_Y := gsDegY n d A
    let D_Z := (r + 1) * (m - 1) * L_Y
    let B3 := ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z
    let B4 := (4 * L_Y + 2) * D_Z + n * (D_Z + (m - 1) * L_Y)
    max ((2 * L_Y + 1) * D_X) (2 * D_Z + L_Y * max B3 B4)

theorem curveListThreshold_le_mul_coeff (n d A m : ℕ) (hm : 2 ≤ m) :
    curveListThreshold n d A m ≤ (m - 1) * curveListCoeff n d A := by
  have hm1 : ¬ (m ≤ 1) := by omega
  have hmpos : 1 ≤ m - 1 := by omega
  unfold curveListThreshold curveListCoeff
  rw [ite_eq_right hm1]
  by_cases hd0 : d = 0
  · subst hd0; simp [Nat.mul_comm]
  · rw [ite_eq_right hd0, ite_eq_right hd0]
    by_cases hd1 : d = 1
    · subst hd1; simp only [↓reduceIte]; exact le_of_eq (by ring)
    · rw [ite_eq_right hd1, ite_eq_right hd1]
      set r := gsMult n d A
      set D_X := gsDegX n d A
      set L_Y := gsDegY n d A
      have hDZ : (r + 1) * (m - 1) * L_Y = (m - 1) * ((r + 1) * L_Y) := by ring
      have hB3 : ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * ((r + 1) * (m - 1) * L_Y) =
          (m - 1) * (((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * ((r + 1) * L_Y)) := by
        rw [hDZ]; ring
      have hB4 : (4 * L_Y + 2) * ((r + 1) * (m - 1) * L_Y) + n * ((r + 1) * (m - 1) * L_Y + (m - 1) * L_Y) =
          (m - 1) * ((4 * L_Y + 2) * ((r + 1) * L_Y) + n * ((r + 1) * L_Y + L_Y)) := by
        rw [hDZ]; ring
      rw [max_le_iff]
      constructor
      · exact le_trans (Nat.le_mul_of_pos_left _ hmpos) (Nat.mul_le_mul_left _ (le_max_left _ _))
      · refine le_trans ?_ (Nat.mul_le_mul_left _ (le_max_right _ _))
        rw [hB3, hB4, Nat.mul_max_mul_left, hDZ]
        exact le_of_eq (by ring)

theorem gsDegY_pow_five_le_curveListThreshold {n d A m : ℕ}
    (hm : 2 ≤ m) (hd : 2 ≤ d) :
    gsDegY n d A ^ 5 ≤ curveListThreshold n d A m := by
  have hm1 : ¬ (m ≤ 1) := by omega
  have hd0 : d ≠ 0 := by omega
  have hd1 : d ≠ 1 := by omega
  unfold curveListThreshold
  rw [ite_eq_right hm1, ite_eq_right hd0, ite_eq_right hd1]
  set r := gsMult n d A
  set L_Y := gsDegY n d A
  set D_Z := (r + 1) * (m - 1) * L_Y
  have hr1 : 1 ≤ r + 1 := by omega
  have hm' : 1 ≤ m - 1 := by omega
  have hDZ : L_Y ≤ D_Z := by
    calc L_Y = 1 * 1 * L_Y := by ring
      _ ≤ (r + 1) * (m - 1) * L_Y :=
          Nat.mul_le_mul_right L_Y (Nat.mul_le_mul hr1 hm')
  have hB3 : L_Y ^ 4 ≤ ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z := by
    have h1 : L_Y ^ 3 ≤ (L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1) := by
      have h2d : 1 ≤ 2 * d := by omega
      calc L_Y ^ 3 = 1 * L_Y * L_Y ^ 2 := by ring
        _ ≤ 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_right L_Y h2d) (by omega)
        _ ≤ _ := Nat.le_add_left _ _
    calc L_Y ^ 4 = L_Y ^ 3 * L_Y := by ring
      _ ≤ _ := Nat.mul_le_mul h1 hDZ
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Nat.le_add_left _ _)
  calc L_Y ^ 5 = L_Y * L_Y ^ 4 := by ring
    _ ≤ L_Y * (((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z) :=
        Nat.mul_le_mul_left L_Y hB3
    _ ≤ L_Y * max _ _ := Nat.mul_le_mul_left L_Y (le_max_left _ _)

/-! ## 2. Additive Degree Bounds on Bivariate & Trivariate Polynomials -/

section DegreeHelpers

variable {F : Type*} [Field F]

/-- Maximum `X`-degree appearing among all `Y`-coefficients of `Q : ((F[Z])[X])[Y]`. -/
noncomputable def maxXDeg (Q : ((F[X])[X])[X]) : ℕ :=
  Q.support.sup fun j => (Q.coeff j).natDegree

theorem coeff_natDegree_le_maxXDeg (Q : ((F[X])[X])[X]) (j : ℕ) :
    (Q.coeff j).natDegree ≤ maxXDeg Q := by
  by_cases hj : j ∈ Q.support
  · exact Finset.le_sup (f := fun j' => (Q.coeff j').natDegree) hj
  · have h0 : Q.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    rw [h0, natDegree_zero]; exact Nat.zero_le _

theorem coeff_coeff_natDegree_le_maxZDeg (Q : ((F[X])[X])[X]) (j i : ℕ) :
    ((Q.coeff j).coeff i).natDegree ≤ maxZDeg Q := by
  by_cases hj : j ∈ Q.support
  · by_cases hi : i ∈ (Q.coeff j).support
    · exact (Finset.le_sup (f := fun i' => ((Q.coeff j).coeff i').natDegree) hi).trans
        (Finset.le_sup (f := fun j' => (Q.coeff j').support.sup fun i' =>
          ((Q.coeff j').coeff i').natDegree) hj)
    · have h0 : (Q.coeff j).coeff i = 0 := by simpa [Polynomial.mem_support_iff] using hi
      rw [h0, natDegree_zero]; exact Nat.zero_le _
  · have h0 : Q.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    rw [h0, coeff_zero, natDegree_zero]; exact Nat.zero_le _

theorem maxZDeg_le_iff {Q : ((F[X])[X])[X]} {B : ℕ} :
    maxZDeg Q ≤ B ↔ ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ B := by
  constructor
  · intro h j i; exact (coeff_coeff_natDegree_le_maxZDeg Q j i).trans h
  · intro h
    unfold maxZDeg
    exact Finset.sup_le fun j _ => Finset.sup_le fun i _ => h j i

theorem maxXDeg_le_iff {Q : ((F[X])[X])[X]} {B : ℕ} :
    maxXDeg Q ≤ B ↔ ∀ j, (Q.coeff j).natDegree ≤ B := by
  constructor
  · intro h j; exact (coeff_natDegree_le_maxXDeg Q j).trans h
  · intro h
    unfold maxXDeg
    exact Finset.sup_le fun j _ => h j

theorem maxCoeffDeg_le_iff {p : (F[X])[X]} {B : ℕ} :
    maxCoeffDeg p ≤ B ↔ ∀ j, (p.coeff j).natDegree ≤ B := by
  constructor
  · intro h j; exact (coeff_natDegree_le_maxCoeffDeg p j).trans h
  · intro h
    unfold maxCoeffDeg
    exact Finset.sup_le fun j _ => h j

/-- Additivity of `maxCoeffDeg` for nonzero bivariate polynomials `f, g : (F[Z])[T]`. -/
theorem maxCoeffDeg_mul {f g : (F[X])[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    maxCoeffDeg (f * g) = maxCoeffDeg f + maxCoeffDeg g := by
  apply le_antisymm
  · rw [maxCoeffDeg_le_iff]
    intro j
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    exact (Polynomial.natDegree_mul_le).trans
      (Nat.add_le_add (coeff_natDegree_le_maxCoeffDeg f x.1) (coeff_natDegree_le_maxCoeffDeg g x.2))
  · -- Pick largest `j_f` attaining `maxCoeffDeg f` and largest `j_g` attaining `maxCoeffDeg g`.
    have hex_max : ∀ (p : (F[X])[X]), p ≠ 0 →
        ∃ j₀, p.coeff j₀ ≠ 0 ∧ (p.coeff j₀).natDegree = maxCoeffDeg p ∧
          ∀ j, j₀ < j → p.coeff j = 0 ∨ (p.coeff j).natDegree < maxCoeffDeg p := by
      intro p hp
      have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
      obtain ⟨j', hj', hmax'⟩ := Finset.exists_mem_eq_sup p.support hsupp (fun j => (p.coeff j).natDegree)
      let S := p.support.filter fun j => (p.coeff j).natDegree = maxCoeffDeg p
      have hSne : S.Nonempty := ⟨j', Finset.mem_filter.mpr ⟨hj', hmax'.symm⟩⟩
      let j₀ := S.max' hSne
      have hj₀ : j₀ ∈ S := Finset.max'_mem S hSne
      refine ⟨j₀, Polynomial.mem_support_iff.mp (Finset.mem_filter.mp hj₀).1,
        (Finset.mem_filter.mp hj₀).2, fun j hj => ?_⟩
      by_cases hjs : j ∈ p.support
      · right
        have hle := coeff_natDegree_le_maxCoeffDeg p j
        have hne : (p.coeff j).natDegree ≠ maxCoeffDeg p := by
          intro heq
          have hmem : j ∈ S := Finset.mem_filter.mpr ⟨hjs, heq⟩
          exact absurd (Finset.le_max' S j hmem) (not_le_of_gt hj)
        omega
      · left; simpa [Polynomial.mem_support_iff] using hjs
    obtain ⟨jf, hfn0, hfd, hfmax⟩ := hex_max f hf
    obtain ⟨jg, hgn0, hgd, hgmax⟩ := hex_max g hg
    set df := maxCoeffDeg f
    set dg := maxCoeffDeg g
    refine le_trans ?_ (coeff_natDegree_le_maxCoeffDeg (f * g) (jf + jg))
    have hcoeff_ne : (((f * g).coeff (jf + jg)).coeff (df + dg)) ≠ 0 := by
      rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      have hmem : (jf, jg) ∈ Finset.antidiagonal (jf + jg) := Finset.mem_antidiagonal.mpr rfl
      rw [← Finset.add_sum_erase _ _ hmem]
      have hother : ∑ x ∈ (Finset.antidiagonal (jf + jg)).erase (jf, jg),
          (f.coeff x.1 * g.coeff x.2).coeff (df + dg) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hne : x ≠ (jf, jg) := (Finset.mem_erase.mp hx).1
        have hsum : x.1 + x.2 = jf + jg := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
        have hlt : (f.coeff x.1 * g.coeff x.2).natDegree < df + dg ∨ f.coeff x.1 * g.coeff x.2 = 0 := by
          by_cases h1 : jf < x.1
          · rcases hfmax x.1 h1 with h0 | hdeg
            · right; simp [h0]
            · left; exact lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_lt_of_le hdeg (coeff_natDegree_le_maxCoeffDeg g x.2))
          · have h2 : jg < x.2 := by
              by_contra hle; apply hne; ext <;> dsimp only <;> omega
            rcases hgmax x.2 h2 with h0 | hdeg
            · right; simp [h0]
            · left; exact lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_le_of_lt (coeff_natDegree_le_maxCoeffDeg f x.1) hdeg)
        rcases hlt with hlt | h0
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        · simp [h0]
      rw [hother, add_zero]
      have hdeg_eq : (f.coeff jf * g.coeff jg).natDegree = df + dg := by
        rw [Polynomial.natDegree_mul hfn0 hgn0, hfd, hgd]
      rw [← hdeg_eq]
      exact Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hfn0 hgn0)
    exact Polynomial.le_natDegree_of_ne_zero hcoeff_ne

/-- Additivity of `maxXDeg` for nonzero trivariate polynomials `A, B : ((F[Z])[X])[Y]`. -/
theorem maxXDeg_mul {A B : ((F[X])[X])[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    maxXDeg (A * B) = maxXDeg A + maxXDeg B := by
  apply le_antisymm
  · rw [maxXDeg_le_iff]
    intro j
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    exact (Polynomial.natDegree_mul_le).trans
      (Nat.add_le_add (coeff_natDegree_le_maxXDeg A x.1) (coeff_natDegree_le_maxXDeg B x.2))
  · have hex_max : ∀ (P : ((F[X])[X])[X]), P ≠ 0 →
        ∃ j₀, P.coeff j₀ ≠ 0 ∧ (P.coeff j₀).natDegree = maxXDeg P ∧
          ∀ j, j₀ < j → P.coeff j = 0 ∨ (P.coeff j).natDegree < maxXDeg P := by
      intro P hP
      have hsupp : P.support.Nonempty := Polynomial.support_nonempty.mpr hP
      obtain ⟨j', hj', hmax'⟩ := Finset.exists_mem_eq_sup P.support hsupp (fun j => (P.coeff j).natDegree)
      let S := P.support.filter fun j => (P.coeff j).natDegree = maxXDeg P
      have hSne : S.Nonempty := ⟨j', Finset.mem_filter.mpr ⟨hj', hmax'.symm⟩⟩
      let j₀ := S.max' hSne
      have hj₀ : j₀ ∈ S := Finset.max'_mem S hSne
      refine ⟨j₀, Polynomial.mem_support_iff.mp (Finset.mem_filter.mp hj₀).1,
        (Finset.mem_filter.mp hj₀).2, fun j hj => ?_⟩
      by_cases hjs : j ∈ P.support
      · right
        have hle := coeff_natDegree_le_maxXDeg P j
        have hne : (P.coeff j).natDegree ≠ maxXDeg P := by
          intro heq
          exact absurd (Finset.le_max' S j (Finset.mem_filter.mpr ⟨hjs, heq⟩)) (not_le_of_gt hj)
        omega
      · left; simpa [Polynomial.mem_support_iff] using hjs
    obtain ⟨jA, hAn0, hAd, hAmax⟩ := hex_max A hA
    obtain ⟨jB, hBn0, hBd, hBmax⟩ := hex_max B hB
    set dA := maxXDeg A
    set dB := maxXDeg B
    refine le_trans ?_ (coeff_natDegree_le_maxXDeg (A * B) (jA + jB))
    have hcoeff_ne : (((A * B).coeff (jA + jB)).coeff (dA + dB)) ≠ 0 := by
      rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      have hmem : (jA, jB) ∈ Finset.antidiagonal (jA + jB) := Finset.mem_antidiagonal.mpr rfl
      rw [← Finset.add_sum_erase _ _ hmem]
      have hother : ∑ x ∈ (Finset.antidiagonal (jA + jB)).erase (jA, jB),
          (A.coeff x.1 * B.coeff x.2).coeff (dA + dB) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hne : x ≠ (jA, jB) := (Finset.mem_erase.mp hx).1
        have hsum : x.1 + x.2 = jA + jB := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
        have hlt : (A.coeff x.1 * B.coeff x.2).natDegree < dA + dB ∨ A.coeff x.1 * B.coeff x.2 = 0 := by
          by_cases h1 : jA < x.1
          · rcases hAmax x.1 h1 with h0 | hdeg
            · right; simp [h0]
            · left; exact lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_lt_of_le hdeg (coeff_natDegree_le_maxXDeg B x.2))
          · have h2 : jB < x.2 := by
              by_contra hle; apply hne; ext <;> dsimp only <;> omega
            rcases hBmax x.2 h2 with h0 | hdeg
            · right; simp [h0]
            · left; exact lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_le_of_lt (coeff_natDegree_le_maxXDeg A x.1) hdeg)
        rcases hlt with hlt | h0
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
        · simp [h0]
      rw [hother, add_zero]
      have hdeg_eq : (A.coeff jA * B.coeff jB).natDegree = dA + dB := by
        rw [Polynomial.natDegree_mul hAn0 hBn0, hAd, hBd]
      rw [← hdeg_eq]
      exact Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hAn0 hBn0)
    exact Polynomial.le_natDegree_of_ne_zero hcoeff_ne

/-- Additivity of `maxZDeg` for nonzero trivariate polynomials `A, B : ((F[Z])[X])[Y]`. -/
theorem maxZDeg_mul {A B : ((F[X])[X])[X]} (hA : A ≠ 0) (hB : B ≠ 0) :
    maxZDeg (A * B) = maxZDeg A + maxZDeg B := by
  apply le_antisymm
  · rw [maxZDeg_le_iff]
    intro j i
    rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun y _ => ?_
    exact (Polynomial.natDegree_mul_le).trans
      (Nat.add_le_add (coeff_coeff_natDegree_le_maxZDeg A x.1 y.1)
        (coeff_coeff_natDegree_le_maxZDeg B x.2 y.2))
  · -- Pick lexicographically largest `(j₀, i₀)` attaining `maxZDeg P`.
    have hex_max : ∀ (P : ((F[X])[X])[X]), P ≠ 0 →
        ∃ j₀ i₀, ((P.coeff j₀).coeff i₀) ≠ 0 ∧ ((P.coeff j₀).coeff i₀).natDegree = maxZDeg P ∧
          (∀ j i, j₀ < j → ((P.coeff j).coeff i) = 0 ∨ ((P.coeff j).coeff i).natDegree < maxZDeg P) ∧
          (∀ i, i₀ < i → ((P.coeff j₀).coeff i) = 0 ∨ ((P.coeff j₀).coeff i).natDegree < maxZDeg P) := by
      intro P hP
      have hsupp : P.support.Nonempty := Polynomial.support_nonempty.mpr hP
      obtain ⟨j', hj', hmaxJ⟩ := Finset.exists_mem_eq_sup P.support hsupp
        (fun j => (P.coeff j).support.sup fun i => ((P.coeff j).coeff i).natDegree)
      let SJ := P.support.filter fun j =>
        (P.coeff j).support.sup (fun i => ((P.coeff j).coeff i).natDegree) = maxZDeg P
      have hSJne : SJ.Nonempty := ⟨j', Finset.mem_filter.mpr ⟨hj', hmaxJ.symm⟩⟩
      let j₀ := SJ.max' hSJne
      have hj₀ : j₀ ∈ SJ := Finset.max'_mem SJ hSJne
      have hj₀_supp : j₀ ∈ P.support := (Finset.mem_filter.mp hj₀).1
      have hj₀_val : (P.coeff j₀).support.sup (fun i => ((P.coeff j₀).coeff i).natDegree) = maxZDeg P :=
        (Finset.mem_filter.mp hj₀).2
      have hisupp : (P.coeff j₀).support.Nonempty :=
        Polynomial.support_nonempty.mpr (Polynomial.mem_support_iff.mp hj₀_supp)
      obtain ⟨i', hi', hmaxI⟩ := Finset.exists_mem_eq_sup (P.coeff j₀).support hisupp
        (fun i => ((P.coeff j₀).coeff i).natDegree)
      let SI := (P.coeff j₀).support.filter fun i => ((P.coeff j₀).coeff i).natDegree = maxZDeg P
      have hSIne : SI.Nonempty := ⟨i', Finset.mem_filter.mpr ⟨hi', hmaxI.symm.trans hj₀_val⟩⟩
      let i₀ := SI.max' hSIne
      have hi₀ : i₀ ∈ SI := Finset.max'_mem SI hSIne
      refine ⟨j₀, i₀, Polynomial.mem_support_iff.mp (Finset.mem_filter.mp hi₀).1,
        (Finset.mem_filter.mp hi₀).2, ?_, ?_⟩
      · intro j i hgt
        by_cases hjs : j ∈ P.support
        · right
          have hsup_le : (P.coeff j).support.sup (fun i' => ((P.coeff j).coeff i').natDegree) ≤ maxZDeg P :=
            Finset.le_sup (f := fun j' => (P.coeff j').support.sup fun i' =>
              ((P.coeff j').coeff i').natDegree) hjs
          have hsup_ne : (P.coeff j).support.sup (fun i' => ((P.coeff j).coeff i').natDegree) ≠ maxZDeg P := by
            intro heq
            exact absurd (Finset.le_max' SJ j (Finset.mem_filter.mpr ⟨hjs, heq⟩)) (not_le_of_gt hgt)
          have hlt_sup : (P.coeff j).support.sup (fun i' => ((P.coeff j).coeff i').natDegree) < maxZDeg P := by
            omega
          by_cases his : i ∈ (P.coeff j).support
          · exact lt_of_le_of_lt (Finset.le_sup (f := fun i' => ((P.coeff j).coeff i').natDegree) his) hlt_sup
          · have h0 : (P.coeff j).coeff i = 0 := by simpa [Polynomial.mem_support_iff] using his
            rw [h0, natDegree_zero]; omega
        · left
          have h0 : P.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hjs
          simp [h0]
      · intro i hgt
        by_cases his : i ∈ (P.coeff j₀).support
        · right
          have hle := coeff_coeff_natDegree_le_maxZDeg P j₀ i
          have hne : ((P.coeff j₀).coeff i).natDegree ≠ maxZDeg P := by
            intro heq
            exact absurd (Finset.le_max' SI i (Finset.mem_filter.mpr ⟨his, heq⟩)) (not_le_of_gt hgt)
          omega
        · left; simpa [Polynomial.mem_support_iff] using his
    obtain ⟨jA, iA, hAn0, hAd, hAjmax, hAimax⟩ := hex_max A hA
    obtain ⟨jB, iB, hBn0, hBd, hBjmax, hBimax⟩ := hex_max B hB
    set dA := maxZDeg A
    set dB := maxZDeg B
    refine le_trans ?_ (coeff_coeff_natDegree_le_maxZDeg (A * B) (jA + jB) (iA + iB))
    have hcoeff_ne : ((((A * B).coeff (jA + jB)).coeff (iA + iB)).coeff (dA + dB)) ≠ 0 := by
      rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
      have hmemJ : (jA, jB) ∈ Finset.antidiagonal (jA + jB) := Finset.mem_antidiagonal.mpr rfl
      rw [← Finset.add_sum_erase _ _ hmemJ]
      have hotherJ : ∑ x ∈ (Finset.antidiagonal (jA + jB)).erase (jA, jB),
          ((A.coeff x.1 * B.coeff x.2).coeff (iA + iB)).coeff (dA + dB) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hne : x ≠ (jA, jB) := (Finset.mem_erase.mp hx).1
        have hsum : x.1 + x.2 = jA + jB := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hx).2
        rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
        refine Finset.sum_eq_zero fun y _ => ?_
        by_cases h1 : jA < x.1
        · rcases hAjmax x.1 y.1 h1 with h0 | hdeg
          · simp [h0]
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_lt_of_le hdeg (coeff_coeff_natDegree_le_maxZDeg B x.2 y.2)))
        · have h2 : jB < x.2 := by
            by_contra hle; apply hne; ext <;> dsimp only <;> omega
          rcases hBjmax x.2 y.2 h2 with h0 | hdeg
          · simp [h0]
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_le_of_lt (coeff_coeff_natDegree_le_maxZDeg A x.1 y.1) hdeg))
      rw [hotherJ, add_zero, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      have hmemI : (iA, iB) ∈ Finset.antidiagonal (iA + iB) := Finset.mem_antidiagonal.mpr rfl
      rw [← Finset.add_sum_erase _ _ hmemI]
      have hotherI : ∑ y ∈ (Finset.antidiagonal (iA + iB)).erase (iA, iB),
          ((A.coeff jA).coeff y.1 * (B.coeff jB).coeff y.2).coeff (dA + dB) = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hne : y ≠ (iA, iB) := (Finset.mem_erase.mp hy).1
        have hsum : y.1 + y.2 = iA + iB := Finset.mem_antidiagonal.mp (Finset.mem_erase.mp hy).2
        by_cases h1 : iA < y.1
        · rcases hAimax y.1 h1 with h0 | hdeg
          · simp [h0]
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_lt_of_le hdeg (coeff_coeff_natDegree_le_maxZDeg B jB y.2)))
        · have h2 : iB < y.2 := by
            by_contra hle; apply hne; ext <;> dsimp only <;> omega
          rcases hBimax y.2 h2 with h0 | hdeg
          · simp [h0]
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt
              (lt_of_le_of_lt Polynomial.natDegree_mul_le
                (Nat.add_lt_add_of_le_of_lt (coeff_coeff_natDegree_le_maxZDeg A jA y.1) hdeg))
      rw [hotherI, add_zero]
      have hdeg_eq : ((A.coeff jA).coeff iA * (B.coeff jB).coeff iB).natDegree = dA + dB := by
        rw [Polynomial.natDegree_mul hAn0 hBn0, hAd, hBd]
      rw [← hdeg_eq]
      exact Polynomial.leadingCoeff_ne_zero.mpr (mul_ne_zero hAn0 hBn0)
    exact Polynomial.le_natDegree_of_ne_zero hcoeff_ne

theorem maxZDeg_le_of_dvd {A B : ((F[X])[X])[X]} (hB : B ≠ 0) (hdvd : A ∣ B) :
    maxZDeg A ≤ maxZDeg B := by
  obtain ⟨C, rfl⟩ := hdvd
  have hA : A ≠ 0 := left_ne_zero_of_mul hB
  have hC : C ≠ 0 := right_ne_zero_of_mul hB
  rw [maxZDeg_mul hA hC]
  exact Nat.le_add_right _ _

theorem maxXDeg_le_of_dvd {A B : ((F[X])[X])[X]} (hB : B ≠ 0) (hdvd : A ∣ B) :
    maxXDeg A ≤ maxXDeg B := by
  obtain ⟨C, rfl⟩ := hdvd
  have hA : A ≠ 0 := left_ne_zero_of_mul hB
  have hC : C ≠ 0 := right_ne_zero_of_mul hB
  rw [maxXDeg_mul hA hC]
  exact Nat.le_add_right _ _

theorem maxCoeffDeg_le_of_dvd {f g : (F[X])[X]} (hg : g ≠ 0) (hdvd : f ∣ g) :
    maxCoeffDeg f ≤ maxCoeffDeg g := by
  obtain ⟨h, rfl⟩ := hdvd
  have hf : f ≠ 0 := left_ne_zero_of_mul hg
  have hh : h ≠ 0 := right_ne_zero_of_mul hg
  rw [maxCoeffDeg_mul hf hh]
  exact Nat.le_add_right _ _

theorem list_prod_natDegree {A : Type*} [CommRing A] [IsDomain A] :
    ∀ (l : List A[X]), (∀ f ∈ l, f ≠ 0) → l.prod.natDegree = (l.map Polynomial.natDegree).sum
  | [], _ => by simp
  | a :: l, h => by
    have ha : a ≠ 0 := h a (List.mem_cons_self ..)
    have hl : ∀ f ∈ l, f ≠ 0 := fun f hf => h f (List.mem_cons_of_mem _ hf)
    have hlp : l.prod ≠ 0 := List.prod_ne_zero fun h0 => hl 0 h0 rfl
    rw [List.prod_cons, List.map_cons, List.sum_cons, Polynomial.natDegree_mul ha hlp,
      list_prod_natDegree l hl]

theorem list_prod_maxZDeg :
    ∀ (l : List ((F[X])[X])[X]), (∀ f ∈ l, f ≠ 0) → maxZDeg l.prod = (l.map maxZDeg).sum
  | [], _ => by
    simp only [List.prod_nil, List.map_nil, List.sum_nil]
    apply Nat.eq_zero_of_le_zero
    rw [maxZDeg_le_iff]
    intro j i
    rw [Polynomial.coeff_one]
    split_ifs
    · rw [Polynomial.coeff_one]; split_ifs <;> simp
    · simp
  | a :: l, h => by
    have ha : a ≠ 0 := h a (List.mem_cons_self ..)
    have hl : ∀ f ∈ l, f ≠ 0 := fun f hf => h f (List.mem_cons_of_mem _ hf)
    have hlp : l.prod ≠ 0 := List.prod_ne_zero fun h0 => hl 0 h0 rfl
    rw [List.prod_cons, List.map_cons, List.sum_cons, maxZDeg_mul ha hlp,
      list_prod_maxZDeg l hl]

theorem list_prod_maxCoeffDeg :
    ∀ (l : List (F[X])[X]), (∀ f ∈ l, f ≠ 0) → maxCoeffDeg l.prod = (l.map maxCoeffDeg).sum
  | [], _ => by
    simp only [List.prod_nil, List.map_nil, List.sum_nil]
    apply Nat.eq_zero_of_le_zero
    rw [maxCoeffDeg_le_iff]
    intro j
    rw [Polynomial.coeff_one]; split_ifs <;> simp
  | a :: l, h => by
    have ha : a ≠ 0 := h a (List.mem_cons_self ..)
    have hl : ∀ f ∈ l, f ≠ 0 := fun f hf => h f (List.mem_cons_of_mem _ hf)
    have hlp : l.prod ≠ 0 := List.prod_ne_zero fun h0 => hl 0 h0 rfl
    rw [List.prod_cons, List.map_cons, List.sum_cons, maxCoeffDeg_mul ha hlp,
      list_prod_maxCoeffDeg l hl]

end DegreeHelpers

/-! ## 3. Step 1: Direct `F`-Linear Low-`Z`-Degree Guruswami–Sudan Interpolation -/

section LowZDegInterp

variable {F : Type*} [Field F]

/-- Curve polynomial `u_Z(x) = ∑ k, Z^k * u_k(x) ∈ F[Z]`. -/
noncomputable def curveWordZ {m : ℕ} (u : Fin m → F → F) (x : F) : F[X] :=
  ∑ k : Fin m, monomial (k : ℕ) (u k x)

theorem curveWordZ_natDegree_le {m : ℕ} (u : Fin m → F → F) (x : F) :
    (curveWordZ u x).natDegree ≤ m - 1 := by
  unfold curveWordZ
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem eval_curveWordZ {m : ℕ} (u : Fin m → F → F) (x β : F) :
    (curveWordZ u x).eval β = ∑ k : Fin m, β ^ (k : ℕ) * u k x := by
  unfold curveWordZ
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_monomial, mul_comm]

theorem coeff_curveWordZ {m : ℕ} (u : Fin m → F → F) (x : F) (k : Fin m) :
    (curveWordZ u x).coeff k.val = u k x := by
  unfold curveWordZ
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hne
    have : b.val ≠ k.val := fun h => hne (Fin.ext h)
    simp [this]
  · intro hmem; exact absurd (Finset.mem_univ k) hmem

/-- `F`-linear embedding from `((i, j), s) ∈ monomialPairs k D_X L_Y ×ˢ range (D_Z + 1)`
to trivariate polynomials `((F[Z])[X])[Y]`. -/
noncomputable def toTriv (k D_X L_Y D_Z : ℕ) :
    (monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) →ₗ[F] ((F[X])[X])[X] where
  toFun c :=
    ∑ q ∈ (monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1)).attach,
      C (monomial q.1.1.1 (monomial q.1.2 (c q))) * X ^ q.1.1.2
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hterm : ∀ q : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1),
        C (monomial q.1.1.1 (monomial q.1.2 (a * c q))) * X ^ q.1.1.2 =
        a • (C (monomial q.1.1.1 (monomial q.1.2 (c q))) * X ^ q.1.1.2) := by
      intro q
      apply Polynomial.ext; intro j
      apply Polynomial.ext; intro i
      apply Polynomial.ext; intro s
      simp only [Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_C_mul_X_pow]
      by_cases hj : j = q.1.1.2
      · simp only [hj, ↓reduceIte, Polynomial.coeff_monomial]
        by_cases hi : q.1.1.1 = i
        · simp only [hi, ↓reduceIte, Polynomial.coeff_monomial]
          by_cases hs : q.1.2 = s
          · simp only [hs, ↓reduceIte]
          · simp only [hs, ↓reduceIte, mul_zero]
        · simp only [hi, ↓reduceIte, coeff_zero, mul_zero]
      · simp only [hj, ↓reduceIte, coeff_zero, mul_zero]
    simp_rw [hterm, ← Finset.smul_sum]

theorem coeff_coeff_coeff_toTriv (k D_X L_Y D_Z : ℕ)
    (c : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) (i j s : ℕ) :
    (((toTriv k D_X L_Y D_Z c).coeff j).coeff i).coeff s =
      if h : ((i, j), s) ∈ monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) then
        c ⟨((i, j), s), h⟩
      else 0 := by
  simp only [toTriv, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  by_cases h : ((i, j), s) ∈ monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1)
  · rw [dite_eq_left h]
    have hterm : ∀ q ∈ (monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1)).attach,
        (((if j = q.1.1.2 then monomial q.1.1.1 (monomial q.1.2 (c q)) else 0).coeff i).coeff s) =
          if q = ⟨((i, j), s), h⟩ then c q else 0 := by
      intro q _
      split_ifs with h1 h2 h2
      · subst h2; simp
      · rw [Polynomial.coeff_monomial]
        split_ifs with h3
        · rw [Polynomial.coeff_monomial]
          split_ifs with h4
          · exfalso; apply h2; ext <;> simp [h3, h1, h4]
          · rfl
        · simp
      · subst h2; exact absurd rfl h1
      · simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    simp
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h1
    · rw [Polynomial.coeff_monomial]
      split_ifs with h2
      · rw [Polynomial.coeff_monomial]
        split_ifs with h3
        · exfalso; apply h
          have heq : ((i, j), s) = q.1 := by ext <;> simp [h1, h2, h3]
          rw [heq]; exact q.2
        · rfl
      · simp
    · simp

theorem toTriv_injective (k D_X L_Y D_Z : ℕ) :
    Function.Injective (toTriv (F := F) k D_X L_Y D_Z) := by
  intro c₁ c₂ h
  funext ⟨⟨⟨i, j⟩, s⟩, hq⟩
  have hc := congrArg (fun Q : ((F[X])[X])[X] => ((Q.coeff j).coeff i).coeff s) h
  simpa [coeff_coeff_coeff_toTriv, hq] using hc

theorem toTriv_natDegree_le (k D_X L_Y D_Z : ℕ)
    (c : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) :
    (toTriv k D_X L_Y D_Z c).natDegree ≤ L_Y := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => ?_
  apply Polynomial.ext; intro i
  apply Polynomial.ext; intro s
  rw [coeff_coeff_coeff_toTriv, coeff_zero, coeff_zero, dite_eq_right]
  intro hmem
  have h1 := (Finset.mem_product.mp hmem).1
  simp only [monomialPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h1
  omega

theorem toTriv_maxXDeg_le (k D_X L_Y D_Z : ℕ)
    (c : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) :
    maxXDeg (toTriv k D_X L_Y D_Z c) ≤ D_X := by
  rw [maxXDeg_le_iff]
  intro j
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  apply Polynomial.ext; intro s
  rw [coeff_coeff_coeff_toTriv, coeff_zero, dite_eq_right]
  intro hmem
  have h1 := (Finset.mem_product.mp hmem).1
  simp only [monomialPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h1
  omega

theorem toTriv_maxZDeg_le (k D_X L_Y D_Z : ℕ)
    (c : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) :
    maxZDeg (toTriv k D_X L_Y D_Z c) ≤ D_Z := by
  rw [maxZDeg_le_iff]
  intro j i
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun s hs => ?_
  rw [coeff_coeff_coeff_toTriv, dite_eq_right]
  intro hmem
  have h2 := Finset.mem_range.mp (Finset.mem_product.mp hmem).2
  omega

theorem toTriv_evalZBiv_hasWeightedDegLE (k D_X L_Y D_Z : ℕ)
    (c : monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) (β : F) :
    HasWeightedDegLE k D_X (evalZBiv β (toTriv k D_X L_Y D_Z c)) := by
  intro j i hgt
  rw [evalZBiv, coeff_coeff_mapBivHom]
  have h0 : ((toTriv k D_X L_Y D_Z c).coeff j).coeff i = 0 := by
    apply Polynomial.ext; intro s
    rw [coeff_coeff_coeff_toTriv, coeff_zero, dite_eq_right]
    intro hmem
    have h1 := (Finset.mem_product.mp hmem).1
    simp only [monomialPairs, Finset.mem_filter] at h1
    omega
  rw [h0, map_zero]

/-- `shiftXRingHom (C x)` preserves `CoeffDegLE B` on `(F[Z])[X]`. -/
theorem coeffDegLE_shiftXRingHom_C {B : ℕ} {x : F} {p : (F[X])[X]}
    (hp : CoeffDegLE B p) : CoeffDegLE B (shiftXRingHom (C x) p) := by
  change CoeffDegLE B (p.eval₂ C (X + C (C x)))
  rw [Polynomial.eval₂_eq_sum_range]
  refine coeffDegLE_sum _ _ fun i _ => ?_
  have hpow : CoeffDegLE 0 ((X + C (C x) : (F[X])[X]) ^ i) := by
    have h1 : CoeffDegLE 0 (X + C (C x) : (F[X])[X]) :=
      coeffDegLE_add (coeffDegLE_X 0) (coeffDegLE_C (by simp))
    simpa using coeffDegLE_pow h1 i
  simpa using coeffDegLE_C_mul (hp i) hpow

/-- `shiftBivRing (C x) yZ Q` has `maxZDeg ≤ maxZDeg Q + Q.natDegree * yZ.natDegree`. -/
theorem maxZDeg_shiftBivRing_le {x : F} {yZ : F[X]} {Q : ((F[X])[X])[X]} :
    maxZDeg (shiftBivRing (C x) yZ Q) ≤ maxZDeg Q + Q.natDegree * yZ.natDegree := by
  rw [maxZDeg_le_iff]
  unfold shiftBivRing
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  have hpow : ∀ j b i, ((((X + C (C yZ) : ((F[X])[X])[X]) ^ j).coeff b).coeff i).natDegree ≤
      j * yZ.natDegree := by
    intro j
    induction j with
    | zero =>
      intro b i
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs
      · rw [Polynomial.coeff_one]; split_ifs <;> simp
      · simp
    | succ j ih =>
      intro b i
      rw [pow_succ, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun u _ => ?_
      rw [Polynomial.coeff_mul]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
      have hlin : (((X + C (C yZ) : ((F[X])[X])[X]).coeff u.2).coeff v.2).natDegree ≤ yZ.natDegree := by
        rw [Polynomial.coeff_add, Polynomial.coeff_add]
        refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · rw [Polynomial.coeff_X]; split_ifs
          · rw [Polynomial.coeff_one]; split_ifs <;> simp
          · simp
        · rw [Polynomial.coeff_C]; split_ifs
          · rw [Polynomial.coeff_C]; split_ifs <;> simp
          · simp
      exact (Polynomial.natDegree_mul_le).trans
        ((Nat.add_le_add (ih u.1 v.1) hlin).trans (le_of_eq (by ring)))
  intro b i
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj_le : j ≤ Q.natDegree :=
    (Polynomial.le_natDegree_of_mem_supp j hj).trans Polynomial.natDegree_map_le
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  rw [Polynomial.coeff_map]
  have hc : ((shiftXRingHom (C x) (Q.coeff j)).coeff v.1).natDegree ≤ maxZDeg Q :=
    coeffDegLE_shiftXRingHom_C (fun r => coeff_coeff_natDegree_le_maxZDeg Q j r) v.1
  exact (Polynomial.natDegree_mul_le).trans
    ((Nat.add_le_add hc (hpow j b v.2)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hj_le) _))

/-- `F`-linear map extracting all `(x, (a, b), s)` coefficients of the Hasse shifts
`shiftBivRing (C x) (curveWordZ u x) (toTriv k D_X L_Y D_Z c)`. -/
noncomputable def evalHasseZ [DecidableEq F] {m : ℕ} (D : Finset F) (u : Fin m → F → F)
    (k D_X L_Y D_Z r : ℕ) :
    (monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1) → F) →ₗ[F]
      ((D ×ˢ multPairs r) ×ˢ Finset.range (D_Z + (m - 1) * L_Y + 1) → F) where
  toFun c q :=
    (((shiftBivRing (C q.1.1.1) (curveWordZ u q.1.1.1) (toTriv k D_X L_Y D_Z c)).coeff
      q.1.1.2.2).coeff q.1.1.2.1).coeff q.1.2
  map_add' c₁ c₂ := by
    funext q
    simp only [Pi.add_apply, map_add, shiftBivRing, Polynomial.map_add, Polynomial.add_comp,
      Polynomial.coeff_add]
  map_smul' a c := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, LinearMap.map_smul]
    have hsmul : ∀ (Q : ((F[X])[X])[X]),
        a • Q = C (C (C a)) * Q := by
      intro Q
      apply Polynomial.ext; intro j
      apply Polynomial.ext; intro i
      apply Polynomial.ext; intro s
      simp [Polynomial.coeff_smul, Polynomial.coeff_C_mul]
    rw [hsmul]
    have hsh : shiftBivRing (C q.1.1.1) (curveWordZ u q.1.1.1) (C (C (C a)) * toTriv k D_X L_Y D_Z c) =
        C (C (C a)) * shiftBivRing (C q.1.1.1) (curveWordZ u q.1.1.1) (toTriv k D_X L_Y D_Z c) := by
      simp [shiftBivRing, shiftXRingHom, Polynomial.map_mul, Polynomial.mul_comp]
    rw [hsh, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]

private theorem exists_ne_zero_mem_ker {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → F) →ₗ[F] (β → F)) (hcard : Fintype.card β < Fintype.card α) :
    ∃ v : α → F, v ≠ 0 ∧ f v = 0 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hdom : Module.finrank F (α → F) = Fintype.card α := Module.finrank_fintype_fun_eq_card F
  have hcod : Module.finrank F (β → F) = Fintype.card β := Module.finrank_fintype_fun_eq_card F
  have hrle : Module.finrank F f.range ≤ Module.finrank F (β → F) := Submodule.finrank_le f.range
  have hker_pos : 0 < Module.finrank F f.ker := by omega
  have hker_ne : f.ker ≠ ⊥ := by
    intro hbot; rw [hbot, finrank_bot] at hker_pos; exact lt_irrefl 0 hker_pos
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  exact ⟨v, hv_ne, LinearMap.mem_ker.mp hv_mem⟩

/-- **Step 1 (`exists_gs_poly_curve_lowZDeg`):**
Direct `F`-linear Guruswami–Sudan interpolation producing a nonzero trivariate
polynomial `Q : ((F[Z])[X])[Y]` with `deg_Y ≤ L_Y`, `deg_X ≤ D_X < r * A`,
and sharp `Z`-degree `maxZDeg Q ≤ (r + 1) * (m - 1) * L_Y` (independent of `|D|`),
annihilating every degree-`< d` polynomial agreeing with `u_β` on `≥ A` points
for every `β ∈ F`. -/
theorem exists_gs_poly_curve_lowZDeg [DecidableEq F] (D : Finset F) (d A m : ℕ)
    (u : Fin m → F → F) (hD : 0 < D.card) (hd : 2 ≤ d) (hJ : D.card * (d - 1) < A ^ 2) :
    let r := gsMult D.card d A
    let D_X := gsDegX D.card d A
    let L_Y := gsDegY D.card d A
    let D_Z := (r + 1) * (m - 1) * L_Y
    ∃ Q : ((F[X])[X])[X],
      Q ≠ 0 ∧
      Q.natDegree ≤ L_Y ∧
      maxXDeg Q ≤ D_X ∧
      maxZDeg Q ≤ D_Z ∧
      (∀ β : F, HasWeightedDegLE (d - 1) D_X (evalZBiv β Q)) ∧
      (∀ β : F, ∀ x ∈ D, VanishesMult r x (∑ k : Fin m, β ^ (k : ℕ) * u k x) (evalZBiv β Q)) ∧
      (∀ (β : F) (p : F[X]),
        p.degree < d →
        A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x).card →
        (evalZBiv β Q).eval p = 0) := by
  intro r D_X L_Y D_Z
  set k := d - 1
  set n := D.card
  set gap := A ^ 2 - n * k
  have hkpos : 1 ≤ k := by omega
  have hgap_pos : 0 < gap := Nat.sub_pos_of_lt hJ
  have hApos : 1 ≤ A := by
    by_contra h0
    have : A = 0 := by omega
    simp [this] at hJ
  have hrpos : 1 ≤ r := Nat.succ_le_succ (Nat.zero_le _)
  have hDX_succ : D_X + 1 = r * A := Nat.sub_add_cancel (Nat.mul_pos hrpos hApos)
  have hLY_eq : L_Y = D_X / k := by
    dsimp only [L_Y, gsDegY]; rw [ite_eq_right (by omega)]
  -- Show `Fintype.card codomain < Fintype.card domain`!
  have hcard_lt :
      Fintype.card ((D ×ˢ multPairs r) ×ˢ Finset.range (D_Z + (m - 1) * L_Y + 1)) <
      Fintype.card (monomialPairs k D_X L_Y ×ˢ Finset.range (D_Z + 1)) := by
    simp only [Fintype.card_coe, Finset.card_product, Finset.card_range]
    set N_mon := (monomialPairs k D_X L_Y).card
    set M_eq := n * (multPairs r).card
    have hmon : (r * A) ^ 2 < 2 * k * N_mon := by
      have h := sq_lt_two_mul_card_monomialPairs hkpos D_X
      rwa [hDX_succ, ← hLY_eq] at h
    have hMeq : 2 * k * M_eq = n * k * r * (r + 1) := by
      have h2 := two_mul_card_multPairs r
      calc 2 * k * (n * (multPairs r).card) = n * k * (2 * (multPairs r).card) := by ring
        _ = n * k * (r * (r + 1)) := by rw [h2]
        _ = n * k * r * (r + 1) := by ring
    -- `r * gap > 2 * k * n`, so `r * gap - n * k > n * k`!
    have hrgap : 2 * k * n < r * gap := by
      change 2 * k * n < ((2 * k * n) / gap + 1) * gap
      have hmod := Nat.div_add_mod (2 * k * n) gap
      have hlt := Nat.mod_lt (2 * k * n) hgap_pos
      have hcomm : gap * ((2 * k * n) / gap) = ((2 * k * n) / gap) * gap := Nat.mul_comm _ _
      rw [Nat.add_mul, one_mul]
      omega
    have hdiff_gt : n * k * r < 2 * k * N_mon - 2 * k * M_eq := by
      have hAsq : A ^ 2 = n * k + gap := (Nat.add_sub_cancel' hJ.le).symm
      have hsub1 : n * k * r * (r + 1) + n * k * r < (r * A) ^ 2 := by
        have h1 : (r * A) ^ 2 = r ^ 2 * (n * k) + r * (r * gap) := by
          rw [mul_pow, hAsq]; ring
        rw [h1]
        have h2 : n * k * r * (r + 1) + n * k * r = r ^ 2 * (n * k) + r * (2 * k * n) := by ring
        rw [h2]
        exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hrgap hrpos) _
      rw [hMeq]; omega
    have hNgtM : M_eq < N_mon := by
      have : 2 * k * M_eq < 2 * k * N_mon := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    have h2k_ineq : 2 * k * (M_eq * ((m - 1) * L_Y)) < 2 * k * ((N_mon - M_eq) * (D_Z + 1)) := by
      have hL : 2 * k * (M_eq * ((m - 1) * L_Y)) = n * k * r * D_Z := by
        have : 2 * k * (M_eq * ((m - 1) * L_Y)) = (2 * k * M_eq) * ((m - 1) * L_Y) := by ring
        rw [this, hMeq]; dsimp only [D_Z]; ring
      have hR : 2 * k * ((N_mon - M_eq) * (D_Z + 1)) = (2 * k * N_mon - 2 * k * M_eq) * (D_Z + 1) := by
        rw [← Nat.mul_assoc, Nat.mul_sub_left_distrib]
      rw [hL, hR]
      calc n * k * r * D_Z
          < n * k * r * (D_Z + 1) :=
            Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self D_Z) (Nat.mul_pos (Nat.mul_pos hD hkpos) hrpos)
        _ ≤ (2 * k * N_mon - 2 * k * M_eq) * (D_Z + 1) :=
            Nat.mul_le_mul_right (D_Z + 1) hdiff_gt.le
    have hineq : M_eq * ((m - 1) * L_Y) < (N_mon - M_eq) * (D_Z + 1) :=
      Nat.lt_of_mul_lt_mul_left h2k_ineq
    have hadd : M_eq * (D_Z + (m - 1) * L_Y + 1) = M_eq * (D_Z + 1) + M_eq * ((m - 1) * L_Y) := by ring
    have hsub : (N_mon - M_eq) * (D_Z + 1) + M_eq * (D_Z + 1) = N_mon * (D_Z + 1) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hNgtM.le]
    omega
  obtain ⟨c, hc_ne, hc_ker⟩ := exists_ne_zero_mem_ker (evalHasseZ D u k D_X L_Y D_Z r) hcard_lt
  set Q := toTriv k D_X L_Y D_Z c
  have hQne : Q ≠ 0 := fun h0 =>
    hc_ne (toTriv_injective k D_X L_Y D_Z (h0.trans (map_zero _).symm))
  have hQdegY : Q.natDegree ≤ L_Y := toTriv_natDegree_le k D_X L_Y D_Z c
  have hQdegX : maxXDeg Q ≤ D_X := toTriv_maxXDeg_le k D_X L_Y D_Z c
  have hQdegZ : maxZDeg Q ≤ D_Z := toTriv_maxZDeg_le k D_X L_Y D_Z c
  have hQvanZ : ∀ x ∈ D, ∀ a b : ℕ, a + b < r →
      ((shiftBivRing (C x) (curveWordZ u x) Q).coeff b).coeff a = 0 := by
    intro x hx a b hab
    apply Polynomial.ext; intro s
    rw [coeff_zero]
    by_cases hs : s ≤ D_Z + (m - 1) * L_Y
    · have hmem : ((x, (a, b)), s) ∈ (D ×ˢ multPairs r) ×ˢ Finset.range (D_Z + (m - 1) * L_Y + 1) := by
        refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hx, ?_⟩, Finset.mem_range.mpr (by omega)⟩
        dsimp only
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩
      exact congrFun hc_ker ⟨((x, (a, b)), s), hmem⟩
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have hdeg := (coeff_coeff_natDegree_le_maxZDeg (shiftBivRing (C x) (curveWordZ u x) Q) b a).trans
        maxZDeg_shiftBivRing_le
      have hu := curveWordZ_natDegree_le u x
      have hmul : Q.natDegree * (curveWordZ u x).natDegree ≤ (m - 1) * L_Y := by
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul hu hQdegY
      omega
  have hQvan : ∀ β : F, ∀ x ∈ D,
      VanishesMult r x (∑ k : Fin m, β ^ (k : ℕ) * u k x) (evalZBiv β Q) := by
    intro β x hx a b hab
    rw [← shiftBivRing_eq_shiftBiv, ← eval_curveWordZ u x β]
    have hshift_eq : shiftBivRing x ((curveWordZ u x).eval β) (evalZBiv β Q) =
        evalZBiv β (shiftBivRing (C x) (curveWordZ u x) Q) := by
      rw [evalZBiv, mapBivHom_shiftBivRing]
      simp
    rw [hshift_eq, evalZBiv, coeff_coeff_mapBivHom, hQvanZ x hx a b hab, map_zero]
  refine ⟨Q, hQne, hQdegY, hQdegX, hQdegZ,
    fun β => toTriv_evalZBiv_hasWeightedDegLE k D_X L_Y D_Z c β, hQvan, ?_⟩
  intro β p hp hagree
  exact eval_eq_zero_of_agree_ge (toTriv_evalZBiv_hasWeightedDegLE k D_X L_Y D_Z c β)
    (hQvan β) hp hagree (by omega)

end LowZDegInterp

/-! ## 4. Step 2: UFD Factorization, Characteristic-`p` Separability, and Weighted Pigeonhole -/

section FactorAndPigeonhole

variable {F : Type*} [Field F]

/-- Over a UFD `A`, every irreducible `f : A[X]` of positive degree is primitive and
remains irreducible in `K[X]` for any fraction field `K` of `A`. -/
theorem irreducible_map_fraction_map_of_natDegree_pos {A : Type*} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {f : A[X]} (hirr : Irreducible f) (hpos : 1 ≤ f.natDegree) :
    Irreducible (f.map (algebraMap A K)) := by
  let _ : GCDMonoid A := UniqueFactorizationMonoid.toGCDMonoid A
  have hprim : f.IsPrimitive := by
    rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
    intro r hr
    obtain ⟨q, hq⟩ := hr
    rcases hirr.isUnit_or_isUnit hq with huC | huq
    · exact Polynomial.isUnit_C.mp huC
    · exfalso
      obtain ⟨u, _, hu_eq⟩ := Polynomial.isUnit_iff.mp huq
      have hdeg : f.natDegree = 0 := by
        rw [hq, ← hu_eq, ← map_mul, Polynomial.natDegree_C]
      omega
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hirr

/-- Non-vanishing of the Sylvester discriminant of an irreducible polynomial
`R : ((F[Z])[X])[Y]` with `1 ≤ R.natDegree` and (`p = 0 ∨ R.natDegree < p`). -/
theorem sylvesterDet_derivative_ne_zero {p : ℕ} [CharP F p] {R : ((F[X])[X])[X]}
    (hirr : Irreducible R) (hpos : 1 ≤ R.natDegree) (hchar : p = 0 ∨ R.natDegree < p) :
    Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R R.derivative ≠ 0 := by
  set K := FractionRing (F[X])[X]
  set φ := algebraMap (F[X])[X] K
  have hφ_inj : Function.Injective φ := IsFractionRing.injective (F[X])[X] K
  set R_K := R.map φ
  have hirr_K : Irreducible R_K := irreducible_map_fraction_map_of_natDegree_pos hirr hpos
  have hdeg_K : R_K.natDegree = R.natDegree := Polynomial.natDegree_map_eq_of_injective hφ_inj R
  have hsep : R_K.Separable := by
    rcases hchar with hp0 | hlt
    · subst hp0
      have : CharZero F := CharP.charP_to_charZero F
      have : CharZero (F[X])[X] := inferInstance
      have : CharZero K := IsFractionRing.charZero_of_isFractionRing (F[X])[X]
      exact hirr_K.separable
    · have : CharP (F[X])[X] p := inferInstance
      have : CharP K p := IsFractionRing.charP_of_isFractionRing (F[X])[X] p
      exact CurveListBridge.separable_of_irreducible_natDegree_lt_char hirr_K (by omega)
  have hder_deg : R_K.derivative.natDegree ≤ max (R.natDegree - 1) 1 :=
    (Polynomial.natDegree_derivative_le R_K).trans (by omega)
  have hdet_K : Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R_K R_K.derivative ≠ 0 :=
    Sylvester.sylvesterDet_ne_zero_of_isCoprime hpos (le_max_right _ _) hdeg_K hder_deg hsep
  intro h0
  apply hdet_K
  have hmap := Sylvester.map_sylvesterDet φ R.natDegree (max (R.natDegree - 1) 1) R R.derivative
  rw [h0, map_zero, ← Polynomial.derivative_map] at hmap
  exact hmap.symm

/-- Number of `x ∈ G` at which a nonzero `f : (F[Z])[X]` vanishes (`f.eval (C x) = 0`)
is at most `f.natDegree`. -/
theorem card_eval_C_eq_zero_le [DecidableEq F] {f : (F[X])[X]} (hf : f ≠ 0) (G : Finset F) :
    (G.filter fun x => f.eval (C x) = 0).card ≤ f.natDegree := by
  classical
  have hsupp : f.support.Nonempty := Polynomial.support_nonempty.mpr hf
  obtain ⟨i₀, hi₀⟩ := hsupp
  have hci₀ : f.coeff i₀ ≠ 0 := Polynomial.mem_support_iff.mp hi₀
  obtain ⟨k₀, hk₀⟩ := Polynomial.support_nonempty.mpr hci₀
  have hck₀ : (f.coeff i₀).coeff k₀ ≠ 0 := Polynomial.mem_support_iff.mp hk₀
  let g : F[X] := ∑ i ∈ Finset.range (f.natDegree + 1), monomial i ((f.coeff i).coeff k₀)
  have hg_deg : g.natDegree ≤ f.natDegree := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hg_ne : g ≠ 0 := by
    intro hg0
    have hc := congrArg (fun q : F[X] => q.coeff i₀) hg0
    rw [coeff_zero] at hc
    dsimp only [g] at hc
    rw [Polynomial.finsetSum_coeff] at hc
    simp_rw [Polynomial.coeff_monomial] at hc
    have hi₀_mem : i₀ ∈ Finset.range (f.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_mem_supp i₀ hi₀))
    rw [Finset.sum_eq_single i₀] at hc
    · simp [hck₀] at hc
    · intro b _ hne; simp [hne]
    · intro hnm; exact absurd hi₀_mem hnm
  have hg_eval : ∀ x : F, g.eval x = (f.eval (C x)).coeff k₀ := by
    intro x
    dsimp only [g]
    rw [Polynomial.eval_finsetSum, Polynomial.eval_eq_sum_range, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_monomial, ← C_pow, mul_comm (f.coeff i), Polynomial.coeff_C_mul, mul_comm]
  have hsub : (G.filter fun x => f.eval (C x) = 0) ⊆ g.roots.toFinset := by
    intro x hx
    have h0 : f.eval (C x) = 0 := (Finset.mem_filter.mp hx).2
    have hgx : g.eval x = 0 := by rw [hg_eval, h0, coeff_zero]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hg_ne).mpr hgx)
  exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' g).trans hg_deg))

/-- Ring automorphism shifting inner `X ↦ X + C x₀` on `((F[Z])[X])[Y]`. -/
noncomputable def shiftXTriv (x₀ : F) : ((F[X])[X])[X] ≃+* ((F[X])[X])[X] where
  toFun P := P.map (shiftXRingHom (C x₀))
  invFun P := P.map (shiftXRingHom (C (-x₀)))
  left_inv P := by
    dsimp only
    rw [Polynomial.map_map]
    have h1 : (shiftXRingHom (C (-x₀) : F[X])).comp (shiftXRingHom (C x₀)) = RingHom.id (F[X])[X] := by
      apply Polynomial.ringHom_ext
      · intro a; simp [shiftXRingHom]
      · simp [shiftXRingHom]
    rw [h1, Polynomial.map_id]
  right_inv P := by
    dsimp only
    rw [Polynomial.map_map]
    have h1 : (shiftXRingHom (C x₀ : F[X])).comp (shiftXRingHom (C (-x₀))) = RingHom.id (F[X])[X] := by
      apply Polynomial.ringHom_ext
      · intro a; simp [shiftXRingHom]
      · simp [shiftXRingHom]
    rw [h1, Polynomial.map_id]
  map_mul' P Q := Polynomial.map_mul _
  map_add' P Q := Polynomial.map_add _

private theorem shiftXRingHom_injective (x₀ : F) :
    Function.Injective (shiftXRingHom (C x₀ : F[X])) := by
  intro p q h
  have h1 := congrArg (shiftXRingHom (C (-x₀) : F[X])) h
  have hcomp : ∀ r : (F[X])[X], shiftXRingHom (C (-x₀) : F[X]) (shiftXRingHom (C x₀) r) = r := by
    intro r
    have hrid : (shiftXRingHom (C (-x₀) : F[X])).comp (shiftXRingHom (C x₀)) = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro a; simp [shiftXRingHom]
      · simp [shiftXRingHom]
    exact RingHom.congr_fun hrid r
  rwa [hcomp, hcomp] at h1

theorem shiftXTriv_natDegree_eq (x₀ : F) (R : ((F[X])[X])[X]) :
    (shiftXTriv x₀ R).natDegree = R.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (shiftXRingHom_injective x₀) R

theorem shiftXTriv_maxZDeg_le (x₀ : F) (R : ((F[X])[X])[X]) :
    maxZDeg (shiftXTriv x₀ R) ≤ maxZDeg R := by
  rw [maxZDeg_le_iff]
  intro j i
  have hcoeff : ((shiftXTriv x₀ R).coeff j) = shiftXRingHom (C x₀) (R.coeff j) :=
    Polynomial.coeff_map _ j
  rw [hcoeff]
  exact coeffDegLE_shiftXRingHom_C (fun r => coeff_coeff_natDegree_le_maxZDeg R j r) i

theorem evalX0_shiftXTriv (x₀ : F) (R : ((F[X])[X])[X]) :
    evalX0 (shiftXTriv x₀ R) = R.map (Polynomial.evalRingHom (C x₀)) := by
  change (R.map (shiftXRingHom (C x₀))).map (Polynomial.evalRingHom 0) =
    R.map (Polynomial.evalRingHom (C x₀))
  rw [Polynomial.map_map]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a; simp [shiftXRingHom]
  · simp [shiftXRingHom]

theorem evalZR_shiftXTriv (β x₀ : F) (R : ((F[X])[X])[X]) (p : F[X]) :
    (evalZR β (shiftXTriv x₀ R)).eval (p.comp (X + C x₀)) =
      ((evalZR β R).eval p).comp (X + C x₀) := by
  have hmap : evalZR β (shiftXTriv x₀ R) =
      (evalZR β R).map (shiftXHom x₀) := by
    change (R.map (shiftXRingHom (C x₀))).map (Polynomial.mapRingHom (Polynomial.evalRingHom β)) =
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom β))).map (shiftXHom x₀)
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    apply RingHom.ext; intro q
    change (shiftXRingHom (C x₀) q).map (Polynomial.evalRingHom β) =
      shiftXRingHom x₀ (q.map (Polynomial.evalRingHom β))
    have h := map_shiftXRingHom (Polynomial.evalRingHom β) (C x₀) q
    simpa using h
  rw [hmap, ← shiftXHom_apply x₀ p, ← shiftXHom_apply x₀ ((evalZR β R).eval p),
    Polynomial.eval_map_apply]

/-- Weighted pigeonhole on a list of items covering `G₀`. -/
theorem exists_weighted_pigeonhole {α β : Type*} [DecidableEq β]
    (items : List α) (w : α → ℕ) (S : α → Finset β) (G₀ : Finset β) (B : ℕ)
    (hcov : ∀ b ∈ G₀, ∃ a ∈ items, b ∈ S a)
    (hgt : (items.map w).sum * B < G₀.card) :
    ∃ a ∈ items, w a * B < (S a).card := by
  by_contra hnone
  push Not at hnone
  have hsub : G₀ ⊆ items.foldr (fun a acc => S a ∪ acc) ∅ := by
    intro b hb
    obtain ⟨a, ha, hba⟩ := hcov b hb
    clear hcov hgt hnone
    induction items with
    | nil => simp at ha
    | cons x xs ih =>
      simp only [List.foldr_cons, Finset.mem_union]
      rcases List.mem_cons.mp ha with rfl | hxs
      · exact Or.inl hba
      · exact Or.inr (ih hxs)
  have hcard_fold : ∀ (l : List α), (∀ a ∈ l, (S a).card ≤ w a * B) →
      (l.foldr (fun a acc => S a ∪ acc) ∅).card ≤ (l.map w).sum * B := by
    intro l hl
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, Nat.add_mul]
      refine (Finset.card_union_le _ _).trans ?_
      exact Nat.add_le_add (hl x (List.mem_cons_self ..))
        (ih fun a ha => hl a (List.mem_cons_of_mem _ ha))
  have hle := (Finset.card_le_card hsub).trans (hcard_fold items hnone)
  omega

end FactorAndPigeonhole

/-! ## 5. Steps 3–5: From Irreducible Pair `(R, H)` to New Correlated Tuple `v ∉ L` -/

section CoreLiftAndExtract

variable {F : Type*} [Field F] [DecidableEq F]

/-- If `g : (F[Z])[T]` vanishes in `E = AdjoinRoot H_K`, then for every `(β, u)` with
`H(β, u) = 0` and `H.leadingCoeff(β) ≠ 0`, `evalZT β u g = 0`. -/
theorem evalZT_eq_zero_of_toE_eq_zero {H : (F[X])[X]}
    (hHt : 1 ≤ H.natDegree)
    {g : (F[X])[X]}
    (hg0 : (AdjoinRoot.mk (H.map (algebraMap F[X] (RatFunc F))))
      (g.map (algebraMap F[X] (RatFunc F))) = 0)
    {β u : F} (hHβ : evalZT β u H = 0) (hlc : H.leadingCoeff.eval β ≠ 0) :
    evalZT β u g = 0 := by
  set K := RatFunc F
  set φ := algebraMap F[X] K
  set H_K := H.map φ
  have hφ_inj : Function.Injective φ := IsFractionRing.injective F[X] K
  have hHdeg : H_K.natDegree = H.natDegree := Polynomial.natDegree_map_eq_of_injective hφ_inj H
  set k := g.natDegree + 1
  set rem := pseudoRem H k g
  have hrem_deg : rem.natDegree < H.natDegree :=
    pseudoRem_natDegree_lt hHt k g (by omega)
  have hdvd : H ∣ C (H.leadingCoeff ^ k) * g - rem := pseudoRem_sub_dvd H k g
  have hrem_E : (AdjoinRoot.mk H_K) (rem.map φ) = 0 := by
    obtain ⟨q, hq⟩ := hdvd
    have hq_map := congrArg (fun P => (AdjoinRoot.mk H_K) (P.map φ)) hq
    have hHK : (AdjoinRoot.mk H_K) (H.map φ) = 0 := AdjoinRoot.mk_self
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_sub, map_mul,
      hHK, zero_mul, hg0, mul_zero, zero_sub, neg_eq_zero] at hq_map
    exact hq_map
  have hrem_dvd : H_K ∣ rem.map φ := (AdjoinRoot.mk_eq_zero).mp hrem_E
  have hrem_zero : rem = 0 := by
    by_contra hne
    have hmap_ne : rem.map φ ≠ 0 := by
      intro h0
      exact hne (Polynomial.map_injective φ hφ_inj (h0.trans (Polynomial.map_zero φ).symm))
    have hle := Polynomial.natDegree_le_of_dvd hrem_dvd hmap_ne
    rw [hHdeg, Polynomial.natDegree_map_eq_of_injective hφ_inj] at hle
    omega
  have hev := pseudoRem_eval₂ (Polynomial.evalRingHom β) u hHβ k g
  change evalZT β u rem = (H.leadingCoeff.eval β) ^ k * evalZT β u g at hev
  rw [hrem_zero, map_zero] at hev
  exact (mul_eq_zero.mp hev.symm).resolve_left (pow_ne_zero k hlc)

/-- Core lifting, Hasse-multiplicity double counting, and Lagrange extraction theorem
for a single winning irreducible pair `(R, H)` at good base point `x₀`. -/
theorem extract_correlated_tuple_of_pair
    {D : Finset F} {d A m D_Z : ℕ} {u : Fin m → F → F}
    {L : Finset (Fin m → F[X])} {G_H : Finset F}
    {pOf : F → F[X]} {x₀ : F}
    {R : ((F[X])[X])[X]} {H : (F[X])[X]}
    (hd : 2 ≤ d) (hdA : d ≤ A) (_hm : 2 ≤ m)
    (hRirr : Irreducible R) (hRpos : 1 ≤ R.natDegree) (hRdegZ : maxZDeg R ≤ D_Z)
    (hHirr : Irreducible H) (hHpos : 1 ≤ H.natDegree) (hHdegZ : maxCoeffDeg H ≤ D_Z)
    (hH_dvd : H ∣ evalX0 (shiftXTriv x₀ R))
    (hΔ₀_ne : Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1)
      (evalX0 (shiftXTriv x₀ R)) (evalX0 (shiftXTriv x₀ R)).derivative ≠ 0)
    (hGH_p : ∀ β ∈ G_H, (pOf β).degree < d ∧
      (∀ v ∈ L, pOf β ≠ ∑ k : Fin m, β ^ (k : ℕ) • v k) ∧
      A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card ∧
      (evalZR β R).eval (pOf β) = 0 ∧
      evalZT β ((pOf β).eval x₀) H = 0)
    (hGH_card3 :
      let ℓ := R.natDegree
      let t := H.natDegree
      let B_C := ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z
      B_C + t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) < G_H.card)
    (hGH_card4 :
      let ℓ := R.natDegree
      let t := H.natDegree
      let B_C := ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z
      B_C + D.card * (D_Z + (m - 1) * ℓ) < G_H.card) :
    ∃ v : Fin m → F[X], v ∉ L ∧ (∀ k, (v k).degree < d) ∧ A ≤ (tupleAgreeSet D u v).card := by
  classical
  set ℓ := R.natDegree
  set t := H.natDegree
  set Rs := shiftXTriv x₀ R
  have hRs_deg : Rs.natDegree = ℓ := shiftXTriv_natDegree_eq x₀ R
  have hRs_degZ : ∀ j i, ((Rs.coeff j).coeff i).natDegree ≤ D_Z := fun j i =>
    (coeff_coeff_natDegree_le_maxZDeg Rs j i).trans ((shiftXTriv_maxZDeg_le x₀ R).trans hRdegZ)
  have hH_coeffZ : CoeffDegLE D_Z H := fun j => (coeff_natDegree_le_maxCoeffDeg H j).trans hHdegZ
  set R₀ := evalX0 Rs
  have hR₀_deg : R₀.natDegree ≤ ℓ := Polynomial.natDegree_map_le.trans hRs_deg.le
  have hR₀'_deg : R₀.derivative.natDegree ≤ max (ℓ - 1) 1 :=
    (Polynomial.natDegree_derivative_le R₀).trans (by omega)
  have hR₀_degZ : ∀ k, (R₀.coeff k).natDegree ≤ D_Z := by
    intro k
    dsimp only [R₀, evalX0]
    rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero]
    exact hRs_degZ k 0
  have hR₀'_degZ : ∀ k, (R₀.derivative.coeff k).natDegree ≤ D_Z := by
    intro k
    rw [Polynomial.coeff_derivative]
    exact (Polynomial.natDegree_mul_le).trans
      (by simpa [Polynomial.natDegree_natCast] using hR₀_degZ (k + 1))
  -- Build Sylvester Bézout inverse `W_raw`, then `W = pseudoRem H ℓ W_raw`.
  set n_s := max (ℓ - 1) 1
  obtain ⟨U_bez, W_raw, _, hWraw_deg, _, hWraw_Z, _, hbez_raw⟩ :=
    Sylvester.sylvester_bezout_deg_le (m := ℓ) (n := n_s) (B_f := D_Z) (B_g := D_Z)
      hRpos (le_max_right _ _) hR₀_deg hR₀'_deg hR₀_degZ hR₀'_degZ
  set Δ₀ := Sylvester.sylvesterDet ℓ n_s R₀ R₀.derivative
  have hΔ₀_degZ : Δ₀.natDegree ≤ (n_s + ℓ) * D_Z := by
    have h := Sylvester.natDegree_sylvesterDet_le (m := ℓ) (n := n_s) hR₀_degZ hR₀'_degZ
    exact h.trans (le_of_eq (by ring))
  have hns_le : n_s ≤ ℓ := by dsimp only [n_s]; omega
  set W := pseudoRem H ℓ W_raw
  have hW_deg : W.natDegree < t :=
    pseudoRem_natDegree_lt hHpos ℓ W_raw (by omega)
  set B_W := 3 * ℓ * D_Z
  have hW_degZ : CoeffDegLE B_W W := by
    have h1 : CoeffDegLE ((n_s + ℓ) * D_Z) W_raw := fun k =>
      (hWraw_Z k).trans (le_of_eq (by ring))
    have h2 := coeffDegLE_pseudoRem hH_coeffZ ℓ _ W_raw h1
    refine coeffDegLE_mono ?_ h2
    calc (n_s + ℓ) * D_Z + ℓ * D_Z = (n_s + 2 * ℓ) * D_Z := by ring
      _ ≤ (3 * ℓ) * D_Z := Nat.mul_le_mul_right D_Z (by omega)
      _ = B_W := rfl
  set Δ₀' := H.leadingCoeff ^ ℓ * Δ₀
  have hbez_H : H ∣ W * R₀.derivative - C Δ₀' := by
    obtain ⟨q1, hq1⟩ := pseudoRem_sub_dvd H ℓ W_raw
    obtain ⟨q2, hq2⟩ := hH_dvd
    refine ⟨-(C (H.leadingCoeff ^ ℓ) * U_bez * q2) - q1 * R₀.derivative, ?_⟩
    have hW_eq : W = C (H.leadingCoeff ^ ℓ) * W_raw - H * q1 := by
      calc W = C (H.leadingCoeff ^ ℓ) * W_raw - (C (H.leadingCoeff ^ ℓ) * W_raw - W) := by ring
        _ = C (H.leadingCoeff ^ ℓ) * W_raw - H * q1 := by rw [hq1]
    rw [hW_eq, map_mul]
    have hsub : C (H.leadingCoeff ^ ℓ) * (U_bez * R₀ + W_raw * R₀.derivative) =
        C (H.leadingCoeff ^ ℓ) * C Δ₀ := congrArg (C (H.leadingCoeff ^ ℓ) * ·) hbez_raw
    calc (C (H.leadingCoeff ^ ℓ) * W_raw - H * q1) * R₀.derivative - C (H.leadingCoeff ^ ℓ) * C Δ₀
        = C (H.leadingCoeff ^ ℓ) * W_raw * R₀.derivative -
            C (H.leadingCoeff ^ ℓ) * (U_bez * R₀ + W_raw * R₀.derivative) -
            H * q1 * R₀.derivative := by rw [← hsub]; ring
      _ = C (H.leadingCoeff ^ ℓ) * W_raw * R₀.derivative -
            C (H.leadingCoeff ^ ℓ) * (U_bez * (H * q2) + W_raw * R₀.derivative) -
            H * q1 * R₀.derivative := by rw [hq2]
      _ = H * (-(C (H.leadingCoeff ^ ℓ) * U_bez * q2) - q1 * R₀.derivative) := by ring
  -- Unified Hensel denominator `D₀ = H.leadingCoeff ^ ((Rs.natDegree + 1) * t) * Δ₀' ≠ 0`.
  set D₀ : F[X] := H.leadingCoeff ^ ((Rs.natDegree + 1) * H.natDegree) * Δ₀'
  have hHlc_ne : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hHirr.ne_zero
  have hD₀_ne : D₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hHlc_ne) (mul_ne_zero (pow_ne_zero _ hHlc_ne) hΔ₀_ne)
  set B_C := ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z
  have hD₀_degZ : D₀.natDegree ≤ B_C := by
    have h1 : (H.leadingCoeff ^ ((ℓ + 1) * t)).natDegree ≤ (ℓ + 1) * t * D_Z :=
      (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hH_coeffZ H.natDegree))
    have h2 : (H.leadingCoeff ^ ℓ).natDegree ≤ ℓ * D_Z :=
      (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ (hH_coeffZ H.natDegree))
    have h3 : Δ₀'.natDegree ≤ 3 * ℓ * D_Z := by
      refine (Polynomial.natDegree_mul_le).trans ((Nat.add_le_add h2 hΔ₀_degZ).trans ?_)
      calc ℓ * D_Z + (n_s + ℓ) * D_Z = (n_s + 2 * ℓ) * D_Z := by ring
        _ ≤ 3 * ℓ * D_Z := Nat.mul_le_mul_right D_Z (by omega)
    dsimp only [D₀]
    rw [hRs_deg]
    refine (Polynomial.natDegree_mul_le).trans ((Nat.add_le_add h1 h3).trans ?_)
    have hring : (ℓ + 1) * t * D_Z + 3 * ℓ * D_Z ≤ B_C := by
      dsimp only [B_C]; nlinarith
    exact hring
  have hB_C_cond : D_Z + B_W + (Rs.natDegree + 1) * H.natDegree * D_Z ≤ B_C := by
    rw [hRs_deg]; dsimp only [B_W, B_C]; exact le_of_eq (by ring)
  -- Filter out roots of `D₀` from `G_H`.
  let G'_H : Finset F := G_H.filter fun β => D₀.eval β ≠ 0
  have hG'_card : G_H.card - B_C ≤ G'_H.card := by
    have hbad_sub : (G_H.filter fun β => D₀.eval β = 0) ⊆ D₀.roots.toFinset := by
      intro β hβ
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hD₀_ne).mpr (Finset.mem_filter.mp hβ).2)
    have hbad_le : (G_H.filter fun β => D₀.eval β = 0).card ≤ B_C :=
      (Finset.card_le_card hbad_sub).trans
        ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' D₀).trans hD₀_degZ))
    have hsplit := Finset.card_filter_add_card_filter_not (s := G_H) (fun β => D₀.eval β = 0)
    have hcompl : (G_H.filter fun β => ¬ D₀.eval β = 0) = G'_H := rfl
    rw [hcompl] at hsplit
    omega
  have hG'_gt3 : t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) < G'_H.card := by
    have h3 : B_C + t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) < G_H.card := hGH_card3
    omega
  have hG'_gt4 : D.card * (D_Z + (m - 1) * ℓ) < G'_H.card := by
    have h4 : B_C + D.card * (D_Z + (m - 1) * ℓ) < G_H.card := hGH_card4
    omega
  -- Run cleared-denominator Hensel lift `b := henselCoeff Rs H W D₀`.
  set b := henselCoeff Rs H W D₀
  have hb_bounds := henselCoeff_deg_bounds hHpos hW_deg hRs_degZ hH_coeffZ hW_degZ hD₀_degZ hB_C_cond
  have hb_eval : ∀ β ∈ G'_H, ∀ s : ℕ,
      evalZT β ((pOf β).eval x₀) (b s) = (D₀.eval β) ^ (henselExp s) * ((pOf β).comp (X + C x₀)).coeff s := by
    intro β hβ s
    have hβGH : β ∈ G_H := (Finset.mem_filter.mp hβ).1
    have hD₀β : D₀.eval β ≠ 0 := (Finset.mem_filter.mp hβ).2
    obtain ⟨_, _, _, hRp, hHβ⟩ := hGH_p β hβGH
    have hp0 : ((pOf β).comp (X + C x₀)).eval 0 = (pOf β).eval x₀ := by
      simp [Polynomial.eval_comp]
    have hRsp : (evalZR β Rs).eval ((pOf β).comp (X + C x₀)) = 0 := by
      rw [evalZR_shiftXTriv, hRp, Polynomial.zero_comp]
    exact henselCoeff_evalZT_eq hbez_H hHβ hD₀β hp0 hRsp s
  -- Step 3: prove EVERY `henselResidualCoeff Rs H b D₀ d q = 0`!
  set K := RatFunc F
  set φ := algebraMap F[X] K
  have hφ_inj : Function.Injective φ := IsFractionRing.injective F[X] K
  set H_K : K[X] := H.map φ
  have hHirr_K : Irreducible H_K := irreducible_map_fraction_map_of_natDegree_pos hHirr hHpos
  have hH_K_deg : H_K.natDegree = t := Polynomial.natDegree_map_eq_of_injective hφ_inj H
  have hres_zero : ∀ q : ℕ, henselResidualCoeff Rs H b D₀ d q = 0 := by
    intro q
    set fq := henselResidualCoeff Rs H b D₀ d q
    by_contra hfq_ne
    have hfq_degT : fq.natDegree < t :=
      henselResidualCoeff_degT_lt hHpos (fun s _ => (hb_bounds s).1) q
    have hfq_degZ : CoeffDegLE (D_Z + 2 * d * ℓ * B_C + ℓ * t * D_Z) fq := by
      have h := henselResidualCoeff_degZ_le (d := d) hRs_degZ hH_coeffZ hD₀_degZ
        (fun s _ => (hb_bounds s).2.2) q
      rwa [hRs_deg] at h
    set n_t := max (t - 1) 1
    have hfq_K_ne : fq.map φ ≠ 0 := fun h0 =>
      hfq_ne (Polynomial.map_injective φ hφ_inj (h0.trans (Polynomial.map_zero φ).symm))
    have hfq_K_deg : (fq.map φ).natDegree < H_K.natDegree := by
      rw [hH_K_deg, Polynomial.natDegree_map_eq_of_injective hφ_inj]; exact hfq_degT
    have hnot_dvd : ¬ (H_K ∣ fq.map φ) := fun hdvd =>
      not_le_of_gt hfq_K_deg (Polynomial.natDegree_le_of_dvd hdvd hfq_K_ne)
    have hcop_K : IsCoprime H_K (fq.map φ) :=
      (hHirr_K.isRelPrime_iff_not_dvd.mpr hnot_dvd).isCoprime
    have hdet_K_ne : Sylvester.sylvesterDet t n_t H_K (fq.map φ) ≠ 0 :=
      Sylvester.sylvesterDet_ne_zero_of_isCoprime hHpos (le_max_right _ _) hH_K_deg
        (by rw [Polynomial.natDegree_map_eq_of_injective hφ_inj]; omega) hcop_K
    set res_q : F[X] := Sylvester.sylvesterDet t n_t H fq
    have hres_ne : res_q ≠ 0 := by
      intro h0
      apply hdet_K_ne
      have hm := Sylvester.map_sylvesterDet φ t n_t H fq
      change φ res_q = _ at hm
      rw [h0, map_zero] at hm
      exact hm.symm
    have hres_deg : res_q.natDegree ≤ t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) := by
      have h1 := Sylvester.natDegree_sylvesterDet_le (m := t) (n := n_t) hH_coeffZ hfq_degZ
      have hnt : n_t ≤ t := by dsimp only [n_t]; omega
      calc res_q.natDegree
          ≤ n_t * D_Z + t * (D_Z + 2 * d * ℓ * B_C + ℓ * t * D_Z) := h1
        _ ≤ t * D_Z + t * (D_Z + 2 * d * ℓ * B_C + ℓ * t * D_Z) :=
            Nat.add_le_add_right (Nat.mul_le_mul_right D_Z hnt) _
        _ = t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) := by ring
    have hres_van : ∀ β ∈ G'_H, res_q.eval β = 0 := by
      intro β hβ
      have hβGH : β ∈ G_H := (Finset.mem_filter.mp hβ).1
      obtain ⟨hpdeg, _, _, hRp, hHβ⟩ := hGH_p β hβGH
      have hp_sh_deg : ((pOf β).comp (X + C x₀)).degree < d := by
        by_cases hp0 : pOf β = 0
        · simp [hp0]
        · have hX : (X + C x₀ : F[X]).natDegree = 1 := Polynomial.natDegree_X_add_C x₀
          have hcomp_deg : ((pOf β).comp (X + C x₀)).natDegree = (pOf β).natDegree := by
            rw [Polynomial.natDegree_comp, hX, mul_one]
          have hpnat : (pOf β).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
          by_cases hc0 : (pOf β).comp (X + C x₀) = 0
          · rw [hc0, degree_zero]; exact WithBot.bot_lt_coe d
          · rw [Polynomial.degree_eq_natDegree hc0, hcomp_deg]
            exact WithBot.coe_lt_coe.mpr hpnat
      have hfq_ev := henselResidualCoeff_evalZT_eq (R := Rs) (H := H) (b := b) (D₀ := D₀) (d := d)
        hHβ hp_sh_deg (fun s _ => hb_eval β hβ s) q
      have hRsp : (evalZR β Rs).eval ((pOf β).comp (X + C x₀)) = 0 := by
        rw [evalZR_shiftXTriv, hRp, Polynomial.zero_comp]
      rw [hRsp, coeff_zero, mul_zero, mul_zero] at hfq_ev
      have hm := Sylvester.map_sylvesterDet (Polynomial.evalRingHom β) t n_t H fq
      change res_q.eval β = _ at hm
      rw [hm]
      refine Sylvester.sylvesterDet_eq_zero_of_common_root hHpos (le_max_right _ _)
        Polynomial.natDegree_map_le
        (Polynomial.natDegree_map_le.trans (by omega))
        (y := (pOf β).eval x₀) ?_ ?_
      · simpa [evalZT, Polynomial.eval_map] using hHβ
      · simpa [evalZT, Polynomial.eval_map] using hfq_ev
    have hsub : G'_H ⊆ res_q.roots.toFinset := fun β hβ =>
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hres_ne).mpr (hres_van β hβ))
    have hcard_le : G'_H.card ≤ t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) :=
      (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' res_q).trans hres_deg))
    omega
  -- Construct the field `E := AdjoinRoot H_K` and degree-`< d` polynomial root `P_orig : E[X]`!
  have : Fact (Irreducible H_K) := ⟨hHirr_K⟩
  let E := AdjoinRoot H_K
  let toE : (F[X])[X] →+* E := (AdjoinRoot.mk H_K).comp (Polynomial.mapRingHom φ)
  let toE_Z : F[X] →+* E := (AdjoinRoot.of H_K).comp φ
  let toE_F : F →+* E := toE_Z.comp C
  have htoE_C : ∀ a : F[X], toE (C a) = toE_Z a := fun a => by
    simp [toE, toE_Z, AdjoinRoot.mk_C]
  have htoE_Z_inj : Function.Injective toE_Z :=
    (AdjoinRoot.of H_K).injective.comp hφ_inj
  have htoE_F_inj : Function.Injective toE_F := htoE_Z_inj.comp Polynomial.C_injective
  have hd₀E_ne : toE_Z D₀ ≠ 0 := fun h => hD₀_ne (htoE_Z_inj (h.trans (map_zero _).symm))
  have hlcE_ne : toE_Z H.leadingCoeff ≠ 0 :=
    fun h => hHlc_ne (htoE_Z_inj (h.trans (map_zero _).symm))
  have hraw_map_zero : (henselResidualRaw Rs b D₀ d).map toE = 0 := by
    apply Polynomial.ext; intro q
    rw [Polynomial.coeff_map, coeff_zero]
    have hres0 := hres_zero q
    obtain ⟨qq, hqq⟩ := pseudoRem_sub_dvd H (Rs.natDegree * H.natDegree) ((henselResidualRaw Rs b D₀ d).coeff q)
    change C (H.leadingCoeff ^ (Rs.natDegree * H.natDegree)) * (henselResidualRaw Rs b D₀ d).coeff q -
      henselResidualCoeff Rs H b D₀ d q = H * qq at hqq
    rw [hres0, sub_zero] at hqq
    have hmap := congrArg toE hqq
    have htoE_H : toE H = 0 := AdjoinRoot.mk_self
    rw [map_mul, map_mul, htoE_H, zero_mul, htoE_C, map_pow] at hmap
    exact (mul_eq_zero.mp hmap).resolve_left (pow_ne_zero _ hlcE_ne)
  let P_E : E[X] := ∑ s ∈ Finset.range d, monomial s (toE (b s) * (toE_Z D₀ ^ henselExp s)⁻¹)
  have hP_E_deg : P_E.degree < d := by
    have hle : P_E.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun s hs => ?_)
      have hslt : s < d := Finset.mem_range.mp hs
      have hsd : s ≤ d - 1 := Nat.le_sub_one_of_lt hslt
      exact (Polynomial.degree_monomial_le s _).trans (Nat.cast_le.mpr hsd)
    have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
    exact hle.trans_lt (Nat.cast_lt.mpr hd1)
  have hP_E_scaled : (henselScaledPoly b D₀ d).map toE = C (toE_Z D₀ ^ (2 * d)) * P_E := by
    unfold henselScaledPoly
    rw [Polynomial.map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hslt : s < d := Finset.mem_range.mp hs
    have hle : henselExp s ≤ 2 * d := by unfold henselExp; split_ifs <;> omega
    rw [Polynomial.map_monomial, map_mul, htoE_C, map_pow, Polynomial.C_mul_monomial]
    congr 1
    have hpow : toE_Z D₀ ^ (2 * d) = toE_Z D₀ ^ (2 * d - henselExp s) * toE_Z D₀ ^ henselExp s := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    have hne : toE_Z D₀ ^ henselExp s ≠ 0 := pow_ne_zero _ hd₀E_ne
    calc toE_Z D₀ ^ (2 * d - henselExp s) * toE (b s)
        = toE_Z D₀ ^ (2 * d - henselExp s) * toE (b s) *
            (toE_Z D₀ ^ henselExp s * (toE_Z D₀ ^ henselExp s)⁻¹) := by
            rw [mul_inv_cancel₀ hne, mul_one]
      _ = toE_Z D₀ ^ (2 * d - henselExp s) * toE_Z D₀ ^ henselExp s *
            (toE (b s) * (toE_Z D₀ ^ henselExp s)⁻¹) := by ring
  set R_E : (E[X])[X] := R.map (Polynomial.mapRingHom toE_Z)
  set Rs_E : (E[X])[X] := Rs.map (Polynomial.mapRingHom toE_Z)
  have hRs_E_eval : Rs_E.eval P_E = 0 := by
    have hraw_eq : (henselResidualRaw Rs b D₀ d).map toE =
        C (toE_Z D₀ ^ (2 * d * Rs.natDegree)) * Rs_E.eval P_E := by
      unfold henselResidualRaw
      rw [Polynomial.map_sum]
      have hRs_ev : Rs_E.eval P_E =
          ∑ j ∈ Finset.range (Rs.natDegree + 1), (Rs.coeff j).map toE_Z * P_E ^ j := by
        have hdeg : Rs_E.natDegree ≤ Rs.natDegree := Polynomial.natDegree_map_le
        rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg)]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Rs_E, Polynomial.coeff_map]
      rw [hRs_ev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjle : j ≤ Rs.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_pow toE j, hP_E_scaled, mul_pow (C (toE_Z D₀ ^ (2 * d))) P_E j,
        ← C_pow, ← pow_mul]
      have hC1 : (C (C (D₀ ^ (2 * d * (Rs.natDegree - j)))) : ((F[X])[X])[X]).map toE =
          C (toE_Z D₀ ^ (2 * d * (Rs.natDegree - j))) := by
        rw [Polynomial.map_C, htoE_C, map_pow]
      have hC2 : ((Rs.coeff j).map C).map toE = (Rs.coeff j).map toE_Z := by
        rw [Polynomial.map_map]; congr 1; apply RingHom.ext; intro a; exact htoE_C a
      rw [hC1, hC2]
      have hpow : C (toE_Z D₀ ^ (2 * d * (Rs.natDegree - j))) * C (toE_Z D₀ ^ (2 * d * j)) =
          C (toE_Z D₀ ^ (2 * d * Rs.natDegree)) := by
        rw [← map_mul, ← pow_add]
        congr 2
        calc 2 * d * (Rs.natDegree - j) + 2 * d * j = 2 * d * ((Rs.natDegree - j) + j) := by ring
          _ = 2 * d * Rs.natDegree := by rw [Nat.sub_add_cancel hjle]
      calc C (toE_Z D₀ ^ (2 * d * (Rs.natDegree - j))) * (Rs.coeff j).map toE_Z *
            (C (toE_Z D₀ ^ (2 * d * j)) * P_E ^ j)
          = (C (toE_Z D₀ ^ (2 * d * (Rs.natDegree - j))) * C (toE_Z D₀ ^ (2 * d * j))) *
              ((Rs.coeff j).map toE_Z * P_E ^ j) := by ring
        _ = C (toE_Z D₀ ^ (2 * d * Rs.natDegree)) * ((Rs.coeff j).map toE_Z * P_E ^ j) := by rw [hpow]
    rw [hraw_map_zero] at hraw_eq
    have hCne : (C (toE_Z D₀ ^ (2 * d * Rs.natDegree)) : E[X]) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ hd₀E_ne)
    exact (mul_eq_zero.mp hraw_eq.symm).resolve_left hCne
  -- Shift `P_E` back by `-x₀` to obtain `P_orig : E[X]` with `R_E.eval P_orig = 0`.
  let P_orig : E[X] := P_E.comp (X - C (toE_F x₀))
  have hP_orig_deg : P_orig.degree < d := by
    by_cases hP0 : P_E = 0
    · simp [P_orig, hP0]
    · have hX : (X - C (toE_F x₀) : E[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C _
      have hnat : P_E.natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP_E_deg
      by_cases ho0 : P_orig = 0
      · rw [ho0, degree_zero]; exact WithBot.bot_lt_coe d
      · rw [Polynomial.degree_eq_natDegree ho0]
        have hcomp : P_orig.natDegree = P_E.natDegree := by
          dsimp only [P_orig]; rw [Polynomial.natDegree_comp, hX, mul_one]
        rw [hcomp]; exact WithBot.coe_lt_coe.mpr hnat
  have hR_E_eval : R_E.eval P_orig = 0 := by
    have hRs_map : Rs_E = R_E.map (shiftXHom (toE_F x₀)) := by
      dsimp only [Rs_E, R_E, Rs, shiftXTriv]
      change (R.map (shiftXRingHom (C x₀))).map (Polynomial.mapRingHom toE_Z) =
        (R.map (Polynomial.mapRingHom toE_Z)).map (shiftXHom (toE_F x₀))
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      apply RingHom.ext; intro q
      exact map_shiftXRingHom toE_Z (C x₀) q
    have hcomp_id : P_orig.comp (X + C (toE_F x₀)) = P_E := by
      dsimp only [P_orig]
      rw [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        add_sub_cancel_right, Polynomial.comp_X]
    have h1 : (R_E.eval P_orig).comp (X + C (toE_F x₀)) = 0 := by
      rw [← hRs_E_eval, hRs_map, ← hcomp_id, ← shiftXHom_apply, ← Polynomial.eval_map_apply]
      rfl
    have h2 := congrArg (fun f : E[X] => f.comp (X - C (toE_F x₀))) h1
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X, Polynomial.zero_comp] at h2
    exact h2
  -- Step 4: Hasse-multiplicity double counting to prove `A ≤ S_P.card`!
  let S_P : Finset F := D.filter fun x => P_orig.eval (toE_F x) = toE_Z (curveWordZ u x)
  have hSP_card : A ≤ S_P.card := by
    -- For every `x ∈ D \ S_P`, at most `D_Z + (m - 1) * ℓ` values of `β ∈ G'_H` have `(pOf β).eval x = u_β x`.
    have hbad_x : ∀ x ∈ D, x ∉ S_P →
        (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card ≤
          D_Z + (m - 1) * ℓ := by
      intro x hxD hxnot
      have hne_E : P_orig.eval (toE_F x) ≠ toE_Z (curveWordZ u x) := fun heq =>
        hxnot (Finset.mem_filter.mpr ⟨hxD, heq⟩)
      set R_x : (F[X])[X] := R.map (Polynomial.evalRingHom (C x))
      have hR_x_ne : R_x ≠ 0 := by
        intro hRx0
        have hdvd_X : C (X - C (C x) : (F[X])[X]) ∣ R := by
          have hall : ∀ j, (X - C (C x) : (F[X])[X]) ∣ R.coeff j := by
            intro j
            rw [Polynomial.dvd_iff_isRoot]
            have := congrArg (fun P : (F[X])[X] => P.coeff j) hRx0
            simpa [R_x, Polynomial.coeff_map] using this
          choose qf hqf using hall
          refine ⟨∑ j ∈ Finset.range (R.natDegree + 1), monomial j (qf j), ?_⟩
          apply Polynomial.ext; intro j
          rw [Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff]
          simp_rw [Polynomial.coeff_monomial]
          by_cases hj : j ≤ R.natDegree
          · rw [Finset.sum_eq_single j]
            · simp [hqf j]
            · intro b _ hne; simp [hne]
            · intro hnm; exact absurd (Finset.mem_range.mpr (by omega)) hnm
          · rw [Finset.sum_eq_zero]
            · rw [mul_zero]; exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            · intro b hb; have := Finset.mem_range.mp hb; simp [show b ≠ j by omega]
        obtain ⟨Q1, hQ1⟩ := hdvd_X
        rcases hRirr.isUnit_or_isUnit hQ1 with huC | huQ1
        · have hu := Polynomial.isUnit_C.mp huC
          obtain ⟨r, _, hr_eq⟩ := Polynomial.isUnit_iff.mp hu
          have hdeg1 : (X - C (C x) : (F[X])[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C _
          rw [← hr_eq, Polynomial.natDegree_C] at hdeg1
          omega
        · obtain ⟨u1, _, hu1_eq⟩ := Polynomial.isUnit_iff.mp huQ1
          have hdeg0 : R.natDegree = 0 := by
            rw [hQ1, ← hu1_eq, ← map_mul, Polynomial.natDegree_C]
          omega
      set uZ := curveWordZ u x
      set R_x_sh : (F[X])[X] := R_x.comp (X + C uZ)
      have hRx_sh_ne : R_x_sh ≠ 0 := by
        intro h0
        apply hR_x_ne
        have h1 := congrArg (fun P : (F[X])[X] => P.comp (X - C uZ)) h0
        simp only [R_x_sh, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
          Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X, Polynomial.zero_comp] at h1
        exact h1
      have hsupp_ne : R_x_sh.support.Nonempty := Polynomial.support_nonempty.mpr hRx_sh_ne
      set μ := R_x_sh.support.min' hsupp_ne
      have hμ_mem : μ ∈ R_x_sh.support := Finset.min'_mem _ hsupp_ne
      have hμ_ne : R_x_sh.coeff μ ≠ 0 := Polynomial.mem_support_iff.mp hμ_mem
      have hμ_lt : ∀ j < μ, R_x_sh.coeff j = 0 := by
        intro j hj
        by_contra hne
        have hmem : j ∈ R_x_sh.support := Polynomial.mem_support_iff.mpr hne
        exact absurd (Finset.min'_le _ j hmem) (not_le_of_gt hj)
      set S_x_sh : (F[X])[X] := ∑ j ∈ Finset.range (R_x_sh.natDegree + 1), monomial j (R_x_sh.coeff (j + μ))
      have hRx_sh_fac : R_x_sh = X ^ μ * S_x_sh := by
        apply Polynomial.ext; intro j
        rw [Polynomial.coeff_X_pow_mul']
        by_cases hj : μ ≤ j
        · rw [ite_eq_left hj]
          dsimp only [S_x_sh]
          rw [Polynomial.finsetSum_coeff]
          simp_rw [Polynomial.coeff_monomial]
          by_cases hlt : j - μ < R_x_sh.natDegree + 1
          · rw [Finset.sum_eq_single (j - μ)]
            · simp [Nat.sub_add_cancel hj]
            · intro b _ hne; simp [hne]
            · intro hnm; exact absurd (Finset.mem_range.mpr hlt) hnm
          · rw [Finset.sum_eq_zero]
            · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            · intro b hb; have := Finset.mem_range.mp hb; simp [show b ≠ j - μ by omega]
        · rw [ite_eq_right hj]; exact hμ_lt j (by omega)
      set S_x : (F[X])[X] := S_x_sh.comp (X - C uZ)
      have hRx_fac : R_x = (X - C uZ) ^ μ * S_x := by
        have h1 := congrArg (fun P : (F[X])[X] => P.comp (X - C uZ)) hRx_sh_fac
        simp only [R_x_sh, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
          Polynomial.C_comp, sub_add_cancel, Polynomial.comp_X, Polynomial.mul_comp,
          Polynomial.pow_comp] at h1
        exact h1
      set c_μ : F[X] := S_x.eval uZ
      have hc_μ_eq : c_μ = R_x_sh.coeff μ := by
        dsimp only [c_μ, S_x]
        rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          sub_self, ← Polynomial.coeff_zero_eq_eval_zero]
        dsimp only [S_x_sh]
        rw [Polynomial.finsetSum_coeff]
        simp_rw [Polynomial.coeff_monomial]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro b _ hne; simp [hne]
        · intro hnm; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ _)) hnm
      have hc_μ_ne : c_μ ≠ 0 := hc_μ_eq ▸ hμ_ne
      have hc_μ_deg : c_μ.natDegree ≤ D_Z + (m - 1) * ℓ := by
        rw [hc_μ_eq]
        have hRx_Z : CoeffDegLE D_Z R_x := by
          intro j
          dsimp only [R_x]
          rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.eval_eq_sum_range]
          refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
          rw [← C_pow]
          exact (Polynomial.natDegree_mul_le).trans
            (by simpa [Polynomial.natDegree_C] using
              (coeff_coeff_natDegree_le_maxZDeg R j i).trans hRdegZ)
        have hRx_deg : R_x.natDegree ≤ ℓ := Polynomial.natDegree_map_le
        have huZ_deg : uZ.natDegree ≤ m - 1 := curveWordZ_natDegree_le u x
        have hlin : CoeffDegLE (m - 1) (X + C uZ : (F[X])[X]) :=
          coeffDegLE_add (coeffDegLE_X _) (coeffDegLE_C huZ_deg)
        have hcomp_Z : CoeffDegLE (D_Z + (m - 1) * ℓ) R_x_sh := by
          dsimp only [R_x_sh]
          rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
          refine coeffDegLE_sum _ _ fun j hj => ?_
          have hjle : j ≤ ℓ := (Polynomial.le_natDegree_of_mem_supp j hj).trans hRx_deg
          refine coeffDegLE_mono ?_ (coeffDegLE_C_mul (hRx_Z j) (coeffDegLE_pow hlin j))
          have : j * (m - 1) ≤ (m - 1) * ℓ := by
            rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (m - 1) hjle
          omega
        exact hcomp_Z μ
      -- Show `(S_x.map toE_Z).eval (P_orig.eval (toE_F x)) = 0` in `E`.
      have hRx_E_zero : (R_x.map toE_Z).eval (P_orig.eval (toE_F x)) = 0 := by
        have h1 : (R_E.eval P_orig).eval (toE_F x) = 0 := by rw [hR_E_eval, eval_zero]
        have h2 : (R_E.eval P_orig).eval (toE_F x) =
            (R_E.map (Polynomial.evalRingHom (toE_F x))).eval (P_orig.eval (toE_F x)) := by
          have := Polynomial.hom_eval₂ R_E (RingHom.id E[X]) (Polynomial.evalRingHom (toE_F x)) P_orig
          simpa [Polynomial.eval_map] using this
        have h3 : R_E.map (Polynomial.evalRingHom (toE_F x)) = R_x.map toE_Z := by
          dsimp only [R_E, R_x]
          rw [Polynomial.map_map, Polynomial.map_map]
          congr 1
          apply RingHom.ext; intro p
          simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
          rw [Polynomial.eval_map]
          exact Polynomial.eval₂_hom toE_Z (C x)
        rw [← h3, ← h2, h1]
      have hSx_E_zero : (S_x.map toE_Z).eval (P_orig.eval (toE_F x)) = 0 := by
        have hmap := congrArg (fun P : (F[X])[X] => (P.map toE_Z).eval (P_orig.eval (toE_F x))) hRx_fac
        simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C] at hmap
        rw [hRx_E_zero] at hmap
        exact (mul_eq_zero.mp hmap.symm).resolve_left (pow_ne_zero μ (sub_ne_zero.mpr hne_E))
      -- Lift `(S_x.map toE_Z).eval (P_orig.eval (toE_F x)) = 0` back to `(F[Z])[T]`!
      set P_val_cl : (F[X])[X] := (henselScaledPoly b D₀ d).eval (C (C (x - x₀)))
      have hP_val_E : toE P_val_cl = toE_Z D₀ ^ (2 * d) * P_orig.eval (toE_F x) := by
        have hhom := Polynomial.hom_eval₂ (henselScaledPoly b D₀ d) (RingHom.id (F[X])[X]) toE
          (C (C (x - x₀)))
        have h1 : toE P_val_cl = ((henselScaledPoly b D₀ d).map toE).eval (toE (C (C (x - x₀)))) := by
          simpa [P_val_cl, Polynomial.eval_map] using hhom
        rw [h1, hP_E_scaled, Polynomial.eval_mul, Polynomial.eval_C, htoE_C]
        congr 1
        dsimp only [P_orig]
        rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        have hxsub : toE_Z (C (x - x₀)) = toE_F x - toE_F x₀ := by
          simp [toE_F, map_sub]
        rw [hxsub]
      set S_cl : (F[X])[X] :=
        ∑ j ∈ Finset.range (S_x.natDegree + 1),
          C (D₀ ^ (2 * d * (S_x.natDegree - j)) * S_x.coeff j) * P_val_cl ^ j
      have hS_cl_E : toE S_cl = 0 := by
        dsimp only [S_cl]
        rw [map_sum]
        have hsum_eq : ∑ j ∈ Finset.range (S_x.natDegree + 1),
            toE (C (D₀ ^ (2 * d * (S_x.natDegree - j)) * S_x.coeff j) * P_val_cl ^ j) =
            toE_Z D₀ ^ (2 * d * S_x.natDegree) * (S_x.map toE_Z).eval (P_orig.eval (toE_F x)) := by
          have hS_ev : (S_x.map toE_Z).eval (P_orig.eval (toE_F x)) =
              ∑ j ∈ Finset.range (S_x.natDegree + 1),
                toE_Z (S_x.coeff j) * P_orig.eval (toE_F x) ^ j := by
            rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Polynomial.coeff_map]
          rw [hS_ev, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjle : j ≤ S_x.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [map_mul, htoE_C, map_mul, map_pow, map_pow, hP_val_E, mul_pow, ← pow_mul]
          have hpow : toE_Z D₀ ^ (2 * d * (S_x.natDegree - j)) * toE_Z D₀ ^ (2 * d * j) =
              toE_Z D₀ ^ (2 * d * S_x.natDegree) := by
            rw [← pow_add]; congr 1
            calc 2 * d * (S_x.natDegree - j) + 2 * d * j = 2 * d * ((S_x.natDegree - j) + j) := by ring
              _ = 2 * d * S_x.natDegree := by rw [Nat.sub_add_cancel hjle]
          calc toE_Z D₀ ^ (2 * d * (S_x.natDegree - j)) * toE_Z (S_x.coeff j) *
                (toE_Z D₀ ^ (2 * d * j) * P_orig.eval (toE_F x) ^ j)
              = (toE_Z D₀ ^ (2 * d * (S_x.natDegree - j)) * toE_Z D₀ ^ (2 * d * j)) *
                  (toE_Z (S_x.coeff j) * P_orig.eval (toE_F x) ^ j) := by ring
            _ = toE_Z D₀ ^ (2 * d * S_x.natDegree) *
                  (toE_Z (S_x.coeff j) * P_orig.eval (toE_F x) ^ j) := by rw [hpow]
        rw [hsum_eq, hSx_E_zero, mul_zero]
      -- Conclude: for every `β ∈ G'_H` with `u_β(x) = (pOf β).eval x`, `c_μ.eval β = 0`!
      have hsub_cμ : (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x) ⊆
          c_μ.roots.toFinset := by
        intro β hβ
        have hβG' : β ∈ G'_H := (Finset.mem_filter.mp hβ).1
        have hagree_x : ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x := (Finset.mem_filter.mp hβ).2
        have hβGH : β ∈ G_H := (Finset.mem_filter.mp hβG').1
        have hD₀β : D₀.eval β ≠ 0 := (Finset.mem_filter.mp hβG').2
        obtain ⟨hpdeg, _, _, _, hHβ⟩ := hGH_p β hβGH
        have hlcβ : H.leadingCoeff.eval β ≠ 0 := by
          intro h0
          apply hD₀β
          dsimp only [D₀, Δ₀']
          have hpos_exp : 0 < (Rs.natDegree + 1) * H.natDegree := Nat.mul_pos (Nat.succ_pos _) hHpos
          rw [Polynomial.eval_mul, Polynomial.eval_pow, h0, zero_pow (Nat.ne_of_gt hpos_exp), zero_mul]
        have hS_cl_β : evalZT β ((pOf β).eval x₀) S_cl = 0 :=
          evalZT_eq_zero_of_toE_eq_zero hHpos hS_cl_E hHβ hlcβ
        have hP_val_β : evalZT β ((pOf β).eval x₀) P_val_cl = (D₀.eval β) ^ (2 * d) * (pOf β).eval x := by
          have hp_sh_deg : ((pOf β).comp (X + C x₀)).degree < d := by
            by_cases hp0 : pOf β = 0
            · simp [hp0]
            · have hX : (X + C x₀ : F[X]).natDegree = 1 := Polynomial.natDegree_X_add_C x₀
              have hpnat : (pOf β).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
              by_cases hc0 : (pOf β).comp (X + C x₀) = 0
              · rw [hc0, degree_zero]; exact WithBot.bot_lt_coe d
              · rw [Polynomial.degree_eq_natDegree hc0, Polynomial.natDegree_comp, hX, mul_one]
                exact WithBot.coe_lt_coe.mpr hpnat
          have hsc := henselScaledPoly_eval b D₀ d hp_sh_deg (fun s _ => hb_eval β hβG' s)
          have hhom := Polynomial.hom_eval₂ (henselScaledPoly b D₀ d) (RingHom.id (F[X])[X])
            (evalZT β ((pOf β).eval x₀)) (C (C (x - x₀)))
          have h1 : evalZT β ((pOf β).eval x₀) P_val_cl =
              (mapEvalZT β ((pOf β).eval x₀) (henselScaledPoly b D₀ d)).eval (x - x₀) := by
            have hC : evalZT β ((pOf β).eval x₀) (C (C (x - x₀))) = x - x₀ := by
              rw [evalZT_C, Polynomial.eval_C]
            dsimp only [P_val_cl, mapEvalZT]
            rw [Polynomial.coe_mapRingHom, Polynomial.eval_map]
            exact hhom.trans (by rw [hC]; rfl)
          rw [h1, hsc, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
            Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel]
        have hS_eval_β : (S_x.map (Polynomial.evalRingHom β)).eval ((pOf β).eval x) = 0 := by
          have hsum_eq : evalZT β ((pOf β).eval x₀) S_cl =
              (D₀.eval β) ^ (2 * d * S_x.natDegree) *
                (S_x.map (Polynomial.evalRingHom β)).eval ((pOf β).eval x) := by
            dsimp only [S_cl]
            rw [map_sum]
            have hS_ev : (S_x.map (Polynomial.evalRingHom β)).eval ((pOf β).eval x) =
                ∑ j ∈ Finset.range (S_x.natDegree + 1),
                  (S_x.coeff j).eval β * ((pOf β).eval x) ^ j := by
              rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp [Polynomial.coeff_map]
            rw [hS_ev, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j hj => ?_
            have hjle : j ≤ S_x.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [map_mul, evalZT_C, Polynomial.eval_mul, Polynomial.eval_pow, map_pow, hP_val_β,
              mul_pow, ← pow_mul]
            have hpow : (D₀.eval β) ^ (2 * d * (S_x.natDegree - j)) * (D₀.eval β) ^ (2 * d * j) =
                (D₀.eval β) ^ (2 * d * S_x.natDegree) := by
              rw [← pow_add]; congr 1
              calc 2 * d * (S_x.natDegree - j) + 2 * d * j = 2 * d * ((S_x.natDegree - j) + j) := by ring
                _ = 2 * d * S_x.natDegree := by rw [Nat.sub_add_cancel hjle]
            calc (D₀.eval β) ^ (2 * d * (S_x.natDegree - j)) * (S_x.coeff j).eval β *
                  ((D₀.eval β) ^ (2 * d * j) * ((pOf β).eval x) ^ j)
                = ((D₀.eval β) ^ (2 * d * (S_x.natDegree - j)) * (D₀.eval β) ^ (2 * d * j)) *
                    ((S_x.coeff j).eval β * ((pOf β).eval x) ^ j) := by ring
              _ = (D₀.eval β) ^ (2 * d * S_x.natDegree) *
                    ((S_x.coeff j).eval β * ((pOf β).eval x) ^ j) := by rw [hpow]
          rw [hS_cl_β] at hsum_eq
          exact (mul_eq_zero.mp hsum_eq.symm).resolve_left (pow_ne_zero _ hD₀β)
        have hcμ_zero : c_μ.eval β = 0 := by
          have h1 : (S_x.eval uZ).eval β =
              (S_x.map (Polynomial.evalRingHom β)).eval (uZ.eval β) := by
            have := Polynomial.hom_eval₂ S_x (RingHom.id F[X]) (Polynomial.evalRingHom β) uZ
            simpa [Polynomial.eval_map] using this
          rw [show c_μ = S_x.eval uZ from rfl, h1, eval_curveWordZ u x β, hagree_x, hS_eval_β]
        exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hc_μ_ne).mpr hcμ_zero)
      exact (Finset.card_le_card hsub_cμ).trans ((Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' c_μ).trans hc_μ_deg))
    -- Double-counting incidences on `G'_H × D`!
    have hsum_ge : G'_H.card * A ≤
        ∑ β ∈ G'_H, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card := by
      calc G'_H.card * A = ∑ _β ∈ G'_H, A := by simp
        _ ≤ _ := Finset.sum_le_sum fun β hβ => (hGH_p β (Finset.mem_filter.mp hβ).1).2.2.1
    have hswap :
        ∑ β ∈ G'_H, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card =
        ∑ x ∈ D, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card := by
      simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    have hsum_le :
        ∑ x ∈ D, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card ≤
          S_P.card * G'_H.card + D.card * (D_Z + (m - 1) * ℓ) := by
      have hsplit_D : ∑ x ∈ D, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card =
          (∑ x ∈ S_P, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card) +
          ∑ x ∈ D \ S_P, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card := by
        have hsub : S_P ⊆ D := Finset.filter_subset _ _
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
      rw [hsplit_D]
      refine Nat.add_le_add ?_ ?_
      · calc ∑ x ∈ S_P, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card
            ≤ ∑ _x ∈ S_P, G'_H.card := Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _
          _ = S_P.card * G'_H.card := by simp
      · calc ∑ x ∈ D \ S_P, (G'_H.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card
            ≤ ∑ _x ∈ D \ S_P, (D_Z + (m - 1) * ℓ) :=
              Finset.sum_le_sum fun x hx =>
                hbad_x x (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
          _ = (D \ S_P).card * (D_Z + (m - 1) * ℓ) := by simp
          _ ≤ D.card * (D_Z + (m - 1) * ℓ) := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
    have hineq : G'_H.card * A ≤ S_P.card * G'_H.card + D.card * (D_Z + (m - 1) * ℓ) :=
      hsum_ge.trans (hswap ▸ hsum_le)
    by_contra hlt
    have hle1 : S_P.card + 1 ≤ A := by omega
    have hmul : (S_P.card + 1) * G'_H.card ≤ G'_H.card * A := by
      rw [Nat.mul_comm G'_H.card A]; exact Nat.mul_le_mul_right G'_H.card hle1
    rw [Nat.add_mul, one_mul] at hmul
    omega
  -- Step 5: Lagrange interpolation on `S₀ ⊆ S_P` (`S₀.card = d`) → `v ∉ L`!
  obtain ⟨S₀, hS₀_sub, hS₀_card⟩ := Finset.exists_subset_card_eq (hdA.trans hSP_card)
  let v : Fin m → F[X] := fun k => Lagrange.interpolate S₀ id (u k)
  have hv_deg : ∀ k : Fin m, (v k).degree < d := fun k => by
    have h := Lagrange.degree_interpolate_lt (s := S₀) (v := id) (u k) (Set.injOn_id _)
    rwa [hS₀_card] at h
  have hv_eval : ∀ k : Fin m, ∀ x ∈ S₀, (v k).eval x = u k x := fun k x hx =>
    Lagrange.eval_interpolate_at_node (u k) (Set.injOn_id _) hx
  let V_E : E[X] := ∑ k : Fin m, C (toE_Z (X ^ (k : ℕ))) * (v k).map toE_F
  have hV_E_deg : V_E.degree < d := by
    have hle : V_E.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
      refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun k _ => ?_)
      have hk_lt : ((v k).map toE_F).degree < d := Polynomial.degree_map_le.trans_lt (hv_deg k)
      have hterm_lt : (C (toE_Z (X ^ (k : ℕ))) * (v k).map toE_F).degree < d := by
        refine (Polynomial.degree_mul_le _ _).trans_lt ?_
        have hC0 : (C (toE_Z (X ^ (k : ℕ))) : E[X]).degree ≤ 0 := Polynomial.degree_C_le
        have hadd : (C (toE_Z (X ^ (k : ℕ))) : E[X]).degree + ((v k).map toE_F).degree ≤
            (0 : WithBot ℕ) + ((v k).map toE_F).degree := add_le_add hC0 le_rfl
        have hz : (0 : WithBot ℕ) + ((v k).map toE_F).degree = ((v k).map toE_F).degree := by simp
        rw [hz] at hadd
        exact hadd.trans_lt hk_lt
      by_cases h0 : C (toE_Z (X ^ (k : ℕ))) * (v k).map toE_F = 0
      · rw [h0, degree_zero]; exact bot_le
      · rw [Polynomial.degree_eq_natDegree h0] at hterm_lt ⊢
        have hnat : (C (toE_Z (X ^ (k : ℕ))) * (v k).map toE_F).natDegree < d :=
          Nat.cast_lt.mp hterm_lt
        exact Nat.cast_le.mpr (Nat.le_sub_one_of_lt hnat)
    have hd1 : d - 1 < d := Nat.sub_lt (by omega) Nat.one_pos
    exact hle.trans_lt (Nat.cast_lt.mpr hd1)
  have hV_E_eval : ∀ x : F, V_E.eval (toE_F x) = toE_Z (∑ k : Fin m, monomial (k : ℕ) ((v k).eval x)) := by
    intro x
    dsimp only [V_E]
    rw [Polynomial.eval_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
      Polynomial.eval₂_hom, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, mul_comm]
    rfl
  have hP_eq_V : P_orig = V_E := by
    refine eq_of_degree_lt_of_agree hP_orig_deg hV_E_deg
      (B := S₀.image toE_F) ?_ ?_
    · rw [Finset.card_image_of_injective S₀ htoE_F_inj, hS₀_card]
    · intro y hy
      obtain ⟨x, hxS₀, rfl⟩ := Finset.mem_image.mp hy
      have hxSP : x ∈ S_P := hS₀_sub hxS₀
      have hP_x : P_orig.eval (toE_F x) = toE_Z (curveWordZ u x) := (Finset.mem_filter.mp hxSP).2
      rw [hP_x, hV_E_eval]
      congr 1
      unfold curveWordZ
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hv_eval k x hxS₀]
  have hv_agree : A ≤ (tupleAgreeSet D u v).card := by
    refine hSP_card.trans (Finset.card_le_card fun x hxSP => ?_)
    have hxD : x ∈ D := (Finset.mem_filter.mp hxSP).1
    have hP_x : P_orig.eval (toE_F x) = toE_Z (curveWordZ u x) := (Finset.mem_filter.mp hxSP).2
    rw [hP_eq_V, hV_E_eval] at hP_x
    have hpoly_eq : ∑ k : Fin m, monomial (k : ℕ) ((v k).eval x) = curveWordZ u x :=
      htoE_Z_inj hP_x
    refine Finset.mem_filter.mpr ⟨hxD, fun k => ?_⟩
    have hc := congrArg (fun q : F[X] => q.coeff k.val) hpoly_eq
    rw [coeff_curveWordZ, Polynomial.finsetSum_coeff] at hc
    simp_rw [Polynomial.coeff_monomial] at hc
    rw [Finset.sum_eq_single k] at hc
    · simpa using hc.symm
    · intro b _ hne
      have : b.val ≠ k.val := fun h => hne (Fin.ext h)
      simp [this]
    · intro hnm; exact absurd (Finset.mem_univ k) hnm
  -- Pick any `β ∈ G'_H` (nonempty since `0 < G'_H.card`) to prove `pOf β = ∑ β^k • v k`, hence `v ∉ L`!
  have hG'_ne : G'_H.Nonempty := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hG'_gt4)
  obtain ⟨β, hβG'⟩ := hG'_ne
  have hβGH : β ∈ G_H := (Finset.mem_filter.mp hβG').1
  have hD₀β : D₀.eval β ≠ 0 := (Finset.mem_filter.mp hβG').2
  obtain ⟨hpdeg, hpnotL, _, _, hHβ⟩ := hGH_p β hβGH
  have hlcβ : H.leadingCoeff.eval β ≠ 0 := by
    intro h0
    apply hD₀β
    dsimp only [D₀, Δ₀']
    have hpos_exp : 0 < (Rs.natDegree + 1) * H.natDegree := Nat.mul_pos (Nat.succ_pos _) hHpos
    rw [Polynomial.eval_mul, Polynomial.eval_pow, h0, zero_pow (Nat.ne_of_gt hpos_exp), zero_mul]
  let V_shift : ((F[X])[X])[X] :=
    ∑ k : Fin m, C (C (X ^ (k : ℕ))) * ((v k).comp (X + C x₀)).map (C.comp C)
  have hV_shift_E : V_shift.map toE = P_E := by
    have hPE_eq : P_E = V_E.comp (X + C (toE_F x₀)) := by
      have h := congrArg (fun f : E[X] => f.comp (X + C (toE_F x₀))) hP_eq_V
      dsimp only [P_orig] at h
      rw [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        add_sub_cancel_right, Polynomial.comp_X] at h
      exact h
    rw [hPE_eq]
    dsimp only [V_shift, V_E]
    rw [Polynomial.map_sum, Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, htoE_C, Polynomial.mul_comp, Polynomial.C_comp]
    congr 1
    rw [Polynomial.map_map]
    have hcomp_eq : toE.comp (C.comp C) = toE_F := by
      apply RingHom.ext; intro a; simp [toE_F, htoE_C]
    rw [hcomp_eq, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  have hdiff_E : (henselScaledPoly b D₀ d - C (C (D₀ ^ (2 * d))) * V_shift).map toE = 0 := by
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, htoE_C, map_pow,
      hP_E_scaled, hV_shift_E, sub_self]
  have hdiff_β : mapEvalZT β ((pOf β).eval x₀)
      (henselScaledPoly b D₀ d - C (C (D₀ ^ (2 * d))) * V_shift) = 0 := by
    apply Polynomial.ext; intro s
    rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.coeff_map, coeff_zero]
    have hcoeff_E : toE ((henselScaledPoly b D₀ d - C (C (D₀ ^ (2 * d))) * V_shift).coeff s) = 0 := by
      have h := congrArg (fun f : E[X] => f.coeff s) hdiff_E
      rw [Polynomial.coeff_map, coeff_zero] at h
      exact h
    exact evalZT_eq_zero_of_toE_eq_zero hHpos hcoeff_E hHβ hlcβ
  have hp_sh_deg : ((pOf β).comp (X + C x₀)).degree < d := by
    by_cases hp0 : pOf β = 0
    · simp [hp0]
    · have hX : (X + C x₀ : F[X]).natDegree = 1 := Polynomial.natDegree_X_add_C x₀
      have hpnat : (pOf β).natDegree < d := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
      by_cases hc0 : (pOf β).comp (X + C x₀) = 0
      · rw [hc0, degree_zero]; exact WithBot.bot_lt_coe d
      · rw [Polynomial.degree_eq_natDegree hc0, Polynomial.natDegree_comp, hX, mul_one]
        exact WithBot.coe_lt_coe.mpr hpnat
  have hsc_β := henselScaledPoly_eval b D₀ d hp_sh_deg (fun s _ => hb_eval β hβG' s)
  have hV_shift_β : mapEvalZT β ((pOf β).eval x₀) V_shift =
      (∑ k : Fin m, β ^ (k : ℕ) • v k).comp (X + C x₀) := by
    dsimp only [V_shift]
    rw [map_sum, Polynomial.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    have hC1 : mapEvalZT β ((pOf β).eval x₀) (C (C (X ^ (k : ℕ)))) = C (β ^ (k : ℕ)) := by
      rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_C, Polynomial.eval_pow,
        Polynomial.eval_X]
    have hC2 : mapEvalZT β ((pOf β).eval x₀) (((v k).comp (X + C x₀)).map (C.comp C)) =
        (v k).comp (X + C x₀) := by
      rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_map]
      have hid : (evalZT β ((pOf β).eval x₀)).comp (C.comp C) = RingHom.id F := by
        apply RingHom.ext; intro a; simp [evalZT_C]
      rw [hid, Polynomial.map_id]
    rw [hC1, hC2, Polynomial.smul_eq_C_mul, Polynomial.mul_comp, Polynomial.C_comp]
  have hdiff_split : mapEvalZT β ((pOf β).eval x₀)
      (henselScaledPoly b D₀ d - C (C (D₀ ^ (2 * d))) * V_shift) =
      mapEvalZT β ((pOf β).eval x₀) (henselScaledPoly b D₀ d) -
        mapEvalZT β ((pOf β).eval x₀) (C (C (D₀ ^ (2 * d)))) *
        mapEvalZT β ((pOf β).eval x₀) V_shift := by
    unfold mapEvalZT
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul]
  rw [hdiff_split, hsc_β, hV_shift_β] at hdiff_β
  have hC_D0_β : mapEvalZT β ((pOf β).eval x₀) (C (C (D₀ ^ (2 * d)))) = C ((D₀.eval β) ^ (2 * d)) := by
    rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_C, Polynomial.eval_pow]
  rw [hC_D0_β, ← mul_sub] at hdiff_β
  have hsh_eq : (pOf β).comp (X + C x₀) = (∑ k : Fin m, β ^ (k : ℕ) • v k).comp (X + C x₀) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hdiff_β).resolve_left (Polynomial.C_ne_zero.mpr (pow_ne_zero _ hD₀β)))
  have hp_eq_v : pOf β = ∑ k : Fin m, β ^ (k : ℕ) • v k := by
    have h1 := congrArg (fun f : F[X] => f.comp (X - C x₀)) hsh_eq
    simp only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      sub_add_cancel, Polynomial.comp_X] at h1
    exact h1
  refine ⟨v, fun hvL => hpnotL v hvL hp_eq_v, hv_deg, hv_agree⟩

end CoreLiftAndExtract

/-! ## 6. Main Unconditional `CurveListCA` Theorems -/

section MainTheorems

variable {F : Type*} [Field F] [DecidableEq F]

/-- Main case `2 ≤ m`, `2 ≤ d` of `CurveListCA` under `p = 0 ∨ gsDegY D.card d A < p`. -/
theorem curveListCA_main_case {p : ℕ} [CharP F p]
    (D : Finset F) (d A m : ℕ) (hJ : D.card * (d - 1) < A ^ 2)
    (hm : 2 ≤ m) (hd : 2 ≤ d) (hchar : p = 0 ∨ gsDegY D.card d A < p)
    (u : Fin m → F → F) (L : Finset (Fin m → F[X])) (G : Finset F)
    (hGcard : curveListThreshold D.card d A m < G.card)
    (hG : ∀ β ∈ G, ∃ p : F[X], p.degree < d ∧
      (∀ v ∈ L, p ≠ ∑ k : Fin m, β ^ (k : ℕ) • v k) ∧
      A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x).card) :
    ∃ v : Fin m → F[X], v ∉ L ∧ (∀ k, (v k).degree < d) ∧ A ≤ (tupleAgreeSet D u v).card := by
  classical
  have hGne : G.Nonempty := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hGcard)
  obtain ⟨β₀, hβ₀⟩ := hGne
  obtain ⟨p₀, _, _, hagree₀⟩ := hG β₀ hβ₀
  have hAD : A ≤ D.card := hagree₀.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hDpos : 0 < D.card := by
    by_contra h0
    have hD0 : D.card = 0 := by omega
    have hA0 : A = 0 := by omega
    simp [hD0, hA0] at hJ
  have hdA : d ≤ A := by
    have h1 : D.card * (d - 1) < D.card * A := by
      calc D.card * (d - 1) < A ^ 2 := hJ
        _ = A * A := sq A
        _ ≤ D.card * A := Nat.mul_le_mul_right A hAD
    have hlt : d - 1 < A := Nat.lt_of_mul_lt_mul_left h1
    omega
  -- Unpack threshold inequalities.
  set n := D.card
  set r := gsMult n d A
  set D_X := gsDegX n d A
  set L_Y := gsDegY n d A
  set D_Z := (r + 1) * (m - 1) * L_Y
  set B3 := ((L_Y ^ 2 + 4 * L_Y + 4) + 2 * d * L_Y * (L_Y ^ 2 + 4 * L_Y + 1)) * D_Z
  set B4 := (4 * L_Y + 2) * D_Z + n * (D_Z + (m - 1) * L_Y)
  have hthresh : curveListThreshold n d A m = max ((2 * L_Y + 1) * D_X) (2 * D_Z + L_Y * max B3 B4) := by
    unfold curveListThreshold
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hthresh] at hGcard
  have hG_gt_x0 : (2 * L_Y + 1) * D_X < G.card := lt_of_le_of_lt (le_max_left _ _) hGcard
  have hG_gt_pigeon : 2 * D_Z + L_Y * max B3 B4 < G.card := lt_of_le_of_lt (le_max_right _ _) hGcard
  -- Choose witness `pOf β` for each `β ∈ G`.
  let pOf : F → F[X] := fun β =>
    if h : β ∈ G then (hG β h).choose else 0
  have hpOf : ∀ β ∈ G, (pOf β).degree < d ∧
      (∀ v ∈ L, pOf β ≠ ∑ k : Fin m, β ^ (k : ℕ) • v k) ∧
      A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card := by
    intro β hβ
    simpa [pOf, dite_eq_left hβ] using (hG β hβ).choose_spec
  -- Step 1: low-`Z`-degree Guruswami–Sudan annihilator `Q`.
  obtain ⟨Q, hQne, hQdegY, hQdegX, hQdegZ, _, _, hQann⟩ :=
    exists_gs_poly_curve_lowZDeg D d A m u hDpos hd hJ
  -- Step 2a: factor `Q` in the UFD `((F[Z])[X])[Y]`.
  let allFacs : List ((F[X])[X])[X] := (UniqueFactorizationMonoid.factors Q).toList
  have hall_irr : ∀ R ∈ allFacs, Irreducible R := fun R hR =>
    UniqueFactorizationMonoid.irreducible_of_factor R (Multiset.mem_toList.mp hR)
  have hall_ne : ∀ R ∈ allFacs, R ≠ 0 := fun R hR => (hall_irr R hR).ne_zero
  have hassoc : Associated allFacs.prod Q := by
    have h := UniqueFactorizationMonoid.factors_prod (α := ((F[X])[X])[X]) hQne
    rwa [← Multiset.prod_toList] at h
  obtain ⟨uQ, huQ_eq⟩ := hassoc
  -- `allFacs.prod * uQ = Q`.
  let Rfacs : List ((F[X])[X])[X] := allFacs.filter fun R => decide (1 ≤ R.natDegree)
  let Cfacs : List ((F[X])[X])[X] := allFacs.filter fun R => decide (¬ 1 ≤ R.natDegree)
  have hQ_eq_split : ∃ Q₀ : ((F[X])[X])[X], Q₀ ≠ 0 ∧ Q₀.natDegree = 0 ∧
      Q = Q₀ * Rfacs.prod := by
    refine ⟨Cfacs.prod * (uQ : ((F[X])[X])[X]), ?_, ?_, ?_⟩
    · exact mul_ne_zero (List.prod_ne_zero fun h0 => hall_ne 0 (List.mem_of_mem_filter h0) rfl) uQ.ne_zero
    · have hC_ne : ∀ f ∈ Cfacs, f ≠ 0 := fun f hf => hall_ne f (List.mem_of_mem_filter hf)
      have hC_deg : Cfacs.prod.natDegree = 0 := by
        rw [list_prod_natDegree Cfacs hC_ne]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        have hnot : ¬ (1 ≤ f.natDegree) := of_decide_eq_true (List.mem_filter.mp hf).2
        omega
      have hu_deg : (uQ : ((F[X])[X])[X]).natDegree = 0 := by
        obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.mp uQ.isUnit
        rw [← hr, Polynomial.natDegree_C]
      rw [Polynomial.natDegree_mul (List.prod_ne_zero fun h0 => hC_ne 0 h0 rfl) uQ.ne_zero,
        hC_deg, hu_deg]
    · have hmul : ∀ (l : List ((F[X])[X])[X]),
          l.prod = (l.filter fun R => decide (1 ≤ R.natDegree)).prod *
            (l.filter fun R => decide (¬ 1 ≤ R.natDegree)).prod := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.prod_cons, List.filter_cons]
          by_cases h1 : 1 ≤ a.natDegree
          · simp [h1, ih]; ring
          · simp [h1, ih]; ring
      have hprod_eq : allFacs.prod = Rfacs.prod * Cfacs.prod := hmul allFacs
      rw [← huQ_eq, hprod_eq]; ring
  obtain ⟨Q₀, hQ₀ne, hQ₀deg, hQ_split⟩ := hQ_eq_split
  have hR_irr : ∀ R ∈ Rfacs, Irreducible R := fun R hR => hall_irr R (List.mem_of_mem_filter hR)
  have hR_pos : ∀ R ∈ Rfacs, 1 ≤ R.natDegree := fun R hR =>
    of_decide_eq_true (List.mem_filter.mp hR).2
  have hR_ne : ∀ R ∈ Rfacs, R ≠ 0 := fun R hR => (hR_irr R hR).ne_zero
  have hR_dvd_Q : ∀ R ∈ Rfacs, R ∣ Q := fun R hR =>
    dvd_trans (List.dvd_prod hR) ⟨Q₀, by rw [hQ_split]; ring⟩
  have hR_sum_degY : (Rfacs.map Polynomial.natDegree).sum ≤ L_Y := by
    have h1 : Rfacs.prod.natDegree ≤ Q.natDegree :=
      Polynomial.natDegree_le_of_dvd ⟨Q₀, by rw [hQ_split]; ring⟩ hQne
    rw [list_prod_natDegree Rfacs hR_ne] at h1
    exact h1.trans hQdegY
  have hR_sum_maxZ : (Rfacs.map maxZDeg).sum ≤ D_Z := by
    have h1 : maxZDeg Rfacs.prod ≤ maxZDeg Q :=
      maxZDeg_le_of_dvd hQne ⟨Q₀, by rw [hQ_split]; ring⟩
    rw [list_prod_maxZDeg Rfacs hR_ne] at h1
    exact h1.trans hQdegZ
  have hR_degY_le : ∀ R ∈ Rfacs, R.natDegree ≤ L_Y := fun R hR =>
    (List.le_sum_of_mem (List.mem_map_of_mem hR)).trans hR_sum_degY
  have hR_maxX_le : ∀ R ∈ Rfacs, maxXDeg R ≤ D_X := fun R hR =>
    (maxXDeg_le_of_dvd hQne (hR_dvd_Q R hR)).trans hQdegX
  have hR_maxZ_le : ∀ R ∈ Rfacs, maxZDeg R ≤ D_Z := fun R hR =>
    (maxZDeg_le_of_dvd hQne (hR_dvd_Q R hR)).trans hQdegZ
  -- Pick ONE good `x₀ ∈ G` avoiding `R.leadingCoeff(Z, x₀) = 0` and `Δ_R(Z, x₀) = 0` for all `R ∈ Rfacs`.
  let badX_of : ((F[X])[X])[X] → Finset F := fun R =>
    (G.filter fun x => R.leadingCoeff.eval (C x) = 0) ∪
    (G.filter fun x => (Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R R.derivative).eval (C x) = 0)
  have hbadX_card : ∀ R ∈ Rfacs, (badX_of R).card ≤ R.leadingCoeff.natDegree + 2 * R.natDegree * D_X := by
    intro R hR
    have hlc_ne : R.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hR_ne R hR)
    have hchar_R : p = 0 ∨ R.natDegree < p := by
      rcases hchar with hp0 | hlt
      · exact Or.inl hp0
      · exact Or.inr (lt_of_le_of_lt (hR_degY_le R hR) hlt)
    have hΔ_ne : Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R R.derivative ≠ 0 :=
      sylvesterDet_derivative_ne_zero (hR_irr R hR) (hR_pos R hR) hchar_R
    have hΔ_deg : (Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R R.derivative).natDegree ≤
        2 * R.natDegree * D_X := by
      have hR_X : ∀ j, (R.coeff j).natDegree ≤ D_X := fun j =>
        (coeff_natDegree_le_maxXDeg R j).trans (hR_maxX_le R hR)
      have hR'_X : ∀ j, (R.derivative.coeff j).natDegree ≤ D_X := fun j => by
        rw [Polynomial.coeff_derivative]
        exact (Polynomial.natDegree_mul_le).trans
          (by simpa [Polynomial.natDegree_natCast] using hR_X (j + 1))
      have hdet := Sylvester.natDegree_sylvesterDet_le
        (m := R.natDegree) (n := max (R.natDegree - 1) 1) hR_X hR'_X
      have hns : max (R.natDegree - 1) 1 ≤ R.natDegree := by
        have := hR_pos R hR; omega
      calc _ ≤ max (R.natDegree - 1) 1 * D_X + R.natDegree * D_X := hdet
        _ ≤ R.natDegree * D_X + R.natDegree * D_X :=
            Nat.add_le_add_right (Nat.mul_le_mul_right D_X hns) _
        _ = 2 * R.natDegree * D_X := by ring
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ?_)
    · exact card_eval_C_eq_zero_le hlc_ne G
    · exact (card_eval_C_eq_zero_le hΔ_ne G).trans hΔ_deg
  have hlc_sum_le : (Rfacs.map fun R => R.leadingCoeff.natDegree).sum ≤ D_X := by
    have hlc_prod : (Rfacs.map fun R => R.leadingCoeff).prod = Rfacs.prod.leadingCoeff := by
      clear hbadX_card
      induction Rfacs with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.prod_cons, Polynomial.leadingCoeff_mul, ih]
    have hlc_ne : ∀ f ∈ Rfacs.map Polynomial.leadingCoeff, f ≠ 0 := by
      intro f hf
      obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hf
      exact Polynomial.leadingCoeff_ne_zero.mpr (hR_ne R hR)
    have hdeg_sum : (Rfacs.map fun R => R.leadingCoeff.natDegree).sum =
        Rfacs.prod.leadingCoeff.natDegree := by
      rw [← hlc_prod, list_prod_natDegree _ hlc_ne, List.map_map]
      rfl
    rw [hdeg_sum]
    have hle_prod : Rfacs.prod.leadingCoeff.natDegree ≤ maxXDeg Rfacs.prod :=
      coeff_natDegree_le_maxXDeg Rfacs.prod Rfacs.prod.natDegree
    exact hle_prod.trans ((maxXDeg_le_of_dvd hQne ⟨Q₀, by rw [hQ_split]; ring⟩).trans hQdegX)
  let badX_all : Finset F := Rfacs.foldr (fun R acc => badX_of R ∪ acc) ∅
  have hbadX_all_le : badX_all.card ≤ (2 * L_Y + 1) * D_X := by
    have hfold : ∀ (l : List ((F[X])[X])[X]),
        (∀ R ∈ l, (badX_of R).card ≤ R.leadingCoeff.natDegree + 2 * R.natDegree * D_X) →
        (l.foldr (fun R acc => badX_of R ∪ acc) ∅).card ≤
          (l.map fun R => R.leadingCoeff.natDegree).sum + 2 * (l.map Polynomial.natDegree).sum * D_X := by
      intro l hl
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        refine (Finset.card_union_le _ _).trans ?_
        have h1 := hl a (List.mem_cons_self ..)
        have h2 := ih fun R hR => hl R (List.mem_cons_of_mem _ hR)
        calc (badX_of a).card + (l.foldr (fun R acc => badX_of R ∪ acc) ∅).card
            ≤ (a.leadingCoeff.natDegree + 2 * a.natDegree * D_X) +
              ((l.map fun R => R.leadingCoeff.natDegree).sum + 2 * (l.map Polynomial.natDegree).sum * D_X) :=
              Nat.add_le_add h1 h2
          _ = a.leadingCoeff.natDegree + (l.map fun R => R.leadingCoeff.natDegree).sum +
              2 * (a.natDegree + (l.map Polynomial.natDegree).sum) * D_X := by ring
    refine (hfold Rfacs hbadX_card).trans ?_
    calc (Rfacs.map fun R => R.leadingCoeff.natDegree).sum + 2 * (Rfacs.map Polynomial.natDegree).sum * D_X
        ≤ D_X + 2 * L_Y * D_X :=
          Nat.add_le_add hlc_sum_le (Nat.mul_le_mul_right D_X (Nat.mul_le_mul_left 2 hR_sum_degY))
      _ = (2 * L_Y + 1) * D_X := by ring
  have hgoodX_ne : (G \ badX_all).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : G ⊆ badX_all := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have := (Finset.card_le_card hsub).trans hbadX_all_le
    omega
  obtain ⟨x₀, hx₀⟩ := hgoodX_ne
  have hx₀_not : x₀ ∉ badX_all := (Finset.mem_sdiff.mp hx₀).2
  have hx₀_good : ∀ R ∈ Rfacs,
      R.leadingCoeff.eval (C x₀) ≠ 0 ∧
      (Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R R.derivative).eval (C x₀) ≠ 0 := by
    intro R hR
    have hnotR : x₀ ∉ badX_of R := by
      intro hmem
      apply hx₀_not
      have hmem_fold : ∀ (l : List ((F[X])[X])[X]), R ∈ l → x₀ ∈ badX_of R →
          x₀ ∈ l.foldr (fun R acc => badX_of R ∪ acc) ∅ := by
        intro l hl hm
        induction l with
        | nil => simp at hl
        | cons a l ih =>
          simp only [List.foldr_cons, Finset.mem_union]
          rcases List.mem_cons.mp hl with rfl | htail
          · exact Or.inl hm
          · exact Or.inr (ih htail)
      exact hmem_fold Rfacs hR hmem
    have hx₀G : x₀ ∈ G := (Finset.mem_sdiff.mp hx₀).1
    constructor
    · intro h0; exact hnotR (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx₀G, h0⟩))
    · intro h0; exact hnotR (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx₀G, h0⟩))
  -- Step 2b: for each `R ∈ Rfacs`, factor `R₀ := evalX0 (shiftXTriv x₀ R)` in `(F[Z])[T]`.
  have hR₀_factor : ∀ R ∈ Rfacs,
      ∃ (cR : F[X]) (Hs : List (F[X])[X]),
        cR ≠ 0 ∧
        (∀ H ∈ Hs, Irreducible H ∧ 1 ≤ H.natDegree ∧ H ∣ evalX0 (shiftXTriv x₀ R) ∧
          maxCoeffDeg H ≤ D_Z) ∧
        evalX0 (shiftXTriv x₀ R) = C cR * Hs.prod ∧
        (Hs.map Polynomial.natDegree).sum = R.natDegree ∧
        cR.natDegree ≤ maxZDeg R := by
    intro R hR
    set R₀ := evalX0 (shiftXTriv x₀ R)
    have hR₀_deg : R₀.natDegree = R.natDegree := by
      have hlc : (R₀.coeff R.natDegree) ≠ 0 := by
        dsimp only [R₀]
        rw [evalX0_shiftXTriv, Polynomial.coeff_map]
        exact (hx₀_good R hR).1
      exact le_antisymm (Polynomial.natDegree_map_le.trans (shiftXTriv_natDegree_eq x₀ R).le)
        (Polynomial.le_natDegree_of_ne_zero hlc)
    have hR₀_ne : R₀ ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hR₀_deg; have := hR_pos R hR; omega
    have hR₀_maxZ : maxCoeffDeg R₀ ≤ maxZDeg R := by
      rw [maxCoeffDeg_le_iff]
      intro j
      dsimp only [R₀, evalX0]
      rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom, ← Polynomial.coeff_zero_eq_eval_zero]
      exact (coeff_coeff_natDegree_le_maxZDeg (shiftXTriv x₀ R) j 0).trans (shiftXTriv_maxZDeg_le x₀ R)
    let fAll := (UniqueFactorizationMonoid.factors R₀).toList
    have hfAll_irr : ∀ f ∈ fAll, Irreducible f := fun f hf =>
      UniqueFactorizationMonoid.irreducible_of_factor f (Multiset.mem_toList.mp hf)
    have hfAll_ne : ∀ f ∈ fAll, f ≠ 0 := fun f hf => (hfAll_irr f hf).ne_zero
    obtain ⟨uR, huR⟩ := show Associated fAll.prod R₀ by
      have h := UniqueFactorizationMonoid.factors_prod (α := (F[X])[X]) hR₀_ne
      rwa [← Multiset.prod_toList] at h
    let Hs := fAll.filter fun H => decide (1 ≤ H.natDegree)
    let Cs := fAll.filter fun H => decide (¬ 1 ≤ H.natDegree)
    have hsplit : R₀ = (Cs.prod * (uR : (F[X])[X])) * Hs.prod := by
      have hmul : ∀ (l : List (F[X])[X]),
          l.prod = (l.filter fun H => decide (1 ≤ H.natDegree)).prod *
            (l.filter fun H => decide (¬ 1 ≤ H.natDegree)).prod := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.prod_cons, List.filter_cons]
          by_cases h1 : 1 ≤ a.natDegree
          · simp [h1, ih]; ring
          · simp [h1, ih]; ring
      rw [← huR, hmul fAll]; ring
    have hC_ne : Cs.prod * (uR : (F[X])[X]) ≠ 0 :=
      mul_ne_zero (List.prod_ne_zero fun h0 => hfAll_ne 0 (List.mem_of_mem_filter h0) rfl) uR.ne_zero
    have hC_deg : (Cs.prod * (uR : (F[X])[X])).natDegree = 0 := by
      have hCs_ne : ∀ f ∈ Cs, f ≠ 0 := fun f hf => hfAll_ne f (List.mem_of_mem_filter hf)
      have hCs_deg : Cs.prod.natDegree = 0 := by
        rw [list_prod_natDegree Cs hCs_ne]
        refine List.sum_eq_zero fun x hx => ?_
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
        have hnot : ¬ (1 ≤ f.natDegree) := of_decide_eq_true (List.mem_filter.mp hf).2
        omega
      have hu_deg : (uR : (F[X])[X]).natDegree = 0 := by
        obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.mp uR.isUnit
        rw [← hr, Polynomial.natDegree_C]
      rw [Polynomial.natDegree_mul (List.prod_ne_zero fun h0 => hCs_ne 0 h0 rfl) uR.ne_zero,
        hCs_deg, hu_deg]
    set cR : F[X] := (Cs.prod * (uR : (F[X])[X])).coeff 0
    have hcR_eq : Cs.prod * (uR : (F[X])[X]) = C cR := Polynomial.eq_C_of_natDegree_eq_zero hC_deg
    have hcR_ne : cR ≠ 0 := fun h0 => hC_ne (by rw [hcR_eq, h0, map_zero])
    rw [hcR_eq] at hsplit
    have hHs_ne : ∀ H ∈ Hs, H ≠ 0 := fun H hH => hfAll_ne H (List.mem_of_mem_filter hH)
    have hHs_sum : (Hs.map Polynomial.natDegree).sum = R.natDegree := by
      rw [← hR₀_deg, hsplit, Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hcR_ne)
        (List.prod_ne_zero fun h0 => hHs_ne 0 h0 rfl), Polynomial.natDegree_C, zero_add,
        list_prod_natDegree Hs hHs_ne]
    have hcR_deg : cR.natDegree ≤ maxZDeg R := by
      have h1 : maxCoeffDeg (C cR) ≤ maxCoeffDeg R₀ :=
        maxCoeffDeg_le_of_dvd hR₀_ne ⟨Hs.prod, hsplit⟩
      have h2 : cR.natDegree ≤ maxCoeffDeg (C cR) := by
        simpa using coeff_natDegree_le_maxCoeffDeg (C cR) 0
      exact h2.trans (h1.trans hR₀_maxZ)
    refine ⟨cR, Hs, hcR_ne, fun H hH => ?_, hsplit, hHs_sum, hcR_deg⟩
    have hdvd : H ∣ R₀ := dvd_trans (List.dvd_prod hH) ⟨C cR, by rw [hsplit, mul_comm]⟩
    exact ⟨hfAll_irr H (List.mem_of_mem_filter hH),
      of_decide_eq_true (List.mem_filter.mp hH).2, hdvd,
      (maxCoeffDeg_le_of_dvd hR₀_ne hdvd).trans (hR₀_maxZ.trans (hR_maxZ_le R hR))⟩
  -- Build flat list of pairs `(R, H)` across all `R ∈ Rfacs`.
  choose cOf HsOf hcOf_ne hHsOf_spec hR₀_eq hHsOf_sum hcOf_deg using fun (R : {R // R ∈ Rfacs}) =>
    hR₀_factor R.1 R.2
  let pairs : List ({R // R ∈ Rfacs} × (F[X])[X]) :=
    Rfacs.attach.flatMap fun R => (HsOf R).map fun H => (R, H)
  -- Filter out `β ∈ G` where `evalZBiv β Q = 0` or `∃ R ∈ Rfacs, cOf R (β) = 0`.
  let badZ_c : Finset F :=
    Rfacs.attach.foldr (fun R acc => (G.filter fun β => (cOf R).eval β = 0) ∪ acc) ∅
  have hbadZ_c_le : badZ_c.card ≤ D_Z := by
    have hfold : ∀ (l : List {R // R ∈ Rfacs}),
        (l.foldr (fun R acc => (G.filter fun β => (cOf R).eval β = 0) ∪ acc) ∅).card ≤
          (l.map fun R => maxZDeg R.1).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        simp only [List.foldr_cons, List.map_cons, List.sum_cons]
        refine (Finset.card_union_le _ _).trans (Nat.add_le_add ?_ ih)
        have hsub : (G.filter fun β => (cOf a).eval β = 0) ⊆ (cOf a).roots.toFinset := fun β hβ =>
          Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hcOf_ne a)).mpr (Finset.mem_filter.mp hβ).2)
        exact (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans
          ((Polynomial.card_roots' (cOf a)).trans (hcOf_deg a)))
    refine (hfold Rfacs.attach).trans ?_
    have hmap : (Rfacs.attach.map fun R => maxZDeg R.1) = Rfacs.map maxZDeg :=
      List.attach_map_val
    rw [hmap]
    exact hR_sum_maxZ
  let badZ_Q : Finset F := G.filter fun β => evalZBiv β Q = 0
  have hbadZ_Q_le : badZ_Q.card ≤ D_Z := (card_evalZBiv_eq_zero_le hQne G).trans hQdegZ
  let G₀ : Finset F := G \ (badZ_Q ∪ badZ_c)
  have hG₀_gt : L_Y * max B3 B4 < G₀.card := by
    have h1 : (badZ_Q ∪ badZ_c).card ≤ 2 * D_Z := by
      refine (Finset.card_union_le _ _).trans ?_; omega
    have h2 : G.card ≤ G₀.card + (badZ_Q ∪ badZ_c).card := by
      have hsub : G ⊆ G₀ ∪ (badZ_Q ∪ badZ_c) := by
        intro β hβ
        by_cases h : β ∈ badZ_Q ∪ badZ_c
        · exact Finset.mem_union_right _ h
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hβ, h⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega
  -- Every `β ∈ G₀` is covered by some `(R, H) ∈ pairs`!
  let S_pair : ({R // R ∈ Rfacs} × (F[X])[X]) → Finset F := fun pr =>
    G₀.filter fun β => (evalZR β pr.1.1).eval (pOf β) = 0 ∧ evalZT β ((pOf β).eval x₀) pr.2 = 0
  have hcov : ∀ β ∈ G₀, ∃ pr ∈ pairs, β ∈ S_pair pr := by
    intro β hβ
    have hβG : β ∈ G := (Finset.mem_sdiff.mp hβ).1
    have hnot_bad : β ∉ badZ_Q ∪ badZ_c := (Finset.mem_sdiff.mp hβ).2
    have hQβ_ne : evalZBiv β Q ≠ 0 := fun h0 =>
      hnot_bad (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hβG, h0⟩))
    have hQβ_eval : (evalZBiv β Q).eval (pOf β) = 0 :=
      hQann β (pOf β) (hpOf β hβG).1 (hpOf β hβG).2.2
    -- `Q = Q₀ * Rfacs.prod`, and `Q₀` has `deg_Y = 0` with `evalZBiv β Q₀ ≠ 0`.
    have hQ₀β_ne : evalZBiv β Q₀ ≠ 0 := fun h0 => by
      apply hQβ_ne; rw [hQ_split, map_mul, h0, zero_mul]
    have hQ₀β_eval_ne : (evalZBiv β Q₀).eval (pOf β) ≠ 0 := by
      have hdeg0 : (evalZBiv β Q₀).natDegree = 0 :=
        Nat.eq_zero_of_le_zero (Polynomial.natDegree_map_le.trans hQ₀deg.le)
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, Polynomial.eval_C]
      intro h0
      apply hQ₀β_ne
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0, h0, map_zero]
    have hprod_eval : ((evalZBiv β Rfacs.prod).eval (pOf β)) = 0 := by
      rw [hQ_split, map_mul, Polynomial.eval_mul] at hQβ_eval
      exact (mul_eq_zero.mp hQβ_eval).resolve_left hQ₀β_eval_ne
    -- Extract some `R ∈ Rfacs` with `(evalZR β R).eval (pOf β) = 0`!
    have hex_R : ∃ R ∈ Rfacs, (evalZR β R).eval (pOf β) = 0 := by
      have hprod_ev : ∀ (l : List ((F[X])[X])[X]),
          (evalZBiv β l.prod).eval (pOf β) = 0 → ∃ R ∈ l, (evalZR β R).eval (pOf β) = 0 := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          intro h0
          rw [List.prod_cons, map_mul, Polynomial.eval_mul] at h0
          rcases mul_eq_zero.mp h0 with ha | hl
          · exact ⟨a, List.mem_cons_self .., ha⟩
          · obtain ⟨R, hR, hR0⟩ := ih hl
            exact ⟨R, List.mem_cons_of_mem _ hR, hR0⟩
      exact hprod_ev Rfacs hprod_eval
    obtain ⟨R, hR, hRβ0⟩ := hex_R
    let Rsub : {R // R ∈ Rfacs} := ⟨R, hR⟩
    have hcRβ_ne : (cOf Rsub).eval β ≠ 0 := by
      intro h0
      apply hnot_bad
      refine Finset.mem_union_right _ ?_
      have hmem_fold : ∀ (l : List {R // R ∈ Rfacs}), Rsub ∈ l →
          β ∈ l.foldr (fun R acc => (G.filter fun β => (cOf R).eval β = 0) ∪ acc) ∅ := by
        intro l hl
        induction l with
        | nil => simp at hl
        | cons a l ih =>
          simp only [List.foldr_cons, Finset.mem_union]
          rcases List.mem_cons.mp hl with rfl | htail
          · exact Or.inl (Finset.mem_filter.mpr ⟨hβG, h0⟩)
          · exact Or.inr (ih htail)
      exact hmem_fold Rfacs.attach (List.mem_attach _ _)
    -- Evaluate `evalX0 (shiftXTriv x₀ R) = C (cOf Rsub) * (HsOf Rsub).prod` at `(β, (pOf β).eval x₀)`.
    have hR₀_ev : evalZT β ((pOf β).eval x₀) (evalX0 (shiftXTriv x₀ R)) = 0 := by
      have h1 : ((evalZR β (shiftXTriv x₀ R)).eval ((pOf β).comp (X + C x₀))).eval 0 = 0 := by
        rw [evalZR_shiftXTriv, hRβ0, Polynomial.zero_comp, eval_zero]
      have h2 : ((evalZR β (shiftXTriv x₀ R)).eval ((pOf β).comp (X + C x₀))).eval 0 =
          ((evalZR β (shiftXTriv x₀ R)).map (Polynomial.evalRingHom 0)).eval ((pOf β).eval x₀) := by
        have hhom := Polynomial.hom_eval₂ (evalZR β (shiftXTriv x₀ R)) (RingHom.id F[X])
          (Polynomial.evalRingHom 0) ((pOf β).comp (X + C x₀))
        have hp0 : ((pOf β).comp (X + C x₀)).eval 0 = (pOf β).eval x₀ := by simp [Polynomial.eval_comp]
        simpa [Polynomial.eval_map, hp0] using hhom
      have h3 : (evalZR β (shiftXTriv x₀ R)).map (Polynomial.evalRingHom 0) =
          (evalX0 (shiftXTriv x₀ R)).map (Polynomial.evalRingHom β) := by
        dsimp only [evalZR, evalX0]
        rw [Polynomial.map_map, Polynomial.map_map]
        congr 1
        apply RingHom.ext; intro q
        simp [Polynomial.eval_map, Polynomial.coeff_zero_eq_eval_zero]
      rw [h3] at h2
      simpa [evalZT, Polynomial.eval_map] using h2.symm.trans h1
    rw [hR₀_eq Rsub, map_mul, evalZT_C] at hR₀_ev
    have hHprod0 : evalZT β ((pOf β).eval x₀) (HsOf Rsub).prod = 0 :=
      (mul_eq_zero.mp hR₀_ev).resolve_left hcRβ_ne
    have hex_H : ∃ H ∈ HsOf Rsub, evalZT β ((pOf β).eval x₀) H = 0 := by
      have hprod_ev : ∀ (l : List (F[X])[X]),
          evalZT β ((pOf β).eval x₀) l.prod = 0 → ∃ H ∈ l, evalZT β ((pOf β).eval x₀) H = 0 := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          intro h0
          rw [List.prod_cons, map_mul] at h0
          rcases mul_eq_zero.mp h0 with ha | hl
          · exact ⟨a, List.mem_cons_self .., ha⟩
          · obtain ⟨H, hH, hH0⟩ := ih hl
            exact ⟨H, List.mem_cons_of_mem _ hH, hH0⟩
      exact hprod_ev (HsOf Rsub) hHprod0
    obtain ⟨H, hH, hHβ0⟩ := hex_H
    refine ⟨(Rsub, H), ?_, Finset.mem_filter.mpr ⟨hβ, hRβ0, hHβ0⟩⟩
    exact List.mem_flatMap.mpr ⟨Rsub, List.mem_attach _ _, List.mem_map.mpr ⟨H, hH, rfl⟩⟩
  -- Total weight of `pairs` is `≤ L_Y`!
  have hweight_sum : (pairs.map fun pr => pr.2.natDegree).sum ≤ L_Y := by
    have hflat : (pairs.map fun pr => pr.2.natDegree).sum =
        (Rfacs.attach.map fun R => ((HsOf R).map Polynomial.natDegree).sum).sum := by
      dsimp only [pairs]
      have hgen : ∀ (l : List {R // R ∈ Rfacs}),
          ((l.flatMap fun R => (HsOf R).map fun H => (R, H)).map fun pr => pr.2.natDegree).sum =
          (l.map fun R => ((HsOf R).map Polynomial.natDegree).sum).sum := by
        intro l
        induction l with
        | nil => simp
        | cons a l ih =>
          simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
            List.sum_cons, ih, List.map_map]
          rfl
      exact hgen Rfacs.attach
    rw [hflat]
    have hEq : (Rfacs.attach.map fun R => ((HsOf R).map Polynomial.natDegree).sum) =
        Rfacs.map Polynomial.natDegree := by
      have h1 : (Rfacs.attach.map fun R => ((HsOf R).map Polynomial.natDegree).sum) =
          Rfacs.attach.map fun R => R.1.natDegree :=
        List.map_congr_left fun R _ => hHsOf_sum R
      rw [h1]
      exact List.attach_map_val
    rw [hEq]
    exact hR_sum_degY
  have hgt_w : (pairs.map fun pr => pr.2.natDegree).sum * max B3 B4 < G₀.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hweight_sum) hG₀_gt
  obtain ⟨⟨Rsub, H⟩, hpr_mem, hwin⟩ :=
    exists_weighted_pigeonhole pairs (fun pr => pr.2.natDegree) S_pair G₀ (max B3 B4) hcov hgt_w
  -- Extract properties of the winning pair `(Rsub.1, H)` and invoke `extract_correlated_tuple_of_pair`!
  obtain ⟨Rsub', _, hHmem_map⟩ := List.mem_flatMap.mp hpr_mem
  obtain ⟨H', hH'mem, hpair_eq⟩ := List.mem_map.mp hHmem_map
  cases hpair_eq
  set R := Rsub.1
  have hRmem : R ∈ Rfacs := Rsub.2
  obtain ⟨hHirr, hHpos, hHdvd, hHdegZ⟩ := hHsOf_spec Rsub H hH'mem
  have hRirr := hR_irr R hRmem
  have hRpos := hR_pos R hRmem
  have hRdegY := hR_degY_le R hRmem
  have hRdegZ := hR_maxZ_le R hRmem
  have hH_le_R : H.natDegree ≤ R.natDegree := by
    have h1 := List.le_sum_of_mem (List.mem_map_of_mem (f := Polynomial.natDegree) hH'mem)
    exact h1.trans (hHsOf_sum Rsub).le
  -- Show `Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1) R₀ R₀.derivative ≠ 0`!
  have hΔ₀_ne : Sylvester.sylvesterDet R.natDegree (max (R.natDegree - 1) 1)
      (evalX0 (shiftXTriv x₀ R)) (evalX0 (shiftXTriv x₀ R)).derivative ≠ 0 := by
    have hmap := Sylvester.map_sylvesterDet (Polynomial.evalRingHom (C x₀))
      R.natDegree (max (R.natDegree - 1) 1) R R.derivative
    rw [← Polynomial.derivative_map, ← evalX0_shiftXTriv x₀ R] at hmap
    rw [← hmap]
    exact (hx₀_good R hRmem).2
  -- Verify `hGH_card3` and `hGH_card4` from `hwin : H.natDegree * max B3 B4 < (S_pair (Rsub, H)).card`!
  set ℓ := R.natDegree
  set t := H.natDegree
  set B_C := ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z
  have hB_C_le_max : B_C ≤ (L_Y ^ 2 + 4 * L_Y + 1) * D_Z := by
    dsimp only [B_C]
    refine Nat.mul_le_mul_right D_Z ?_
    have h1 : (ℓ + 1) * t ≤ L_Y ^ 2 + L_Y := by
      have : (ℓ + 1) * t ≤ (L_Y + 1) * L_Y := Nat.mul_le_mul (by omega) (hH_le_R.trans hRdegY)
      calc (ℓ + 1) * t ≤ (L_Y + 1) * L_Y := this
        _ = L_Y ^ 2 + L_Y := by ring
    omega
  have hB_C_le_t : B_C ≤ t * ((4 * L_Y + 2) * D_Z) := by
    dsimp only [B_C]
    have h1 : (ℓ + 1) * t + 3 * ℓ + 1 ≤ t * (4 * L_Y + 2) := by
      have ht1 : 1 ≤ t := hHpos
      have hℓ : ℓ ≤ L_Y := hRdegY
      nlinarith
    calc ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z ≤ t * (4 * L_Y + 2) * D_Z := Nat.mul_le_mul_right D_Z h1
      _ = t * ((4 * L_Y + 2) * D_Z) := by ring
  have hcard3 : B_C + t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C) < (S_pair (Rsub, H)).card := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (Nat.mul_le_mul_left t (le_max_left B3 B4)) hwin)
    have h1 : (ℓ * t + 2) * D_Z ≤ (L_Y ^ 2 + 2) * D_Z := by
      refine Nat.mul_le_mul_right D_Z ?_
      have : ℓ * t ≤ L_Y * L_Y := Nat.mul_le_mul hRdegY (hH_le_R.trans hRdegY)
      have hsq : L_Y * L_Y = L_Y ^ 2 := (sq L_Y).symm
      omega
    have h2 : 2 * d * ℓ * B_C ≤ 2 * d * L_Y * ((L_Y ^ 2 + 4 * L_Y + 1) * D_Z) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 * d) hRdegY) hB_C_le_max
    calc B_C + t * ((ℓ * t + 2) * D_Z + 2 * d * ℓ * B_C)
        ≤ t * ((4 * L_Y + 2) * D_Z) + t * ((L_Y ^ 2 + 2) * D_Z + 2 * d * L_Y * ((L_Y ^ 2 + 4 * L_Y + 1) * D_Z)) :=
          Nat.add_le_add hB_C_le_t (Nat.mul_le_mul_left t (Nat.add_le_add h1 h2))
      _ = t * B3 := by dsimp only [B3]; ring
  have hcard4 : B_C + n * (D_Z + (m - 1) * ℓ) < (S_pair (Rsub, H)).card := by
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt (Nat.mul_le_mul_left t (le_max_right B3 B4)) hwin)
    have h1 : n * (D_Z + (m - 1) * ℓ) ≤ t * (n * (D_Z + (m - 1) * L_Y)) := by
      have hle : n * (D_Z + (m - 1) * ℓ) ≤ n * (D_Z + (m - 1) * L_Y) :=
        Nat.mul_le_mul_left n (Nat.add_le_add_left (Nat.mul_le_mul_left (m - 1) hRdegY) D_Z)
      exact hle.trans (Nat.le_mul_of_pos_left _ hHpos)
    calc B_C + n * (D_Z + (m - 1) * ℓ)
        ≤ t * ((4 * L_Y + 2) * D_Z) + t * (n * (D_Z + (m - 1) * L_Y)) := Nat.add_le_add hB_C_le_t h1
      _ = t * B4 := by dsimp only [B4]; ring
  exact extract_correlated_tuple_of_pair hd hdA hm hRirr hRpos hRdegZ hHirr hHpos hHdegZ
    hHdvd hΔ₀_ne
    (fun β hβ => by
      have hβG₀ := (Finset.mem_filter.mp hβ).1
      have hβG := (Finset.mem_sdiff.mp hβG₀).1
      exact ⟨(hpOf β hβG).1, (hpOf β hβG).2.1, (hpOf β hβG).2.2,
        (Finset.mem_filter.mp hβ).2.1, (Finset.mem_filter.mp hβ).2.2⟩)
    hcard3 hcard4

/-- **General Unconditional `CurveListCA` under `p = 0 ∨ gsDegY |D| d A < p`.**
Handles all edge cases (`D.card = 0`, `m = 0`, `m = 1`, `d = 0`, `d = 1`) and
dispatches `m ≥ 2, d ≥ 2` to `curveListCA_main_case`. -/
theorem curveListCA_of_char_bound {p : ℕ} [CharP F p]
    (hchar : ∀ (D : Finset F) (d A m : ℕ) (G : Finset F),
      D.card * (d - 1) < A ^ 2 → 2 ≤ m → 2 ≤ d →
      curveListThreshold D.card d A m < G.card →
      p = 0 ∨ gsDegY D.card d A < p) :
    CurveListCA F curveListThreshold := by
  intro D d A m hJ u L G _ hGcard hG
  classical
  have hGne : G.Nonempty := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hGcard)
  -- Case 1: `m ≤ 1` (`m = 0` or `m = 1`).
  by_cases hm1 : m ≤ 1
  · obtain ⟨β₀, hβ₀⟩ := hGne
    obtain ⟨p₀, hp₀_deg, hp₀_notL, hp₀_ag⟩ := hG β₀ hβ₀
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm1 with rfl | rfl
    · -- `m = 0`: `v = Fin.elim0`, `∑ k : Fin 0, ... = 0`, `tupleAgreeSet D u v = D`.
      refine ⟨Fin.elim0, ?_, fun k => Fin.elim0 k, ?_⟩
      · intro hvL
        have h0 : p₀ = 0 := by
          have hAD : A ≤ D.card := hp₀_ag.trans (Finset.card_le_card (Finset.filter_subset _ _))
          by_cases hd0 : d = 0
          · subst hd0
            by_contra hne
            have := Polynomial.degree_eq_natDegree hne
            rw [this] at hp₀_deg
            exact not_lt_of_ge (WithBot.coe_le_coe.mpr (Nat.zero_le _)) hp₀_deg
          · have hdA : d ≤ A := by
              have h1 : D.card * (d - 1) < D.card * A :=
                lt_of_lt_of_le hJ (by rw [sq]; exact Nat.mul_le_mul_right A hAD)
              have := Nat.lt_of_mul_lt_mul_left h1
              omega
            exact eq_of_degree_lt_of_agree hp₀_deg
              (by rw [degree_zero]; exact WithBot.bot_lt_coe d) (hdA.trans hp₀_ag) fun x hx => by
                have := (Finset.mem_filter.mp hx).2
                simp at this
                rw [eval_zero]
                exact this.symm
        exact hp₀_notL Fin.elim0 hvL (by simp [h0])
      · have htot : tupleAgreeSet D u Fin.elim0 = D := by
          ext x; simp [tupleAgreeSet]
        rw [htot]
        exact hp₀_ag.trans (Finset.card_le_card (Finset.filter_subset _ _))
    · -- `m = 1`: `v 0 = p₀`.
      refine ⟨fun _ => p₀, ?_, fun _ => hp₀_deg, ?_⟩
      · intro hvL
        exact hp₀_notL (fun _ => p₀) hvL (by simp)
      · have heq : tupleAgreeSet D u (fun _ => p₀) =
            D.filter fun x => ∑ k : Fin 1, β₀ ^ (k : ℕ) * u k x = p₀.eval x := by
          ext x; simp [tupleAgreeSet]
        rwa [heq]
  · -- `m ≥ 2`.
    have hm : 2 ≤ m := by omega
    -- Case 2: `d = 0`.
    by_cases hd0 : d = 0
    · subst hd0
      have hthresh0 : curveListThreshold D.card 0 A m = D.card * (m - 1) := by
        unfold curveListThreshold; rw [ite_eq_right (by omega), ite_eq_left rfl]
      rw [hthresh0] at hGcard
      have hp_zero : ∀ β ∈ G, ∀ p : F[X], p.degree < (0 : ℕ) → p = 0 := by
        intro _ _ p hp
        by_contra hne
        rw [Polynomial.degree_eq_natDegree hne] at hp
        exact not_lt_of_ge (WithBot.coe_le_coe.mpr (Nat.zero_le _)) hp
      let v : Fin m → F[X] := fun _ => 0
      refine ⟨v, ?_, fun _ => by rw [degree_zero]; exact WithBot.bot_lt_coe 0, ?_⟩
      · intro hvL
        obtain ⟨β₀, hβ₀⟩ := hGne
        obtain ⟨p₀, hp₀_deg, hp₀_notL, _⟩ := hG β₀ hβ₀
        exact hp₀_notL v hvL (by simp [v, hp_zero β₀ hβ₀ p₀ hp₀_deg])
      · -- Double counting `{(β, x) ∈ G × D | ∑ β^k * u k x = 0}`.
        have hsum_ge : G.card * A ≤ ∑ β ∈ G, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card := by
          calc G.card * A = ∑ _β ∈ G, A := by simp
            _ ≤ _ := Finset.sum_le_sum fun β hβ => by
                obtain ⟨p, hpdeg, _, hag⟩ := hG β hβ
                simpa [hp_zero β hβ p hpdeg] using hag
        have hswap : ∑ β ∈ G, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card =
            ∑ x ∈ D, (G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card := by
          simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]; exact Finset.sum_comm
        set S := tupleAgreeSet D u v
        have hsum_le : ∑ x ∈ D, (G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card ≤
            S.card * G.card + D.card * (m - 1) := by
          have hsub : S ⊆ D := Finset.filter_subset _ _
          have hsplit_D : ∑ x ∈ D, (G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card =
              (∑ x ∈ S, (G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card) +
              ∑ x ∈ D \ S, (G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = 0).card := by
            rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
          rw [hsplit_D]
          refine Nat.add_le_add ?_ ?_
          · calc _ ≤ ∑ _x ∈ S, G.card := Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _
              _ = S.card * G.card := by simp
          · calc _ ≤ ∑ _x ∈ D \ S, (m - 1) := Finset.sum_le_sum fun x hx => by
                  have hxD := (Finset.mem_sdiff.mp hx).1
                  have hxnot := (Finset.mem_sdiff.mp hx).2
                  have ha : (fun k : Fin m => u k x) ≠ 0 := by
                    intro h0
                    exact hxnot (Finset.mem_filter.mpr ⟨hxD, fun k => by simp [v, congrFun h0 k]⟩)
                  have hlt := ProximityGap.card_roots_lt ha G
                  omega
              _ = (D \ S).card * (m - 1) := by simp
              _ ≤ D.card * (m - 1) := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
        have hineq : G.card * A ≤ S.card * G.card + D.card * (m - 1) := hsum_ge.trans (hswap ▸ hsum_le)
        by_contra hlt
        have hmul : (S.card + 1) * G.card ≤ G.card * A := by
          rw [Nat.mul_comm G.card A]; exact Nat.mul_le_mul_right G.card (by omega)
        rw [Nat.add_mul, one_mul] at hmul
        omega
    · -- Case 3: `d = 1`.
      by_cases hd1 : d = 1
      · subst hd1
        have hthresh1 : curveListThreshold D.card 1 A m = D.card * (m - 1) * (D.card / A + 1) := by
          unfold curveListThreshold
          rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
        rw [hthresh1] at hGcard
        have hApos : 1 ≤ A := by
          by_contra h0
          have hA0 : A = 0 := by omega
          subst hA0
          simp at hJ
        let pOf : F → F[X] := fun β => if h : β ∈ G then (hG β h).choose else 0
        have hpOf : ∀ β ∈ G, (pOf β).degree < (1 : ℕ) ∧
            (∀ v ∈ L, pOf β ≠ ∑ k : Fin m, β ^ (k : ℕ) • v k) ∧
            A ≤ (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card :=
          fun β hβ => by simpa [pOf, dite_eq_left hβ] using (hG β hβ).choose_spec
        have hconst : ∀ β ∈ G, pOf β = C ((pOf β).coeff 0) := fun β hβ => by
          apply Polynomial.eq_C_of_natDegree_eq_zero
          by_cases h0 : pOf β = 0
          · simp [h0]
          · have hlt := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (hpOf β hβ).1
            omega
        -- Pigeonhole over `x ∈ D`: pick `x₀ ∈ D` with `|G_{x₀}| * |D| ≥ |G| * A`.
        let Gx : F → Finset F := fun x =>
          G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x
        have hsum_ge : G.card * A ≤ ∑ x ∈ D, (Gx x).card := by
          have h1 : G.card * A ≤ ∑ β ∈ G, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card := by
            calc G.card * A = ∑ _β ∈ G, A := by simp
              _ ≤ _ := Finset.sum_le_sum fun β hβ => (hpOf β hβ).2.2
          have hswap : ∑ β ∈ G, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x = (pOf β).eval x).card =
              ∑ x ∈ D, (Gx x).card := by
            dsimp only [Gx]
            simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]; exact Finset.sum_comm
          rwa [hswap] at h1
        have hDpos : 0 < D.card := by
          obtain ⟨β₀, hβ₀⟩ := hGne
          have hAD : A ≤ D.card := (hpOf β₀ hβ₀).2.2.trans (Finset.card_le_card (Finset.filter_subset _ _))
          omega
        have hex_x₀ : ∃ x₀ ∈ D, D.card * (m - 1) < (Gx x₀).card := by
          by_contra hall
          push Not at hall
          have hle : ∑ x ∈ D, (Gx x).card ≤ D.card * (D.card * (m - 1)) := by
            calc ∑ x ∈ D, (Gx x).card ≤ ∑ _x ∈ D, (D.card * (m - 1)) := Finset.sum_le_sum hall
              _ = D.card * (D.card * (m - 1)) := by simp
          have hdiv : D.card < (D.card / A + 1) * A := by
            have hm1 := Nat.div_add_mod D.card A
            have hm2 := Nat.mod_lt D.card hApos
            have hcomm : A * (D.card / A) = (D.card / A) * A := Nat.mul_comm _ _
            rw [Nat.add_mul, one_mul]; omega
          have hmul : D.card * (D.card * (m - 1)) < G.card * A := by
            have h1 : D.card * (m - 1) * D.card < D.card * (m - 1) * ((D.card / A + 1) * A) :=
              Nat.mul_lt_mul_of_pos_left hdiv (Nat.mul_pos hDpos (by omega))
            have h2 : D.card * (m - 1) * ((D.card / A + 1) * A) =
                (D.card * (m - 1) * (D.card / A + 1)) * A := by ring
            have h3 : (D.card * (m - 1) * (D.card / A + 1)) * A < G.card * A :=
              Nat.mul_lt_mul_of_pos_right hGcard hApos
            calc D.card * (D.card * (m - 1)) = D.card * (m - 1) * D.card := by ring
              _ < G.card * A := lt_trans (h2 ▸ h1) h3
          omega
        obtain ⟨x₀, _, hx₀_gt⟩ := hex_x₀
        let v : Fin m → F[X] := fun k => C (u k x₀)
        have hv_deg : ∀ k, (v k).degree < (1 : ℕ) := fun k =>
          (Polynomial.degree_C_le).trans_lt (WithBot.coe_lt_coe.mpr (by decide))
        have hGx_eq : ∀ β ∈ Gx x₀, pOf β = ∑ k : Fin m, β ^ (k : ℕ) • v k := by
          intro β hβ
          have hβG := (Finset.mem_filter.mp hβ).1
          have heq := (Finset.mem_filter.mp hβ).2
          rw [hconst β hβG] at heq ⊢
          rw [Polynomial.eval_C] at heq
          rw [← heq]
          dsimp only [v]
          simp only [Polynomial.smul_eq_C_mul, ← map_mul, ← map_sum]
        have hv_notL : v ∉ L := by
          intro hvL
          obtain ⟨β, hβ⟩ := Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hx₀_gt)
          exact (hpOf β (Finset.mem_filter.mp hβ).1).2.1 v hvL (hGx_eq β hβ)
        -- Double counting on `Gx x₀ × D`!
        set S := tupleAgreeSet D u v
        have hsum_ge2 : (Gx x₀).card * A ≤
            ∑ x ∈ D, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card := by
          have h1 : (Gx x₀).card * A ≤
              ∑ β ∈ Gx x₀, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card := by
            calc (Gx x₀).card * A = ∑ _β ∈ Gx x₀, A := by simp
              _ ≤ _ := Finset.sum_le_sum fun β hβ => by
                  have hβG := (Finset.mem_filter.mp hβ).1
                  refine (hpOf β hβG).2.2.trans (Finset.card_le_card fun x hx => ?_)
                  have hxD := (Finset.mem_filter.mp hx).1
                  have hxeq := (Finset.mem_filter.mp hx).2
                  refine Finset.mem_filter.mpr ⟨hxD, ?_⟩
                  rw [hGx_eq β hβ, Polynomial.eval_finsetSum] at hxeq
                  simp only [v, Polynomial.eval_smul, Polynomial.eval_C, smul_eq_mul] at hxeq
                  simp only [mul_sub, Finset.sum_sub_distrib, hxeq, sub_self]
          have hswap : ∑ β ∈ Gx x₀, (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card =
              ∑ x ∈ D, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card := by
            simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]; exact Finset.sum_comm
          rwa [hswap] at h1
        have hsum_le2 : ∑ x ∈ D, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card ≤
            S.card * (Gx x₀).card + D.card * (m - 1) := by
          have hsub : S ⊆ D := Finset.filter_subset _ _
          have hsplit_D : ∑ x ∈ D, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card =
              (∑ x ∈ S, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card) +
              ∑ x ∈ D \ S, ((Gx x₀).filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - u k x₀) = 0).card := by
            rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
          rw [hsplit_D]
          refine Nat.add_le_add ?_ ?_
          · calc _ ≤ ∑ _x ∈ S, (Gx x₀).card := Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _
              _ = S.card * (Gx x₀).card := by simp
          · calc _ ≤ ∑ _x ∈ D \ S, (m - 1) := Finset.sum_le_sum fun x hx => by
                  have hxD := (Finset.mem_sdiff.mp hx).1
                  have hxnot := (Finset.mem_sdiff.mp hx).2
                  have ha : (fun k : Fin m => u k x - u k x₀) ≠ 0 := by
                    intro h0
                    refine hxnot (Finset.mem_filter.mpr ⟨hxD, fun k => ?_⟩)
                    simp only [v, Polynomial.eval_C]
                    exact sub_eq_zero.mp (congrFun h0 k)
                  have hlt := ProximityGap.card_roots_lt ha (Gx x₀)
                  omega
              _ = (D \ S).card * (m - 1) := by simp
              _ ≤ D.card * (m - 1) := Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset)
        have hineq : (Gx x₀).card * A ≤ S.card * (Gx x₀).card + D.card * (m - 1) :=
          hsum_ge2.trans hsum_le2
        refine ⟨v, hv_notL, hv_deg, ?_⟩
        show A ≤ S.card
        by_contra hlt
        have hmul : (S.card + 1) * (Gx x₀).card ≤ (Gx x₀).card * A := by
          rw [Nat.mul_comm (Gx x₀).card A]; exact Nat.mul_le_mul_right (Gx x₀).card (by omega)
        rw [Nat.add_mul, one_mul] at hmul
        omega
      · -- Case 4: `2 ≤ m`, `2 ≤ d` — main case!
        have hd : 2 ≤ d := by omega
        exact curveListCA_main_case D d A m hJ hm hd (hchar D d A m G hJ hm hd hGcard) u L G hGcard hG

/-- **Unconditional `CurveListCA` for ANY finite field `F` of characteristic `p ≥ 2`
and extension degree at most `4` (`Fintype.card F ≤ p ^ 4`)!**
In particular, holds with ZERO extra hypotheses for `Fp`, `Fp2`, `Fp3` (Goldilocks
`Fp3Model`), and `Fp4`, because `gsDegY^5 ≤ curveListThreshold < G.card ≤ p^4 < p^5`
automatically forces `gsDegY < p`! -/
theorem curveListCA_of_fintype_char [Fintype F] {p : ℕ} [CharP F p]
    (hp : 2 ≤ p) (hcard : Fintype.card F ≤ p ^ 4) :
    CurveListCA F curveListThreshold := by
  refine curveListCA_of_char_bound (p := p) fun D d A m G _ hm hd hGcard => Or.inr ?_
  have h1 : gsDegY D.card d A ^ 5 ≤ curveListThreshold D.card d A m :=
    gsDegY_pow_five_le_curveListThreshold hm hd
  have h2 : G.card ≤ p ^ 4 := (Finset.card_le_univ G).trans hcard
  have h3 : p ^ 4 < p ^ 5 := by
    have : p ^ 5 = p * p ^ 4 := by ring
    rw [this]
    have hpos : 0 < p ^ 4 := pow_pos (by omega) 4
    nlinarith
  have hpow_lt : gsDegY D.card d A ^ 5 < p ^ 5 := lt_trans (lt_of_le_of_lt h1 hGcard) (lt_of_le_of_lt h2 h3)
  by_contra hge
  have hle : p ≤ gsDegY D.card d A := Nat.le_of_not_lt hge
  exact absurd (Nat.pow_le_pow_left hle 5) (not_le_of_gt hpow_lt)

end MainTheorems

end CurveListCAProof

end CertiFri

