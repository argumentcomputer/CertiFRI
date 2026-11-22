import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import CertiFriProofs.Theory.ProximityGap.Johnson

/-!
# The Guruswami–Sudan algebraic list-decoding core

This file formalizes, **unconditionally** over an arbitrary field `K` (of any
characteristic, finite or infinite), the bivariate interpolation and root-finding
machinery behind Guruswami–Sudan list decoding up to the Johnson radius
`A ^ 2 > |D| * (d - 1)`, together with its parametric instantiation over the
rational function field `RatFunc F`:

* `HasWeightedDegLE k D_X Q`: the `(1, k)`-weighted degree of a bivariate
  polynomial `Q : (K[X])[X]` is at most `D_X`.
* `eval_degree_le_of_hasWeightedDegLE`: if `HasWeightedDegLE (d - 1) D_X Q` and
  `p.degree < d`, then `(Q.eval p).degree ≤ D_X`.
* `shiftBiv x y Q` & `VanishesMult r x y Q`: characteristic-free multiplicity-`r`
  vanishing at `(x, y)` via the shifted bivariate polynomial
  `Q(X + x, Y + y)` having no monomials `X^a Y^b` with `a + b < r` (equivalently,
  all `(a, b)`-Hasse derivatives with `a + b < r` vanish at `(x, y)`).
* `dvd_eval_of_vanishesMult`: if `VanishesMult r x y Q` and `p.eval x = y`, then
  `(X - C x) ^ r ∣ Q.eval p`.
* `eval_eq_zero_of_agree_ge` & `X_sub_C_dvd_of_agree_ge`: **Guruswami–Sudan root
  theorem** — if `Q` has `(1, d - 1)`-weighted degree `D_X < r * A` and vanishes
  to multiplicity at least `r` at `(x, w x)` for all `x ∈ D`, then every
  polynomial `p` of degree below `d` agreeing with `w` on at least `A` points of
  `D` satisfies `Q.eval p = 0` and `(Y - p) ∣ Q`.
* `exists_gs_poly`: **Guruswami–Sudan interpolation existence** — whenever
  `0 < D.card`, `1 ≤ d`, and `D.card * (d - 1) < A ^ 2`, there exist `r ≥ 1`,
  `D_X < r * A`, and a nonzero `Q : (K[X])[X]` of `(1, d - 1)`-weighted degree
  at most `D_X` vanishing to multiplicity at least `r` at `(x, w x)` for every
  `x ∈ D`.
* `exists_gs_poly_curve`: **Parametric Guruswami–Sudan interpolation** over
  `RatFunc F` (`F(Z)`) for a Reed–Solomon curve `w_Z(x) = ∑ k, Z^k * u_k(x)`,
  establishing the exact bivariate algebraic annihilator that opens BCIKS20
  Section 5 / BCHKS25 / DKT26.

## Remaining bridge to unconditional `CurveListCA`

To discharge `CurveListCA F T` (`ProximityGap/JohnsonMCA.lean`) unconditionally
from `exists_gs_poly_curve`, what remains is the bivariate factorization /
rationality step over `F(Z)[X][Y]`:
1. Clear `Z`-denominators of `Q_Z ∈ (RatFunc F)[X][Y]` to obtain a primitive
   polynomial in `F[Z][X][Y]` with controlled `Z`-degree.
2. Strip `p`-th powers / repeated irreducible factors in characteristic `p` so
   the `Y`-derivative `∂Q/∂Y` is nonzero on the irreducible factor capturing
   the good parameters `β ∈ G`.
3. Hensel-lift the root `p_{z₀}(X) ∈ F[X]` at a good `z₀ ∈ G` to a formal power
   series `P(Z, X) ∈ F(X)[[Z - z₀]]` and prove `P` is a polynomial in `Z` of
   degree `< m` (BCIKS Lemma 5.5–5.6, or the sharpened BCHKS25 / DKT26 curve
   threshold).
-/

namespace CertiFri

namespace GuruswamiSudan

open Polynomial Finset

/-! ## Weighted degree of bivariate polynomials -/

section WeightedDegree

variable {K : Type*} [Field K]

/-- A bivariate polynomial `Q : (K[X])[X]` (outer indeterminate `Y`, inner
indeterminate `X`) has `(1, k)`-weighted degree at most `D_X` when every
monomial `X ^ i * Y ^ j` with `i + k * j > D_X` has coefficient zero. -/
def HasWeightedDegLE (k D_X : ℕ) (Q : (K[X])[X]) : Prop :=
  ∀ j i : ℕ, D_X < i + k * j → (Q.coeff j).coeff i = 0

/-- If `HasWeightedDegLE (d - 1) D_X Q` and `p.degree < d`, then the univariate
composition `Q.eval p : K[X]` has degree at most `D_X`. -/
theorem eval_degree_le_of_hasWeightedDegLE {d D_X : ℕ} {Q : (K[X])[X]} {p : K[X]}
    (hQ : HasWeightedDegLE (d - 1) D_X Q) (hp : p.degree < d) :
    (Q.eval p).degree ≤ (D_X : WithBot ℕ) := by
  rw [eval_eq_sum]
  refine (degree_sum_le Q.support fun j => Q.coeff j * p ^ j).trans ?_
  rw [Finset.sup_le_iff]
  intro j _
  by_cases hc : Q.coeff j = 0
  · simp [hc]
  · have hdeg_c : (Q.coeff j).degree ≤ ((D_X - (d - 1) * j : ℕ) : WithBot ℕ) := by
      rw [degree_le_iff_coeff_zero]
      intro i hi
      have hkj : (d - 1) * j ≤ D_X := by
        by_contra hlt
        push Not at hlt
        apply hc
        ext m
        rw [coeff_zero]
        exact hQ j m (by omega)
      have hgt : D_X < i + (d - 1) * j := by
        have hiN : D_X - (d - 1) * j < i := WithBot.coe_lt_coe.mp hi
        omega
      exact hQ j i hgt
    have hkj : (d - 1) * j ≤ D_X := by
      by_contra hlt
      push Not at hlt
      apply hc
      ext m
      rw [coeff_zero]
      exact hQ j m (by omega)
    have hp_le : p.degree ≤ ((d - 1 : ℕ) : WithBot ℕ) := by
      cases d with
      | zero =>
        have hp0 : p = 0 := by
          by_contra hne
          have := degree_eq_natDegree hne
          rw [this] at hp
          exact not_lt_of_ge (WithBot.coe_le_coe.mpr (Nat.zero_le _)) hp
        simp [hp0]
      | succ d' =>
        by_cases hp0 : p = 0
        · simp [hp0]
        · rw [degree_eq_natDegree hp0] at hp ⊢
          exact WithBot.coe_le_coe.mpr (Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp hp))
    have hpow : (p ^ j).degree ≤ (((d - 1) * j : ℕ) : WithBot ℕ) := by
      refine (degree_pow_le p j).trans ?_
      have h1 : j • p.degree ≤ j • ((d - 1 : ℕ) : WithBot ℕ) :=
        nsmul_le_nsmul_right hp_le j
      refine h1.trans ?_
      rw [nsmul_eq_mul, Nat.mul_comm]
      exact le_of_eq (by simp)
    calc (Q.coeff j * p ^ j).degree
        ≤ (Q.coeff j).degree + (p ^ j).degree := degree_mul_le _ _
      _ ≤ ((D_X - (d - 1) * j : ℕ) : WithBot ℕ) + (((d - 1) * j : ℕ) : WithBot ℕ) :=
          add_le_add hdeg_c hpow
      _ = (D_X : WithBot ℕ) := by
          norm_cast
          exact Nat.sub_add_cancel hkj

/-! ## Characteristic-free multiplicity vanishing (Hasse shift) -/

/-- Ring homomorphism shifting the inner indeterminate `X ↦ X + x`. -/
noncomputable def shiftXHom (x : K) : K[X] →+* K[X] :=
  eval₂RingHom C (X + C x)

@[simp] theorem shiftXHom_apply (x : K) (p : K[X]) :
    shiftXHom x p = p.comp (X + C x) := rfl

@[simp] theorem shiftXHom_C (x c : K) :
    shiftXHom x (C c) = C c := by
  simp [shiftXHom]

/-- Shifted bivariate polynomial `Q(X + x, Y + y)`. Its `(a, b)`-coefficient is
the `(a, b)`-Hasse derivative of `Q` evaluated at `(x, y)`. -/
noncomputable def shiftBiv (x y : K) (Q : (K[X])[X]) : (K[X])[X] :=
  (Q.map (shiftXHom x)).comp (X + C (C y))

theorem shiftBiv_add (x y : K) (Q₁ Q₂ : (K[X])[X]) :
    shiftBiv x y (Q₁ + Q₂) = shiftBiv x y Q₁ + shiftBiv x y Q₂ := by
  simp [shiftBiv, Polynomial.map_add, Polynomial.add_comp]

theorem shiftBiv_C_C_mul (x y c : K) (Q : (K[X])[X]) :
    shiftBiv x y (C (C c) * Q) = C (C c) * shiftBiv x y Q := by
  simp [shiftBiv, Polynomial.map_mul, Polynomial.mul_comp]

/-- `Q` vanishes to multiplicity at least `r` at `(x, y)` when every monomial
`X ^ a * Y ^ b` with `a + b < r` has coefficient zero in `Q(X + x, Y + y)`. -/
def VanishesMult (r : ℕ) (x y : K) (Q : (K[X])[X]) : Prop :=
  ∀ a b : ℕ, a + b < r → ((shiftBiv x y Q).coeff b).coeff a = 0

/-- Fundamental shift-evaluation identity:
`(Q.eval p)(X + x) = (shiftBiv x y Q).eval (p(X + x) - y)`. -/
theorem eval_comp_shift (x y : K) (Q : (K[X])[X]) (p : K[X]) :
    (Q.eval p).comp (X + C x) = (shiftBiv x y Q).eval (p.comp (X + C x) - C y) := by
  rw [shiftBiv, eval_comp]
  have hev : (X + C (C y)).eval (p.comp (X + C x) - C y) = p.comp (X + C x) := by
    simp [sub_add_cancel]
  rw [hev, ← shiftXHom_apply x (Q.eval p), ← shiftXHom_apply x p]
  exact (eval_map_apply (shiftXHom x) p).symm

/-- **Multiplicity divisibility.** If `Q` vanishes to multiplicity at least `r`
at `(x, y)` and `p.eval x = y`, then `(X - C x) ^ r ∣ Q.eval p`. -/
theorem dvd_eval_of_vanishesMult {r : ℕ} {x y : K} {Q : (K[X])[X]} {p : K[X]}
    (hvan : VanishesMult r x y Q) (hp : p.eval x = y) :
    (X - C x) ^ r ∣ Q.eval p := by
  let q : K[X] := p.comp (X + C x) - C y
  have hq0 : q.eval 0 = 0 := by
    simp [q, eval_comp, hp]
  have hXdvd : X ∣ q := by
    have h := Polynomial.dvd_iff_isRoot.mpr hq0
    simpa [sub_zero] using h
  obtain ⟨h, hq_eq⟩ := hXdvd
  have hXrdvd : X ^ r ∣ (Q.eval p).comp (X + C x) := by
    rw [eval_comp_shift x y Q p]
    change X ^ r ∣ (shiftBiv x y Q).eval q
    rw [eval_eq_sum]
    refine Finset.dvd_sum fun b _ => ?_
    dsimp only
    rw [hq_eq, mul_pow, ← mul_assoc]
    have hc_dvd : X ^ r ∣ (shiftBiv x y Q).coeff b * X ^ b := by
      rw [as_sum_range' ((shiftBiv x y Q).coeff b) (((shiftBiv x y Q).coeff b).natDegree + 1)
        (Nat.lt_succ_self _), Finset.sum_mul]
      refine Finset.dvd_sum fun a _ => ?_
      by_cases hab : a + b < r
      · rw [hvan a b hab, monomial_zero_right, zero_mul]
        exact dvd_zero _
      · have hge : r ≤ a + b := Nat.le_of_not_lt hab
        rw [← C_mul_X_pow_eq_monomial, mul_assoc, ← pow_add]
        exact dvd_mul_of_dvd_right (pow_dvd_pow X hge) _
    exact dvd_mul_of_dvd_left hc_dvd _
  obtain ⟨g, hg⟩ := hXrdvd
  refine ⟨g.comp (X - C x), ?_⟩
  have hcomp := congrArg (fun f : K[X] => f.comp (X - C x)) hg
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp,
    sub_add_cancel, Polynomial.comp_X] at hcomp
  exact hcomp

/-! ## Guruswami–Sudan root theorem -/

/-- **Guruswami–Sudan root theorem.** If `Q` has `(1, d - 1)`-weighted degree at
most `D_X < r * A` and vanishes to multiplicity at least `r` at `(x, w x)` for
every `x ∈ D`, then every polynomial `p` of degree below `d` agreeing with `w`
on at least `A` points of `D` satisfies `Q.eval p = 0`. -/
theorem eval_eq_zero_of_agree_ge [DecidableEq K] {D : Finset K} {d r A D_X : ℕ}
    {w : K → K} {Q : (K[X])[X]} {p : K[X]}
    (hdegQ : HasWeightedDegLE (d - 1) D_X Q)
    (hvan : ∀ x ∈ D, VanishesMult r x (w x) Q)
    (hp : p.degree < d)
    (hagree : A ≤ (D.filter fun x => w x = p.eval x).card)
    (hDX : D_X < r * A) :
    Q.eval p = 0 := by
  let S : Finset K := D.filter fun x => w x = p.eval x
  have hprod_dvd : (∏ x ∈ S, (X - C x) ^ r) ∣ Q.eval p := by
    refine Finset.prod_dvd_of_coprime ?_ fun x hx => ?_
    · intro x hx y hy hxy
      exact (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy))).pow
    · have hxD : x ∈ D := (mem_filter.mp hx).1
      have hx_eq : p.eval x = w x := ((mem_filter.mp hx).2).symm
      exact dvd_eval_of_vanishesMult (hvan x hxD) hx_eq
  have hmonic : (∏ x ∈ S, (X - C x) ^ r).Monic :=
    monic_prod_of_monic _ _ fun x _ => (monic_X_sub_C x).pow r
  have hprod_deg : (∏ x ∈ S, (X - C x) ^ r).natDegree = S.card * r := by
    rw [natDegree_prod_of_monic _ _ fun x _ => (monic_X_sub_C x).pow r]
    simp [natDegree_pow]
  by_contra hne
  have hle1 : (∏ x ∈ S, (X - C x) ^ r).natDegree ≤ (Q.eval p).natDegree :=
    natDegree_le_of_dvd hprod_dvd hne
  have hle2 : (Q.eval p).natDegree ≤ D_X := by
    have h := eval_degree_le_of_hasWeightedDegLE hdegQ hp
    rw [degree_eq_natDegree hne] at h
    exact WithBot.coe_le_coe.mp h
  have hge : r * A ≤ S.card * r := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right r hagree
  omega

/-- Corollary: `Y - p` divides `Q` in `(K[X])[Y]` for every polynomial `p`
agreeing with `w` on at least `A` points of `D`. -/
theorem X_sub_C_dvd_of_agree_ge [DecidableEq K] {D : Finset K} {d r A D_X : ℕ}
    {w : K → K} {Q : (K[X])[X]} {p : K[X]}
    (hdegQ : HasWeightedDegLE (d - 1) D_X Q)
    (hvan : ∀ x ∈ D, VanishesMult r x (w x) Q)
    (hp : p.degree < d)
    (hagree : A ≤ (D.filter fun x => w x = p.eval x).card)
    (hDX : D_X < r * A) :
    X - C p ∣ Q :=
  Polynomial.dvd_iff_isRoot.mpr (eval_eq_zero_of_agree_ge hdegQ hvan hp hagree hDX)

/-! ## Dimension counting and existence of the interpolation polynomial -/

/-- Index set of bivariate monomials `(i, j)` with `i + k * j ≤ D_X` and `j ≤ L_Y`. -/
def monomialPairs (k D_X L_Y : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D_X + 1) ×ˢ Finset.range (L_Y + 1)).filter fun p => p.1 + k * p.2 ≤ D_X

/-- Index set of Hasse derivative orders `(a, b)` with `a + b < r`. -/
def multPairs (r : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range r ×ˢ Finset.range r).filter fun p => p.1 + p.2 < r

/-- Exact triangular count: `2 * (multPairs r).card = r * (r + 1)`. -/
theorem two_mul_card_multPairs (r : ℕ) :
    2 * (multPairs r).card = r * (r + 1) := by
  have hsum : (multPairs r).card = ∑ b ∈ Finset.range r, (r - b) := by
    rw [multPairs, card_filter, sum_product_right]
    refine sum_congr rfl fun b hb => ?_
    have hbr : b < r := mem_range.mp hb
    rw [← card_filter]
    have hset : (Finset.range r).filter (fun a => a + b < r) = Finset.range (r - b) := by
      ext a
      simp only [mem_filter, mem_range]
      omega
    rw [hset, card_range]
  rw [hsum]
  clear hsum
  induction r with
  | zero => simp
  | succ n ih =>
    have hstep : ∑ b ∈ Finset.range (n + 1), (n + 1 - b) =
        (n + 1) + ∑ b ∈ Finset.range n, (n - b) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ]
      omega
    rw [hstep, Nat.mul_add, ih]
    ring

/-- Arithmetic-progression sum identity in `ℕ`:
`2 * ∑ j ∈ range (L + 1), (M - k * j) = (L + 1) * (2 * M - k * L)` when `k * L ≤ M`. -/
private theorem two_mul_sum_sub_mul (M k : ℕ) :
    ∀ L : ℕ, k * L ≤ M →
      2 * (∑ j ∈ Finset.range (L + 1), (M - k * j)) = (L + 1) * (2 * M - k * L) := by
  intro L
  induction L with
  | zero =>
    intro _
    simp
  | succ L ih =>
    intro hle
    have hle' : k * L ≤ M := le_trans (Nat.mul_le_mul_left k (Nat.le_succ L)) hle
    rw [Finset.sum_range_succ, Nat.mul_add, ih hle']
    have h1 : k * (L + 1) ≤ M := hle
    have h2 : k * L ≤ 2 * M := by omega
    have h3 : k * (L + 1) ≤ 2 * M := by omega
    zify [h1, h2, h3]
    ring

/-- Exact sum formula for `(monomialPairs k D_X L_Y).card` when `k * L_Y ≤ D_X`. -/
theorem card_monomialPairs_eq {k D_X L_Y : ℕ} (hL : k * L_Y ≤ D_X) :
    (monomialPairs k D_X L_Y).card = ∑ j ∈ Finset.range (L_Y + 1), (D_X + 1 - k * j) := by
  rw [monomialPairs, card_filter, sum_product_right]
  refine sum_congr rfl fun j hj => ?_
  have hjle : j ≤ L_Y := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hkj : k * j ≤ D_X := le_trans (Nat.mul_le_mul_left k hjle) hL
  rw [← card_filter]
  have hset : (Finset.range (D_X + 1)).filter (fun i => i + k * j ≤ D_X) =
      Finset.range (D_X + 1 - k * j) := by
    ext i
    simp only [mem_filter, mem_range]
    omega
  rw [hset, card_range]

/-- Strict quadratic lower bound on monomial count for `k ≥ 1`:
`(D_X + 1) ^ 2 < 2 * k * (monomialPairs k D_X (D_X / k)).card`. -/
theorem sq_lt_two_mul_card_monomialPairs {k : ℕ} (hk : 1 ≤ k) (D_X : ℕ) :
    (D_X + 1) ^ 2 < 2 * k * (monomialPairs k D_X (D_X / k)).card := by
  let L : ℕ := D_X / k
  let rem : ℕ := D_X % k
  have hdiv : k * L + rem = D_X := Nat.div_add_mod D_X k
  have hrem : rem < k := Nat.mod_lt D_X (by omega)
  have hLle : k * L ≤ D_X := by omega
  have hcard := card_monomialPairs_eq hLle
  have hsum := two_mul_sum_sub_mul (D_X + 1) k L (by omega)
  have h2k : 2 * k * (monomialPairs k D_X L).card = k * ((L + 1) * (2 * (D_X + 1) - k * L)) := by
    rw [hcard]
    have : 2 * k * ∑ j ∈ Finset.range (L + 1), (D_X + 1 - k * j) =
        k * (2 * ∑ j ∈ Finset.range (L + 1), (D_X + 1 - k * j)) := by ring
    rw [this, hsum]
  rw [h2k]
  have hsub : k * L ≤ 2 * (D_X + 1) := by omega
  zify [hsub]
  have hdivZ : (k : ℤ) * (L : ℤ) + (rem : ℤ) = (D_X : ℤ) := by exact_mod_cast hdiv
  have hremZ : (rem : ℤ) + 1 ≤ (k : ℤ) := by exact_mod_cast hrem
  have hdiff : (k : ℤ) * (((L : ℤ) + 1) * (2 * ((D_X : ℤ) + 1) - (k : ℤ) * (L : ℤ))) -
      ((D_X : ℤ) + 1) ^ 2 =
      (k : ℤ) ^ 2 * (L : ℤ) + ((rem : ℤ) + 1) * (2 * (k : ℤ) - ((rem : ℤ) + 1)) := by
    rw [← hdivZ]
    ring
  have hpos : (0 : ℤ) < (k : ℤ) ^ 2 * (L : ℤ) +
      ((rem : ℤ) + 1) * (2 * (k : ℤ) - ((rem : ℤ) + 1)) := by
    have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have hLZ : (0 : ℤ) ≤ (L : ℤ) := Int.natCast_nonneg L
    have hrem0 : (0 : ℤ) ≤ (rem : ℤ) := Int.natCast_nonneg rem
    nlinarith
  linarith

private theorem smul_biv (a : K) (Q : (K[X])[X]) : a • Q = C (C a) * Q := by
  ext j i
  simp [Polynomial.coeff_smul]

/-- Build a bivariate polynomial from a coefficient assignment on `monomialPairs k D_X L_Y`. -/
noncomputable def toBiv (k D_X L_Y : ℕ) :
    (monomialPairs k D_X L_Y → K) →ₗ[K] (K[X])[X] where
  toFun c := ∑ p ∈ (monomialPairs k D_X L_Y).attach,
    C (monomial p.1.1 (c p)) * X ^ p.1.2
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have hterm : ∀ p : monomialPairs k D_X L_Y,
        C (monomial p.1.1 (a * c p)) * X ^ p.1.2 =
        C (C a) * (C (monomial p.1.1 (c p)) * X ^ p.1.2) := by
      intro p
      rw [← mul_assoc, ← Polynomial.C_mul, C_mul_monomial]
    simp_rw [hterm, ← Finset.mul_sum, smul_biv]

/-- Coefficient extraction for `toBiv`: at `(i, j)` the coefficient is `c ⟨(i, j), h⟩`
if `(i, j) ∈ monomialPairs k D_X L_Y` and `0` otherwise. -/
theorem coeff_toBiv (k D_X L_Y : ℕ) (c : monomialPairs k D_X L_Y → K) (i j : ℕ) :
    ((toBiv k D_X L_Y c).coeff j).coeff i =
      if h : (i, j) ∈ monomialPairs k D_X L_Y then c ⟨(i, j), h⟩ else 0 := by
  simp only [toBiv, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases h : (i, j) ∈ monomialPairs k D_X L_Y
  · rw [dite_eq_left h]
    have hterm : ∀ p ∈ (monomialPairs k D_X L_Y).attach,
        (if j = p.1.2 then monomial p.1.1 (c p) else 0).coeff i =
        if p = ⟨(i, j), h⟩ then c p else 0 := by
      intro p _
      split_ifs with h1 h2 h2
      · subst h2; simp
      · rw [coeff_monomial]
        split_ifs with h3
        · exfalso; apply h2; ext <;> simp [h3, h1]
        · rfl
      · subst h2; exact absurd rfl h1
      · simp
    rw [sum_congr rfl hterm, Finset.sum_ite_eq']
    simp
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun p _ => ?_
    split_ifs with h1
    · rw [coeff_monomial]
      split_ifs with h2
      · exfalso; apply h; rw [← h2, h1]; exact p.2
      · rfl
    · simp

theorem toBiv_injective (k D_X L_Y : ℕ) :
    Function.Injective (toBiv (K := K) k D_X L_Y) := by
  intro c₁ c₂ h
  funext ⟨⟨i, j⟩, hp⟩
  have hc := congrArg (fun Q : (K[X])[X] => (Q.coeff j).coeff i) h
  simpa [coeff_toBiv, hp] using hc

theorem toBiv_hasWeightedDegLE (k D_X L_Y : ℕ) (c : monomialPairs k D_X L_Y → K) :
    HasWeightedDegLE k D_X (toBiv k D_X L_Y c) := by
  intro j i hgt
  rw [coeff_toBiv, dite_eq_right]
  intro hmem
  simp only [monomialPairs, mem_filter] at hmem
  omega

/-- Linear map evaluating all `(a, b)`-Hasse derivatives (`a + b < r`) of
`toBiv k D_X L_Y c` at every point `(x, w x)` for `x ∈ D`. -/
noncomputable def evalHasse [DecidableEq K] (D : Finset K) (w : K → K) (k D_X L_Y r : ℕ) :
    (monomialPairs k D_X L_Y → K) →ₗ[K] (D ×ˢ multPairs r → K) where
  toFun c q := ((shiftBiv q.1.1 (w q.1.1) (toBiv k D_X L_Y c)).coeff q.1.2.2).coeff q.1.2.1
  map_add' c₁ c₂ := by
    funext q
    simp [map_add, shiftBiv_add]
  map_smul' a c := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, LinearMap.map_smul]
    rw [smul_biv, shiftBiv_C_C_mul, coeff_C_mul, coeff_C_mul]

/-- Any linear map from a higher-dimensional finite function space to a
lower-dimensional one has a nonzero vector in its kernel. -/
private theorem exists_ne_zero_mem_ker_of_card_lt {α β : Type*} [Fintype α] [Fintype β]
    (f : (α → K) →ₗ[K] (β → K)) (hcard : Fintype.card β < Fintype.card α) :
    ∃ v : α → K, v ≠ 0 ∧ f v = 0 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hdom : Module.finrank K (α → K) = Fintype.card α :=
    Module.finrank_fintype_fun_eq_card K
  have hcod : Module.finrank K (β → K) = Fintype.card β :=
    Module.finrank_fintype_fun_eq_card K
  have hrle : Module.finrank K f.range ≤ Module.finrank K (β → K) :=
    Submodule.finrank_le f.range
  have hker_pos : 0 < Module.finrank K f.ker := by omega
  have hker_ne : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    exact lt_irrefl 0 hker_pos
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  exact ⟨v, hv_ne, LinearMap.mem_ker.mp hv_mem⟩

/-- **Guruswami–Sudan interpolation existence up to the Johnson radius.**

Whenever `0 < D.card`, `1 ≤ d`, and `D.card * (d - 1) < A ^ 2`, there exist a
multiplicity `r ≥ 1`, a weighted degree bound `D_X < r * A`, and a nonzero
bivariate polynomial `Q : (K[X])[X]` of `(1, d - 1)`-weighted degree at most
`D_X` vanishing to multiplicity at least `r` at `(x, w x)` for every `x ∈ D`. -/
theorem exists_gs_poly [DecidableEq K] (D : Finset K) (d A : ℕ) (w : K → K)
    (hD : 0 < D.card) (hJ : D.card * (d - 1) < A ^ 2) :
    ∃ (r D_X : ℕ) (Q : (K[X])[X]),
      1 ≤ r ∧ D_X < r * A ∧ Q ≠ 0 ∧
      HasWeightedDegLE (d - 1) D_X Q ∧
      ∀ x ∈ D, VanishesMult r x (w x) Q := by
  rcases Nat.eq_zero_or_pos (d - 1) with hk0 | hkpos
  · -- Degenerate constant-polynomial case `d = 1` (`d - 1 = 0`).
    have hApos : 1 ≤ A := by
      by_contra h0
      have hA0 : A = 0 := by omega
      simp [hA0] at hJ
    let r : ℕ := 1
    let D_X : ℕ := A - 1
    let L_Y : ℕ := D.card
    have hlt : Fintype.card (D ×ˢ multPairs r) < Fintype.card (monomialPairs (d - 1) D_X L_Y) := by
      simp only [Fintype.card_coe, card_product]
      have hmp : (multPairs 1).card = 1 := by
        have h := two_mul_card_multPairs 1
        omega
      have hmon : (monomialPairs (d - 1) D_X L_Y).card = (D_X + 1) * (L_Y + 1) := by
        rw [hk0, monomialPairs]
        have htriv : (Finset.range (D_X + 1) ×ˢ Finset.range (L_Y + 1)).filter
            (fun p => p.1 + 0 * p.2 ≤ D_X) = Finset.range (D_X + 1) ×ˢ Finset.range (L_Y + 1) := by
          ext ⟨i, j⟩
          simp only [mem_filter, mem_product, mem_range, zero_mul, add_zero, and_iff_left_iff_imp]
          omega
        rw [htriv, card_product, card_range, card_range]
      rw [hmp, hmon]
      have hDX1 : D_X + 1 = A := by omega
      rw [hDX1]
      nlinarith
    obtain ⟨c, hc_ne, hc_ker⟩ :=
      exists_ne_zero_mem_ker_of_card_lt (evalHasse D w (d - 1) D_X L_Y r) hlt
    refine ⟨r, D_X, toBiv (d - 1) D_X L_Y c, le_rfl, by omega, ?_,
      toBiv_hasWeightedDegLE _ _ _ c, ?_⟩
    · intro h0
      exact hc_ne (toBiv_injective (d - 1) D_X L_Y (h0.trans (map_zero _).symm))
    · intro x hx a b hab
      have hmem : (x, (a, b)) ∈ D ×ˢ multPairs r := by
        refine mem_product.mpr ⟨hx, mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hab⟩⟩
        · exact mem_range.mpr (show a < r by omega)
        · exact mem_range.mpr (show b < r by omega)
      exact congrFun hc_ker ⟨(x, (a, b)), hmem⟩
  · -- General case `k = d - 1 ≥ 1`: pick `r = (d - 1) * D.card`, `D_X = r * A - 1`.
    let k : ℕ := d - 1
    let r : ℕ := k * D.card
    have hrpos : 1 ≤ r := Nat.mul_pos hkpos hD
    have hApos : 1 ≤ A := by
      by_contra h0
      have hA0 : A = 0 := by omega
      simp [hA0] at hJ
    have hrApos : 1 ≤ r * A := Nat.mul_pos hrpos hApos
    let D_X : ℕ := r * A - 1
    let L_Y : ℕ := D_X / k
    have hDX_succ : D_X + 1 = r * A := Nat.sub_add_cancel hrApos
    have hlt : Fintype.card (D ×ˢ multPairs r) < Fintype.card (monomialPairs k D_X L_Y) := by
      simp only [Fintype.card_coe, card_product]
      have hmon := sq_lt_two_mul_card_monomialPairs hkpos D_X
      rw [hDX_succ] at hmon
      have hmul := two_mul_card_multPairs r
      have h2k_rhs : 2 * k * (D.card * (multPairs r).card) = k * D.card * (r * (r + 1)) := by
        calc 2 * k * (D.card * (multPairs r).card)
            = k * D.card * (2 * (multPairs r).card) := by ring
          _ = k * D.card * (r * (r + 1)) := by rw [hmul]
      have hgap : k * D.card * (r + 1) ≤ r * A ^ 2 := by
        have hJ' : k * D.card + 1 ≤ A ^ 2 := by
          have : k * D.card < A ^ 2 := by rw [Nat.mul_comm]; exact hJ
          omega
        calc k * D.card * (r + 1)
            = r * (k * D.card + 1) := rfl
          _ ≤ r * A ^ 2 := Nat.mul_le_mul_left r hJ'
      have h2k_lt : 2 * k * (D.card * (multPairs r).card) <
          2 * k * (monomialPairs k D_X L_Y).card := by
        rw [h2k_rhs]
        calc k * D.card * (r * (r + 1))
            = r * (k * D.card * (r + 1)) := by ring
          _ ≤ r * (r * A ^ 2) := Nat.mul_le_mul_left r hgap
          _ = (r * A) ^ 2 := by ring
          _ < 2 * k * (monomialPairs k D_X L_Y).card := hmon
      exact Nat.lt_of_mul_lt_mul_left h2k_lt
    obtain ⟨c, hc_ne, hc_ker⟩ :=
      exists_ne_zero_mem_ker_of_card_lt (evalHasse D w k D_X L_Y r) hlt
    refine ⟨r, D_X, toBiv k D_X L_Y c, hrpos, by omega, ?_,
      toBiv_hasWeightedDegLE k D_X L_Y c, ?_⟩
    · intro h0
      exact hc_ne (toBiv_injective k D_X L_Y (h0.trans (map_zero _).symm))
    · intro x hx a b hab
      have hmem : (x, (a, b)) ∈ D ×ˢ multPairs r := by
        refine mem_product.mpr ⟨hx, mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, hab⟩⟩
        · exact mem_range.mpr (show a < r by omega)
        · exact mem_range.mpr (show b < r by omega)
      exact congrFun hc_ker ⟨(x, (a, b)), hmem⟩

end WeightedDegree

/-! ## Parametric Guruswami–Sudan interpolation over `RatFunc F` -/

section ParametricCurve

variable {F : Type*} [Field F]

/-- **Parametric Guruswami–Sudan annihilator over `F(Z)` (`RatFunc F`).**

Given words `u : Fin m → F → F` on `D` with `0 < D.card`, `1 ≤ d`, and
`D.card * (d - 1) < A ^ 2`, there exist `r ≥ 1`, `D_X < r * A`, and a nonzero
bivariate polynomial `Q_Z : ((RatFunc F)[X])[X]` of `(1, d - 1)`-weighted degree
at most `D_X` vanishing to multiplicity at least `r` at
`(RatFunc.C x, ∑ k, RatFunc.X ^ k * RatFunc.C (u k x))` for every `x ∈ D`. -/
theorem exists_gs_poly_curve (D : Finset F) (d A m : ℕ) (u : Fin m → F → F)
    (hD : 0 < D.card) (hJ : D.card * (d - 1) < A ^ 2) :
    ∃ (r D_X : ℕ) (Q : ((RatFunc F)[X])[X]),
      1 ≤ r ∧ D_X < r * A ∧ Q ≠ 0 ∧
      HasWeightedDegLE (d - 1) D_X Q ∧
      ∀ x ∈ D,
        VanishesMult r (RatFunc.C x)
          (∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k x)) Q := by
  classical
  let D' : Finset (RatFunc F) := D.image (RatFunc.C : F → RatFunc F)
  have hC_inj : Function.Injective (RatFunc.C : F → RatFunc F) :=
    (RatFunc.C : F →+* RatFunc F).injective
  have hcard : D'.card = D.card := card_image_of_injective D hC_inj
  let wZ : RatFunc F → RatFunc F := fun y =>
    if h : ∃ x ∈ D, RatFunc.C x = y then
      ∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k h.choose)
    else 0
  have hwZ : ∀ x ∈ D, wZ (RatFunc.C x) = ∑ k : Fin m, RatFunc.X ^ (k : ℕ) * RatFunc.C (u k x) := by
    intro x hx
    have hex : ∃ x' ∈ D, RatFunc.C x' = RatFunc.C x := ⟨x, hx, rfl⟩
    simp only [wZ, dite_eq_left hex]
    have hch : hex.choose = x := hC_inj hex.choose_spec.2
    rw [hch]
  obtain ⟨r, D_X, Q, hr, hDX, hQne, hQdeg, hQvan⟩ :=
    exists_gs_poly D' d A wZ (by omega) (by rwa [hcard])
  refine ⟨r, D_X, Q, hr, hDX, hQne, hQdeg, fun x hx => ?_⟩
  have hmem : RatFunc.C x ∈ D' := mem_image_of_mem _ hx
  have hv := hQvan (RatFunc.C x) hmem
  rwa [hwZ x hx] at hv

end ParametricCurve

end GuruswamiSudan

end CertiFri
