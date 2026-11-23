import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import CertiFriProofs.Theory.ProximityGap.Sylvester

/-!
# Finite-Order Hensel Lifting with Exact Coefficient Degree Bounds (`HenselLift`)

Implements cleared-denominator finite-order Hensel lifting in `(F[Z])[T] / (H)`
along a trivariate polynomial `R(Z, X, Y) = 0` at `X = 0`, using exact
pseudo-remainder reduction `pseudoRem` by `H(Z, T)` (avoiding monicization
blow-up and keeping the `Z`-degree growth strictly linear in the lifting order
`i`):

* `pseudoRem H k f`: `k`-step pseudo-remainder of `f` by `H`, satisfying
  `H ∣ C (H.leadingCoeff ^ k) * f - pseudoRem H k f`, strict degree reduction
  `(pseudoRem H k f).natDegree < H.natDegree`, exact evaluation
  `(pseudoRem H k f).eval₂ ψ u = (ψ H.leadingCoeff) ^ k * f.eval₂ ψ u` when
  `H.eval₂ ψ u = 0`, and exact `Z`-degree growth `≤ B_f + k * B_H`.
* `henselCoeff`: cleared-denominator Hensel lift sequence `b : ℕ → (F[Z])[T]`
  for `R(Z, X, Y) = 0` with `b 0 = T` and unified denominator `D₀ = h_top ^ ((ℓ + 1) * t) * Δ₀`
  at exponent `henselExp i = if i = 0 then 0 else 2 * i - 1`.
* `henselCoeff_degT_le`, `henselCoeff_degT_lt`: `(b 0).natDegree ≤ t` and
  `(b i).natDegree < t` for all `i ≥ 1`.
* `henselCoeff_degZ_le`: linear `Z`-degree bound `≤ henselExp i * C` for all `i`,
  with `C = (2 * ℓ * t + 2 * t + 3 * ℓ + 1) * D_Z`.
* `henselCoeff_eval_eq`: for every specialization `β ∈ F` with `D₀(β) ≠ 0`,
  `H(β, u_β) = 0`, and every `p : F[X]` with `p.eval 0 = u_β` and
  `R(β, X, p(X)) = 0`, `eval₂ (eval β) u_β (b i) = (D₀.eval β) ^ (henselExp i) * p.coeff i`
  for every `i : ℕ`.
* `henselResidual`: cleared-denominator residual polynomial
  `F_res(Z, T, X) := D₀ ^ (2 * d * ℓ) * R(Z, X, P_{<d}(X))` (reduced mod `H` in `T`),
  with exact `Z`-degree bound and specialization identity.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace CertiFri

namespace HenselLift

open Polynomial Finset

/-! ## 1. Exact Pseudo-Remainder Reduction -/

section PseudoRem

variable {A : Type*} [CommRing A]

/-- `k`-step pseudo-remainder of `f : A[X]` by `H : A[X]`. Every step multiplies
by `H.leadingCoeff` (and subtracts a multiple of `H` when `H.natDegree ≤ f.natDegree`),
so the cumulative multiplier is always exactly `H.leadingCoeff ^ k`. -/
noncomputable def pseudoRem (H : A[X]) : ℕ → A[X] → A[X]
  | 0, f => f
  | k + 1, f =>
      let f' :=
        if H.natDegree ≤ f.natDegree then
          C H.leadingCoeff * f - C (f.coeff f.natDegree) * X ^ (f.natDegree - H.natDegree) * H
        else
          C H.leadingCoeff * f
      pseudoRem H k f'

/-- Exact divisibility invariant of `pseudoRem`:
`H ∣ C (H.leadingCoeff ^ k) * f - pseudoRem H k f`. -/
theorem pseudoRem_sub_dvd (H : A[X]) :
    ∀ (k : ℕ) (f : A[X]), H ∣ C (H.leadingCoeff ^ k) * f - pseudoRem H k f
  | 0, f => by simp [pseudoRem]
  | k + 1, f => by
      dsimp only [pseudoRem]
      set f' :=
        if H.natDegree ≤ f.natDegree then
          C H.leadingCoeff * f - C (f.coeff f.natDegree) * X ^ (f.natDegree - H.natDegree) * H
        else
          C H.leadingCoeff * f
      have ih := pseudoRem_sub_dvd H k f'
      have hstep : H ∣ C H.leadingCoeff * f - f' := by
        dsimp only [f']
        split_ifs
        · refine ⟨C (f.coeff f.natDegree) * X ^ (f.natDegree - H.natDegree), ?_⟩
          ring
        · simp
      have hmul : H ∣ C (H.leadingCoeff ^ k) * (C H.leadingCoeff * f - f') :=
        dvd_mul_of_dvd_right hstep _
      have hsum : H ∣ C (H.leadingCoeff ^ k) * (C H.leadingCoeff * f - f') +
          (C (H.leadingCoeff ^ k) * f' - pseudoRem H k f') :=
        dvd_add hmul ih
      have hid : C (H.leadingCoeff ^ k) * (C H.leadingCoeff * f - f') +
          (C (H.leadingCoeff ^ k) * f' - pseudoRem H k f') =
          C (H.leadingCoeff ^ (k + 1)) * f - pseudoRem H k f' := by
        rw [pow_succ, map_mul]
        ring
      rwa [hid] at hsum

/-- Single reduction step strictly lowers `natDegree` whenever `1 ≤ H.natDegree ≤ f.natDegree`. -/
private theorem natDegree_pseudoStep_lt {H f : A[X]} (hH : 1 ≤ H.natDegree)
    (hle : H.natDegree ≤ f.natDegree) :
    (C H.leadingCoeff * f - C (f.coeff f.natDegree) * X ^ (f.natDegree - H.natDegree) * H).natDegree <
      f.natDegree := by
  set m := f.natDegree
  set t := H.natDegree
  set g := C H.leadingCoeff * f - C (f.coeff m) * X ^ (m - t) * H
  have hm_pos : 0 < m := lt_of_lt_of_le (by omega) hle
  by_cases hg0 : g = 0
  · rw [hg0, natDegree_zero]; exact hm_pos
  · have hdeg : g.natDegree ≤ m - 1 := by
      refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun r hr => ?_
      have hrm : m ≤ r := by omega
      dsimp only [g]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      by_cases heq : r = m
      · subst heq
        have hsub : m - t ≤ m := Nat.sub_le m t
        rw [ite_eq_left hsub]
        have hmt : m - (m - t) = t := Nat.sub_sub_self hle
        rw [hmt]
        show H.leadingCoeff * f.coeff m - f.coeff m * H.leadingCoeff = 0
        ring
      · have hgt : m < r := by omega
        have hf0 : f.coeff r = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hgt
        have hsub : m - t ≤ r := by omega
        rw [ite_eq_left hsub]
        have hHgt : t < r - (m - t) := by omega
        have hH0 : H.coeff (r - (m - t)) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hHgt
        rw [hf0, hH0, mul_zero, mul_zero, sub_self]
    omega

/-- Degree reduction of `pseudoRem`: if `1 ≤ H.natDegree` and `f.natDegree < H.natDegree + k`,
then `(pseudoRem H k f).natDegree < H.natDegree`. -/
theorem pseudoRem_natDegree_lt {H : A[X]} (hH : 1 ≤ H.natDegree) :
    ∀ (k : ℕ) (f : A[X]), f.natDegree < H.natDegree + k →
      (pseudoRem H k f).natDegree < H.natDegree
  | 0, f, hlt => by simpa [pseudoRem] using hlt
  | k + 1, f, hlt => by
      dsimp only [pseudoRem]
      refine pseudoRem_natDegree_lt hH k _ ?_
      split_ifs with hle
      · have hstep := natDegree_pseudoStep_lt hH hle
        omega
      · have h1 : (C H.leadingCoeff * f).natDegree ≤ f.natDegree :=
          Polynomial.natDegree_C_mul_le _ _
        omega

/-- Evaluation of `pseudoRem` under any homomorphism killing `H`:
`(pseudoRem H k f).eval₂ ψ u = (ψ H.leadingCoeff) ^ k * f.eval₂ ψ u`. -/
theorem pseudoRem_eval₂ {F : Type*} [CommRing F] (ψ : A →+* F) (u : F)
    {H : A[X]} (hH : H.eval₂ ψ u = 0) (k : ℕ) (f : A[X]) :
    (pseudoRem H k f).eval₂ ψ u = (ψ H.leadingCoeff) ^ k * f.eval₂ ψ u := by
  obtain ⟨q, hq⟩ := pseudoRem_sub_dvd H k f
  have hev := congrArg (Polynomial.eval₂ ψ u) hq
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, map_pow,
    Polynomial.eval₂_mul, hH, zero_mul] at hev
  exact (sub_eq_zero.mp hev).symm

end PseudoRem

section PseudoRemDeg

variable {F : Type*} [CommRing F]

/-- Uniform coefficient-degree bound for a polynomial `p : (F[Z])[T]`:
every `T`-coefficient of `p` has `Z`-degree at most `B`. -/
def CoeffDegLE (B : ℕ) (p : (F[X])[X]) : Prop :=
  ∀ j, (p.coeff j).natDegree ≤ B

theorem coeffDegLE_mono {B₁ B₂ : ℕ} (h : B₁ ≤ B₂) {p : (F[X])[X]} (hp : CoeffDegLE B₁ p) :
    CoeffDegLE B₂ p := fun j => (hp j).trans h

theorem coeffDegLE_zero (B : ℕ) : CoeffDegLE (F := F) B 0 := fun j => by simp

theorem coeffDegLE_X (B : ℕ) : CoeffDegLE (F := F) B X := fun j => by
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem coeffDegLE_C {a : F[X]} {B : ℕ} (ha : a.natDegree ≤ B) : CoeffDegLE B (C a) := fun j => by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem coeffDegLE_add {B : ℕ} {p q : (F[X])[X]} (hp : CoeffDegLE B p) (hq : CoeffDegLE B q) :
    CoeffDegLE B (p + q) := fun j => by
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hp j) (hq j))

theorem coeffDegLE_sub {B : ℕ} {p q : (F[X])[X]} (hp : CoeffDegLE B p) (hq : CoeffDegLE B q) :
    CoeffDegLE B (p - q) := fun j => by
  rw [Polynomial.coeff_sub]
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (hp j) (hq j))

theorem coeffDegLE_neg {B : ℕ} {p : (F[X])[X]} (hp : CoeffDegLE B p) :
    CoeffDegLE B (-p) := fun j => by
  rw [Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hp j

theorem coeffDegLE_sum {ι : Type*} (s : Finset ι) {B : ℕ} (f : ι → (F[X])[X])
    (hf : ∀ i ∈ s, CoeffDegLE B (f i)) :
    CoeffDegLE B (∑ i ∈ s, f i) := fun j => by
  rw [Polynomial.finsetSum_coeff]
  exact Polynomial.natDegree_sum_le_of_forall_le s _ fun i hi => hf i hi j

theorem coeffDegLE_C_mul {B_a B_p : ℕ} {a : F[X]} {p : (F[X])[X]}
    (ha : a.natDegree ≤ B_a) (hp : CoeffDegLE B_p p) :
    CoeffDegLE (B_a + B_p) (C a * p) := fun j => by
  rw [Polynomial.coeff_C_mul]
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add ha (hp j))

theorem coeffDegLE_mul {B_p B_q : ℕ} {p q : (F[X])[X]}
    (hp : CoeffDegLE B_p p) (hq : CoeffDegLE B_q q) :
    CoeffDegLE (B_p + B_q) (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp x.1) (hq x.2))

theorem coeffDegLE_pow {B : ℕ} {p : (F[X])[X]} (hp : CoeffDegLE B p) :
    ∀ n : ℕ, CoeffDegLE (n * B) (p ^ n)
  | 0 => by
      simpa using coeffDegLE_C (F := F) (a := 1) (B := 0) (by simp)
  | n + 1 => by
      rw [pow_succ, Nat.add_mul, one_mul]
      exact coeffDegLE_mul (coeffDegLE_pow hp n) hp

theorem coeffDegLE_X_pow_mul {B : ℕ} (n : ℕ) {p : (F[X])[X]} (hp : CoeffDegLE B p) :
    CoeffDegLE B (X ^ n * p) := fun j => by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs
  · exact hp _
  · simp

/-- Exact `Z`-degree growth under `pseudoRem H k f`:
if `CoeffDegLE B_H H` and `CoeffDegLE B_f f`, then `CoeffDegLE (B_f + k * B_H) (pseudoRem H k f)`. -/
theorem coeffDegLE_pseudoRem {B_H : ℕ} {H : (F[X])[X]} (hH : CoeffDegLE B_H H) :
    ∀ (k B_f : ℕ) (f : (F[X])[X]), CoeffDegLE B_f f →
      CoeffDegLE (B_f + k * B_H) (pseudoRem H k f)
  | 0, B_f, f, hf => by simpa [pseudoRem] using hf
  | k + 1, B_f, f, hf => by
      dsimp only [pseudoRem]
      have hstep : CoeffDegLE (B_f + B_H)
          (if H.natDegree ≤ f.natDegree then
            C H.leadingCoeff * f - C (f.coeff f.natDegree) * X ^ (f.natDegree - H.natDegree) * H
          else
            C H.leadingCoeff * f) := by
        have hlc : H.leadingCoeff.natDegree ≤ B_H := hH H.natDegree
        split_ifs
        · refine coeffDegLE_sub ?_ ?_
          · rw [Nat.add_comm B_f B_H]
            exact coeffDegLE_C_mul hlc hf
          · rw [mul_assoc]
            exact coeffDegLE_C_mul (hf f.natDegree) (coeffDegLE_X_pow_mul _ hH)
        · rw [Nat.add_comm B_f B_H]
          exact coeffDegLE_C_mul hlc hf
      have hrec := coeffDegLE_pseudoRem hH k (B_f + B_H) _ hstep
      have hring : B_f + B_H + k * B_H = B_f + (k + 1) * B_H := by ring
      rwa [hring] at hrec

end PseudoRemDeg

/-! ## 2. Exact Taylor Split of `R(Z, X, Y)` and Cleared-Denominator Hensel Recurrence -/

section HenselCore

variable {F : Type*} [Field F]

/-- Exponent of `D₀` in the denominator of the `i`-th Hensel coefficient:
`0` at `i = 0`, and `2 * i - 1` for `i ≥ 1`. -/
def henselExp (i : ℕ) : ℕ :=
  if i = 0 then 0 else 2 * i - 1

/-- Lift a polynomial `a : F[Z]` to a constant polynomial in `((F[Z])[T])[X]`
(constant in `T` and `X`). -/
noncomputable def liftZ (a : F[X]) : ((F[X])[X])[X] :=
  C (C a)

/-- Evaluate `R : ((F[Z])[X])[Y]` at `X = 0`, yielding `R₀ : (F[Z])[T]`. -/
noncomputable def evalX0 (R : ((F[X])[X])[X]) : (F[X])[X] :=
  R.map (Polynomial.evalRingHom 0)

/-- Lift `R : ((F[Z])[X])[Y]` into `(((F[Z])[T])[X])[Y]` by mapping coefficients
`F[Z] → (F[Z])[T]` via `C`, keeping `X` inner and `Y` outer. -/
noncomputable def liftRToT (R : ((F[X])[X])[X]) : (((F[X])[X])[X])[X] :=
  R.map (Polynomial.mapRingHom (C : F[X] →+* (F[X])[X]))

/-- Shift the inner `X` variable down by 1 (extracting `R_hi` so
`R(Z, X, Y) = R₀(Z, Y) + X * R_hi(Z, X, Y)`). -/
noncomputable def divXInner (p : (F[X])[X]) : (F[X])[X] :=
  ∑ i ∈ Finset.range p.natDegree, monomial i (p.coeff (i + 1))

theorem eval0_add_X_mul_divXInner (p : (F[X])[X]) :
    C (p.eval 0) + X * divXInner p = p := by
  apply Polynomial.ext
  intro i
  cases i with
  | zero =>
    simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ i =>
    rw [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add, Polynomial.coeff_X_mul]
    unfold divXInner
    rw [Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    by_cases hi : i < p.natDegree
    · rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hne
        simp [hne]
      · intro hmem; exact absurd (Finset.mem_range.mpr hi) hmem
    · rw [Finset.sum_eq_zero]
      · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
      · intro b hb
        have hlt : b < p.natDegree := Finset.mem_range.mp hb
        have hne : b ≠ i := by omega
        simp [hne]

/-- `R_hi` satisfies `R(Z, X, Y) = C (R₀(Z, Y)) + X * R_hi(Z, X, Y)` in `((F[Z])[X])[Y]`. -/
noncomputable def RHi (R : ((F[X])[X])[X]) : ((F[X])[X])[X] :=
  ∑ j ∈ Finset.range (R.natDegree + 1), monomial j (divXInner (R.coeff j))

theorem R_eq_evalX0_add_X_mul_RHi (R : ((F[X])[X])[X]) :
    R = (evalX0 R).map C + (C X) * RHi R := by
  apply Polynomial.ext
  intro j
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_C_mul]
  unfold RHi evalX0
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_monomial]
  by_cases hj : j ≤ R.natDegree
  · have hmem : j ∈ Finset.range (R.natDegree + 1) := Finset.mem_range.mpr (by omega)
    rw [Finset.sum_eq_single j]
    · simp only [↓reduceIte, coe_evalRingHom]
      exact (congrArg (fun q : (F[X])[X] => q.coeff i)
        (eval0_add_X_mul_divXInner (R.coeff j))).symm
    · intro b _ hne
      simp [hne]
    · intro hnm; exact absurd hmem hnm
  · have hR0 : R.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [Finset.sum_eq_zero]
    · simp [hR0]
    · intro b hb
      have hlt : b < R.natDegree + 1 := Finset.mem_range.mp hb
      have hne : b ≠ j := by omega
      simp [hne]

/-- Second-order Taylor remainder of `f : A[Y]` around `y : A` with increment `δ : A`:
`f(y + δ) = f(y) + f'(y) * δ + δ ^ 2 * taylorTail2 f y δ`. -/
noncomputable def taylorTail2 {A : Type*} [CommRing A] (f : A[X]) (y δ : A) : A :=
  ∑ j ∈ Finset.range (f.natDegree + 1),
    f.coeff j * ∑ r ∈ Finset.Ico 2 (j + 1),
      ((Nat.choose j r : ℕ) : A) * y ^ (j - r) * δ ^ (r - 2)

theorem taylor2_identity {A : Type*} [CommRing A] (f : A[X]) (y δ : A) :
    f.eval (y + δ) = f.eval y + f.derivative.eval y * δ + δ ^ 2 * taylorTail2 f y δ := by
  have hterm : ∀ j : ℕ, (y + δ) ^ j =
      y ^ j + (j : A) * y ^ (j - 1) * δ +
        δ ^ 2 * ∑ r ∈ Finset.Ico 2 (j + 1), ((Nat.choose j r : ℕ) : A) * y ^ (j - r) * δ ^ (r - 2) := by
    intro j
    rw [add_comm y δ, add_pow]
    cases j with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp [Finset.sum_range_succ]
      | succ k =>
        have hsplit : Finset.range (k + 3) = {0, 1} ∪ Finset.Ico 2 (k + 3) := by
          ext r; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_Ico]; omega
        have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Ico 2 (k + 3)) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          simp only [Finset.mem_insert, Finset.mem_singleton] at hr1
          simp only [Finset.mem_Ico] at hr2
          omega
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
        have h0 : δ ^ 0 * y ^ (k + 1 + 1 - 0) * ((Nat.choose (k + 1 + 1) 0 : ℕ) : A) = y ^ (k + 1 + 1) := by
          simp
        have h1 : δ ^ 1 * y ^ (k + 1 + 1 - 1) * ((Nat.choose (k + 1 + 1) 1 : ℕ) : A) =
            ((k + 1 + 1 : ℕ) : A) * y ^ (k + 1 + 1 - 1) * δ := by
          simp [Nat.choose_one_right]; ring
        have h2 : ∑ r ∈ Finset.Ico 2 (k + 3),
            δ ^ r * y ^ (k + 1 + 1 - r) * ((Nat.choose (k + 1 + 1) r : ℕ) : A) =
            δ ^ 2 * ∑ r ∈ Finset.Ico 2 (k + 3),
              ((Nat.choose (k + 1 + 1) r : ℕ) : A) * y ^ (k + 1 + 1 - r) * δ ^ (r - 2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r hr => ?_
          have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
          have hpow : δ ^ r = δ ^ 2 * δ ^ (r - 2) := by
            rw [← pow_add, Nat.add_sub_cancel' hr2]
          rw [hpow]; ring
        rw [h0, h1, h2]
  have hf_eval : ∀ x : A, f.eval x = ∑ j ∈ Finset.range (f.natDegree + 1), f.coeff j * x ^ j := by
    intro x
    rw [Polynomial.eval_eq_sum_range]
  have hf'_eval : f.derivative.eval y =
      ∑ j ∈ Finset.range (f.natDegree + 1), f.coeff j * ((j : A) * y ^ (j - 1)) := by
    rw [Polynomial.eval_eq_sum_range' (n := f.natDegree + 1)
      (lt_of_le_of_lt (Polynomial.natDegree_derivative_le f) (by omega))]
    cases hn : f.natDegree with
    | zero =>
      simp [Polynomial.coeff_derivative,
        Polynomial.coeff_eq_zero_of_natDegree_lt (show f.natDegree < 1 by omega)]
    | succ m =>
      rw [Finset.sum_range_succ' (fun j => f.coeff j * ((j : A) * y ^ (j - 1))) (m + 1)]
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      rw [Finset.sum_range_succ (fun k => f.derivative.coeff k * y ^ k) (m + 1)]
      have htop : f.derivative.coeff (m + 1) = 0 := by
        rw [Polynomial.coeff_derivative]
        have h0 : f.coeff (m + 2) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [h0, zero_mul]
      rw [htop, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Polynomial.coeff_derivative, Nat.add_sub_cancel]
      push_cast; ring
  rw [hf_eval (y + δ), hf_eval y, hf'_eval]
  unfold taylorTail2
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hterm j]; ring

/-- Scaled `X`-substitution `p(D₀^2 * X)` for `p : (F[Z])[X]`, lifted to `((F[Z])[T])[X]`. -/
noncomputable def scaleXToTX (D₀ : F[X]) (p : (F[X])[X]) : ((F[X])[X])[X] :=
  ∑ q ∈ Finset.range (p.natDegree + 1),
    monomial q (C (p.coeff q * D₀ ^ (2 * q)))

/-- **Raw step polynomial `B_i(X) ∈ ((F[Z])[T])[X]`** whose `X^i`-coefficient gives
the cleared-denominator Hensel correction at order `i ≥ 1` (using previous
coefficients `b 0, …, b (i - 1)`):
`B_i(X) = (X G(X))^2 * taylorTail2 R₀ b₀ (D₀ X G(X)) + X * R_hi(Z, D₀^2 X, b₀ + D₀ X G(X))`. -/
noncomputable def henselStepPoly (R : ((F[X])[X])[X]) (D₀ : F[X])
    (prev : ℕ → (F[X])[X]) (i : ℕ) : ((F[X])[X])[X] :=
  let G : ((F[X])[X])[X] := ∑ s ∈ Finset.Ico 1 i, monomial (s - 1) (prev s)
  let XG : ((F[X])[X])[X] := X * G
  let δ : ((F[X])[X])[X] := C (C D₀) * XG
  let R0T : (((F[X])[X])[X])[X] := (evalX0 R).map (C.comp C)
  let b0 : ((F[X])[X])[X] := C (prev 0)
  let term1 : ((F[X])[X])[X] := XG ^ 2 * taylorTail2 R0T b0 δ
  let yPoly : ((F[X])[X])[X] := b0 + δ
  let term2 : ((F[X])[X])[X] :=
    X * ∑ j ∈ Finset.range (R.natDegree + 1),
      scaleXToTX D₀ (divXInner (R.coeff j)) * yPoly ^ j
  term1 + term2

/-- Exact cleared-denominator Hensel lift sequence `henselCoeff R H W D₀ i : (F[Z])[T]`:
* `i = 0`: `T` (`Polynomial.X`),
* `i ≥ 1`: reduce `c_i = (henselStepPoly ...).coeff i` by `pseudoRem H (ℓ * t)`,
  multiply by `-W`, and reduce by `pseudoRem H t`. -/
noncomputable def henselCoeff (R : ((F[X])[X])[X]) (H W : (F[X])[X]) (D₀ : F[X]) :
    ℕ → (F[X])[X]
  | 0 => X
  | i + 1 =>
      let prev : ℕ → (F[X])[X] := fun s => if s ≤ i then henselCoeff R H W D₀ s else 0
      let c_i : (F[X])[X] := (henselStepPoly R D₀ prev (i + 1)).coeff (i + 1)
      let c_red : (F[X])[X] := pseudoRem H (R.natDegree * H.natDegree) c_i
      pseudoRem H H.natDegree (-W * c_red)
termination_by i => i

theorem henselCoeff_zero (R : ((F[X])[X])[X]) (H W : (F[X])[X]) (D₀ : F[X]) :
    henselCoeff R H W D₀ 0 = X := by
  rw [henselCoeff]

theorem henselCoeff_succ (R : ((F[X])[X])[X]) (H W : (F[X])[X]) (D₀ : F[X]) (i : ℕ) :
    henselCoeff R H W D₀ (i + 1) =
      pseudoRem H H.natDegree
        (-W * pseudoRem H (R.natDegree * H.natDegree)
          ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1))) := by
  rw [henselCoeff]
  apply congrArg (pseudoRem H H.natDegree)
  apply congrArg (-W * ·)
  apply congrArg (pseudoRem H (R.natDegree * H.natDegree))
  apply congrArg (fun P : ((F[X])[X])[X] => P.coeff (i + 1))
  unfold henselStepPoly
  have hG : (∑ s ∈ Finset.Ico 1 (i + 1),
      monomial (s - 1) (if s ≤ i then henselCoeff R H W D₀ s else 0)) =
      ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (henselCoeff R H W D₀ s) := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hle : s ≤ i := by have := (Finset.mem_Ico.mp hs).2; omega
    simp [hle]
  have h0 : (if 0 ≤ i then henselCoeff R H W D₀ 0 else 0) = henselCoeff R H W D₀ 0 := by
    simp
  simp only [hG, h0]

/-! ## 3. Exact `T`-Degree and `Z`-Degree Bounds for `henselCoeff` -/

/-- `T`-degree bound on any coefficient of a polynomial `P : ((F[Z])[T])[X]`. -/
def PolyTDegLE (M : ℕ) (P : ((F[X])[X])[X]) : Prop :=
  ∀ k, (P.coeff k).natDegree ≤ M

theorem polyTDegLE_mono {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) {P : ((F[X])[X])[X]} (hP : PolyTDegLE M₁ P) :
    PolyTDegLE M₂ P := fun k => (hP k).trans h

theorem polyTDegLE_zero (M : ℕ) : PolyTDegLE (F := F) M 0 := fun k => by simp

theorem polyTDegLE_C {a : (F[X])[X]} {M : ℕ} (ha : a.natDegree ≤ M) : PolyTDegLE M (C a) :=
  fun k => by rw [Polynomial.coeff_C]; split_ifs <;> simp [ha]

theorem polyTDegLE_monomial {a : (F[X])[X]} {M : ℕ} (n : ℕ) (ha : a.natDegree ≤ M) :
    PolyTDegLE M (monomial n a) := fun k => by
  rw [Polynomial.coeff_monomial]; split_ifs <;> simp [ha]

theorem polyTDegLE_add {M : ℕ} {P Q : ((F[X])[X])[X]}
    (hP : PolyTDegLE M P) (hQ : PolyTDegLE M Q) : PolyTDegLE M (P + Q) := fun k => by
  rw [Polynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP k) (hQ k))

theorem polyTDegLE_sum {ι : Type*} (s : Finset ι) {M : ℕ} (f : ι → ((F[X])[X])[X])
    (hf : ∀ i ∈ s, PolyTDegLE M (f i)) : PolyTDegLE M (∑ i ∈ s, f i) := fun k => by
  rw [Polynomial.finsetSum_coeff]
  exact Polynomial.natDegree_sum_le_of_forall_le s _ fun i hi => hf i hi k

theorem polyTDegLE_mul {M₁ M₂ : ℕ} {P Q : ((F[X])[X])[X]}
    (hP : PolyTDegLE M₁ P) (hQ : PolyTDegLE M₂ Q) : PolyTDegLE (M₁ + M₂) (P * Q) := fun k => by
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hP x.1) (hQ x.2))

theorem polyTDegLE_pow {M : ℕ} {P : ((F[X])[X])[X]} (hP : PolyTDegLE M P) :
    ∀ n : ℕ, PolyTDegLE (n * M) (P ^ n)
  | 0 => by simpa using polyTDegLE_C (F := F) (a := 1) (M := 0) (by simp)
  | n + 1 => by
      rw [pow_succ, Nat.add_mul, one_mul]
      exact polyTDegLE_mul (polyTDegLE_pow hP n) hP

theorem polyTDegLE_X_mul {M : ℕ} {P : ((F[X])[X])[X]} (hP : PolyTDegLE M P) :
    PolyTDegLE M (X * P) := fun k => by
  cases k with
  | zero => simp
  | succ k => rw [Polynomial.coeff_X_mul]; exact hP k

theorem polyTDegLE_scaleXToTX (D₀ : F[X]) (p : (F[X])[X]) :
    PolyTDegLE 0 (scaleXToTX D₀ p) :=
  polyTDegLE_sum _ _ fun q _ => polyTDegLE_monomial q (Polynomial.natDegree_C _).le

/-- Weighted `Z`-degree invariant in `X`: the `X^k`-coefficient of `P : ((F[Z])[T])[X]`
has `Z`-degree at most `B₀ + 2 * k * B_C`. -/
def WeightedZDeg (B₀ B_C : ℕ) (P : ((F[X])[X])[X]) : Prop :=
  ∀ k, CoeffDegLE (B₀ + 2 * k * B_C) (P.coeff k)

theorem weightedZDeg_mono {B₁ B₂ B_C : ℕ} (h : B₁ ≤ B₂) {P : ((F[X])[X])[X]}
    (hP : WeightedZDeg B₁ B_C P) : WeightedZDeg B₂ B_C P :=
  fun k => coeffDegLE_mono (by omega) (hP k)

theorem weightedZDeg_zero (B₀ B_C : ℕ) : WeightedZDeg (F := F) B₀ B_C 0 :=
  fun k => by simpa using coeffDegLE_zero (F := F) (B₀ + 2 * k * B_C)

theorem weightedZDeg_add {B₀ B_C : ℕ} {P Q : ((F[X])[X])[X]}
    (hP : WeightedZDeg B₀ B_C P) (hQ : WeightedZDeg B₀ B_C Q) : WeightedZDeg B₀ B_C (P + Q) :=
  fun k => by rw [Polynomial.coeff_add]; exact coeffDegLE_add (hP k) (hQ k)

theorem weightedZDeg_sum {ι : Type*} (s : Finset ι) {B₀ B_C : ℕ} (f : ι → ((F[X])[X])[X])
    (hf : ∀ i ∈ s, WeightedZDeg B₀ B_C (f i)) : WeightedZDeg B₀ B_C (∑ i ∈ s, f i) :=
  fun k => by
    rw [Polynomial.finsetSum_coeff]
    exact coeffDegLE_sum s _ fun i hi => hf i hi k

theorem weightedZDeg_mul {B₁ B₂ B_C : ℕ} {P Q : ((F[X])[X])[X]}
    (hP : WeightedZDeg B₁ B_C P) (hQ : WeightedZDeg B₂ B_C Q) :
    WeightedZDeg (B₁ + B₂) B_C (P * Q) := fun k => by
  rw [Polynomial.coeff_mul]
  refine coeffDegLE_sum _ _ fun x hx => ?_
  have hsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
  have hmul := coeffDegLE_mul (hP x.1) (hQ x.2)
  refine coeffDegLE_mono ?_ hmul
  have : B₁ + 2 * x.1 * B_C + (B₂ + 2 * x.2 * B_C) = B₁ + B₂ + 2 * k * B_C := by
    rw [← hsum]; ring
  omega

theorem weightedZDeg_pow {B₀ B_C : ℕ} {P : ((F[X])[X])[X]} (hP : WeightedZDeg B₀ B_C P) :
    ∀ n : ℕ, WeightedZDeg (n * B₀) B_C (P ^ n)
  | 0 => by
      intro k
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs
      · exact coeffDegLE_mono (Nat.zero_le _)
          (by simpa using coeffDegLE_C (F := F) (a := 1) (B := 0) (by simp))
      · exact coeffDegLE_zero _
  | n + 1 => by
      rw [pow_succ, Nat.add_mul, one_mul]
      exact weightedZDeg_mul (weightedZDeg_pow hP n) hP

theorem weightedZDeg_C_C {a : F[X]} {B₀ B_C : ℕ} (ha : a.natDegree ≤ B₀) :
    WeightedZDeg B₀ B_C (C (C a)) := fun k => by
  rw [Polynomial.coeff_C]
  split_ifs
  · exact coeffDegLE_mono (by omega) (coeffDegLE_C ha)
  · exact coeffDegLE_zero _

theorem weightedZDeg_scaleXToTX {D₀ : F[X]} {B_p B_C : ℕ} {p : (F[X])[X]}
    (hD₀ : D₀.natDegree ≤ B_C) (hp : ∀ q, (p.coeff q).natDegree ≤ B_p) :
    WeightedZDeg B_p B_C (scaleXToTX D₀ p) :=
  weightedZDeg_sum _ _ fun q _ k => by
    rw [Polynomial.coeff_monomial]
    split_ifs with hqk
    · subst hqk
      refine coeffDegLE_C ?_
      exact (Polynomial.natDegree_mul_le).trans
        (Nat.add_le_add (hp q) ((Polynomial.natDegree_pow_le).trans
          (Nat.mul_le_mul_left (2 * q) hD₀)))
    · exact coeffDegLE_zero _

theorem weightedZDeg_natCast (n B_C : ℕ) : WeightedZDeg (F := F) 0 B_C (n : ((F[X])[X])[X]) := by
  intro k
  have h1 : (n : ((F[X])[X])[X]) = C (C (n : F[X])) := by simp
  rw [h1]
  exact weightedZDeg_C_C (B₀ := 0) (B_C := B_C) (Polynomial.natDegree_natCast (R := F) n ▸ le_rfl) k

/-- Core degree invariant of `henselCoeff`: for every `i : ℕ`,
1. `(henselCoeff R H W D₀ i).natDegree ≤ t` (and `< t` for `i ≥ 1`),
2. `CoeffDegLE (henselExp i * B_C) (henselCoeff R H W D₀ i)`. -/
theorem henselCoeff_deg_bounds {R : ((F[X])[X])[X]} {H W : (F[X])[X]} {D₀ : F[X]}
    {D_Z B_W B_C : ℕ}
    (hHt : 1 ≤ H.natDegree) (hWdeg : W.natDegree < H.natDegree)
    (hRdegZ : ∀ j i, ((R.coeff j).coeff i).natDegree ≤ D_Z)
    (hHdegZ : CoeffDegLE D_Z H) (hWdegZ : CoeffDegLE B_W W)
    (hD₀ : D₀.natDegree ≤ B_C)
    (hC : D_Z + B_W + (R.natDegree + 1) * H.natDegree * D_Z ≤ B_C) :
    ∀ i : ℕ,
      (henselCoeff R H W D₀ i).natDegree ≤ H.natDegree ∧
      (1 ≤ i → (henselCoeff R H W D₀ i).natDegree < H.natDegree) ∧
      CoeffDegLE (henselExp i * B_C) (henselCoeff R H W D₀ i) := by
  intro i
  induction i using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [henselCoeff_zero]
      refine ⟨by simpa using hHt, fun h => by omega, ?_⟩
      simpa [henselExp] using coeffDegLE_X (F := F) 0
    | succ i =>
      rw [henselCoeff_succ]
      set t := H.natDegree
      set ℓ := R.natDegree
      set b := henselCoeff R H W D₀
      set prev_T : ∀ s < i + 1, (b s).natDegree ≤ t := fun s hs => (ih s hs).1
      -- Bound `T`-degree of `henselStepPoly R D₀ b (i + 1)` by `ℓ * t`.
      have hG_T : PolyTDegLE t (∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)) :=
        polyTDegLE_sum _ _ fun s hs =>
          polyTDegLE_monomial (s - 1) (prev_T s (Finset.mem_Ico.mp hs).2)
      have hXG_T : PolyTDegLE t (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)) :=
        polyTDegLE_X_mul hG_T
      have hδ_T : PolyTDegLE t (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) := by
        simpa using polyTDegLE_mul (polyTDegLE_C (a := C D₀) (M := 0) (Polynomial.natDegree_C _).le) hXG_T
      have hb0_T : PolyTDegLE t (C (b 0)) :=
        polyTDegLE_C (prev_T 0 (Nat.zero_lt_succ i))
      have hy_T : PolyTDegLE t (C (b 0) +
          C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) :=
        polyTDegLE_add hb0_T hδ_T
      have hstep_T : PolyTDegLE (ℓ * t) (henselStepPoly R D₀ b (i + 1)) := by
        unfold henselStepPoly
        refine polyTDegLE_add ?_ ?_
        · -- `term1 = XG^2 * taylorTail2 R0T b0 δ`
          have htail : PolyTDegLE ((ℓ - 2) * t)
              (taylorTail2 ((evalX0 R).map (C.comp C)) (C (b 0))
                (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)))) := by
            unfold taylorTail2
            refine polyTDegLE_sum _ _ fun j hj => ?_
            have hj_le : j ≤ ℓ := by
              have h1 : j < ((evalX0 R).map (C.comp C)).natDegree + 1 := Finset.mem_range.mp hj
              have h2 : ((evalX0 R).map (C.comp C)).natDegree ≤ ℓ :=
                Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
              omega
            have hcoeff0 : PolyTDegLE 0 (((evalX0 R).map (C.comp C)).coeff j) := by
              rw [Polynomial.coeff_map]
              exact polyTDegLE_C (a := C _) (M := 0) (Polynomial.natDegree_C _).le
            have hinner : PolyTDegLE ((ℓ - 2) * t)
                (∑ r ∈ Finset.Ico 2 (j + 1),
                  ((Nat.choose j r : ℕ) : ((F[X])[X])[X]) * (C (b 0)) ^ (j - r) *
                    (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) ^ (r - 2)) := by
              refine polyTDegLE_sum _ _ fun r hr => ?_
              have hr2 : 2 ≤ r := (Finset.mem_Ico.mp hr).1
              have hrj : r ≤ j := by have := (Finset.mem_Ico.mp hr).2; omega
              have hch : PolyTDegLE 0 ((Nat.choose j r : ℕ) : ((F[X])[X])[X]) := by
                have heq : ((Nat.choose j r : ℕ) : ((F[X])[X])[X]) = C (C (Nat.choose j r : F[X])) := by
                  simp
                rw [heq]; exact polyTDegLE_C (Polynomial.natDegree_C _).le
              have h1 := polyTDegLE_mul hch (polyTDegLE_pow hb0_T (j - r))
              have h2 := polyTDegLE_mul h1 (polyTDegLE_pow hδ_T (r - 2))
              refine polyTDegLE_mono ?_ h2
              have hsub : j - r + (r - 2) = j - 2 := by omega
              calc 0 + (j - r) * t + (r - 2) * t = (j - r + (r - 2)) * t := by ring
                _ = (j - 2) * t := by rw [hsub]
                _ ≤ (ℓ - 2) * t := Nat.mul_le_mul_right t (by omega)
            simpa using polyTDegLE_mul hcoeff0 hinner
          by_cases hℓ2 : 2 ≤ ℓ
          · have hmul := polyTDegLE_mul (polyTDegLE_pow hXG_T 2) htail
            refine polyTDegLE_mono ?_ hmul
            have : 2 + (ℓ - 2) = ℓ := by omega
            exact le_of_eq (calc 2 * t + (ℓ - 2) * t = (2 + (ℓ - 2)) * t := by ring
              _ = ℓ * t := by rw [this])
          · -- When `ℓ < 2`, `taylorTail2` is empty (`0`)!
            have hzero : taylorTail2 ((evalX0 R).map (C.comp C)) (C (b 0))
                (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) = 0 := by
              unfold taylorTail2
              refine Finset.sum_eq_zero fun j hj => ?_
              have h1 : j < ((evalX0 R).map (C.comp C)).natDegree + 1 := Finset.mem_range.mp hj
              have h2 : ((evalX0 R).map (C.comp C)).natDegree ≤ ℓ :=
                Polynomial.natDegree_map_le.trans Polynomial.natDegree_map_le
              have hempty : Finset.Ico 2 (j + 1) = ∅ := Finset.Ico_eq_empty (by omega)
              rw [hempty, Finset.sum_empty, mul_zero]
            rw [hzero, mul_zero]
            exact polyTDegLE_zero _
        · -- `term2 = X * ∑ j ≤ ℓ, scaleXToTX D₀ (divXInner (R.coeff j)) * yPoly ^ j`
          refine polyTDegLE_X_mul (polyTDegLE_sum _ _ fun j hj => ?_)
          have hj_le : j ≤ ℓ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          have h1 := polyTDegLE_mul (polyTDegLE_scaleXToTX D₀ (divXInner (R.coeff j)))
            (polyTDegLE_pow hy_T j)
          refine polyTDegLE_mono ?_ h1
          simpa using Nat.mul_le_mul_right t hj_le
      have hc_red_lt : (pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))).natDegree < t :=
        pseudoRem_natDegree_lt hHt (ℓ * t) _ (lt_of_le_of_lt (hstep_T (i + 1)) (by omega))
      have hprod_lt : (-W * pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))).natDegree <
          t + t := by
        have h1 : (-W * pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))).natDegree ≤
            (-W).natDegree + (pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))).natDegree :=
          Polynomial.natDegree_mul_le
        rw [Polynomial.natDegree_neg] at h1
        omega
      have hfinal_lt : (pseudoRem H t (-W * pseudoRem H (ℓ * t)
          ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1)))).natDegree < t :=
        pseudoRem_natDegree_lt hHt t _ hprod_lt
      -- Now prove the `Z`-degree bound `CoeffDegLE ((2 * (i + 1) - 1) * B_C)`.
      have hG_Z : WeightedZDeg B_C B_C (∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)) :=
        weightedZDeg_sum _ _ fun s hs k => by
          rw [Polynomial.coeff_monomial]
          split_ifs with hsk
          · have hs1 : 1 ≤ s := (Finset.mem_Ico.mp hs).1
            have hslt : s < i + 1 := (Finset.mem_Ico.mp hs).2
            have hbZ := (ih s hslt).2.2
            have heq : henselExp s * B_C = B_C + 2 * k * B_C := by
              unfold henselExp
              have hs0 : s ≠ 0 := by omega
              rw [ite_eq_right hs0]
              have h2 : 2 * s - 1 = 2 * k + 1 := by omega
              rw [h2]; ring
            rwa [heq] at hbZ
          · exact coeffDegLE_zero _
      have hXG_Z : ∀ k, CoeffDegLE ((2 * k - 1) * B_C)
          ((X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)).coeff k) := by
        intro k
        cases k with
        | zero => simp [coeffDegLE_zero]
        | succ k =>
          rw [Polynomial.coeff_X_mul]
          have hk := hG_Z k
          refine coeffDegLE_mono ?_ hk
          have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          rw [this]; ring_nf; exact le_rfl
      -- `δ = C (C D₀) * XG` has `WeightedZDeg 0 B_C δ`!
      have hδ_Z : WeightedZDeg 0 B_C
          (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) := by
        intro k
        rw [Polynomial.coeff_C_mul]
        cases k with
        | zero => simp [coeffDegLE_zero]
        | succ k =>
          have h1 := coeffDegLE_C_mul hD₀ (hXG_Z (k + 1))
          refine coeffDegLE_mono ?_ h1
          have : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
          rw [this]
          have hring : B_C + (2 * k + 1) * B_C = 0 + 2 * (k + 1) * B_C := by ring
          omega
      have hb0_Z : WeightedZDeg 0 B_C (C (b 0)) := by
        intro k
        rw [Polynomial.coeff_C]
        split_ifs
        · exact coeffDegLE_mono (Nat.zero_le _) (by simpa [henselExp] using (ih 0 (Nat.zero_lt_succ i)).2.2)
        · exact coeffDegLE_zero _
      have hy_Z : WeightedZDeg 0 B_C (C (b 0) +
          C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) :=
        weightedZDeg_add hb0_Z hδ_Z
      -- Bound `Z`-degree of `(henselStepPoly R D₀ b (i + 1)).coeff (i + 1)` by `D_Z + 2 * i * B_C`!
      have hci_Z : CoeffDegLE (D_Z + 2 * i * B_C)
          ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1)) := by
        unfold henselStepPoly
        rw [Polynomial.coeff_add]
        refine coeffDegLE_add ?_ ?_
        · -- `term1 = XG ^ 2 * taylorTail2 ...`
          have hXG2_Z : ∀ k, CoeffDegLE (2 * (k - 1) * B_C)
              (((X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)) ^ 2).coeff k) := by
            intro k
            rw [sq, Polynomial.coeff_mul]
            refine coeffDegLE_sum _ _ fun x hx => ?_
            have hxsum : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
            cases h1 : x.1 with
            | zero => simp [coeffDegLE_zero]
            | succ a =>
              cases h2 : x.2 with
              | zero => simp [coeffDegLE_zero]
              | succ b' =>
                have hm := coeffDegLE_mul (hXG_Z (a + 1)) (hXG_Z (b' + 1))
                refine coeffDegLE_mono ?_ hm
                have ha : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
                have hb : 2 * (b' + 1) - 1 = 2 * b' + 1 := by omega
                have hk : k - 1 = a + b' + 1 := by omega
                rw [ha, hb, hk]
                have : (2 * a + 1) * B_C + (2 * b' + 1) * B_C = 2 * (a + b' + 1) * B_C := by ring
                omega
          have htail_Z : WeightedZDeg D_Z B_C
              (taylorTail2 ((evalX0 R).map (C.comp C)) (C (b 0))
                (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s)))) := by
            unfold taylorTail2
            refine weightedZDeg_sum _ _ fun j _ => ?_
            have hR0j : WeightedZDeg D_Z B_C (((evalX0 R).map (C.comp C)).coeff j) := by
              rw [Polynomial.coeff_map]
              have hev : (evalX0 R).coeff j = (R.coeff j).coeff 0 := by
                simp [evalX0, Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero]
              rw [hev]
              exact weightedZDeg_C_C (hRdegZ j 0)
            have hinner : WeightedZDeg 0 B_C
                (∑ r ∈ Finset.Ico 2 (j + 1),
                  ((Nat.choose j r : ℕ) : ((F[X])[X])[X]) * (C (b 0)) ^ (j - r) *
                    (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) ^ (r - 2)) := by
              refine weightedZDeg_sum _ _ fun r _ => ?_
              have h1 := weightedZDeg_mul (weightedZDeg_natCast (Nat.choose j r) B_C)
                (weightedZDeg_pow hb0_Z (j - r))
              have h2 := weightedZDeg_mul h1 (weightedZDeg_pow hδ_Z (r - 2))
              simpa using h2
            simpa using weightedZDeg_mul hR0j hinner
          rw [Polynomial.coeff_mul]
          refine coeffDegLE_sum _ _ fun x hx => ?_
          have hxsum : x.1 + x.2 = i + 1 := Finset.mem_antidiagonal.mp hx
          cases hx1 : x.1 with
          | zero =>
            rw [sq, Polynomial.coeff_mul]
            simp [coeffDegLE_zero]
          | succ k1 =>
            have hmul := coeffDegLE_mul (hXG2_Z (k1 + 1)) (htail_Z x.2)
            refine coeffDegLE_mono ?_ hmul
            have hk : k1 + x.2 = i := by omega
            have hsub : k1 + 1 - 1 = k1 := by omega
            rw [hsub]
            have : 2 * k1 * B_C + (D_Z + 2 * x.2 * B_C) = D_Z + 2 * i * B_C := by
              rw [← hk]; ring
            omega
        · -- `term2 = X * ∑ j ≤ ℓ, scaleXToTX D₀ (divXInner (R.coeff j)) * yPoly ^ j`
          rw [Polynomial.coeff_X_mul]
          have hsumZ : WeightedZDeg D_Z B_C
              (∑ j ∈ Finset.range (ℓ + 1),
                scaleXToTX D₀ (divXInner (R.coeff j)) *
                  (C (b 0) + C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (b s))) ^ j) := by
            refine weightedZDeg_sum _ _ fun j _ => ?_
            have hdiv : ∀ q, ((divXInner (R.coeff j)).coeff q).natDegree ≤ D_Z := by
              intro q
              unfold divXInner
              rw [Polynomial.finsetSum_coeff]
              refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
              rw [Polynomial.coeff_monomial]
              split_ifs
              · exact hRdegZ j (r + 1)
              · simp
            have hsx := weightedZDeg_scaleXToTX hD₀ hdiv
            simpa using weightedZDeg_mul hsx (weightedZDeg_pow hy_Z j)
          exact hsumZ i
      -- Apply `pseudoRem` twice and multiply by `-W`.
      have hcred_Z : CoeffDegLE (D_Z + 2 * i * B_C + ℓ * t * D_Z)
          (pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))) :=
        coeffDegLE_pseudoRem hHdegZ (ℓ * t) _ _ hci_Z
      have hmulW_Z : CoeffDegLE (B_W + (D_Z + 2 * i * B_C + ℓ * t * D_Z))
          (-W * pseudoRem H (ℓ * t) ((henselStepPoly R D₀ b (i + 1)).coeff (i + 1))) :=
        coeffDegLE_mul (coeffDegLE_neg hWdegZ) hcred_Z
      have hfin_Z := coeffDegLE_pseudoRem hHdegZ t _ _ hmulW_Z
      refine ⟨hfinal_lt.le, fun _ => hfinal_lt, coeffDegLE_mono ?_ hfin_Z⟩
      have hexp : henselExp (i + 1) = 2 * i + 1 := by
        unfold henselExp; simp; omega
      rw [hexp]
      have hring1 : B_W + (D_Z + 2 * i * B_C + ℓ * t * D_Z) + t * D_Z =
          2 * i * B_C + (D_Z + B_W + (ℓ + 1) * t * D_Z) := by ring
      have hring2 : (2 * i + 1) * B_C = 2 * i * B_C + B_C := by ring
      rw [hring1, hring2]
      exact Nat.add_le_add_left hC _

/-! ## 4. Exact Specialization Identity (`eval₂ (eval β) u_β (b i) = D₀(β)^{e(i)} * p.coeff i`) -/

/-- Ring homomorphism `φ_β : (F[Z])[T] →+* F` sending `Z ↦ β` and `T ↦ u`. -/
noncomputable def evalZT (β u : F) : (F[X])[X] →+* F :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom β) u

/-- Lifted homomorphism `((F[Z])[T])[X] →+* F[X]` applying `evalZT β u` to each `X`-coefficient. -/
noncomputable def mapEvalZT (β u : F) : ((F[X])[X])[X] →+* F[X] :=
  Polynomial.mapRingHom (evalZT β u)

/-- Evaluate `R : ((F[Z])[X])[Y]` at `Z = β`, returning a bivariate polynomial `(F[X])[Y]`. -/
noncomputable def evalZR (β : F) (R : ((F[X])[X])[X]) : (F[X])[X] :=
  R.map (Polynomial.mapRingHom (Polynomial.evalRingHom β))

theorem evalZT_C (β u : F) (a : F[X]) : evalZT β u (C a) = a.eval β := by
  simp [evalZT]

theorem evalZT_X (β u : F) : evalZT β u X = u := by
  simp [evalZT]

theorem mapEvalZT_scaleXToTX (β u : F) (D₀ : F[X]) (p : (F[X])[X]) :
    mapEvalZT β u (scaleXToTX D₀ p) =
      (p.map (Polynomial.evalRingHom β)).comp (C (D₀.eval β ^ 2) * X) := by
  unfold mapEvalZT scaleXToTX
  rw [map_sum]
  have hcomp : (p.map (Polynomial.evalRingHom β)).comp (C (D₀.eval β ^ 2) * X) =
      ∑ q ∈ Finset.range (p.natDegree + 1),
        C ((p.coeff q).eval β) * (C (D₀.eval β ^ 2) * X) ^ q := by
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
    rw [Finset.sum_subset (s₂ := Finset.range (p.natDegree + 1))]
    · refine Finset.sum_congr rfl fun q _ => ?_
      simp [Polynomial.coeff_map]
    · intro q hq
      have hlt : q ≤ (p.map (Polynomial.evalRingHom β)).natDegree :=
        Polynomial.le_natDegree_of_mem_supp q hq
      have hle : (p.map (Polynomial.evalRingHom β)).natDegree ≤ p.natDegree :=
        Polynomial.natDegree_map_le
      exact Finset.mem_range.mpr (by omega)
    · intro q _ hnot
      have h0 : (p.map (Polynomial.evalRingHom β)).coeff q = 0 := by
        simpa [Polynomial.mem_support_iff] using hnot
      simp [h0]
  rw [hcomp]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.coe_mapRingHom, Polynomial.map_monomial, evalZT_C, Polynomial.eval_mul,
    Polynomial.eval_pow, mul_pow, ← C_pow, ← pow_mul, mul_comm 2 q,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul]
  ring

/-- **Exact Hensel Specialization Theorem:**
Suppose `H(β, u) = 0`, `D₀ = h_top ^ ((ℓ + 1) * t) * Δ₀` with `D₀(β) ≠ 0`,
`W * R₀' ≡ C Δ₀ (mod H)`, and `p : F[X]` satisfies `p.eval 0 = u` and
`(evalZR β R).eval p = 0` in `F[X]`. Then for EVERY `i : ℕ`:
`evalZT β u (henselCoeff R H W D₀ i) = (D₀.eval β) ^ (henselExp i) * p.coeff i`. -/
theorem henselCoeff_evalZT_eq {R : ((F[X])[X])[X]} {H W : (F[X])[X]} {Δ₀ : F[X]}
    (hbez : H ∣ W * (evalX0 R).derivative - C Δ₀)
    {β u : F} (hHβ : evalZT β u H = 0)
    (hD₀ne : (H.leadingCoeff ^ ((R.natDegree + 1) * H.natDegree) * Δ₀).eval β ≠ 0)
    {p : F[X]} (hp0 : p.eval 0 = u) (hRp : (evalZR β R).eval p = 0) :
    let D₀ := H.leadingCoeff ^ ((R.natDegree + 1) * H.natDegree) * Δ₀
    ∀ i : ℕ, evalZT β u (henselCoeff R H W D₀ i) = (D₀.eval β) ^ (henselExp i) * p.coeff i := by
  intro D₀ i
  have hD₀_val : D₀.eval β = (H.leadingCoeff.eval β) ^ ((R.natDegree + 1) * H.natDegree) * Δ₀.eval β := by
    simp [D₀]
  have hW_rel : evalZT β u W * evalZT β u (evalX0 R).derivative = Δ₀.eval β := by
    obtain ⟨q, hq⟩ := hbez
    have hev := congrArg (evalZT β u) hq
    simp only [map_sub, map_mul, evalZT_C, hHβ, zero_mul] at hev
    exact sub_eq_zero.mp hev
  induction i using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [henselCoeff_zero, evalZT_X, henselExp, ite_eq_left rfl, pow_zero, one_mul,
        Polynomial.coeff_zero_eq_eval_zero, hp0]
    | succ i =>
      rw [henselCoeff_succ]
      set t := H.natDegree
      set ℓ := R.natDegree
      set d₀ := D₀.eval β
      have hd₀_ne : d₀ ≠ 0 := hD₀ne
      have hH_ev2 : H.eval₂ (Polynomial.evalRingHom β) u = 0 := hHβ
      -- Evaluate `pseudoRem` twice at `(β, u)`.
      have hpr1 : evalZT β u (pseudoRem H (ℓ * t)
            ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1))) =
          (H.leadingCoeff.eval β) ^ (ℓ * t) *
            evalZT β u ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)) := by
        simpa [evalZT] using pseudoRem_eval₂ (Polynomial.evalRingHom β) u hH_ev2 (ℓ * t) _
      have hpr2 : evalZT β u (pseudoRem H t
            (-W * pseudoRem H (ℓ * t)
              ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)))) =
          (H.leadingCoeff.eval β) ^ t *
            (-(evalZT β u W) * evalZT β u (pseudoRem H (ℓ * t)
              ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)))) := by
        have h := pseudoRem_eval₂ (Polynomial.evalRingHom β) u hH_ev2 t
          (-W * pseudoRem H (ℓ * t)
            ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)))
        change evalZT β u _ = (H.leadingCoeff.eval β) ^ t * evalZT β u _ at h
        rw [h, map_mul, map_neg]
      rw [hpr2, hpr1]
      -- Compute `evalZT β u ((henselStepPoly ...).coeff (i + 1))` by comparing `coeff (i + 1)`
      -- of `(evalZR β R).eval (p.comp (C (d₀^2) * X)) = 0`!
      set p_sc : F[X] := p.comp (C (d₀ ^ 2) * X)
      have hp_sc_coeff : ∀ s, p_sc.coeff s = d₀ ^ (2 * s) * p.coeff s := by
        intro s
        simp only [p_sc]
        rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, Polynomial.finsetSum_coeff]
        have hterm : ∀ k ∈ p.support,
            (C (p.coeff k) * (C (d₀ ^ 2) * X) ^ k).coeff s =
              if k = s then d₀ ^ (2 * s) * p.coeff s else 0 := by
          intro k _
          rw [mul_pow, ← C_pow, ← pow_mul, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul_X_pow]
          by_cases hks : k = s
          · subst hks; simp; ring
          · have hsk : s ≠ k := Ne.symm hks
            simp [hks, hsk]
        rw [Finset.sum_congr rfl hterm]
        by_cases hs : s ∈ p.support
        · rw [Finset.sum_ite_eq' p.support s, ite_eq_left hs]
        · rw [Finset.sum_ite_eq' p.support s, ite_eq_right hs]
          have hp0s : p.coeff s = 0 := by simpa [Polynomial.mem_support_iff] using hs
          rw [hp0s, mul_zero]
      -- Split `p_sc` into low part `y_β` (`deg ≤ i`) and high part `X^(i+1) * rem`!
      set G_β : F[X] := mapEvalZT β u (∑ s ∈ Finset.Ico 1 (i + 1), monomial (s - 1) (henselCoeff R H W D₀ s))
      set XG_β : F[X] := X * G_β
      set δ_β : F[X] := C d₀ * XG_β
      set y_β : F[X] := C u + δ_β
      have hy_β_coeff : ∀ s, y_β.coeff s = if s ≤ i then p_sc.coeff s else 0 := by
        intro s
        dsimp only [y_β, δ_β, XG_β, G_β]
        cases s with
        | zero =>
          simp [hp_sc_coeff 0, Polynomial.coeff_zero_eq_eval_zero, hp0]
        | succ k =>
          rw [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_mul, mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
            Polynomial.finsetSum_coeff]
          simp_rw [Polynomial.coeff_monomial]
          by_cases hk : k + 1 ≤ i
          · have hmem : k + 1 ∈ Finset.Ico 1 (i + 1) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
            rw [Finset.sum_eq_single (k + 1)]
            · simp only [Nat.add_sub_cancel, ↓reduceIte, ite_eq_left hk]
              rw [ih (k + 1) (by omega), hp_sc_coeff (k + 1)]
              have hexp : henselExp (k + 1) = 2 * k + 1 := by unfold henselExp; simp; omega
              rw [hexp, ← mul_assoc, ← pow_succ']
              have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
              rw [h2]
            · intro b hb hne
              have hb1 : 1 ≤ b := (Finset.mem_Ico.mp hb).1
              have hne' : b - 1 ≠ k := by omega
              simp [hne']
            · intro hnm; exact absurd hmem hnm
          · rw [ite_eq_right hk, Finset.sum_eq_zero]
            · simp
            · intro b hb
              have hb1 : 1 ≤ b := (Finset.mem_Ico.mp hb).1
              have hb2 : b < i + 1 := (Finset.mem_Ico.mp hb).2
              have hne' : b - 1 ≠ k := by omega
              simp [hne']
      -- Therefore `p_sc - y_β` vanishes on degrees `0 .. i`, so `p_sc = y_β + X^(i+1) * Q_hi`!
      have hps_diff : ∀ s ≤ i, (p_sc - y_β).coeff s = 0 := by
        intro s hs
        rw [Polynomial.coeff_sub, hy_β_coeff s, ite_eq_left hs, sub_self]
      have hps_eq : ∃ Q_hi : F[X], p_sc = y_β + X ^ (i + 1) * Q_hi ∧
          Q_hi.coeff 0 = p_sc.coeff (i + 1) := by
        refine ⟨∑ s ∈ Finset.range (p_sc.natDegree + 1),
            monomial s ((p_sc - y_β).coeff (s + (i + 1))), ?_, ?_⟩
        · ext s
          rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
          by_cases hs : i + 1 ≤ s
          · rw [ite_eq_left hs, Polynomial.finsetSum_coeff]
            simp_rw [Polynomial.coeff_monomial]
            have hsub : s - (i + 1) + (i + 1) = s := Nat.sub_add_cancel hs
            by_cases hlt : s - (i + 1) < p_sc.natDegree + 1
            · rw [Finset.sum_eq_single (s - (i + 1))]
              · rw [ite_eq_left rfl, hsub, Polynomial.coeff_sub]
                ring
              · intro b _ hne; simp [hne]
              · intro hnm; exact absurd (Finset.mem_range.mpr hlt) hnm
            · rw [Finset.sum_eq_zero]
              · have hp0s : p_sc.coeff s = 0 :=
                  Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
                have hy0s : y_β.coeff s = 0 := by rw [hy_β_coeff s, ite_eq_right (by omega)]
                rw [hp0s, hy0s, add_zero]
              · intro b hb
                have hblt : b < p_sc.natDegree + 1 := Finset.mem_range.mp hb
                have hne : b ≠ s - (i + 1) := by omega
                simp [hne]
          · rw [ite_eq_right hs, add_zero, hy_β_coeff s, ite_eq_left (by omega)]
        · rw [Polynomial.finsetSum_coeff]
          simp_rw [Polynomial.coeff_monomial]
          rw [Finset.sum_eq_single 0]
          · rw [ite_eq_left rfl, zero_add, Polynomial.coeff_sub, hy_β_coeff (i + 1),
              ite_eq_right (by omega), sub_zero]
          · intro b _ hne; simp [hne]
          · intro hnm; exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ _)) hnm
      obtain ⟨Q_hi, hQ_hi, hQ0⟩ := hps_eq
      -- Evaluate `evalZR β R` at `X ↦ d₀^2 * X` and `Y ↦ p_sc` (= 0)!
      set R_β : (F[X])[X] := evalZR β R
      set R_sc : (F[X])[X] := R_β.map (Polynomial.compRingHom (C (d₀ ^ 2) * X))
      have hR_sc_p : R_sc.eval p_sc = 0 := by
        have hcomp : R_sc.eval p_sc = (R_β.eval p).comp (C (d₀ ^ 2) * X) := by
          unfold R_sc p_sc
          rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
          rw [Polynomial.sum_comp]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Polynomial.mul_comp, Polynomial.pow_comp]
          rfl
        rw [hcomp, hRp, Polynomial.zero_comp]
      -- Expand `R_sc.eval (y_β + X^(i+1) * Q_hi)` modulo `X^(i+2)`!
      -- Notice `R_sc.eval (y_β + X^(i+1) * Q_hi) - (R_sc.eval y_β + R_sc.derivative.eval y_β * X^(i+1) * Q_hi)`
      -- is divisible by `X^(2*(i+1))`, so its `(i+1)`-th coeff is `0`!
      have htay_p := taylor2_identity R_sc y_β (X ^ (i + 1) * Q_hi)
      rw [← hQ_hi, hR_sc_p] at htay_p
      have hcoeff_main := congrArg (fun f : F[X] => f.coeff (i + 1)) htay_p.symm
      rw [Polynomial.coeff_zero, Polynomial.coeff_add, Polynomial.coeff_add] at hcoeff_main
      have htail_0 : ((X ^ (i + 1) * Q_hi) ^ 2 * taylorTail2 R_sc y_β (X ^ (i + 1) * Q_hi)).coeff (i + 1) = 0 := by
        rw [mul_pow, ← pow_mul, mul_assoc, Polynomial.coeff_X_pow_mul']
        rw [ite_eq_right (by omega)]
      -- Compute `(R_sc.derivative.eval y_β * (X ^ (i + 1) * Q_hi)).coeff (i + 1)`:
      have hlin_term : (R_sc.derivative.eval y_β * (X ^ (i + 1) * Q_hi)).coeff (i + 1) =
          evalZT β u (evalX0 R).derivative * p_sc.coeff (i + 1) := by
        rw [mul_left_comm, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self,
          Polynomial.mul_coeff_zero, hQ0]
        congr 1
        rw [Polynomial.coeff_zero_eq_eval_zero]
        have hy0 : y_β.eval 0 = u := by
          rw [← Polynomial.coeff_zero_eq_eval_zero, hy_β_coeff 0, ite_eq_left (Nat.zero_le _),
            hp_sc_coeff 0, mul_zero, pow_zero, one_mul, Polynomial.coeff_zero_eq_eval_zero, hp0]
        have hcomp_ev0 : (Polynomial.evalRingHom (0 : F)).comp
            (Polynomial.compRingHom (C (d₀ ^ 2) * X)) = Polynomial.evalRingHom 0 := by
          apply RingHom.ext
          intro q
          simp
        have hRder_map : R_sc.derivative.map (Polynomial.evalRingHom 0) =
            (evalX0 R).derivative.map (Polynomial.evalRingHom β) := by
          have h1 : R_sc.derivative = R_β.derivative.map (Polynomial.compRingHom (C (d₀ ^ 2) * X)) :=
            Polynomial.derivative_map _ _
          have h2 : R_β.derivative = R.derivative.map (Polynomial.mapRingHom (Polynomial.evalRingHom β)) :=
            Polynomial.derivative_map _ _
          have h3 : (evalX0 R).derivative = R.derivative.map (Polynomial.evalRingHom 0) :=
            Polynomial.derivative_map _ _
          rw [h1, Polynomial.map_map, hcomp_ev0, h2, h3, Polynomial.map_map, Polynomial.map_map]
          congr 1
          apply RingHom.ext
          intro q
          simp [Polynomial.eval_map, Polynomial.coeff_zero_eq_eval_zero]
        have heval_hom : (R_sc.derivative.eval y_β).eval 0 =
            (R_sc.derivative.map (Polynomial.evalRingHom 0)).eval (y_β.eval 0) := by
          have := Polynomial.hom_eval₂ R_sc.derivative (RingHom.id F[X]) (Polynomial.evalRingHom 0) y_β
          simpa [Polynomial.eval_map] using this
        rw [heval_hom, hRder_map, hy0]
        simp [evalZT, Polynomial.eval_map]
      -- Relate `(R_sc.eval y_β).coeff (i + 1)` to `d₀ ^ 2 * evalZT β u ((henselStepPoly ...).coeff (i + 1))`!
      have hstep_eval : (R_sc.eval y_β).coeff (i + 1) =
          d₀ ^ 2 * evalZT β u ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)) := by
        have hsplit : R_sc = ((evalX0 R).map (Polynomial.evalRingHom β)).map C +
            C (C (d₀ ^ 2) * X) * ((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom β)))) := by
          have hR := R_eq_evalX0_add_X_mul_RHi R
          have hC_comp : (((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom β))).comp C) =
              C.comp (Polynomial.evalRingHom β) := by
            apply RingHom.ext; intro a; simp
          have hCX : (Polynomial.compRingHom (C (d₀ ^ 2) * X))
              ((Polynomial.mapRingHom (Polynomial.evalRingHom β)) X) = C (d₀ ^ 2) * X := by
            simp
          calc R_sc
              = (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom β))).map
                  (Polynomial.compRingHom (C (d₀ ^ 2) * X)) := rfl
            _ = (((evalX0 R).map C + C X * RHi R).map (Polynomial.mapRingHom (Polynomial.evalRingHom β))).map
                  (Polynomial.compRingHom (C (d₀ ^ 2) * X)) := by rw [← hR]
            _ = ((evalX0 R).map (((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
                  (Polynomial.mapRingHom (Polynomial.evalRingHom β))).comp C)) +
                C ((Polynomial.compRingHom (C (d₀ ^ 2) * X))
                  ((Polynomial.mapRingHom (Polynomial.evalRingHom β)) X)) *
                ((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
                  (Polynomial.mapRingHom (Polynomial.evalRingHom β)))) := by
                simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
                  Polynomial.map_map, RingHom.comp_assoc]
            _ = ((evalX0 R).map (Polynomial.evalRingHom β)).map C +
                C (C (d₀ ^ 2) * X) * ((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
                  (Polynomial.mapRingHom (Polynomial.evalRingHom β)))) := by
                rw [hC_comp, ← Polynomial.map_map, hCX]
        have heval_split : R_sc.eval y_β =
            (((evalX0 R).map (Polynomial.evalRingHom β)).map C).eval y_β +
            (C (d₀ ^ 2) * X) * (((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom β)))).eval y_β) := by
          rw [hsplit, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
        have htay0 := taylor2_identity (((evalX0 R).map (Polynomial.evalRingHom β)).map C) (C u) δ_β
        have hR0_ev : (((evalX0 R).map (Polynomial.evalRingHom β)).map C).eval (C u) =
            C (((evalX0 R).map (Polynomial.evalRingHom β)).eval u) := by
          rw [Polynomial.eval_map, Polynomial.eval₂_hom]
        have hR0_der_ev : (((evalX0 R).map (Polynomial.evalRingHom β)).map C).derivative.eval (C u) =
            C ((((evalX0 R).map (Polynomial.evalRingHom β)).derivative).eval u) := by
          rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_hom]
        -- Check `mapEvalZT β u (henselStepPoly ...)`!
        have hmap_step : mapEvalZT β u (henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)) =
            XG_β ^ 2 * taylorTail2 (((evalX0 R).map (Polynomial.evalRingHom β)).map C) (C u) δ_β +
            X * (((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom β)))).eval y_β) := by
          unfold henselStepPoly
          rw [map_add]
          congr 1
          · -- term1
            rw [map_mul, map_pow]
            have hX_map : mapEvalZT β u (X : ((F[X])[X])[X]) = X := by
              rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_X]
            have hXG_map : mapEvalZT β u (X * ∑ s ∈ Finset.Ico 1 (i + 1),
                monomial (s - 1) (henselCoeff R H W D₀ s)) = XG_β := by
              rw [map_mul, hX_map]
            have hδ_map : mapEvalZT β u (C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1),
                monomial (s - 1) (henselCoeff R H W D₀ s))) = δ_β := by
              rw [map_mul, hXG_map]
              have hC_D0 : mapEvalZT β u (C (C D₀)) = C d₀ := by
                rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_C]
              rw [hC_D0]
            have hb0_map : mapEvalZT β u (C (henselCoeff R H W D₀ 0)) = C u := by
              rw [henselCoeff_zero, mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_X]
            rw [hXG_map]
            congr 1
            unfold taylorTail2
            have hR0T_map : ((evalX0 R).map (C.comp C)).map (mapEvalZT β u) =
                ((evalX0 R).map (Polynomial.evalRingHom β)).map C := by
              rw [Polynomial.map_map, Polynomial.map_map]
              congr 1
              apply RingHom.ext
              intro a
              simp [mapEvalZT, Polynomial.coe_mapRingHom, evalZT_C]
            have hR0T_deg : (((evalX0 R).map (Polynomial.evalRingHom β)).map C).natDegree ≤
                ((evalX0 R).map (C.comp C)).natDegree := by
              rw [← hR0T_map]; exact Polynomial.natDegree_map_le
            rw [map_sum]
            symm
            rw [Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hR0T_deg 1))]
            · refine Finset.sum_congr rfl fun j _ => ?_
              have hcj : mapEvalZT β u (((evalX0 R).map (C.comp C)).coeff j) =
                  (((evalX0 R).map (Polynomial.evalRingHom β)).map C).coeff j := by
                rw [← Polynomial.coeff_map, hR0T_map]
              rw [map_mul, map_sum, hcj]
              congr 1
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [map_mul, map_mul, map_natCast, map_pow, map_pow, hb0_map, hδ_map]
            · intro j _ hnot
              have hgt : (((evalX0 R).map (Polynomial.evalRingHom β)).map C).natDegree < j := by
                have := Finset.mem_range.not.mp hnot; omega
              have h0 : ((((evalX0 R).map (Polynomial.evalRingHom β)).map C).coeff j) = 0 :=
                Polynomial.coeff_eq_zero_of_natDegree_lt hgt
              rw [h0, zero_mul]
          · -- term2
            rw [map_mul, map_sum]
            have hX_map : mapEvalZT β u (X : ((F[X])[X])[X]) = X := by
              rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_X]
            have hy_map : mapEvalZT β u (C (henselCoeff R H W D₀ 0) +
                C (C D₀) * (X * ∑ s ∈ Finset.Ico 1 (i + 1),
                  monomial (s - 1) (henselCoeff R H W D₀ s))) = y_β := by
              rw [map_add, map_mul, henselCoeff_zero]
              have hXG_map : mapEvalZT β u (X * ∑ s ∈ Finset.Ico 1 (i + 1),
                  monomial (s - 1) (henselCoeff R H W D₀ s)) = XG_β := by
                rw [map_mul, hX_map]
              have hC_b0 : mapEvalZT β u (C (X : (F[X])[X])) = C u := by
                rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_X]
              have hC_D0 : mapEvalZT β u (C (C D₀)) = C d₀ := by
                rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_C]
              rw [hC_b0, hC_D0, hXG_map]
            rw [hX_map]
            congr 1
            have hRHi_eval : ((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
                (Polynomial.mapRingHom (Polynomial.evalRingHom β)))).eval y_β =
                ∑ j ∈ Finset.range (R.natDegree + 1),
                  ((divXInner (R.coeff j)).map (Polynomial.evalRingHom β)).comp (C (d₀ ^ 2) * X) *
                    y_β ^ j := by
              unfold RHi
              rw [Polynomial.map_sum, Polynomial.eval_finsetSum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Polynomial.map_monomial, Polynomial.eval_monomial]
              rfl
            rw [hRHi_eval]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_pow, hy_map, mapEvalZT_scaleXToTX]
        -- Now take `coeff (i + 1)` of `heval_split`!
        have hδ_coeff : δ_β.coeff (i + 1) = 0 := by
          have h1 := hy_β_coeff (i + 1)
          rw [ite_eq_right (by omega)] at h1
          dsimp only [y_β] at h1
          rwa [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add] at h1
        rw [heval_split, Polynomial.coeff_add]
        have h1 : ((((evalX0 R).map (Polynomial.evalRingHom β)).map C).eval y_β).coeff (i + 1) =
            d₀ ^ 2 * (XG_β ^ 2 * taylorTail2 (((evalX0 R).map (Polynomial.evalRingHom β)).map C) (C u) δ_β).coeff (i + 1) := by
          change ((((evalX0 R).map (Polynomial.evalRingHom β)).map C).eval (C u + δ_β)).coeff (i + 1) = _
          rw [htay0, hR0_ev, hR0_der_ev, Polynomial.coeff_add, Polynomial.coeff_add,
            Polynomial.coeff_C_succ, Polynomial.coeff_C_mul, hδ_coeff, mul_zero, zero_add, zero_add]
          have hδsq : δ_β ^ 2 = C (d₀ ^ 2) * XG_β ^ 2 := by
            dsimp only [δ_β]; rw [mul_pow, ← C_pow]
          rw [hδsq, mul_assoc, Polynomial.coeff_C_mul]
        have h2 : ((C (d₀ ^ 2) * X) * (((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
            (Polynomial.mapRingHom (Polynomial.evalRingHom β)))).eval y_β)).coeff (i + 1) =
            d₀ ^ 2 * (X * (((RHi R).map ((Polynomial.compRingHom (C (d₀ ^ 2) * X)).comp
              (Polynomial.mapRingHom (Polynomial.evalRingHom β)))).eval y_β)).coeff (i + 1) := by
          rw [mul_assoc, Polynomial.coeff_C_mul]
        rw [h1, h2, ← mul_add, ← Polynomial.coeff_add, ← hmap_step]
        rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
      -- Put `hcoeff_main`, `htail_0`, `hlin_term`, and `hstep_eval` together!
      rw [htail_0, add_zero, hlin_term, hstep_eval, hp_sc_coeff (i + 1)] at hcoeff_main
      have hpow_split : d₀ ^ (2 * (i + 1)) = d₀ ^ 2 * d₀ ^ (2 * i) := by
        rw [← pow_add]; congr 1; omega
      rw [hpow_split] at hcoeff_main
      have hfac : d₀ ^ 2 * (evalZT β u ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)) +
          evalZT β u (evalX0 R).derivative * d₀ ^ (2 * i) * p.coeff (i + 1)) = 0 := by
        calc _ = d₀ ^ 2 * evalZT β u ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)) +
              evalZT β u (evalX0 R).derivative * (d₀ ^ 2 * d₀ ^ (2 * i) * p.coeff (i + 1)) := by ring
          _ = 0 := hcoeff_main
      have hci_eq : evalZT β u ((henselStepPoly R D₀ (henselCoeff R H W D₀) (i + 1)).coeff (i + 1)) =
          -(evalZT β u (evalX0 R).derivative * d₀ ^ (2 * i) * p.coeff (i + 1)) := by
        have h0 := (mul_eq_zero.mp hfac).resolve_left (pow_ne_zero 2 hd₀_ne)
        exact eq_neg_of_add_eq_zero_left h0
      rw [hci_eq]
      have hexp : henselExp (i + 1) = 2 * i + 1 := by unfold henselExp; simp; omega
      rw [hexp]
      calc (H.leadingCoeff.eval β) ^ t *
            (-evalZT β u W * ((H.leadingCoeff.eval β) ^ (ℓ * t) *
              -(evalZT β u (evalX0 R).derivative * d₀ ^ (2 * i) * p.coeff (i + 1))))
          = ((H.leadingCoeff.eval β) ^ ((ℓ + 1) * t) *
              (evalZT β u W * evalZT β u (evalX0 R).derivative)) *
              d₀ ^ (2 * i) * p.coeff (i + 1) := by
            have hpow : (H.leadingCoeff.eval β) ^ ((ℓ + 1) * t) =
                (H.leadingCoeff.eval β) ^ t * (H.leadingCoeff.eval β) ^ (ℓ * t) := by
              rw [← pow_add]; congr 1; ring
            rw [hpow]; ring
        _ = d₀ * d₀ ^ (2 * i) * p.coeff (i + 1) := by
            rw [hW_rel, ← hD₀_val]
        _ = d₀ ^ (2 * i + 1) * p.coeff (i + 1) := by
            rw [← pow_succ', show 2 * i + 1 = (2 * i) + 1 by rfl]

/-! ## 5. Cleared-Denominator Residual `henselResidual` -/

/-- Cleared-denominator degree-`< d` Hensel polynomial in `((F[Z])[T])[X]`:
`∑_{s < d} (D₀ ^ (2 * d - henselExp s) * b s) * X ^ s`. -/
noncomputable def henselScaledPoly (b : ℕ → (F[X])[X]) (D₀ : F[X]) (d : ℕ) : ((F[X])[X])[X] :=
  ∑ s ∈ Finset.range d, monomial s (C (D₀ ^ (2 * d - henselExp s)) * b s)

theorem henselScaledPoly_eval (b : ℕ → (F[X])[X]) (D₀ : F[X]) (d : ℕ)
    {β u : F} {p : F[X]} (hpdeg : p.degree < d)
    (hb : ∀ s < d, evalZT β u (b s) = (D₀.eval β) ^ (henselExp s) * p.coeff s) :
    mapEvalZT β u (henselScaledPoly b D₀ d) = C ((D₀.eval β) ^ (2 * d)) * p := by
  ext s
  unfold henselScaledPoly mapEvalZT
  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  have hterm : ∀ k ∈ Finset.range d,
      ((Polynomial.mapRingHom (evalZT β u)) (monomial k (C (D₀ ^ (2 * d - henselExp k)) * b k))).coeff s =
        if k = s then (D₀.eval β) ^ (2 * d) * p.coeff s else 0 := by
    intro k hk
    have hklt : k < d := Finset.mem_range.mp hk
    rw [Polynomial.coe_mapRingHom, Polynomial.map_monomial, Polynomial.coeff_monomial]
    split_ifs with hks
    · subst hks
      rw [map_mul, evalZT_C, Polynomial.eval_pow, hb k hklt, ← mul_assoc, ← pow_add]
      have hle : henselExp k ≤ 2 * d := by unfold henselExp; split_ifs <;> omega
      rw [Nat.sub_add_cancel hle]
    · rfl
  rw [Finset.sum_congr rfl hterm]
  by_cases hs : s < d
  · rw [Finset.sum_eq_single s]
    · simp
    · intro k _ hne; simp [hne]
    · intro hnm; exact absurd (Finset.mem_range.mpr hs) hnm
  · rw [Finset.sum_eq_zero]
    · have hp0 : p.coeff s = 0 := by
        by_cases hpz : p = 0
        · simp [hpz]
        · have hnat := (Polynomial.natDegree_lt_iff_degree_lt hpz).mpr hpdeg
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hp0, mul_zero]
    · intro k hk
      have hklt : k < d := Finset.mem_range.mp hk
      have hne : k ≠ s := by omega
      simp [hne]

/-- Raw (unreduced in `T`) cleared-denominator residual `D₀^{2 d ℓ} * R(Z, X, P_{<d}(X))`. -/
noncomputable def henselResidualRaw (R : ((F[X])[X])[X]) (b : ℕ → (F[X])[X])
    (D₀ : F[X]) (d : ℕ) : ((F[X])[X])[X] :=
  ∑ j ∈ Finset.range (R.natDegree + 1),
    C (C (D₀ ^ (2 * d * (R.natDegree - j)))) *
      ((R.coeff j).map C) * (henselScaledPoly b D₀ d) ^ j

/-- `T`-reduced cleared-denominator residual: each `X`-coefficient `q` of
`henselResidualRaw` is reduced by `pseudoRem H (R.natDegree * H.natDegree)`. -/
noncomputable def henselResidualCoeff (R : ((F[X])[X])[X]) (H : (F[X])[X])
    (b : ℕ → (F[X])[X]) (D₀ : F[X]) (d q : ℕ) : (F[X])[X] :=
  pseudoRem H (R.natDegree * H.natDegree) ((henselResidualRaw R b D₀ d).coeff q)

theorem henselResidualCoeff_degT_lt {R : ((F[X])[X])[X]} {H : (F[X])[X]}
    {b : ℕ → (F[X])[X]} {D₀ : F[X]} {d : ℕ}
    (hHt : 1 ≤ H.natDegree) (hbT : ∀ s < d, (b s).natDegree ≤ H.natDegree) (q : ℕ) :
    (henselResidualCoeff R H b D₀ d q).natDegree < H.natDegree := by
  have hP_T : PolyTDegLE H.natDegree (henselScaledPoly b D₀ d) := by
    unfold henselScaledPoly
    refine polyTDegLE_sum _ _ fun s hs => polyTDegLE_monomial s ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans (hbT s (Finset.mem_range.mp hs))
  have hraw_T : PolyTDegLE (R.natDegree * H.natDegree) (henselResidualRaw R b D₀ d) := by
    unfold henselResidualRaw
    refine polyTDegLE_sum _ _ fun j hj => ?_
    have hj_le : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : PolyTDegLE 0 (C (C (D₀ ^ (2 * d * (R.natDegree - j)))) * (R.coeff j).map C) := by
      simpa using polyTDegLE_mul
        (polyTDegLE_C (a := C (D₀ ^ (2 * d * (R.natDegree - j)))) (M := 0)
          (Polynomial.natDegree_C _).le)
        (show PolyTDegLE 0 ((R.coeff j).map C) from fun k => by
          rw [Polynomial.coeff_map]; exact (Polynomial.natDegree_C _).le)
    have h2 := polyTDegLE_mul h1 (polyTDegLE_pow hP_T j)
    refine polyTDegLE_mono ?_ h2
    simpa using Nat.mul_le_mul_right H.natDegree hj_le
  exact pseudoRem_natDegree_lt hHt (R.natDegree * H.natDegree) _
    (lt_of_le_of_lt (hraw_T q) (by omega))

theorem henselResidualCoeff_degZ_le {R : ((F[X])[X])[X]} {H : (F[X])[X]}
    {b : ℕ → (F[X])[X]} {D₀ : F[X]} {d D_Z B_C : ℕ}
    (hRdegZ : ∀ j i, ((R.coeff j).coeff i).natDegree ≤ D_Z)
    (hHdegZ : CoeffDegLE D_Z H)
    (hD₀ : D₀.natDegree ≤ B_C)
    (hbZ : ∀ s < d, CoeffDegLE (henselExp s * B_C) (b s)) (q : ℕ) :
    CoeffDegLE (D_Z + 2 * d * R.natDegree * B_C + R.natDegree * H.natDegree * D_Z)
      (henselResidualCoeff R H b D₀ d q) := by
  have hP_Z : ∀ k, CoeffDegLE (2 * d * B_C) ((henselScaledPoly b D₀ d).coeff k) := by
    intro k
    unfold henselScaledPoly
    rw [Polynomial.finsetSum_coeff]
    refine coeffDegLE_sum _ _ fun s hs => ?_
    rw [Polynomial.coeff_monomial]
    split_ifs with hsk
    · have hslt : s < d := Finset.mem_range.mp hs
      have hle : henselExp s ≤ 2 * d := by unfold henselExp; split_ifs <;> omega
      have h1 : (D₀ ^ (2 * d - henselExp s)).natDegree ≤ (2 * d - henselExp s) * B_C :=
        (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ hD₀)
      have h2 := coeffDegLE_C_mul h1 (hbZ s hslt)
      refine coeffDegLE_mono ?_ h2
      have : (2 * d - henselExp s) * B_C + henselExp s * B_C = 2 * d * B_C := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hle]
      omega
    · exact coeffDegLE_zero _
  have hP_pow_Z : ∀ j k, CoeffDegLE (j * (2 * d * B_C)) (((henselScaledPoly b D₀ d) ^ j).coeff k) := by
    intro j
    induction j with
    | zero =>
      intro k
      rw [pow_zero, Polynomial.coeff_one]
      split_ifs
      · simpa using coeffDegLE_C (F := F) (a := 1) (B := 0) (by simp)
      · exact coeffDegLE_zero _
    | succ j ih =>
      intro k
      rw [pow_succ, Polynomial.coeff_mul]
      refine coeffDegLE_sum _ _ fun x _ => ?_
      have hm := coeffDegLE_mul (ih x.1) (hP_Z x.2)
      refine coeffDegLE_mono ?_ hm
      rw [Nat.add_mul, one_mul]
  have hraw_Z : CoeffDegLE (D_Z + 2 * d * R.natDegree * B_C)
      ((henselResidualRaw R b D₀ d).coeff q) := by
    unfold henselResidualRaw
    rw [Polynomial.finsetSum_coeff]
    refine coeffDegLE_sum _ _ fun j hj => ?_
    have hj_le : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Polynomial.coeff_mul]
    refine coeffDegLE_sum _ _ fun x _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]
    have hD_pow : (D₀ ^ (2 * d * (R.natDegree - j))).natDegree ≤ 2 * d * (R.natDegree - j) * B_C :=
      (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left _ hD₀)
    have hleft : CoeffDegLE (2 * d * (R.natDegree - j) * B_C + D_Z)
        (C (D₀ ^ (2 * d * (R.natDegree - j))) * C ((R.coeff j).coeff x.1)) :=
      coeffDegLE_C_mul hD_pow (coeffDegLE_C (hRdegZ j x.1))
    have hm := coeffDegLE_mul hleft (hP_pow_Z j x.2)
    refine coeffDegLE_mono ?_ hm
    have hring : 2 * d * (R.natDegree - j) * B_C + D_Z + j * (2 * d * B_C) =
        D_Z + 2 * d * ((R.natDegree - j) + j) * B_C := by ring
    rw [hring, Nat.sub_add_cancel hj_le]
  exact coeffDegLE_pseudoRem hHdegZ (R.natDegree * H.natDegree) _ _ hraw_Z

theorem henselResidualCoeff_evalZT_eq {R : ((F[X])[X])[X]} {H : (F[X])[X]}
    {b : ℕ → (F[X])[X]} {D₀ : F[X]} {d : ℕ}
    {β u : F} (hHβ : evalZT β u H = 0)
    {p : F[X]} (hpdeg : p.degree < d)
    (hb : ∀ s < d, evalZT β u (b s) = (D₀.eval β) ^ (henselExp s) * p.coeff s) (q : ℕ) :
    evalZT β u (henselResidualCoeff R H b D₀ d q) =
      (H.leadingCoeff.eval β) ^ (R.natDegree * H.natDegree) *
        ((D₀.eval β) ^ (2 * d * R.natDegree) * ((evalZR β R).eval p).coeff q) := by
  unfold henselResidualCoeff
  have hpr : evalZT β u (pseudoRem H (R.natDegree * H.natDegree) ((henselResidualRaw R b D₀ d).coeff q)) =
      (H.leadingCoeff.eval β) ^ (R.natDegree * H.natDegree) *
        evalZT β u ((henselResidualRaw R b D₀ d).coeff q) := by
    simpa [evalZT] using pseudoRem_eval₂ (Polynomial.evalRingHom β) u hHβ (R.natDegree * H.natDegree) _
  rw [hpr]
  congr 1
  have hmap_raw : mapEvalZT β u (henselResidualRaw R b D₀ d) =
      C ((D₀.eval β) ^ (2 * d * R.natDegree)) * (evalZR β R).eval p := by
    unfold henselResidualRaw
    rw [map_sum]
    have hP := henselScaledPoly_eval b D₀ d hpdeg hb
    have hR_eval : (evalZR β R).eval p =
        ∑ j ∈ Finset.range (R.natDegree + 1),
          ((R.coeff j).map (Polynomial.evalRingHom β)) * p ^ j := by
      have hdeg_le : (evalZR β R).natDegree ≤ R.natDegree := Polynomial.natDegree_map_le
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg_le)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [evalZR, Polynomial.coeff_map]
    rw [hR_eval, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ R.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [map_mul, map_mul, map_pow (mapEvalZT β u) (henselScaledPoly b D₀ d) j, hP, mul_pow,
      ← C_pow, ← pow_mul]
    have hC1 : mapEvalZT β u (C (C (D₀ ^ (2 * d * (R.natDegree - j))))) =
        C ((D₀.eval β) ^ (2 * d * (R.natDegree - j))) := by
      rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.map_C, evalZT_C, Polynomial.eval_pow]
    have hC2 : mapEvalZT β u ((R.coeff j).map C) = (R.coeff j).map (Polynomial.evalRingHom β) := by
      unfold mapEvalZT
      rw [Polynomial.coe_mapRingHom, Polynomial.map_map]
      congr 1; apply RingHom.ext; intro a; simp [evalZT_C]
    rw [hC1, hC2]
    have hpow_add : C ((D₀.eval β) ^ (2 * d * (R.natDegree - j))) *
        C ((D₀.eval β) ^ (2 * d * j)) = C ((D₀.eval β) ^ (2 * d * R.natDegree)) := by
      rw [← map_mul, ← pow_add]
      congr 2
      calc 2 * d * (R.natDegree - j) + 2 * d * j = 2 * d * ((R.natDegree - j) + j) := by ring
        _ = 2 * d * R.natDegree := by rw [Nat.sub_add_cancel hj_le]
    calc C ((D₀.eval β) ^ (2 * d * (R.natDegree - j))) *
          (R.coeff j).map (Polynomial.evalRingHom β) *
          (C ((D₀.eval β) ^ (2 * d * j)) * p ^ j)
        = (C ((D₀.eval β) ^ (2 * d * (R.natDegree - j))) * C ((D₀.eval β) ^ (2 * d * j))) *
            ((R.coeff j).map (Polynomial.evalRingHom β) * p ^ j) := by ring
      _ = C ((D₀.eval β) ^ (2 * d * R.natDegree)) *
            ((R.coeff j).map (Polynomial.evalRingHom β) * p ^ j) := by rw [hpow_add]
  have hcoeff := congrArg (fun f : F[X] => f.coeff q) hmap_raw
  rw [mapEvalZT, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_C_mul] at hcoeff
  exact hcoeff

end HenselCore

end HenselLift

end CertiFri

