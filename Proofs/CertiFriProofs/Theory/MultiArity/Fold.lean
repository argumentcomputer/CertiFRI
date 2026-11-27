import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CertiFriProofs.Theory.Fold
import CertiFriProofs.Theory.Domain
import CertiFriProofs.Theory.ProximityGap.UniqueDecoding
import CertiFriProofs.Theory.ProximityGap.UniqueDecodingMCA
import CertiFriProofs.Theory.ProximityGap.JohnsonMCA

/-!
# Multi-arity (`m = 2 ^ a`) FRI folding algebra and proximity gaps

Generalizes `Theory/Fold.lean` and `Theory/StepMCA.lean` from binary folding
(`m = 2`) to arbitrary fold arity `m` (in particular `m = 2 ^ a` for `a ≥ 1`,
covering `a ∈ {1, 2, 3}`, i.e. fold factors `2, 4, 8`).

## Main results

1. **Polynomial `m`-splitting & unfolding:**
   * `splitPart m p j`, `unfoldPolyArity m v`, `foldPolyArity m β p`
   * `unfoldPolyArity_splitPart`, `degree_unfoldPolyArity_lt`, `degree_foldPolyArity_lt`
2. **Coset DFT decomposition (`partAt` and `foldAtPow`):**
   * `partAt ζ m f j x = (∑ r : Fin m, (ζ ^ r * x)⁻¹ ^ j * f (ζ ^ r * x)) / m`
   * `foldAtPow ζ m f β x = ∑ j : Fin m, β ^ j * partAt ζ m f j x`
   * `partAt_eq_of_pow_eq`, `foldAtPow_eq_of_pow_eq`: coset invariance
   * `sum_pow_mul_partAt`: exact pointwise reconstruction `∑ j, x ^ j * partAt ζ m f j x = f x`
   * `foldAtPow_two_eq_foldAt`: agrees identically with binary `foldAt` at `m = 2, ζ = -1`
3. **Iterated binary fold equals `2 ^ a`-ary fold (`foldRowMultiM_eq_foldAtPow`):**
   * Proves via `foldAt_eq_eval_foldPoly` and `eval_eq_evenPart_add_mul_oddPart`
     that `a` passes of binary `foldRow` with `β, β ^ 2, …, β ^ (2 ^ (a - 1))`
     on a bit-reversed `2 ^ a`-coset row equal `foldAtPow (ω ^ 2 ^ (n - a)) (2 ^ a) c β x₀`.
4. **Multi-arity proximity gaps (`StepMCAArity`):**
   * `StepMCAArity.of_curveMCA`: `(m + 1)`-term `CurveMCA` on `D'` implies `StepMCAArity`
     on `PowStep m ζ D D'` with the exact same threshold and error.
   * `stepMCAArity_ud`: **100% unconditional** unique-decoding multi-arity folding
     proximity gap with error `m * ((1 + δ) * |D'|) / |F| = ((1 + δ) * |D|) / |F|`
     — completely independent of `m` (`m * |D'| = |D|` cancels `m`!).
   * `stepMCAArity_of_curveListCA_rel`: Johnson-regime multi-arity folding proximity
     gap from `CurveListCA` (discharged unconditionally over `Fp3Model` by
     `curveListCA_fp3`), where the Johnson list-decoding term `m * L_J * (1 - θ) * |D'|`
     likewise cancels `m` to `L_J * (1 - θ) * |D|`.
-/

namespace CertiFri

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## 1. Polynomial `m`-splitting and unfolding -/

section PolySplit

/-- Iterated `divX`: shifts polynomial coefficients down by `j`. -/
noncomputable def iterDivX : ℕ → F[X] → F[X]
  | 0, p => p
  | j + 1, p => iterDivX j (divX p)

theorem coeff_iterDivX (p : F[X]) (j n : ℕ) :
    (iterDivX j p).coeff n = p.coeff (n + j) := by
  induction j generalizing p with
  | zero => simp [iterDivX]
  | succ j ih =>
    rw [iterDivX, ih, coeff_divX]
    ring_nf

/-- The `j`-th `m`-decimated part of `p`: `(splitPart m p j).coeff n = p.coeff (m * n + j)`. -/
noncomputable def splitPart (m : ℕ) (p : F[X]) (j : ℕ) : F[X] :=
  contract m (iterDivX j p)

theorem coeff_splitPart {m : ℕ} (hm : m ≠ 0) (p : F[X]) (j n : ℕ) :
    (splitPart m p j).coeff n = p.coeff (m * n + j) := by
  rw [splitPart, coeff_contract hm, coeff_iterDivX, mul_comm]

theorem degree_splitPart_lt {m d j : ℕ} {p : F[X]} (hm : 0 < m)
    (hp : p.degree < (m * d : ℕ)) : (splitPart m p j).degree < d := by
  rw [degree_lt_iff_coeff_zero] at hp ⊢
  intro n hn
  rw [coeff_splitPart (Nat.pos_iff_ne_zero.mp hm)]
  exact hp _ (by nlinarith)

/-- Reconstruct a polynomial from its `m` decimated parts:
`∑ j : Fin m, X ^ j * (v j).comp (X ^ m)`. -/
noncomputable def unfoldPolyArity (m : ℕ) (v : Fin m → F[X]) : F[X] :=
  ∑ j : Fin m, X ^ j.val * (v j).comp (X ^ m)

theorem eval_unfoldPolyArity (m : ℕ) (v : Fin m → F[X]) (x : F) :
    (unfoldPolyArity m v).eval x = ∑ j : Fin m, x ^ j.val * (v j).eval (x ^ m) := by
  simp [unfoldPolyArity, eval_finsetSum, eval_comp]

private theorem coeff_X_pow_mul_comp_X_pow {m : ℕ} (hm : 0 < m) (q : F[X]) (j k : ℕ) :
    (X ^ j * q.comp (X ^ m)).coeff k =
      if j ≤ k ∧ m ∣ (k - j) then q.coeff ((k - j) / m) else 0 := by
  rw [← expand_eq_comp_X_pow, coeff_X_pow_mul']
  by_cases hjk : j ≤ k
  · simp [hjk, coeff_expand hm]
  · simp [hjk]

theorem degree_unfoldPolyArity_lt {m d : ℕ} {v : Fin m → F[X]} (hm : 0 < m)
    (hv : ∀ j : Fin m, (v j).degree < d) :
    (unfoldPolyArity m v).degree < (m * d : ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [unfoldPolyArity, finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_X_pow_mul_comp_X_pow hm]
  split_ifs with h
  · have hq : d ≤ (k - j.val) / m := by
      have hj := j.isLt
      have hdiv : m * ((k - j.val) / m) = k - j.val := Nat.mul_div_cancel' h.2
      by_contra hlt
      have hle : (k - j.val) / m + 1 ≤ d := by omega
      have hmul : m * ((k - j.val) / m + 1) ≤ m * d := Nat.mul_le_mul_left m hle
      rw [mul_add, mul_one, hdiv] at hmul
      omega
    exact (degree_lt_iff_coeff_zero (v j) d).mp (hv j) _ hq
  · rfl

theorem unfoldPolyArity_splitPart {m : ℕ} (hm : 0 < m) (p : F[X]) :
    unfoldPolyArity m (fun j => splitPart m p j.val) = p := by
  ext k
  rw [unfoldPolyArity, finsetSum_coeff]
  let j₀ : Fin m := ⟨k % m, Nat.mod_lt k hm⟩
  rw [Finset.sum_eq_single j₀]
  · rw [coeff_X_pow_mul_comp_X_pow hm]
    have hle : k % m ≤ k := Nat.mod_le k m
    have hdvd : m ∣ k - k % m := by
      refine ⟨k / m, ?_⟩
      have := Nat.div_add_mod k m
      omega
    have hq : (k - k % m) / m = k / m := by
      have hsub : k - k % m = m * (k / m) := by
        have := Nat.div_add_mod k m; omega
      rw [hsub, Nat.mul_div_cancel_left _ hm]
    simp only [j₀, hle, hdvd, and_self, ↓reduceIte, hq,
      coeff_splitPart (Nat.pos_iff_ne_zero.mp hm)]
    congr 1
    exact Nat.div_add_mod k m
  · intro j _ hne
    rw [coeff_X_pow_mul_comp_X_pow hm]
    split_ifs with h
    · exfalso
      obtain ⟨hjk, q, hq⟩ := h
      have hmod : k % m = j.val := by
        have hk : k = j.val + m * q := by omega
        rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
      exact hne (Fin.ext hmod.symm)
    · rfl
  · intro hmem; exact absurd (Finset.mem_univ j₀) hmem

/-- The `m`-ary fold of a polynomial `p` with challenge `β`:
`∑ j : Fin m, C (β ^ j) * splitPart m p j`. -/
noncomputable def foldPolyArity (m : ℕ) (β : F) (p : F[X]) : F[X] :=
  ∑ j : Fin m, C (β ^ j.val) * splitPart m p j.val

theorem degree_foldPolyArity_lt {m d : ℕ} {p : F[X]} (hm : 0 < m) (β : F)
    (hp : p.degree < (m * d : ℕ)) : (foldPolyArity m β p).degree < d := by
  unfold foldPolyArity
  exact mem_degreeLT.mp ((degreeLT F d).sum_mem fun j _ =>
    mem_degreeLT.mpr (Fold.degree_C_mul_lt (β ^ j.val) (degree_splitPart_lt hm hp)))

end PolySplit

/-! ## 2. Coset DFT decomposition (`partAt` and `foldAtPow`) -/

section CosetDft

/-- The `j`-th `m`-split component of `f` on the `m`-coset of `x`, computed via
the inverse DFT with primitive `m`-th root of unity `ζ`. -/
def partAt (ζ : F) (m : ℕ) (f : F → F) (j : ℕ) (x : F) : F :=
  (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * f (ζ ^ r.val * x)) / (m : F)

/-- The `m`-ary fold of `f` with challenge `β` on the `m`-coset of `x`:
`∑ j : Fin m, β ^ j * partAt ζ m f j x`. -/
def foldAtPow (ζ : F) (m : ℕ) (f : F → F) (β x : F) : F :=
  ∑ j : Fin m, β ^ j.val * partAt ζ m f j.val x

/-- Multiplying `x` by `ζ` shifts the DFT sum cyclically, leaving `partAt` invariant. -/
theorem partAt_mul_zeta {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (f : F → F) (j : ℕ) (x : F) :
    partAt ζ m f j (ζ * x) = partAt ζ m f j x := by
  unfold partAt
  congr 1
  let e : Fin m ≃ Fin m :=
    { toFun := fun r =>
        if h : r.val + 1 < m then ⟨r.val + 1, h⟩ else ⟨0, hm⟩
      invFun := fun r =>
        if h : r.val = 0 then ⟨m - 1, by omega⟩ else ⟨r.val - 1, by omega⟩
      left_inv := fun r => by
        by_cases h1 : r.val + 1 < m
        · simp only [dite_eq_left h1]
          have h2 : r.val + 1 ≠ 0 := by omega
          simp only [dite_eq_right h2]
          ext; simp
        · simp only [dite_eq_right h1, ↓reduceDIte]
          exact Fin.ext (by show m - 1 = r.val; omega)
      right_inv := fun r => by
        by_cases h1 : r.val = 0
        · simp only [dite_eq_left h1]
          have h2 : ¬ (m - 1 + 1 < m) := by omega
          simp only [dite_eq_right h2]
          ext; dsimp only; omega
        · simp only [dite_eq_right h1]
          have h2 : r.val - 1 + 1 < m := by omega
          simp only [dite_eq_left h2]
          ext; dsimp only; omega }
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hpow : ζ ^ (e.symm r).val * ζ = ζ ^ r.val := by
    dsimp only [e, Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
    split_ifs with h
    · rw [h, pow_zero, ← pow_succ, Nat.sub_add_cancel hm, hζ.pow_eq_one]
    · rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [← mul_assoc, hpow]

theorem partAt_mul_zeta_pow {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (f : F → F) (j k : ℕ) (x : F) :
    partAt ζ m f j (ζ ^ k * x) = partAt ζ m f j x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, partAt_mul_zeta hζ hm, ih]

theorem exists_zeta_pow_eq_of_pow_eq {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    {x y : F} (hx : x ≠ 0) (hxy : x ^ m = y ^ m) :
    ∃ k < m, y = ζ ^ k * x := by
  have hpow : (y * x⁻¹) ^ m = 1 := by
    rw [mul_pow, inv_pow, ← hxy, mul_inv_cancel₀ (pow_ne_zero m hx)]
  have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp hm⟩
  obtain ⟨k, hk, hzk⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨k, hk, ?_⟩
  rw [hzk, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem partAt_eq_of_pow_eq {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (f : F → F) (j : ℕ) {x y : F} (hx : x ≠ 0) (hxy : x ^ m = y ^ m) :
    partAt ζ m f j x = partAt ζ m f j y := by
  obtain ⟨k, -, rfl⟩ := exists_zeta_pow_eq_of_pow_eq hζ hm hx hxy
  exact (partAt_mul_zeta_pow hζ hm f j k x).symm

theorem foldAtPow_eq_of_pow_eq {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm : 0 < m)
    (f : F → F) (β : F) {x y : F} (hx : x ≠ 0) (hxy : x ^ m = y ^ m) :
    foldAtPow ζ m f β x = foldAtPow ζ m f β y := by
  unfold foldAtPow
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partAt_eq_of_pow_eq hζ hm f j.val hx hxy]

/-- Orthogonality of powers of a primitive `m`-th root of unity. -/
theorem sum_zeta_pow_eq {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (k : ℕ) :
    (∑ r : Fin m, (ζ ^ k) ^ r.val) = if m ∣ k then (m : F) else 0 := by
  by_cases hdvd : m ∣ k
  · obtain ⟨q, rfl⟩ := hdvd
    rw [ite_eq_left ⟨q, rfl⟩]
    have h1 : ζ ^ (m * q) = 1 := by rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [h1]
  · rw [ite_eq_right hdvd]
    have hne : ζ ^ k ≠ 1 := by
      intro h1
      exact hdvd (hζ.dvd_of_pow_eq_one k h1)
    have hpow : (ζ ^ k) ^ m = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    have hgeom : (∑ r : Fin m, (ζ ^ k) ^ r.val) * (ζ ^ k - 1) = (ζ ^ k) ^ m - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun r => (ζ ^ k) ^ r)]
      exact geom_sum_mul (ζ ^ k) m
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

theorem sum_zeta_inv_pow_eq {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (k : ℕ) :
    (∑ j : Fin m, ((ζ ^ k)⁻¹) ^ j.val) = if m ∣ k then (m : F) else 0 := by
  have hζinv : IsPrimitiveRoot ζ⁻¹ m := hζ.inv
  have hinv_pow : ∀ j : ℕ, ((ζ ^ k)⁻¹) ^ j = ((ζ⁻¹) ^ k) ^ j := fun j => by
    rw [← inv_pow]
  simp_rw [hinv_pow]
  exact sum_zeta_pow_eq hζinv k

/-- Exact reconstruction of `f x` from its `m` coset components `partAt ζ m f j x`. -/
theorem sum_pow_mul_partAt {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm_pos : 0 < m)
    (hm : (m : F) ≠ 0) (f : F → F) {x : F} (hx : x ≠ 0) :
    ∑ j : Fin m, x ^ j.val * partAt ζ m f j.val x = f x := by
  unfold partAt
  simp_rw [mul_div_assoc', ← Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ r : Fin m,
      (∑ j : Fin m, x ^ j.val * ((ζ ^ r.val * x)⁻¹ ^ j.val * f (ζ ^ r.val * x))) =
        (if r.val = 0 then (m : F) else 0) * f (ζ ^ r.val * x) := by
    intro r
    have hsimp : ∀ j : Fin m,
        x ^ j.val * ((ζ ^ r.val * x)⁻¹ ^ j.val * f (ζ ^ r.val * x)) =
          ((ζ ^ r.val)⁻¹) ^ j.val * f (ζ ^ r.val * x) := by
      intro j
      rw [mul_inv, mul_pow, ← mul_assoc, ← mul_assoc]
      congr 1
      have hxx : x ^ j.val * x⁻¹ ^ j.val = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
      calc x ^ j.val * (ζ ^ r.val)⁻¹ ^ j.val * x⁻¹ ^ j.val
          = ((ζ ^ r.val)⁻¹ ^ j.val) * (x ^ j.val * x⁻¹ ^ j.val) := by ring
        _ = (ζ ^ r.val)⁻¹ ^ j.val := by rw [hxx, mul_one]
    simp_rw [hsimp, ← Finset.sum_mul]
    congr 1
    rw [sum_zeta_inv_pow_eq hζ r.val]
    have hdvd : m ∣ r.val ↔ r.val = 0 :=
      ⟨fun h => Nat.eq_zero_of_dvd_of_lt h r.isLt, fun h => by rw [h]; exact dvd_zero m⟩
    simp [hdvd]
  simp_rw [hterm]
  rw [Finset.sum_eq_single ⟨0, hm_pos⟩]
  · simp [mul_div_cancel_left₀ _ hm]
  · intro r _ hne
    have hr0 : r.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [hr0]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Where `f` agrees with `p` on the `m`-coset of `x`, `partAt ζ m f j x` equals
`(splitPart m p j).eval (x ^ m)`. -/
theorem partAt_eq_eval_splitPart {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm_pos : 0 < m)
    (hm : (m : F) ≠ 0) {f : F → F} {p : F[X]} {x : F} (hx : x ≠ 0)
    (h : ∀ r : Fin m, f (ζ ^ r.val * x) = p.eval (ζ ^ r.val * x)) {j : ℕ} (hj : j < m) :
    partAt ζ m f j x = (splitPart m p j).eval (x ^ m) := by
  unfold partAt
  have hpeval : ∀ r : Fin m,
      p.eval (ζ ^ r.val * x) =
        ∑ k : Fin m, (ζ ^ r.val * x) ^ k.val * (splitPart m p k.val).eval (x ^ m) := by
    intro r
    have hpow : (ζ ^ r.val * x) ^ m = x ^ m := by
      rw [mul_pow, pow_right_comm, hζ.pow_eq_one, one_pow, one_mul]
    conv_lhs => rw [← unfoldPolyArity_splitPart hm_pos p]
    rw [eval_unfoldPolyArity]
    refine Finset.sum_congr rfl fun k _ => by rw [hpow]
  have hsum : (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * f (ζ ^ r.val * x)) =
      (m : F) * (splitPart m p j).eval (x ^ m) := by
    calc (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * f (ζ ^ r.val * x))
        = ∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j *
            ∑ k : Fin m, (ζ ^ r.val * x) ^ k.val * (splitPart m p k.val).eval (x ^ m) :=
          Finset.sum_congr rfl fun r _ => by rw [h r, hpeval r]
      _ = ∑ k : Fin m,
            (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ k.val) *
              (splitPart m p k.val).eval (x ^ m) := by
          simp_rw [Finset.mul_sum, ← mul_assoc]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => by rw [← Finset.sum_mul]
      _ = (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ j) *
            (splitPart m p j).eval (x ^ m) := by
          rw [Finset.sum_eq_single ⟨j, hj⟩]
          · intro k _ hne
            have hinner : (∑ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ k.val) = 0 := by
              have hzeta_ne : ζ ≠ 0 := hζ.ne_zero (Nat.pos_iff_ne_zero.mp hm_pos)
              by_cases hkj : j ≤ k.val
              · have hterm : ∀ r : Fin m,
                    (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ k.val =
                      (ζ ^ (k.val - j)) ^ r.val * x ^ (k.val - j) := by
                  intro r
                  have hne_rx : ζ ^ r.val * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hzeta_ne) hx
                  have hsplit : (ζ ^ r.val * x) ^ k.val =
                      (ζ ^ r.val * x) ^ j * (ζ ^ r.val * x) ^ (k.val - j) := by
                    rw [← pow_add, Nat.add_sub_cancel' hkj]
                  rw [hsplit, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hne_rx),
                    one_mul, mul_pow, pow_right_comm]
                simp_rw [hterm, ← Finset.sum_mul]
                rw [sum_zeta_pow_eq hζ (k.val - j)]
                have hndvd : ¬ m ∣ (k.val - j) := by
                  intro hd
                  have hkpos : 0 < k.val - j := by
                    have : k.val ≠ j := fun e => hne (Fin.ext e)
                    omega
                  have := Nat.le_of_dvd hkpos hd
                  omega
                simp [hndvd]
              · have hjk : k.val < j := lt_of_not_ge hkj
                have hterm : ∀ r : Fin m,
                    (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ k.val =
                      ((ζ⁻¹) ^ (j - k.val)) ^ r.val * (x⁻¹) ^ (j - k.val) := by
                  intro r
                  have hne_rx : ζ ^ r.val * x ≠ 0 := mul_ne_zero (pow_ne_zero _ hzeta_ne) hx
                  have hsplit : (ζ ^ r.val * x)⁻¹ ^ j =
                      (ζ ^ r.val * x)⁻¹ ^ (j - k.val) * (ζ ^ r.val * x)⁻¹ ^ k.val := by
                    rw [← pow_add, Nat.sub_add_cancel (le_of_lt hjk)]
                  have hcan : (ζ ^ r.val * x)⁻¹ ^ k.val * (ζ ^ r.val * x) ^ k.val = 1 := by
                    rw [← mul_pow, inv_mul_cancel₀ hne_rx, one_pow]
                  rw [hsplit, mul_assoc, hcan, mul_one, mul_inv, mul_pow, ← inv_pow,
                    pow_right_comm]
                simp_rw [hterm, ← Finset.sum_mul]
                have hζinv : IsPrimitiveRoot ζ⁻¹ m := hζ.inv
                rw [sum_zeta_pow_eq hζinv (j - k.val)]
                have hndvd : ¬ m ∣ (j - k.val) := by
                  intro hd
                  have := Nat.le_of_dvd (by omega) hd
                  omega
                simp [hndvd]
            rw [hinner, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = (m : F) * (splitPart m p j).eval (x ^ m) := by
          congr 1
          have h1 : ∀ r : Fin m, (ζ ^ r.val * x)⁻¹ ^ j * (ζ ^ r.val * x) ^ j = 1 := fun r => by
            have hne_rx : ζ ^ r.val * x ≠ 0 :=
              mul_ne_zero (pow_ne_zero _ (hζ.ne_zero (Nat.pos_iff_ne_zero.mp hm_pos))) hx
            rw [← mul_pow, inv_mul_cancel₀ hne_rx, one_pow]
          rw [Finset.sum_congr rfl fun r _ => h1 r]
          simp
  rw [hsum, mul_div_cancel_left₀ _ hm]

theorem foldAtPow_eq_eval_foldPolyArity {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m)
    (hm_pos : 0 < m) (hm : (m : F) ≠ 0) {f : F → F} {p : F[X]} (β : F) {x : F} (hx : x ≠ 0)
    (h : ∀ r : Fin m, f (ζ ^ r.val * x) = p.eval (ζ ^ r.val * x)) :
    foldAtPow ζ m f β x = (foldPolyArity m β p).eval (x ^ m) := by
  unfold foldAtPow foldPolyArity
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, partAt_eq_eval_splitPart hζ hm_pos hm hx h j.isLt]

theorem eq_eval_unfoldPolyArity {ζ : F} {m : ℕ} (hζ : IsPrimitiveRoot ζ m) (hm_pos : 0 < m)
    (hm : (m : F) ≠ 0) {f : F → F} {v : Fin m → F[X]} {x : F} (hx : x ≠ 0)
    (h : ∀ j : Fin m, partAt ζ m f j.val x = (v j).eval (x ^ m)) :
    f x = (unfoldPolyArity m v).eval x := by
  rw [eval_unfoldPolyArity, ← sum_pow_mul_partAt hζ hm_pos hm f hx]
  refine Finset.sum_congr rfl fun j _ => by rw [h j]

/-- At `m = 2, ζ = -1`, `foldAtPow` agrees identically with binary `foldAt`. -/
theorem foldAtPow_two_eq_foldAt (h2 : (2 : F) ≠ 0) (f : F → F) (β : F) {x : F} (hx : x ≠ 0) :
    foldAtPow (-1) 2 f β x = foldAt f β x := by
  unfold foldAtPow partAt foldAt evenAt oddAt
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_mul, Nat.cast_ofNat]
  field_simp
  ring

end CosetDft

/-! ## 3. `PowStep`, `GoodChallengeArity`, and unconditional multi-arity proximity gaps -/

section MultiStepMCA

/-- `D'` is the set of `m`-th powers of `D`, and `D` is closed under
multiplication by a primitive `m`-th root of unity `ζ`, so `x ↦ x ^ m` is
`m`-to-1 from `D` onto `D'`. -/
structure PowStep (m : ℕ) (ζ : F) (D D' : Finset F) : Prop where
  m_pos : 0 < m
  m_ne_zero : (m : F) ≠ 0
  prim : IsPrimitiveRoot ζ m
  ne_zero : ∀ x ∈ D, x ≠ 0
  mul_zeta_mem : ∀ x ∈ D, ζ * x ∈ D
  pow_mem : ∀ x ∈ D, x ^ m ∈ D'
  exists_pow : ∀ y ∈ D', ∃ x ∈ D, x ^ m = y

theorem PowStep.mul_zeta_pow_mem {m : ℕ} {ζ : F} {D D' : Finset F}
    (h : PowStep m ζ D D') {x : F} (hx : x ∈ D) (k : ℕ) : ζ ^ k * x ∈ D := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', mul_assoc]; exact h.mul_zeta_mem _ ih

/-- Above a subset `B ⊆ D'`, there are exactly `m * B.card` points in `D`. -/
theorem PowStep.card_filter_pow [DecidableEq F] {m : ℕ} {ζ : F} {D D' : Finset F}
    (h : PowStep m ζ D D') {B : Finset F} (hB : B ⊆ D') :
    (D.filter fun x => x ^ m ∈ B).card = m * B.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x ^ m)
    (s := D.filter fun x => x ^ m ∈ B) (t := B) fun x hx => (Finset.mem_filter.mp hx).2,
    mul_comm]
  refine Finset.sum_const_nat fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := h.exists_pow y (hB hy)
  have hfibre : ((D.filter fun a => a ^ m ∈ B).filter fun a => a ^ m = x ^ m) =
      (Finset.univ : Finset (Fin m)).image fun r => ζ ^ r.val * x := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro ha
      obtain ⟨k, hk, rfl⟩ := exists_zeta_pow_eq_of_pow_eq h.prim h.m_pos (h.ne_zero x hx) ha.2.symm
      exact ⟨⟨k, hk⟩, rfl⟩
    · rintro ⟨r, rfl⟩
      have hpow : (ζ ^ r.val * x) ^ m = x ^ m := by
        rw [mul_pow, pow_right_comm, h.prim.pow_eq_one, one_pow, one_mul]
      exact ⟨⟨h.mul_zeta_pow_mem hx r.val, hpow ▸ hy⟩, hpow⟩
  rw [hfibre, Finset.card_image_of_injective]
  · simp
  · intro r₁ r₂ hr
    have hmul := mul_right_cancel₀ (h.ne_zero x hx) hr
    exact Fin.ext (h.prim.pow_inj r₁.isLt r₂.isLt hmul)

theorem PowStep.card_eq {m : ℕ} {ζ : F} {D D' : Finset F} (h : PowStep m ζ D D') :
    D.card = m * D'.card := by
  classical
  rw [← h.card_filter_pow (Finset.Subset.refl D'), Finset.filter_true_of_mem h.pow_mem]

/-- Two-adic subgroups separated by `a ≥ 1` folding bits form a `PowStep (2 ^ a)`. -/
theorem powStep_twoAdicDomain [DecidableEq F] {ω : F} {n k a : ℕ}
    (hω : IsPrimitiveRoot ω (2 ^ n)) (ha : 0 < a) (hka : k + a ≤ n) :
    PowStep (2 ^ a) (ω ^ 2 ^ (n - a))
      (twoAdicDomain ω n k) (twoAdicDomain ω n (k + a)) := by
  have hn_pos : 0 < n := by omega
  have h2ne : (2 : F) ≠ 0 := Domain.two_ne_zero_of_isPrimitiveRoot hω hn_pos
  have hprim : IsPrimitiveRoot (ω ^ 2 ^ (n - a)) (2 ^ a) :=
    Domain.isPrimitiveRoot_generator hω (by omega)
  have hpow_eq : ∀ x : F, x ^ 2 ^ (n - k) = (x ^ 2 ^ a) ^ 2 ^ (n - (k + a)) := fun x => by
    rw [← pow_mul, ← pow_add]
    congr 2; omega
  refine ⟨by positivity, ?_, hprim, ?_, ?_, ?_, ?_⟩
  · push_cast; exact pow_ne_zero a h2ne
  · intro x hx h0
    rw [mem_twoAdicDomain_iff hω (by omega), h0, zero_pow (by positivity)] at hx
    exact zero_ne_one hx
  · intro x hx
    rw [mem_twoAdicDomain_iff hω (by omega)] at hx ⊢
    have hζpow : (ω ^ 2 ^ (n - a)) ^ 2 ^ (n - k) = 1 := by
      have hdvd : 2 ^ a ∣ 2 ^ (n - k) := Nat.pow_dvd_pow 2 (by omega)
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, pow_mul, hprim.pow_eq_one, one_pow]
    rw [mul_pow, hζpow, hx, one_mul]
  · intro x hx
    rw [mem_twoAdicDomain_iff hω (by omega)] at hx
    rw [mem_twoAdicDomain_iff hω hka, ← hpow_eq, hx]
  · intro y hy
    simp only [twoAdicDomain, Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨j, -, rfl⟩ := hy
    refine ⟨(ω ^ 2 ^ k) ^ j, ?_, ?_⟩
    · rw [mem_twoAdicDomain_iff hω (by omega), ← pow_mul, mul_comm, pow_mul,
        (Domain.isPrimitiveRoot_pow_two_pow hω (by omega)).pow_eq_one, one_pow]
    · rw [pow_right_comm, ← pow_mul ω, ← pow_add]

/-- The challenge `β` is good for the `m`-ary folding round on `(D, D')` with
committed word `c` on `D` and rolled-in input `ro` on `D'`. -/
def GoodChallengeArity (m : ℕ) (ζ : F) (D D' : Finset F) (d' : ℕ) (θ : ℝ)
    (ro c : F → F) (β : F) : Prop :=
  ∀ p : F[X], p.degree < d' → ∀ B ⊆ D', θ * D'.card ≤ B.card →
    (∀ x ∈ D, x ^ m ∈ B → foldAtPow ζ m c β x + β ^ m * ro (x ^ m) = p.eval (x ^ m)) →
    (∃ p₀ : F[X], p₀.degree < (m * d' : ℕ) ∧ ∀ x ∈ D, x ^ m ∈ B → c x = p₀.eval x) ∧
    (∃ p₁ : F[X], p₁.degree < d' ∧ ∀ y ∈ B, ro y = p₁.eval y)

/-- Mutual correlated agreement for one `m`-ary folding round with input `ro`. -/
def StepMCAArityFor [Fintype F] (m : ℕ) (ζ : F) (D D' : Finset F) (d' : ℕ) (θ ε : ℝ)
    (ro : F → F) : Prop :=
  ∀ c : F → F, ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
    ∀ β ∉ bad, GoodChallengeArity m ζ D D' d' θ ro c β

/-- `StepMCAArityFor` for every rolled-in input `ro`. -/
def StepMCAArity [Fintype F] (m : ℕ) (ζ : F) (D D' : Finset F) (d' : ℕ) (θ ε : ℝ) : Prop :=
  ∀ ro : F → F, StepMCAArityFor m ζ D D' d' θ ε ro

theorem nonneg_of_stepMCAArity [Fintype F] {m : ℕ} {ζ : F} {D D' : Finset F} {d' : ℕ} {θ ε : ℝ}
    (h : StepMCAArity m ζ D D' d' θ ε) : 0 ≤ ε := by
  obtain ⟨bad, hbad, -⟩ := h (fun _ => 0) (fun _ => 0)
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg bad.card).trans hbad) hF

theorem StepMCAArity.mono_error [Fintype F] {m : ℕ} {ζ : F} {D D' : Finset F} {d' : ℕ}
    {θ ε ε' : ℝ} (h : StepMCAArity m ζ D D' d' θ ε) (hle : ε ≤ ε') :
    StepMCAArity m ζ D D' d' θ ε' := by
  intro ro c
  obtain ⟨bad, hbad, hgood⟩ := h ro c
  exact ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)), hgood⟩

/-- **Multi-arity folding proximity gap from `(m + 1)`-term `CurveMCA`:**
`foldAtPow ζ m c β (s y) + β ^ m * ro y` is literally the `(m + 1)`-term
parameterized curve `∑ k : Fin (m + 1), β ^ k * u k y` where `u 0, …, u (m - 1)`
are the `m` coset components `partAt ζ m c j (s y)` and `u m = ro`. -/
theorem StepMCAArity.of_curveMCA [Fintype F] {m : ℕ} {ζ : F} {D D' : Finset F}
    (hstep : PowStep m ζ D D') {d' : ℕ} {θ ε : ℝ}
    (h : CurveMCA D' d' (m + 1) θ ε) :
    StepMCAArity m ζ D D' d' θ ε := by
  intro ro c
  choose! s hs using hstep.exists_pow
  let u : Fin (m + 1) → F → F := fun k y =>
    if hk : k.val < m then partAt ζ m c k.val (s y) else ro y
  obtain ⟨bad, hbad, hgood⟩ := h u
  refine ⟨bad, hbad, fun β hβ p hp B hB hcard hfold => ?_⟩
  have hcurve : ∀ y ∈ B, ∑ k : Fin (m + 1), β ^ k.val * u k y = p.eval y := by
    intro y hy
    rw [Fin.sum_univ_castSucc]
    have hlast : u (Fin.last m) y = ro y := by simp [u]
    have hinit : ∀ j : Fin m, u j.castSucc y = partAt ζ m c j.val (s y) := fun j => by
      simp [u, j.isLt]
    simp_rw [hinit, hlast, Fin.val_castSucc, Fin.val_last]
    obtain ⟨hsD, hspow⟩ := hs y (hB hy)
    have hfy := hfold (s y) hsD (by rwa [hspow])
    rw [hspow] at hfy
    exact hfy
  obtain ⟨v, hv, huv⟩ := hgood β hβ p hp B hB hcard hcurve
  refine ⟨⟨unfoldPolyArity m (fun j => v j.castSucc),
      degree_unfoldPolyArity_lt hstep.m_pos (fun j => hv j.castSucc), fun x hx hxB => ?_⟩,
    v (Fin.last m), hv (Fin.last m), fun y hy => ?_⟩
  · refine eq_eval_unfoldPolyArity hstep.prim hstep.m_pos hstep.m_ne_zero (hstep.ne_zero x hx)
      fun j => ?_
    obtain ⟨-, hspow⟩ := hs (x ^ m) (hB hxB)
    have hpart := partAt_eq_of_pow_eq hstep.prim hstep.m_pos c j.val (hstep.ne_zero x hx) hspow.symm
    have hvj := huv j.castSucc (x ^ m) hxB
    simp only [u, Fin.val_castSucc, j.isLt, ↓reduceDIte] at hvj
    exact hpart.trans hvj
  · have hvm := huv (Fin.last m) y hy
    simpa [u] using hvm

/-- When no input joins (`ro = 0`), `m`-term `CurveMCA` suffices for `m`-ary folding. -/
theorem StepMCAArityFor.zero_of_curveMCA [Fintype F] {m : ℕ} {ζ : F} {D D' : Finset F}
    (hstep : PowStep m ζ D D') {d' : ℕ} {θ ε : ℝ}
    (h : CurveMCA D' d' m θ ε) :
    StepMCAArityFor m ζ D D' d' θ ε (fun _ => 0) := by
  intro c
  choose! s hs using hstep.exists_pow
  let u : Fin m → F → F := fun j y => partAt ζ m c j.val (s y)
  obtain ⟨bad, hbad, hgood⟩ := h u
  refine ⟨bad, hbad, fun β hβ p hp B hB hcard hfold => ?_⟩
  have hcurve : ∀ y ∈ B, ∑ j : Fin m, β ^ j.val * u j y = p.eval y := by
    intro y hy
    obtain ⟨hsD, hspow⟩ := hs y (hB hy)
    have hfy := hfold (s y) hsD (by rwa [hspow])
    rw [hspow, mul_zero, add_zero] at hfy
    exact hfy
  obtain ⟨v, hv, huv⟩ := hgood β hβ p hp B hB hcard hcurve
  refine ⟨⟨unfoldPolyArity m v, degree_unfoldPolyArity_lt hstep.m_pos hv, fun x hx hxB => ?_⟩,
    0, by rw [degree_zero]; exact WithBot.bot_lt_coe d', fun _ _ => eval_zero.symm⟩
  refine eq_eval_unfoldPolyArity hstep.prim hstep.m_pos hstep.m_ne_zero (hstep.ne_zero x hx)
    fun j => ?_
  obtain ⟨-, hspow⟩ := hs (x ^ m) (hB hxB)
  exact (partAt_eq_of_pow_eq hstep.prim hstep.m_pos c j.val (hstep.ne_zero x hx) hspow.symm).trans
    (huv j (x ^ m) hxB)

/-- **Unconditional unique-decoding multi-arity folding proximity gap.**
Because `(m + 1) - 1 = m` and `m * |D'| = |D|`, the error simplifies to
`((1 + δ) * |D|) / |F|` — completely independent of the arity `m`! -/
theorem stepMCAArity_ud [Fintype F] [DecidableEq F] {m : ℕ} {ζ : F} {D D' : Finset F}
    (hstep : PowStep m ζ D D') (d' : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdist : 2 * (δ * D'.card) + d' ≤ D'.card) :
    StepMCAArity m ζ D D' d' (1 - δ) (((1 + δ) * D.card) / Fintype.card F) := by
  have hcurve := curveMCA_of_curveCA (curveCA_udThreshold (F := F)) D' d' (m + 1) δ hδ hdist
  have hcard : (D.card : ℝ) = (m : ℝ) * (D'.card : ℝ) := by exact_mod_cast hstep.card_eq
  have heq : (((m + 1 - 1 : ℕ) : ℝ) * ((1 + δ) * D'.card) / Fintype.card F) =
      ((1 + δ) * D.card) / Fintype.card F := by
    rw [Nat.add_sub_cancel, hcard]
    ring
  rw [heq] at hcurve
  exact StepMCAArity.of_curveMCA hstep hcurve

/-- **Johnson-regime multi-arity folding proximity gap from `CurveListCA`.**
The Johnson list-decoding term `m * L_J * (1 - θ) * |D'|` simplifies via
`m * |D'| = |D|` to `L_J * (1 - θ) * |D|`, completely independent of `m`! -/
theorem stepMCAArity_of_curveListCA_rel [Fintype F] [DecidableEq F]
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA F T)
    {m : ℕ} {ζ : F} {D D' : Finset F} (hstep : PowStep m ζ D D') (d' : ℕ)
    {ρ θ T_bound : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hd : (d' : ℝ) ≤ ρ * D'.card) (hgap : ρ < θ ^ 2)
    (hT0 : 0 ≤ T_bound) (hT : (T D'.card d' ⌈θ * D'.card⌉₊ (m + 1) : ℝ) ≤ T_bound) :
    StepMCAArity m ζ D D' d' θ
      ((T_bound + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * D.card)) / Fintype.card F) := by
  have hcurve := curveMCA_of_curveListCA_rel hca D' d' (m + 1) hθ0 hθ1 hd hgap hT0 hT
  have hcard : (D.card : ℝ) = (m : ℝ) * (D'.card : ℝ) := by exact_mod_cast hstep.card_eq
  have heq :
      (T_bound + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * D'.card) * (((m + 1 - 1 : ℕ) : ℝ))) /
        Fintype.card F =
      (T_bound + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * D.card)) / Fintype.card F := by
    rw [Nat.add_sub_cancel, hcard]
    ring
  rw [heq] at hcurve
  exact StepMCAArity.of_curveMCA hstep hcurve

end MultiStepMCA

/-! ## 4. Iterated binary fold equals `2 ^ a`-ary coset fold (`foldRowMultiM`) -/

section IterFoldEquiv

/-- Model-field version of binary `foldRow`: the value at `β` of the line through
`(x, e₀)` and `(-x, e₁)`. -/
def foldRowM (β x e₀ e₁ : F) : F :=
  e₀ + (β - x) * (e₁ - e₀) / (-x - x)

/-- Model-field version of `Fri.foldRowMulti`: iterates `logArity` binary
`foldRowM` passes with `β, β ^ 2, …, β ^ (2 ^ (logArity - 1))` on the `2 ^ logArity`
bit-reversed coset evaluations. -/
def foldRowMultiM (ω : F) (n : ℕ) : (logArity curLevel groupIdx : ℕ) → F → Array F → F
  | 0, _, _, _, evals => evals.getD 0 0
  | a + 1, curLevel, groupIdx, β, evals =>
    let next := Array.ofFn (n := 2 ^ a) fun r =>
      foldRowM β (pointOfIndex ω n (n - curLevel) (2 * (groupIdx * 2 ^ a + r.val)))
        (evals.getD (2 * r.val) 0) (evals.getD (2 * r.val + 1) 0)
    foldRowMultiM ω n a (curLevel + 1) groupIdx (β * β) next

theorem foldRowMultiM_one (ω : F) (n curLevel groupIdx : ℕ) (β : F) (evals : Array F) :
    foldRowMultiM ω n 1 curLevel groupIdx β evals =
      foldRowM β (pointOfIndex ω n (n - curLevel) (2 * groupIdx))
        (evals.getD 0 0) (evals.getD 1 0) := by
  simp [foldRowMultiM, Array.getD]

/-- **Core algebraic equivalence:** for any polynomial `g` of degree `< 2 ^ a`,
iterating `a` binary `foldRowM` passes with `β, β ^ 2, …, β ^ (2 ^ (a - 1))`
on the evaluations of `g` at the `2 ^ a` bit-reversed coset points
`pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r)` returns `g.eval β`. -/
theorem foldRowMultiM_eq_eval_poly {ω : F} {n : ℕ} (hω : IsPrimitiveRoot ω (2 ^ n)) :
    ∀ (a curLevel groupIdx : ℕ) (β : F) (g : F[X]) (evals : Array F),
      curLevel + a ≤ n →
      g.degree < (2 ^ a : ℕ) →
      (∀ r < 2 ^ a, evals.getD r 0 = g.eval (pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r))) →
      foldRowMultiM ω n a curLevel groupIdx β evals = g.eval β
  | 0, curLevel, groupIdx, β, g, evals, _, hg, hevals => by
    simp only [foldRowMultiM, pow_zero] at hg ⊢
    rw [hevals 0 Nat.zero_lt_one]
    have hconst : g = C (g.coeff 0) := by
      ext k
      cases k with
      | zero => simp
      | succ k =>
        rw [coeff_C_of_ne_zero (Nat.succ_ne_zero k)]
        exact (degree_lt_iff_coeff_zero g 1).mp hg (k + 1) (by omega)
    rw [hconst, eval_C, eval_C]
  | a + 1, curLevel, groupIdx, β, g, evals, hka, hg, hevals => by
    have hn_pos : 0 < n := by omega
    have h2ne : (2 : F) ≠ 0 := Domain.two_ne_zero_of_isPrimitiveRoot hω hn_pos
    have hdeg_fold : (foldPoly β g).degree < (2 ^ a : ℕ) := by
      refine degree_foldPoly_lt β ?_
      simpa [pow_succ', mul_comm] using hg
    unfold foldRowMultiM
    have hnext : ∀ r < 2 ^ a,
        (Array.ofFn (n := 2 ^ a) fun r : Fin (2 ^ a) =>
          foldRowM β (pointOfIndex ω n (n - curLevel) (2 * (groupIdx * 2 ^ a + r.val)))
            (evals.getD (2 * r.val) 0) (evals.getD (2 * r.val + 1) 0)).getD r 0 =
          (foldPoly β g).eval (pointOfIndex ω n (n - (curLevel + 1)) (groupIdx * 2 ^ a + r)) := by
      intro r hr
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hr, Option.getD_some]
      have hidx0 : 2 * (groupIdx * 2 ^ a + r) = groupIdx * 2 ^ (a + 1) + 2 * r := by
        rw [pow_succ]; ring
      have hidx1 : 2 * (groupIdx * 2 ^ a + r) + 1 = groupIdx * 2 ^ (a + 1) + (2 * r + 1) := by
        rw [pow_succ]; ring
      have hr0 : 2 * r < 2 ^ (a + 1) := by rw [pow_succ]; omega
      have hr1 : 2 * r + 1 < 2 ^ (a + 1) := by rw [pow_succ]; omega
      have hsub : n - curLevel = (n - (curLevel + 1)) + 1 := by omega
      have hlt : n - (curLevel + 1) < n := by omega
      set u := groupIdx * 2 ^ a + r
      set x := pointOfIndex ω n (n - curLevel) (2 * u)
      have hx_ne : x ≠ 0 :=
        pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (by positivity)))
      have hneg : pointOfIndex ω n (n - curLevel) (2 * u + 1) = -x := by
        change pointOfIndex ω n (n - curLevel) (2 * u + 1) = -pointOfIndex ω n (n - curLevel) (2 * u)
        rw [hsub, pointOfIndex_two_mul_add_one hω hlt u, pointOfIndex_two_mul]
      have hsq : x ^ 2 = pointOfIndex ω n (n - (curLevel + 1)) u := by
        change pointOfIndex ω n (n - curLevel) (2 * u) ^ 2 = pointOfIndex ω n (n - (curLevel + 1)) u
        rw [hsub, pointOfIndex_sq hω hlt (2 * u), Nat.mul_div_cancel_left u two_pos]
      have he0 : evals.getD (2 * r) 0 = g.eval x := by
        rw [hevals (2 * r) hr0, ← hidx0]
      have he1 : evals.getD (2 * r + 1) 0 = g.eval (-x) := by
        rw [hevals (2 * r + 1) hr1, ← hidx1, hneg]
      rw [he0, he1, ← hsq]
      have hfold_eq : foldRowM β x (g.eval x) (g.eval (-x)) = foldAt g.eval β x := by
        unfold foldRowM
        exact (foldAt_eq_interpolate h2ne g.eval β hx_ne).symm
      rw [hfold_eq]
      exact foldAt_eq_eval_foldPoly h2ne β hx_ne rfl rfl
    rw [foldRowMultiM_eq_eval_poly hω a (curLevel + 1) groupIdx (β * β) (foldPoly β g) _
      (by omega) hdeg_fold hnext]
    rw [foldPoly, eval_add, eval_mul, eval_C, ← sq, ← eval_eq_evenPart_add_mul_oddPart]

/-- **Iterated binary fold equals `2 ^ a`-ary coset fold `foldAtPow`:**
whenever `evals[r]` holds `c (pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r))`
for all `r < 2 ^ a`, `foldRowMultiM` computes `foldAtPow (ω ^ 2 ^ (n - a)) (2 ^ a) c β x₀`
at `x₀ = pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a)`. -/
theorem foldRowMultiM_eq_foldAtPow {ω : F} {n a curLevel groupIdx : ℕ}
    (hω : IsPrimitiveRoot ω (2 ^ n)) (ha : 0 < a) (hka : curLevel + a ≤ n)
    (c : F → F) (β : F) (evals : Array F)
    (hevals : ∀ r < 2 ^ a,
      evals.getD r 0 = c (pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r))) :
    foldRowMultiM ω n a curLevel groupIdx β evals =
      foldAtPow (ω ^ 2 ^ (n - a)) (2 ^ a) c β
        (pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a)) := by
  have hn_pos : 0 < n := by omega
  have h2ne : (2 : F) ≠ 0 := Domain.two_ne_zero_of_isPrimitiveRoot hω hn_pos
  have hm_ne : ((2 ^ a : ℕ) : F) ≠ 0 := by push_cast; exact pow_ne_zero a h2ne
  have hprim : IsPrimitiveRoot (ω ^ 2 ^ (n - a)) (2 ^ a) :=
    Domain.isPrimitiveRoot_generator hω (by omega)
  set ζ := ω ^ 2 ^ (n - a)
  set x₀ := pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a)
  have hx₀_ne : x₀ ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (hω.ne_zero (by positivity)))
  let g : F[X] := ∑ j : Fin (2 ^ a), C (partAt ζ (2 ^ a) c j.val x₀) * X ^ j.val
  have hg_deg : g.degree < (2 ^ a : ℕ) := by
    refine mem_degreeLT.mp ((degreeLT F (2 ^ a)).sum_mem fun j _ => mem_degreeLT.mpr ?_)
    refine (degree_mul_le _ _).trans_lt ?_
    have hc : (C (partAt ζ (2 ^ a) c j.val x₀)).degree ≤ 0 := degree_C_le
    have hx : (X ^ j.val : F[X]).degree ≤ (j.val : ℕ) := degree_X_pow_le _
    calc (C (partAt ζ (2 ^ a) c j.val x₀)).degree + (X ^ j.val : F[X]).degree
        ≤ 0 + (j.val : ℕ) := add_le_add hc hx
      _ = (j.val : ℕ) := zero_add _
      _ < (2 ^ a : ℕ) := WithBot.coe_lt_coe.mpr j.isLt
  have hg_eval : ∀ r < 2 ^ a,
      evals.getD r 0 = g.eval (pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r)) := by
    intro r hr
    rw [hevals r hr]
    set x_r := pointOfIndex ω n (n - curLevel) (groupIdx * 2 ^ a + r)
    have hpow_eq : x₀ ^ 2 ^ a = x_r ^ 2 ^ a := by
      have h0 : x₀ ^ 2 ^ a = pointOfIndex ω n (n - curLevel - a) ((groupIdx * 2 ^ a) >>> a) :=
        pointOfIndex_pow_two_pow hω (by omega) (by omega) (groupIdx * 2 ^ a)
      have hr' : x_r ^ 2 ^ a =
          pointOfIndex ω n (n - curLevel - a) ((groupIdx * 2 ^ a + r) >>> a) :=
        pointOfIndex_pow_two_pow hω (by omega) (by omega) (groupIdx * 2 ^ a + r)
      rw [h0, hr', Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (by positivity), Nat.mul_comm groupIdx,
        Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hr, Nat.add_zero]
    have hxr_ne : x_r ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by positivity)] at hpow_eq
      exact pow_ne_zero _ hx₀_ne hpow_eq
    have hg_at : g.eval x_r = ∑ j : Fin (2 ^ a), x_r ^ j.val * partAt ζ (2 ^ a) c j.val x_r := by
      simp only [g, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm, partAt_eq_of_pow_eq hprim (by positivity) c j.val hx₀_ne hpow_eq]
    rw [hg_at, sum_pow_mul_partAt hprim (by positivity) hm_ne c hxr_ne]
  rw [foldRowMultiM_eq_eval_poly hω a curLevel groupIdx β g evals hka hg_deg hg_eval]
  simp only [g, foldAtPow, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun j _ => mul_comm _ _

end IterFoldEquiv

end CertiFri
