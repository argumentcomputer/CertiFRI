import Mathlib.LinearAlgebra.Lagrange
import CertiFriProofs.Theory.Basic
import CertiFriProofs.Theory.ProximityGap.LinearCode

/-!
# An unconditional proximity gap for Reed–Solomon codes

The soundness theorems take `CurveMCA D d m θ ε` as a hypothesis. This file
proves that hypothesis outright, with no assumption, in the regime where an
elementary argument works: agreement sets that miss fewer than a
`1 / (m + 1)` fraction of the minimum distance.

* `eq_of_degree_lt_of_agree`, `eq_of_agree_of_card`: the distance of the
  Reed–Solomon code, and unique decoding.
* `curveMCA_of_card`, `curveMCA_of_card_lt`: `CurveMCA` for agreement sets that
  miss at most `e` points of `D`, when `(m + 1) * e + d ≤ D.card`, with error
  `(m - 1) * (e + 1) / |F|`.
* `curveMCA_of_relDist`: the same in relative terms, for agreement
  `θ = 1 - δ` with `(m + 1) * δ * D.card + d ≤ D.card`.
* `curveMCA_two_of_relDist`, `curveMCA_three_of_relDist`: the cases `m = 2`
  and `m = 3`.

The proof instantiates `curve_mca_of_minDist`, which holds for every linear
code, with the code of restrictions to `D` of polynomials of degree below `d`.

Not covered: larger radii. With rate `ρ = d / D.card` the results here reach
`δ ≤ (1 - ρ) / (m + 1)`; the unique-decoding radius is `(1 - ρ) / 2` and the
Johnson radius is `1 - √ρ`. For those the hypothesis `CurveMCA` stays a
hypothesis.
-/

namespace CertiFri

open Polynomial Finset

variable {F : Type*} [Field F]

/-! ## The distance of the Reed–Solomon code -/

/-- Two polynomials of degree below `d` that agree on `d` points are equal. -/
theorem eq_of_degree_lt_of_agree {p q : F[X]} {d : ℕ} (hp : p.degree < d) (hq : q.degree < d)
    {B : Finset F} (hB : d ≤ B.card) (h : ∀ x ∈ B, p.eval x = q.eval x) : p = q :=
  eq_of_degrees_lt_of_eval_finset_eq B (hp.trans_le (Nat.cast_le.mpr hB))
    (hq.trans_le (Nat.cast_le.mpr hB)) h

/-- Unique decoding: two polynomials of degree below `d`, each agreeing with
`f` on a subset of `D`, are equal when the two subsets are large enough to
overlap in `d` points. -/
theorem eq_of_agree_of_card {f : F → F} {p q : F[X]} {d : ℕ} {D B₁ B₂ : Finset F}
    (hp : p.degree < d) (hq : q.degree < d) (h₁ : B₁ ⊆ D) (h₂ : B₂ ⊆ D)
    (hcard : D.card + d ≤ B₁.card + B₂.card)
    (hf₁ : ∀ x ∈ B₁, f x = p.eval x) (hf₂ : ∀ x ∈ B₂, f x = q.eval x) : p = q := by
  classical
  refine eq_of_degree_lt_of_agree hp hq (B := B₁ ∩ B₂) ?_ fun x hx => ?_
  · have h := card_union_add_card_inter B₁ B₂
    have hU : (B₁ ∪ B₂).card ≤ D.card := card_le_card (union_subset h₁ h₂)
    omega
  · rw [mem_inter] at hx
    rw [← hf₁ x hx.1, hf₂ x hx.2]

/-! ## The Reed–Solomon code as a linear code -/

namespace ProximityGap

/-- The Reed–Solomon code as a linear code of length `D.card`: the restrictions
to `D` of the polynomials of degree below `d`. -/
noncomputable def rsCode (D : Finset F) (d : ℕ) : Submodule F (D → F) :=
  (degreeLT F d).map (LinearMap.pi fun x : D => leval (x : F))

/-- A word on `D` is in the Reed–Solomon code exactly when it is the
restriction of a polynomial of degree below `d`. -/
theorem mem_rsCode {D : Finset F} {d : ℕ} {c : D → F} :
    c ∈ rsCode D d ↔ ∃ p : F[X], p.degree < d ∧ ∀ x : D, c x = p.eval (x : F) := by
  simp only [rsCode, Submodule.mem_map, mem_degreeLT]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, fun _ => rfl⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, funext fun x => (h x).symm⟩

/-- The minimum distance of the Reed–Solomon code: a nonzero codeword vanishes
at fewer than `d` points of `D`, so its weight is at least `D.card - d + 1`. -/
theorem rsCode_minDist [DecidableEq F] (D : Finset F) (d : ℕ) (c : D → F)
    (hc : c ∈ rsCode D d) (hne : c ≠ 0) :
    D.card + 1 - d ≤ (univ.filter fun x => c x ≠ 0).card := by
  obtain ⟨p, hp, hcp⟩ := mem_rsCode.mp hc
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset D)) fun x => c x ≠ 0
  have hz : (univ.filter fun x : D => ¬c x ≠ 0).card < d := by
    by_contra hge
    refine hne (funext fun x => ?_)
    have hp0 : p = 0 := by
      refine eq_of_degree_lt_of_agree hp (by simp)
        (B := (univ.filter fun x : D => ¬c x ≠ 0).map (Function.Embedding.subtype _))
        (by simpa using hge) fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      rw [eval_zero, Function.Embedding.subtype_apply, ← hcp x]
      exact not_not.mp (mem_filter.mp hx).2
    rw [hcp x, hp0, eval_zero, Pi.zero_apply]
  rw [card_univ, Fintype.card_coe] at hsplit
  omega

end ProximityGap

open ProximityGap

/-! ## The Reed–Solomon instance of `CurveMCA` -/

variable [Fintype F]

/-- `CurveMCA` survives raising the agreement threshold and the error. -/
theorem ProximityGap.curveMCA_mono {D : Finset F} {d m : ℕ} {θ θ' ε ε' : ℝ}
    (h : CurveMCA D d m θ ε) (hθ : θ ≤ θ') (hε : ε ≤ ε') : CurveMCA D d m θ' ε' := by
  intro u
  obtain ⟨bad, hbad, hgood⟩ := h u
  exact ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)),
    fun β hβ p hp B hBD hB => hgood β hβ p hp B hBD
      ((mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _)).trans hB)⟩

/-- **Mutual correlated agreement for Reed–Solomon codes, unconditionally.**

Let `(m + 1) * e + d ≤ D.card`, and let the agreement threshold `θ` be such
that a subset of `D` holding a fraction `θ` of it misses at most `e` points
(`D.card - (e + 1) < θ * D.card`). Then `CurveMCA` holds with error
`(m - 1) * (e + 1) / |F|`: for all but `(m - 1) * (e + 1)` values of `β`, a set
of that size on which `∑ k, β ^ k * u k` agrees with a polynomial of degree
below `d` is a set on which every `u k` does. -/
theorem curveMCA_of_card_lt (D : Finset F) (d m e : ℕ) (θ : ℝ)
    (hθ : (D.card : ℝ) - (e + 1) < θ * D.card)
    (hdist : (m + 1) * e + d ≤ D.card) :
    CurveMCA D d m θ ((((m - 1) * (e + 1) : ℕ) : ℝ) / Fintype.card F) := by
  classical
  intro u
  obtain ⟨bad, hbad, h⟩ := curve_mca_of_minDist (rsCode D d) (D.card + 1 - d)
    (rsCode_minDist D d) m e (by omega) fun k (x : D) => u k x
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨bad, ?_, fun β hβ p hp B hBD hB hagree => ?_⟩
  · rw [div_mul_cancel₀ _ hF]
    exact_mod_cast hbad
  · have hBcard : Fintype.card D ≤ (B.subtype (· ∈ D)).card + e := by
      have hlt : (D.card : ℝ) < (B.card + e + 1 : ℕ) := by
        push_cast
        linarith
      rw [Fintype.card_coe, card_subtype, filter_true_of_mem hBD]
      exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hlt)
    obtain ⟨v, hv, huv⟩ := h β hβ (fun x => p.eval (x : F))
      (mem_rsCode.mpr ⟨p, hp, fun _ => rfl⟩) (B.subtype (· ∈ D)) hBcard
      fun j hj => hagree j (mem_subtype.mp hj)
    choose q hq hqv using fun k => mem_rsCode.mp (hv k)
    refine ⟨q, hq, fun k x hx => ?_⟩
    rw [← hqv k ⟨x, hBD hx⟩]
    exact huv k ⟨x, hBD hx⟩ (mem_subtype.mpr hx)

/-- **Mutual correlated agreement for Reed–Solomon codes, unconditionally.**

Let `(m + 1) * e + d ≤ D.card` and let the agreement threshold `θ` be at least
`1 - e / D.card`. Then `CurveMCA` holds with error `(m - 1) * (e + 1) / |F|`.
`curveMCA_of_card_lt` is the same statement for a slightly larger range of
`θ`. -/
theorem curveMCA_of_card (D : Finset F) (d m e : ℕ) (θ : ℝ)
    (hθ : (D.card : ℝ) - e ≤ θ * D.card)
    (hdist : (m + 1) * e + d ≤ D.card) :
    CurveMCA D d m θ ((((m - 1) * (e + 1) : ℕ) : ℝ) / Fintype.card F) :=
  curveMCA_of_card_lt D d m e θ (by linarith) hdist

/-- **Mutual correlated agreement for Reed–Solomon codes, in relative terms.**

If `(m + 1) * (δ * D.card) + d ≤ D.card`, then `CurveMCA` holds for agreement
`1 - δ` (relative distance `δ`) with error `(m - 1) * (δ * D.card + 1) / |F|`.

Writing `ρ = d / D.card` for the rate, the condition is `δ ≤ (1 - ρ) / (m + 1)`.
For the two curves the protocol uses, with `D` and `d` the domain and degree
bound of the code the folded word lives in:

* `m = 2`, a plain fold `even + β * odd`: every `δ ≤ (1 - ρ) / 3`, with error
  `(δ * D.card + 1) / |F|` (`curveMCA_two_of_relDist`).
* `m = 3`, a fold with an input joining, `even + β * odd + β ^ 2 * input`: every
  `δ ≤ (1 - ρ) / 4`, with error `2 * (δ * D.card + 1) / |F|`
  (`curveMCA_three_of_relDist`).

Only the integer `⌊δ * D.card⌋` matters, so the condition can be relaxed to
`(m + 1) * ⌊δ * D.card⌋ + d ≤ D.card` by going through `curveMCA_of_card_lt`. -/
theorem curveMCA_of_relDist (D : Finset F) (d m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdist : (m + 1) * (δ * D.card) + d ≤ D.card) :
    CurveMCA D d m (1 - δ) (((m - 1 : ℕ) : ℝ) * (δ * D.card + 1) / Fintype.card F) := by
  have hnn : 0 ≤ δ * D.card := mul_nonneg hδ (Nat.cast_nonneg _)
  have hfloor : (⌊δ * D.card⌋₊ : ℝ) ≤ δ * D.card := Nat.floor_le hnn
  have hlt : δ * D.card < ⌊δ * D.card⌋₊ + 1 := Nat.lt_floor_add_one _
  have hdist' : (m + 1) * ⌊δ * D.card⌋₊ + d ≤ D.card := by
    have h1 : ((m : ℝ) + 1) * ⌊δ * D.card⌋₊ ≤ (m + 1) * (δ * D.card) :=
      mul_le_mul_of_nonneg_left hfloor (by positivity)
    have h2 : (((m + 1) * ⌊δ * D.card⌋₊ + d : ℕ) : ℝ) ≤ (D.card : ℕ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp h2
  refine curveMCA_mono
    (curveMCA_of_card_lt D d m ⌊δ * D.card⌋₊ (1 - δ) (by linarith) hdist') le_rfl ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  push_cast
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

/-- The plain fold, `m = 2`: if `3 * (δ * D.card) + d ≤ D.card`, that is
`δ ≤ (1 - ρ) / 3` for the rate `ρ = d / D.card`, then `CurveMCA` holds for
agreement `1 - δ` with error `(δ * D.card + 1) / |F|`. -/
theorem curveMCA_two_of_relDist (D : Finset F) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdist : 3 * (δ * D.card) + d ≤ D.card) :
    CurveMCA D d 2 (1 - δ) ((δ * D.card + 1) / Fintype.card F) := by
  have h := curveMCA_of_relDist D d 2 δ hδ (by norm_num; linarith)
  norm_num at h
  exact h

/-- The fold with an input joining, `m = 3`: if `4 * (δ * D.card) + d ≤ D.card`,
that is `δ ≤ (1 - ρ) / 4` for the rate `ρ = d / D.card`, then `CurveMCA` holds
for agreement `1 - δ` with error `2 * (δ * D.card + 1) / |F|`. -/
theorem curveMCA_three_of_relDist (D : Finset F) (d : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdist : 4 * (δ * D.card) + d ≤ D.card) :
    CurveMCA D d 3 (1 - δ) (2 * (δ * D.card + 1) / Fintype.card F) := by
  have h := curveMCA_of_relDist D d 3 δ hδ (by norm_num; linarith)
  norm_num at h
  exact h

end CertiFri
