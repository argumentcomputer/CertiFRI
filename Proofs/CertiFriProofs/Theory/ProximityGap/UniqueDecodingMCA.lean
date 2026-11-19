import CertiFriProofs.Theory.ProximityGap
import CertiFriProofs.Theory.ProximityGap.CorrelatedAgreement
import CertiFriProofs.Theory.StepMCA

/-!
# The proximity hypotheses at the unique-decoding radius, from correlated agreement

The soundness theorems take two hypotheses about Reed–Solomon codes, `CurveMCA`
(batching) and `StepMCA` (folding). This file derives both from correlated
agreement for curves in the unique-decoding regime, `CurveCA F T`
(`ProximityGap/CorrelatedAgreement.lean`), for every relative distance `δ` with
`2 * δ + ρ ≤ 1`, where `ρ` is the rate of the code, and for curves of any
number of terms.

* `curve_mca_of_curveCA`: correlated agreement with threshold `T` gives mutual
  correlated agreement with at most `T D.card e m` exceptional parameters, as
  soon as `(m - 1) * e ≤ T D.card e m`. Mutual means that the set on which the
  combination agrees with a codeword is itself a set on which every term does.
* `curveMCA_of_curveCA_card`, `curveMCA_of_curveCA`: `CurveMCA` for agreement
  sets that miss at most `e` points with `2 * e + d ≤ D.card`, and in relative
  terms for agreement `1 - δ` with `2 * (δ * D.card) + d ≤ D.card`. The error is
  `udThreshold D.card e m / |F|`, at most
  `(m - 1) * (D.card * (δ * D.card + 1) + 1) / |F|`.
* `stepMCA_of_curveCA`: `StepMCA` for a folding round into `D'`, for agreement
  `1 - δ` with `2 * (δ * D'.card) + d' ≤ D'.card`, with error
  `2 * (D'.card * (δ * D'.card + 1) + 1) / |F|`.
* `curveMCA_of_curveCA_of_card_le`, `stepMCA_of_curveCA_of_card_le`: the last
  two with the size of the domain replaced by an upper bound in the error.

## What is assumed

`CurveCA F T` is a hypothesis of every theorem here, at `T := udThreshold` from
the second on. It is a statement about Reed–Solomon codes alone. Nothing else
is assumed.

## What is not covered

The proof of `CurveCA F udThreshold`, and any radius beyond unique decoding:
for `δ > (1 - ρ) / 2` the hypotheses `CurveMCA` and `StepMCA` stay hypotheses.

## The argument

Let `G` be the set of parameters `β` at which the combination `∑ k, β ^ k * u k`
is within `e` errors of a polynomial of degree below `d`. If `G` has at most
`T D.card e m` elements, it is the exceptional set. Otherwise correlated
agreement gives polynomials `v k` such that the points of `D` where some `u k`
differs from `v k` number at most `e`. The exceptional parameters are then the
roots of the nonzero polynomials `∑ k, (u k x - v k x) X ^ k` at those points
`x`: at most `e * (m - 1)` values. For any other `β`, a polynomial `p` that
agrees with the combination on a set `B` missing at most `e` points is
`∑ k, β ^ k • v k` by unique decoding, so the combination of the `u k - v k`
vanishes on `B`, and a point of `B` where some `u k` differs from `v k` would
make `β` exceptional.
-/

namespace CertiFri

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Mutual correlated agreement in the unique-decoding regime, from
correlated agreement.**

Assume correlated agreement for curves with threshold `T` (`CurveCA F T`). Let
`2 * e + d ≤ D.card` and `(m - 1) * e ≤ T D.card e m`. For every choice of words
`u k` there is a set `bad` of at most `T D.card e m` values of `β` outside which
the following holds: whenever the combination `∑ k, β ^ k * u k` agrees with a
polynomial of degree below `d` on a subset `B` of `D` that misses at most `e`
points, every `u k` agrees with a polynomial of degree below `d` on that same
`B`. -/
theorem curve_mca_of_curveCA {T : ℕ → ℕ → ℕ → ℕ} (hca : CurveCA F T) (D : Finset F) (d e m : ℕ)
    (he : 2 * e + d ≤ D.card) (hT : (m - 1) * e ≤ T D.card e m) (u : Fin m → F → F) [Fintype F] :
    ∃ bad : Finset F, bad.card ≤ T D.card e m ∧
      ∀ β ∉ bad, ∀ p : F[X], p.degree < d → ∀ B ⊆ D, D.card ≤ B.card + e →
        (∀ x ∈ B, ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x) →
        ∃ v : Fin m → F[X], (∀ k, (v k).degree < d) ∧ ∀ k, ∀ x ∈ B, u k x = (v k).eval x := by
  classical
  -- Agreement on a subset of `D` missing at most `e` points is at most `e` errors.
  have hclose : ∀ (β : F) (p : F[X]) (B : Finset F), B ⊆ D → D.card ≤ B.card + e →
      (∀ x ∈ B, ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x) →
      (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x ≠ p.eval x).card ≤ e := by
    intro β p B hBD hB hagree
    have hsub : (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x ≠ p.eval x) ⊆ D \ B :=
      fun x hx => mem_sdiff.mpr
        ⟨(mem_filter.mp hx).1, fun hxB => (mem_filter.mp hx).2 (hagree x hxB)⟩
    have hcard := card_le_card hsub
    have hsdiff := card_sdiff_add_card_eq_card hBD
    omega
  -- The parameters at which the combination is within `e` errors of the code.
  let G : Finset F := univ.filter fun β => ∃ p : F[X], p.degree < d ∧
    (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x ≠ p.eval x).card ≤ e
  by_cases hG : G.card ≤ T D.card e m
  · -- Few close parameters: they are the exceptional set.
    exact ⟨G, hG, fun β hβ p hp B hBD hB hagree =>
      absurd (mem_filter.mpr ⟨mem_univ _, p, hp, hclose β p B hBD hB hagree⟩) hβ⟩
  · -- Many close parameters: the `u k` agree with polynomials `v k` outside a set
    -- `S` of at most `e` points, and the exceptional set is where the combination
    -- of the `u k - v k` vanishes at a point of `S`.
    obtain ⟨v, hv, hE⟩ := hca D d e m he u G (not_le.mp hG) fun β hβ => (mem_filter.mp hβ).2
    refine ⟨(D.filter fun x => ∃ k, u k x ≠ (v k).eval x).biUnion fun x =>
      univ.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - (v k).eval x) = 0, ?_, ?_⟩
    · calc ((D.filter fun x => ∃ k, u k x ≠ (v k).eval x).biUnion fun x =>
            univ.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k x - (v k).eval x) = 0).card
          ≤ ∑ x ∈ D.filter fun x => ∃ k, u k x ≠ (v k).eval x,
            (univ.filter fun β =>
              ∑ k : Fin m, β ^ (k : ℕ) * (u k x - (v k).eval x) = 0).card :=
            card_biUnion_le
        _ ≤ ∑ _x ∈ D.filter fun x => ∃ k, u k x ≠ (v k).eval x, (m - 1) :=
            sum_le_sum fun x hx => by
              have ha : (fun k => u k x - (v k).eval x) ≠ 0 := by
                obtain ⟨k, hk⟩ := (mem_filter.mp hx).2
                exact fun h0 => hk (sub_eq_zero.mp (congrFun h0 k))
              have := ProximityGap.card_roots_lt ha univ
              omega
        _ = (D.filter fun x => ∃ k, u k x ≠ (v k).eval x).card * (m - 1) := by simp
        _ ≤ e * (m - 1) := Nat.mul_le_mul_right _ hE
        _ ≤ T D.card e m := by
            rw [Nat.mul_comm]
            exact hT
    · intro β hβ p hp B hBD hB hagree
      -- By unique decoding, `p` is the combination of the `v k`.
      have hq : (∑ k : Fin m, β ^ (k : ℕ) • v k).degree < d :=
        mem_degreeLT.mp ((degreeLT F d).sum_mem fun k _ =>
          (degreeLT F d).smul_mem _ (mem_degreeLT.mpr (hv k)))
      have hpq : p = ∑ k : Fin m, β ^ (k : ℕ) • v k := by
        refine eq_of_agree_of_card (f := fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x) hp hq hBD
          (sdiff_subset : D \ (D.filter fun x => ∃ k, u k x ≠ (v k).eval x) ⊆ D) ?_ hagree
          fun x hx => ?_
        · have hsdiff := card_sdiff_add_card_eq_card
            (filter_subset (fun x => ∃ k, u k x ≠ (v k).eval x) D)
          omega
        · rw [mem_sdiff, mem_filter, not_and, not_exists] at hx
          rw [eval_finsetSum]
          refine sum_congr rfl fun k _ => ?_
          rw [eval_smul, smul_eq_mul, not_not.mp (hx.2 hx.1 k)]
      refine ⟨v, hv, fun k x hx => ?_⟩
      by_contra hne
      refine hβ (mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨hBD hx, k, hne⟩,
        mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
      have hx' := hagree x hx
      rw [hpq, eval_finsetSum] at hx'
      simp only [mul_sub, sum_sub_distrib, hx', eval_smul, smul_eq_mul, sub_self]

variable [Fintype F]

/-- **`CurveMCA` at the unique-decoding radius, in absolute terms.**

Assume correlated agreement with the threshold `udThreshold`. Let
`2 * e + d ≤ D.card`, and let the agreement threshold `θ` be such that a subset
of `D` holding a fraction `θ` of it misses at most `e` points
(`D.card - (e + 1) < θ * D.card`). Then `CurveMCA` holds for curves of any
number `m` of terms, with error `udThreshold D.card e m / |F|`. -/
theorem curveMCA_of_curveCA_card (hca : CurveCA F udThreshold) (D : Finset F) (d m e : ℕ) (θ : ℝ)
    (hθ : (D.card : ℝ) - (e + 1) < θ * D.card) (hdist : 2 * e + d ≤ D.card) :
    CurveMCA D d m θ ((udThreshold D.card e m : ℝ) / Fintype.card F) := by
  intro u
  have hT : (m - 1) * e ≤ udThreshold D.card e m :=
    Nat.mul_le_mul_left _ (by nlinarith)
  obtain ⟨bad, hbad, h⟩ := curve_mca_of_curveCA hca D d e m hdist hT u
  have hF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨bad, ?_, fun β hβ p hp B hBD hB hagree => h β hβ p hp B hBD ?_ hagree⟩
  · rw [div_mul_cancel₀ _ hF]
    exact_mod_cast hbad
  · have hlt : (D.card : ℝ) < (B.card + e + 1 : ℕ) := by
      push_cast
      linarith
    exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp hlt)

/-- **`CurveMCA` at the unique-decoding radius, in relative terms.**

Assume correlated agreement with the threshold `udThreshold`. If
`2 * (δ * D.card) + d ≤ D.card`, then `CurveMCA` holds for agreement `1 - δ`
(relative distance `δ`) and curves of any number `m` of terms, with error
`(m - 1) * (D.card * (δ * D.card + 1) + 1) / |F|`.

Writing `ρ = d / D.card` for the rate, the condition is `δ ≤ (1 - ρ) / 2`: the
unique-decoding radius. Only the integer `⌊δ * D.card⌋` matters;
`curveMCA_of_curveCA_card` is the statement in terms of it. -/
theorem curveMCA_of_curveCA (hca : CurveCA F udThreshold) (D : Finset F) (d m : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hdist : 2 * (δ * D.card) + d ≤ D.card) :
    CurveMCA D d m (1 - δ)
      (((m - 1 : ℕ) : ℝ) * (D.card * (δ * D.card + 1) + 1) / Fintype.card F) := by
  have hnn : 0 ≤ δ * D.card := mul_nonneg hδ (Nat.cast_nonneg _)
  have hfloor : (⌊δ * D.card⌋₊ : ℝ) ≤ δ * D.card := Nat.floor_le hnn
  have hlt : δ * D.card < ⌊δ * D.card⌋₊ + 1 := Nat.lt_floor_add_one _
  have hdist' : 2 * ⌊δ * D.card⌋₊ + d ≤ D.card := by
    have h2 : ((2 * ⌊δ * D.card⌋₊ + d : ℕ) : ℝ) ≤ (D.card : ℕ) := by
      push_cast
      linarith
    exact Nat.cast_le.mp h2
  refine ProximityGap.curveMCA_mono
    (curveMCA_of_curveCA_card hca D d m ⌊δ * D.card⌋₊ (1 - δ) (by linarith) hdist') le_rfl ?_
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [udThreshold]
  push_cast
  gcongr

/-- **The folding hypothesis at the unique-decoding radius.**

Assume correlated agreement with the threshold `udThreshold`. If
`2 * (δ * |D'|) + d' ≤ |D'|`, the folding round from `D` to `D'` satisfies
`StepMCA` for agreement `1 - δ`, whatever input joins, with error
`2 * (|D'| * (δ * |D'| + 1) + 1) / |F|`. Here `D'` is the domain the round folds
into and `d'` its degree bound. -/
theorem stepMCA_of_curveCA (hca : CurveCA F udThreshold) {D D' : Finset F}
    (hstep : SquareStep D D') (d' : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdist : 2 * (δ * D'.card) + d' ≤ D'.card) :
    StepMCA D D' d' (1 - δ) (2 * (D'.card * (δ * D'.card + 1) + 1) / Fintype.card F) := by
  have h := curveMCA_of_curveCA hca D' d' 3 δ hδ hdist
  norm_num at h
  exact StepMCA.of_curveMCA hstep h

/-! ## With a bound on the size of the domain

The errors above grow with the size of the domain. In the statements below the
size is replaced by any upper bound `N`, so that one expression bounds the
errors of several domains. -/

/-- `curveMCA_of_curveCA` with the size of the domain replaced by an upper
bound `N` in the error: if `2 * (δ * D.card) + d ≤ D.card` and `D.card ≤ N`,
then `CurveMCA` holds for agreement `1 - δ` with error
`(m - 1) * (N * (δ * N + 1) + 1) / |F|`. -/
theorem curveMCA_of_curveCA_of_card_le (hca : CurveCA F udThreshold) (D : Finset F) (d m : ℕ)
    {δ N : ℝ} (hδ : 0 ≤ δ) (hdist : 2 * (δ * D.card) + d ≤ D.card) (hN : (D.card : ℝ) ≤ N) :
    CurveMCA D d m (1 - δ) (((m - 1 : ℕ) : ℝ) * (N * (δ * N + 1) + 1) / Fintype.card F) := by
  refine ProximityGap.curveMCA_mono (curveMCA_of_curveCA hca D d m δ hδ hdist) le_rfl ?_
  have hD : (0 : ℝ) ≤ N := (Nat.cast_nonneg D.card).trans hN
  gcongr

/-- `stepMCA_of_curveCA` with the size of the domain replaced by an upper bound
`N` in the error: if `2 * (δ * |D'|) + d' ≤ |D'|` and `|D'| ≤ N`, the folding
round from `D` to `D'` satisfies `StepMCA` for agreement `1 - δ` with error
`2 * (N * (δ * N + 1) + 1) / |F|`. -/
theorem stepMCA_of_curveCA_of_card_le (hca : CurveCA F udThreshold) {D D' : Finset F}
    (hstep : SquareStep D D') (d' : ℕ) {δ N : ℝ} (hδ : 0 ≤ δ)
    (hdist : 2 * (δ * D'.card) + d' ≤ D'.card) (hN : (D'.card : ℝ) ≤ N) :
    StepMCA D D' d' (1 - δ) (2 * (N * (δ * N + 1) + 1) / Fintype.card F) := by
  have h := curveMCA_of_curveCA_of_card_le hca D' d' 3 hδ hdist hN
  norm_num at h
  exact StepMCA.of_curveMCA hstep h

end CertiFri
