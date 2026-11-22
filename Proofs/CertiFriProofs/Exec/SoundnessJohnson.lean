import CertiFriProofs.Exec.SoundnessUD
import CertiFriProofs.P3.GoldilocksExt3
import CertiFriProofs.Theory.ProximityGap.JohnsonMCA

/-!
# Soundness of the executable verifier up to the Johnson radius (`θ > √ρ`)

`Exec.soundness_uniqueDecoding` (`Exec/SoundnessUnconditional.lean`) proves
unconditional soundness up to the unique-decoding radius `δ ≤ (1 - ρ) / 2`
(agreement `θ ≥ (1 + ρ) / 2`). Reaching 128-bit query soundness at practical
query counts (`q = 112–128` at blowup `2 ^ 2`, or `q = 80` at blowup `2 ^ 3`)
requires operating in the list-decoding (Johnson) regime `θ > √ρ`
(relative distance `δ < 1 - √ρ`).

This file wires the list-decoding peeling reduction (`ProximityGap/JohnsonMCA.lean`)
and the interleaved Johnson bound (`ProximityGap/Johnson.lean`) into
`Exec.soundness` (`Exec/Soundness.lean`) and instantiates the result for the
verified Goldilocks cubic trinomial extension `Fp3` (`P3/GoldilocksExt3.lean`):

* `Exec.soundness_johnson`: soundness of `Fri.verify` at any agreement `θ` with
  `0 < θ ≤ 1` and `ρ < θ ^ 2` (where `ρ = (1 / 2) ^ params.logBlowup`), assuming
  `CurveListCA K T` bounded per curve term by `cT`. With
  `L_J = (θ - ρ) / (θ ^ 2 - ρ)` and `n = logMaxHeight params.logBlowup shape`,
  the round errors are:
  - batching: `(claimRefs.length) * (cT + L_J * ((1 - θ) * 2 ^ n)) / |K|`;
  - folding: `(2 * cT + L_J * ((1 - θ) * 2 ^ n)) / |K| / 2 ^ commitPowBits`;
  - query: `θ ^ numQueries / 2 ^ queryPowBits`.
* `Exec.soundness_johnson_sqrt_gap`: specialization to `θ = √ρ + η` (`η > 0`,
  `√ρ + η ≤ 1`).
* `CertiFri.P3.Exec.goldilocksExt3_soundness_johnson`: concrete instantiation
  for `Goldilocks` / `GoldilocksExt3` (`|K| = Goldilocks.order ^ 3 ≈ 2 ^ 192`).

## What is assumed

Everything `Exec/Soundness.lean` assumes, plus `CurveListCA K T` (list-decoding
correlated agreement in the Johnson regime, e.g. BCIKS20 Theorem 6.2, BCHKS25,
or DKT26). The algebraic Guruswami–Sudan core up to the parametric annihilator
over `RatFunc K` is proved unconditionally in `ProximityGap/GuruswamiSudan.lean`;
see its module docstring for the remaining factorization / Hensel-lifting bridge.
-/

namespace CertiFri

open Polynomial Finset

section CurveMCATrivial

variable {F : Type*} [Field F] [Fintype F]

/-- `CurveMCA` holds vacuously for `m = 0` or `m = 1` with zero bad challenges
and any nonnegative error bound. -/
private theorem curveMCA_of_le_one (D : Finset F) (d m : ℕ) (hm : m ≤ 1) (θ ε : ℝ) (hε : 0 ≤ ε) :
    CurveMCA D d m θ ε := by
  intro u
  refine ⟨∅, ?_, fun _ _ p hp B _ _ hagree => ?_⟩
  · simp only [card_empty, Nat.cast_zero]
    exact mul_nonneg hε (Nat.cast_nonneg _)
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · exact ⟨Fin.elim0, fun k => k.elim0, fun k => k.elim0⟩
    · refine ⟨fun _ => p, fun _ => hp, fun k x hx => ?_⟩
      have hk : k = 0 := Subsingleton.elim k 0
      subst hk
      have h := hagree x hx
      simpa using h

end CurveMCATrivial

namespace Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)
  [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- **Soundness of the executable verifier up to the Johnson radius (`θ > √ρ`).**

Assume `CurveListCA K T` (`ProximityGap/JohnsonMCA.lean`) with per-term bound
`cT ≥ 0` on every level `j ≤ rounds` (for `2 ≤ k` curve terms). Let
`ρ = (1 / 2) ^ params.logBlowup`, `0 < θ ≤ 1`, and `ρ < θ ^ 2`, and let
`L_J = (θ - ρ) / (θ ^ 2 - ρ)` be the relative Johnson list-size bound.
Then `Fri.verify` satisfies the random-oracle soundness bound at agreement `θ`
with query error `θ ^ numQueries / 2 ^ queryPowBits`. -/
theorem soundness_johnson {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA K T)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  let LJ : ℝ := (θ - ρ) / (θ ^ 2 - ρ)
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : P.finalDegree = 2 ^ params.logFinalPolyLen := rfl
  have hLJ_nn : 0 ≤ LJ := by
    have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
    have hnum : 0 ≤ θ - ρ := by nlinarith
    exact div_nonneg hnum hden.le
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hdeg_le : ∀ j ≤ P.rounds,
      ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * ((twoAdicDomain P.ω P.n j).card : ℝ) := by
    intro j hj
    rw [hfinal, Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj]
    push_cast
    have h1 : ρ * (2 : ℝ) ^ params.logBlowup = 1 := by
      dsimp only [ρ]
      rw [← mul_pow]
      norm_num
    rw [← mul_assoc, h1, one_mul]
  have hcard_dom : ∀ j ≤ P.rounds,
      (twoAdicDomain P.ω P.n j).card = 2 ^ (P.n - j) := by
    intro j hj
    exact card_twoAdicDomain P.prim (by omega)
  let εα : ℕ → ℝ := fun j =>
    ((P.numClaims j - 1 : ℕ) : ℝ) *
      (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  let εβ : ℕ → ℝ := fun _ =>
    (2 * cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hmca : ∀ j ≤ P.rounds,
      CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j) θ (εα j) := by
    intro j hj
    by_cases hk : P.numClaims j ≤ 1
    · refine curveMCA_of_le_one _ _ _ hk θ (εα j) ?_
      dsimp only [εα]
      positivity
    · have hk2 : 2 ≤ P.numClaims j := by omega
      have hcard_img : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card = 2 ^ (P.n - j) := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), hcard_dom j hj]
      have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
        rw [hcard_img]
        exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n j)
      have hd_img : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
          ρ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
        exact hdeg_le j hj
      have hTj : (T ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card
          (2 ^ (P.rounds - j) * P.finalDegree)
          ⌈θ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ)⌉₊
          (P.numClaims j) : ℝ) ≤ ((P.numClaims j - 1 : ℕ) : ℝ) * cT := by
        rw [hcard_img, hfinal]
        push_cast
        exact hT j (P.numClaims j) hj hk2
      have hcurve := curveMCA_of_curveListCA_of_card_le hca
        ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) (P.numClaims j)
        hθ0 hθ1 hd_img hgap (by positivity) hTj hcard_le
      refine ProximityGap.curveMCA_mono hcurve le_rfl ?_
      dsimp only [εα, LJ, ρ]
      refine le_of_eq ?_
      ring
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i) := by
    intro i hi
    have hi1 : i + 1 ≤ P.rounds := hi
    have hn1 : 1 ≤ P.n := by omega
    have hcard_i1 : (twoAdicDomain P.ω P.n (i + 1)).card = 2 ^ (P.n - (i + 1)) :=
      hcard_dom (i + 1) hi1
    have hcard_le : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ (2 : ℝ) ^ (P.n - 1) := by
      rw [hcard_i1]
      exact_mod_cast Nat.pow_le_pow_right two_pos (by omega)
    have hTi : (T (twoAdicDomain P.ω P.n (i + 1)).card
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
        ⌈θ * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ)⌉₊ 3 : ℝ) ≤ 2 * cT := by
      rw [hcard_i1, hfinal]
      push_cast
      have h := hT (i + 1) 3 hi1 (by omega)
      norm_num at h
      exact h
    have hst := stepMCA_of_curveListCA_of_card_le hca (P.ldt.step i hi)
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
      hθ0 hθ1 (hdeg_le (i + 1) hi1) hgap (by positivity) hTi hcard_le
    have h2pow : 2 * (2 : ℝ) ^ (P.n - 1) = (2 : ℝ) ^ P.n := by
      conv_rhs => rw [← Nat.sub_add_cancel hn1, pow_succ']
    have heq : (2 * cT + 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1)))) / Fintype.card K = εβ i := by
      dsimp only [εβ]
      have : 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1))) =
          LJ * ((1 - θ) * (2 * (2 : ℝ) ^ (P.n - 1))) := by ring
      rw [this, h2pow]
    rwa [heq] at hst
  refine soundness m params shape wf hθ0.le hmca hstep ?_ ?_ hq hadv attempt
  · -- Batching sum bounded by `claimRefs.length`.
    dsimp only [εα]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have hsum : (∑ j ∈ Finset.range (P.rounds + 1), ((P.numClaims j - 1 : ℕ) : ℝ)) ≤
        ((claimRefs params.logBlowup shape).length : ℝ) := by
      exact_mod_cast sum_numClaims_sub_one_le m params shape wf
    refine le_trans ?_ hα
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsum (by positivity)) (Nat.cast_nonneg _)
  · intro i _
    exact hβ

/-- **Soundness of `Fri.verify` at Johnson agreement `θ = √ρ + η`.**

Specialization of `soundness_johnson` to `θ = Real.sqrt ρ + η` for any
margin `η > 0` with `√ρ + η ≤ 1`, where `ρ = (1 / 2) ^ params.logBlowup`. -/
theorem soundness_johnson_sqrt_gap {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA K T)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {η cT : ℝ} (hη0 : 0 < η)
    (hθ1 : Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η ≤ 1)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈(Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η) *
          (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η - (1 / 2 : ℝ) ^ params.logBlowup) /
            ((Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - (Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η)) *
            (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K ≤ εmax)
    (hβ : (2 * cT + ((Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η - (1 / 2 : ℝ) ^ params.logBlowup) /
            ((Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - (Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η)) *
            (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η) ^ params.numQueries /
        2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift
          (Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η)
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  have hρpos : (0 : ℝ) < (1 / 2 : ℝ) ^ params.logBlowup := by positivity
  have hsqrt : 0 < Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) := Real.sqrt_pos.mpr hρpos
  have hθ0 : 0 < Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η := by linarith
  have hgap : (1 / 2 : ℝ) ^ params.logBlowup <
      (Real.sqrt ((1 / 2 : ℝ) ^ params.logBlowup) + η) ^ 2 := by
    have hsq := Real.sq_sqrt hρpos.le
    nlinarith
  exact soundness_johnson m params shape wf hca hheight hθ0 hθ1 hgap hcT0 hT hα hβ hq hadv attempt

end Exec

namespace P3.Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

/-- **Soundness of `Fri.verify` over Goldilocks cubic trinomial `Fp3`
(`X^3 - X - 1`, `|K| = p^3 ≈ 2^192`) up to the Johnson radius (`θ > √ρ`).**

Instantiates `Exec.soundness_johnson` with the verified `goldilocksExt3_fieldModel`
and `goldilocksExt3_wellFormed`, substituting `Fintype.card Fp3Model = Goldilocks.order ^ 3`. -/
theorem goldilocksExt3_soundness_johnson {D : Type} [DecidableEq D] [Inhabited D] [Fintype D]
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
    (params : FriParams) (shape : ClaimShape)
    (hlog : logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (CertiFri.Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hlog)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → CertiFri.Exec.Attempt Goldilocks GoldilocksExt3 D) :
    prob (fun res l =>
        (∃ f : ∀ x, CertiFri.Exec.OracleAnswer (D := D) goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog) x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            CertiFri.Exec.accepts goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog) f (attempt res.1) = true) ∧
        ClaimsFail (CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).ldt
          (CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).shift θ
          ((CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).claims
            (CertiFri.Exec.view goldilocksExt3_fieldModel params shape
              (firstMessage (attempt res.1).commitments
                (attempt res.1).points (attempt res.1).values))
            (committedRow l)))
      (CertiFri.Exec.experiment goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hlog) adv attempt) [] ≤
      (Q + ((CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
          (CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) * εmax +
        ((max ((CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).batches +
          (CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
            (goldilocksExt3_wellFormed params shape hlog)).rounds + 2) +
            (CertiFri.Exec.modelParams goldilocksExt3_fieldModel params shape
              (goldilocksExt3_wellFormed params shape hlog)).verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model]
    push_cast
    rfl
  exact CertiFri.Exec.soundness_johnson goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hlog) hca hheight hθ0 hθ1 hgap hcT0 hT
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

end P3.Exec

end CertiFri
