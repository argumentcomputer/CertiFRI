import CertiFriProofs.Theory.Compiled.SoundnessView
import CertiFriProofs.Theory.ProximityGap.UniqueDecodingMCA

/-!
# Soundness of the compiled protocol at the unique-decoding radius

The soundness theorems of `Compiled/SoundnessView.lean` take the batching
hypothesis `CurveMCA` and the folding hypothesis `StepMCA`. Here both are
discharged from correlated agreement in the unique-decoding regime
(`CurveCA F udThreshold`, `ProximityGap/CorrelatedAgreement.lean`), in Plonky3's
parameters: `n = rounds + logBlowup + logFinalPolyLen` and
`finalDegree = 2 ^ logFinalPolyLen`, so that every level has rate
`2 ^ (-logBlowup)`. The agreement is `θ = 1 - δ` for any `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup ≤ 1`, that is, any relative distance up to the
unique-decoding radius `(1 - ρ) / 2` of the rate `ρ = 2 ^ (-logBlowup)`.

## Results

* `Params.curveMCA_of_rate_of_curveCA`: the batching hypothesis of every level,
  for curves of any number `m` of terms, with error
  `(m - 1) * (2 ^ n * (δ * 2 ^ n + 1) + 1) / |F|`.
* `Params.stepMCA_of_rate_of_curveCA`: the folding hypothesis of every round,
  with error `2 * (2 ^ n * (δ * 2 ^ n + 1) + 1) / |F|`.
* `Params.soundness_grind_view_of_imp_of_curveCA`:
  `Params.soundness_grind_view_of_imp` at agreement `1 - δ` with no proximity
  hypothesis, for any event that holds only when the model verifier accepted.
* `Params.soundness_grind_view_of_curveCA`: the same for the event that the
  model verifier accepts.

The errors are stated with the size `2 ^ n` of the first domain at every level.
Level `j` has `2 ^ (n - j)` points; `curveMCA_of_curveCA_of_card_le` and
`stepMCA_of_curveCA_of_card_le` give the errors with that size.

## What is assumed

`CurveCA F udThreshold`, as a hypothesis of every theorem, and the assumptions
of `Params.soundness_grind_view_of_imp` other than `hmca` and `hstep`: the
random-oracle model with chained challenges and the modelling choices of
`Compiled/Read.lean` and `Compiled/Verifier.lean`.

## Not covered

The proof of `CurveCA F udThreshold`. Relative distances beyond the
unique-decoding radius: for those, `Params.soundness_grind_view_of_imp` keeps
its two proximity hypotheses.
-/

namespace CertiFri.Compiled

open Oracle OracleComp
open PcsRbr (Chal ClaimsFail GrindChal)

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

namespace Params

variable (P : Params F)

/-! ## The proximity hypotheses in Plonky3's parameters -/

omit [Fintype F] in
/-- The coset on which the inputs of level `j` are committed has no more points
than the first domain. -/
private theorem card_image_shift_le (j : ℕ) :
    (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ 2 ^ P.n := by
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
  rw [twoAdicDomain]
  refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
  rw [Finset.card_range]
  exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)

/-- **The batching hypothesis in Plonky3's parameters, at the unique-decoding
radius.** Assume correlated agreement with the threshold `udThreshold`. Let
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`,
and let `δ ≥ 0` with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then on the coset of
every level `j ≤ rounds`, `CurveMCA` holds at agreement `1 - δ` for curves of
any number `m` of terms, with error
`(m - 1) * (2 ^ n * (δ * 2 ^ n + 1) + 1) / |F|`. -/
theorem curveMCA_of_rate_of_curveCA (hca : CurveCA F udThreshold) {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ logBlowup ≤ 1) {j : ℕ} (hj : j ≤ P.rounds) (m : ℕ) :
    CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) m (1 - δ)
      (((m - 1 : ℕ) : ℝ) * ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F) := by
  refine curveMCA_of_curveCA_of_card_le hca _ _ m hδ ?_ (P.card_image_shift_le j)
  have h := Compose.twoAdic_relDist hn P.prim hrate (i := j) hj
  rw [← hfinal] at h
  rwa [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]

/-- **The folding hypothesis in Plonky3's parameters, at the unique-decoding
radius.** Assume correlated agreement with the threshold `udThreshold`. Let
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`,
and let `δ ≥ 0` with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then every folding round
satisfies `StepMCA` at agreement `1 - δ`, with error
`2 * (2 ^ n * (δ * 2 ^ n + 1) + 1) / |F|`. -/
theorem stepMCA_of_rate_of_curveCA (hca : CurveCA F udThreshold) {logBlowup logFinalPolyLen : ℕ}
    (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ logBlowup ≤ 1) {i : ℕ} (hi : i < P.rounds) :
    StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ)
      (2 * ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F) := by
  refine stepMCA_of_curveCA_of_card_le hca (P.ldt.step i hi) _ hδ ?_ ?_
  · have h := Compose.twoAdic_relDist hn P.prim hrate (i := i + 1) hi
    rwa [← hfinal] at h
  · rw [ldt_domain, card_twoAdicDomain P.prim (by have := P.rounds_le; omega)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le _ _)

/-! ## Soundness with no proximity hypothesis -/

/-- **Soundness for an event that implies acceptance, on raw messages, at the
unique-decoding radius, with no proximity hypothesis.**

`soundness_grind_view_of_imp` at agreement `θ = 1 - δ`, in Plonky3's parameters:
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`.
Assume correlated agreement with the threshold `udThreshold`, and let `δ ≥ 0`
with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then neither the batching hypothesis nor
the folding hypothesis is needed. With `c = 2 ^ n * (δ * 2 ^ n + 1) + 1`, the
number `εmax` bounds the error of every round, divided by `2 ^ bits i` in round
`i`:

* the batching round, `(∑ j ≤ rounds, (numClaims j - 1)) * c / |F|`;
* each folding round, `2 * c / |F|`;
* the query round, `(1 - δ) ^ queries`.

In the experiment `experimentGrindView`, let `E` be an event of the adversary's
output and the final log that holds only when the model verifier accepted.
Then the probability that `E` holds while the claims of the adversary's first
message, read through `view`, fail is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + (rounds + 2) + P.verifierQueries`. -/
theorem soundness_grind_view_of_imp_of_curveCA (hca : CurveCA F udThreshold)
    {M : Type} [DecidableEq M] (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    {logBlowup logFinalPolyLen : ℕ} (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ logBlowup ≤ 1) {εmax : ℝ}
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), ((P.numClaims j - 1 : ℕ) : ℝ)) *
        ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds,
      2 * ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F / 2 ^ bits (i + 1) ≤ εmax)
    (hq : (1 - δ) ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries)
    (E : A → Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) → Prop)
    (hE : ∀ (out : A × Transcript M (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)) (b : Bool)
      (l' : Log (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l →
      Outcome (P.verifyGrindView bits view (proofOf out.1) out.2) l b l' →
      E out.1 l' → b = true) :
    prob (fun res l => E res.1 l ∧
        ClaimsFail P.ldt P.shift (1 - δ) (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries) *
          (Q + (P.rounds + 2) + P.verifierQueries - 1) / (2 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  refine P.soundness_grind_view_of_imp bits view hθ
    (fun j hj => P.curveMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hj (P.numClaims j))
    (fun i hi => P.stepMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hi) ?_ hβ hq hadv msgs
    proofOf E hE
  rw [← Finset.sum_div, ← Finset.sum_mul]
  exact hα

/-- **Soundness with proof of work, on raw messages, at the unique-decoding
radius, with no proximity hypothesis.**

`soundness_grind_view` at agreement `θ = 1 - δ`, in Plonky3's parameters:
`n = rounds + logBlowup + logFinalPolyLen` and `finalDegree = 2 ^ logFinalPolyLen`.
Assume correlated agreement with the threshold `udThreshold`, and let `δ ≥ 0`
with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Whatever the adversary, as long as it
makes at most `Q` oracle queries: in the experiment `experimentGrindView`, the
probability that the model verifier accepts while the claims of the adversary's
first message, read through `view`, fail is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + (rounds + 2) + P.verifierQueries`. The number `εmax` bounds the
error of every round as in `soundness_grind_view_of_imp_of_curveCA`. -/
theorem soundness_grind_view_of_curveCA (hca : CurveCA F udThreshold)
    {M : Type} [DecidableEq M] (bits : ℕ → ℕ) (view : M → Msg F D P.batches)
    {logBlowup logFinalPolyLen : ℕ} (hn : P.n = P.rounds + logBlowup + logFinalPolyLen)
    (hfinal : P.finalDegree = 2 ^ logFinalPolyLen) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ logBlowup ≤ 1) {εmax : ℝ}
    (hα : (∑ j ∈ Finset.range (P.rounds + 1), ((P.numClaims j - 1 : ℕ) : ℝ)) *
        ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds,
      2 * ((2 : ℝ) ^ P.n * (δ * 2 ^ P.n + 1) + 1) / Fintype.card F / 2 ^ bits (i + 1) ≤ εmax)
    (hq : (1 - δ) ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M (GrindChal bits (Chal P.ldt P.queries)) F D) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : A → ℕ → M) (proofOf : A → Proof F D P.batches P.queries) :
    prob (fun res l => res.2 = true ∧
        ClaimsFail P.ldt P.shift (1 - δ) (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindView bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((P.batches + 1) * (P.rounds + 2) + 3) * (Q + (P.rounds + 2) + P.verifierQueries) *
          (Q + (P.rounds + 2) + P.verifierQueries - 1) / (2 * Fintype.card D) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) logBlowup
    linarith
  refine P.soundness_grind_view bits view hθ
    (fun j hj => P.curveMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hj (P.numClaims j))
    (fun i hi => P.stepMCA_of_rate_of_curveCA hca hn hfinal hδ hrate hi) ?_ hβ hq hadv msgs
    proofOf
  rw [← Finset.sum_div, ← Finset.sum_mul]
  exact hα

end Params

end CertiFri.Compiled
