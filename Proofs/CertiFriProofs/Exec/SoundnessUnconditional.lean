import CertiFriProofs.Theory.ProximityGap.UniqueDecoding
import CertiFriProofs.Exec.SoundnessUD

/-!
# Soundness of the executable verifier with no proximity hypothesis

The soundness theorems of `Exec/Soundness.lean` take two hypotheses about
Reed–Solomon codes, `CurveMCA` (batching) and `StepMCA` (folding). Up to the
unique-decoding radius both are theorems: `curveCA_udThreshold`
(`Theory/ProximityGap/UniqueDecoding.lean`) proves correlated agreement there,
and `Theory/ProximityGap/UniqueDecodingMCA.lean` derives the two hypotheses
from it. This file states the results with nothing left to assume about the
code.

* `curveMCA_uniqueDecoding`, `stepMCA_uniqueDecoding`: the two hypotheses, for
  every relative distance `δ` with `2 * (δ * D.card) + d ≤ D.card`, that is
  `δ ≤ (1 - ρ) / 2` for the rate `ρ = d / D.card`.
* `Exec.soundness_uniqueDecoding`: soundness of `Fri.verify` at agreement
  `1 - δ`, for `2 * δ + (1 / 2) ^ logBlowup ≤ 1`.

## The errors

With `n = logMaxHeight params.logBlowup shape`, the log of the size of the
first domain, and `c = 2 ^ n * (δ * 2 ^ n + 1) + 1`:

* batching round: `(number of claimed values) * c / |K|`;
* each folding round: `2 * c / |K| / 2 ^ commitPowBits`;
* query round: `(1 - δ) ^ numQueries / 2 ^ queryPowBits`.

`c` is quadratic in the size of the domain, so the first two errors are small
only when the field is much larger than the square of the domain.

## What is assumed

What `Exec/Soundness.lean` lists, except the two proximity hypotheses: the
random-oracle model with chained challenges, ideal primitives, `FieldModel`
and `WellFormed`, Merkle commitments with one path per query, a fixed shape.

## Not covered

Relative distances beyond the unique-decoding radius, where `Exec.soundness`
keeps its hypotheses. Everything `Exec/Soundness.lean` lists as not covered.
-/

namespace CertiFri

open Polynomial

section Gap

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **The batching hypothesis, proved up to the unique-decoding radius.** If
`2 * (δ * D.card) + d ≤ D.card`, then `CurveMCA` holds for curves of any number
`m` of terms at agreement `1 - δ`, with error
`(m - 1) * (D.card * (δ * D.card + 1) + 1) / |F|`. -/
theorem curveMCA_uniqueDecoding (D : Finset F) (d m : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hdist : 2 * (δ * D.card) + d ≤ D.card) :
    CurveMCA D d m (1 - δ)
      (((m - 1 : ℕ) : ℝ) * (D.card * (δ * D.card + 1) + 1) / Fintype.card F) :=
  curveMCA_of_curveCA (curveCA_udThreshold F) D d m δ hδ hdist

/-- **The folding hypothesis, proved up to the unique-decoding radius.** If
`2 * (δ * D'.card) + d' ≤ D'.card`, then `StepMCA` holds at agreement `1 - δ`
with error `2 * (D'.card * (δ * D'.card + 1) + 1) / |F|`. -/
theorem stepMCA_uniqueDecoding {D D' : Finset F} (hstep : SquareStep D D') (d' : ℕ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hdist : 2 * (δ * D'.card) + d' ≤ D'.card) :
    StepMCA D D' d' (1 - δ) (2 * (D'.card * (δ * D'.card + 1) + 1) / Fintype.card F) :=
  stepMCA_of_curveCA (curveCA_udThreshold F) hstep d' hδ hdist

end Gap

namespace Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)
  [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- **Soundness of the executable verifier up to the unique-decoding radius,
with no proximity hypothesis.**

Let no committed column be shorter than the final height, and let `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Whatever the adversary, as long as it makes
at most `Q` oracle queries, the probability that `Fri.verify` accepts its
attempt while the claims fail at agreement `1 - δ` is at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|),

with `N = Q + (rounds + 2) + verifierQueries`, provided `εmax` bounds the error
of every round. With `n = logMaxHeight params.logBlowup shape` and
`c = 2 ^ n * (δ * 2 ^ n + 1) + 1`, these are
`(number of claimed values) * c / |K|` for the batching round,
`2 * c / |K| / 2 ^ commitPowBits` for a folding round, and
`(1 - δ) ^ numQueries / 2 ^ queryPowBits` for the query round.

The experiment, the event and the remaining assumptions are those of
`Exec.soundness`. -/
theorem soundness_uniqueDecoding
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((2 : ℝ) ^ logMaxHeight params.logBlowup shape *
          (δ * 2 ^ logMaxHeight params.logBlowup shape + 1) + 1) / Fintype.card K ≤ εmax)
    (hβ : 2 * ((2 : ℝ) ^ logMaxHeight params.logBlowup shape *
          (δ * 2 ^ logMaxHeight params.logBlowup shape + 1) + 1) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift
          (1 - δ)
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        (((modelParams m params shape wf).batches + 1) *
            ((modelParams m params shape wf).rounds + 2) + 3) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries - 1) / (2 * Fintype.card D) :=
  soundness_of_curveCA_of_claimRefs m params shape wf (curveCA_udThreshold K) hheight hδ hrate
    hα hβ hq hadv attempt

end Exec

end CertiFri
