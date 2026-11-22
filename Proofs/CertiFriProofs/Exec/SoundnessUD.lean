import CertiFriProofs.Exec.Soundness
import CertiFriProofs.Theory.Compiled.SoundnessUD

/-!
# Soundness of the executable verifier at the unique-decoding radius

`Exec.soundness` (`Exec/Soundness.lean`) bounds the probability that the
executable verifier `Fri.verify` accepts claims that fail, under the batching
hypothesis `CurveMCA` and the folding hypothesis `StepMCA`. Here both are
discharged from correlated agreement in the unique-decoding regime
(`CurveCA K udThreshold`, `Theory/ProximityGap/CorrelatedAgreement.lean`), for
agreement `θ = 1 - δ` with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`: any relative
distance `δ` up to the unique-decoding radius of the rate `2 ^ (-logBlowup)`.

## Results

* `soundness_of_curveCA`: `Exec.soundness` at agreement `1 - δ` with no
  proximity hypothesis. With `n = logMaxHeight params.logBlowup shape` and
  `c = (1 + δ) * 2 ^ n`, the error of the batching round is
  `(∑ j ≤ rounds, (numClaims j - 1)) * c / |K|`, that of a folding round
  `c / |K| / 2 ^ commitPowBits`, and that of the query round
  `(1 - δ) ^ numQueries / 2 ^ queryPowBits`.
* `sum_numClaims_sub_one_le`: the sum in the batching error is at most the
  number of claimed values, `(claimRefs params.logBlowup shape).length`.
* `soundness_of_curveCA_of_claimRefs`: `soundness_of_curveCA` with the batching
  error `(claimRefs params.logBlowup shape).length * c / |K|`.

## What is assumed

`CurveCA K udThreshold`, as a hypothesis of both soundness theorems, and what
`Exec.soundness` assumes other than `hmca` and `hstep`: the random-oracle model
with chained challenges, `FieldModel`, `WellFormed`, and ideal primitives. The
module documentation of `Exec/Soundness.lean` lists these and describes the
experiment and the event.

## What is not covered

The proof of `CurveCA K udThreshold`. Relative distances beyond the
unique-decoding radius, for which `Exec.soundness` keeps its two proximity
hypotheses. Everything `Exec/Soundness.lean` lists as not covered.
-/

namespace CertiFri.Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-! ## The number of claims -/

/-- If every element of a list satisfies at most one of the predicates `p j`
with `j` in `s`, the sublists selected by these predicates have no more
elements in total than the list. -/
private theorem sum_length_filter_le {α : Type*} (l : List α) (s : Finset ℕ) (p : ℕ → α → Bool)
    (hp : ∀ a, ∀ i ∈ s, ∀ j ∈ s, p i a = true → p j a = true → i = j) :
    ∑ j ∈ s, (l.filter (p j)).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hcons : ∀ j, ((a :: l).filter (p j)).length =
        (if p j a = true then 1 else 0) + (l.filter (p j)).length := by
      intro j
      rw [List.filter_cons]
      split <;> simp [Nat.add_comm]
    have hone : ∑ j ∈ s, (if p j a = true then 1 else 0) ≤ 1 := by
      rw [← Finset.card_filter]
      exact Finset.card_le_one.mpr fun i hi j hj =>
        hp a i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
          (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    simp only [hcons, Finset.sum_add_distrib, List.length_cons]
    omega

omit [DecidableEq K] [DecidableEq D] [Inhabited D] in
/-- **The number of terms of the batching error.** Level `j` of the model holds
`numClaims j` claims and contributes `numClaims j - 1` to the batching error.
Over all levels this is at most the number of claimed values of the shape: the
claims of the levels are disjoint sublists of `claimRefs`. -/
theorem sum_numClaims_sub_one_le :
    ∑ j ∈ Finset.range (numRounds params shape + 1),
        ((modelParams m params shape wf).numClaims j - 1) ≤
      (claimRefs params.logBlowup shape).length := by
  refine (Finset.sum_le_sum fun j _ => Nat.sub_le _ 1).trans ?_
  refine sum_length_filter_le (claimRefs params.logBlowup shape) _
    (fun j c => c.logHeight + j == logMaxHeight params.logBlowup shape) fun c i _ j _ hi hj => ?_
  rw [beq_iff_eq] at hi hj
  omega

/-! ## Soundness -/

section Soundness

variable [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- **Soundness of the executable verifier at the unique-decoding radius, with
no proximity hypothesis.**

Assume correlated agreement with the threshold `udThreshold` over the field `K`
of the model. Let no committed column be shorter than the final height, and let
`δ ≥ 0` with `2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Then `soundness` holds at
agreement `θ = 1 - δ` with neither the batching nor the folding hypothesis:
whatever the adversary, as long as it makes at most `Q` oracle queries, the
probability that the executable verifier accepts its attempt while the claims
of the attempt fail is at most

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

with `N = Q + (rounds + 2) + P.verifierQueries`. The doc comment of `soundness`
says what "accepts" and "the claims fail" mean.

With `n = logMaxHeight params.logBlowup shape`, the log of the size of the
first domain, and `c = (1 + δ) * 2 ^ n`, the number `εmax` bounds
the error of every round:

* the batching round, `(∑ j ≤ rounds, (numClaims j - 1)) * c / |K|`, where
  `numClaims j` is the number of claims of level `j`;
* each folding round, `c / |K| / 2 ^ commitPowBits`;
* the query round, `(1 - δ) ^ numQueries / 2 ^ queryPowBits`. -/
theorem soundness_of_curveCA (hca : CurveCA K udThreshold)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : (∑ j ∈ Finset.range (numRounds params shape + 1),
          (((modelParams m params shape wf).numClaims j - 1 : ℕ) : ℝ)) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift (1 - δ)
          ((modelParams m params shape wf).claims (view m params shape (firstMessage (attempt res.1).commitments
            (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches + (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) ^ 2 /
          (4 * Fintype.card D) :=
  (modelParams m params shape wf).soundness_grind_view_of_imp_of_curveCA hca (powBits params shape)
    (view m params shape) (logBlowup := params.logBlowup) (logFinalPolyLen := params.logFinalPolyLen)
    (by
      show logMaxHeight params.logBlowup shape =
        numRounds params shape + params.logBlowup + params.logFinalPolyLen
      unfold numRounds FriParams.logFinalHeight at *
      omega)
    rfl hδ hrate
    (by rw [powBits_zero, pow_zero, div_one]; exact hα)
    (fun i hi => by rw [powBits_succ_of_lt params shape hi]; exact hβ)
    (by rw [show (modelParams m params shape wf).rounds = numRounds params shape from rfl,
      powBits_last]; exact hq)
    hadv (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)
    (fun a l => ∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
      (∀ x y, l.dlookup x = some y → f x = y) ∧ accepts m params shape wf f (attempt a) = true)
    (fun out l b l' hexp hver hE => by
      obtain ⟨f, hf, hacc⟩ := hE
      have hrun := (modelParams m params shape wf).run_verifyGrindView_of_outcome hexp hver f
      rw [toFun_eq_self hf] at hrun
      exact hrun.symm.trans (run_model_of_accepts m params shape wf f _ hacc))

/-- **Soundness of the executable verifier at the unique-decoding radius, with
the batching error in terms of the number of claimed values.**

`soundness_of_curveCA` with the error of the batching round bounded by
`(claimRefs params.logBlowup shape).length * c / |K|`, where
`c = (1 + δ) * 2 ^ n` and `n = logMaxHeight params.logBlowup shape`.
The length of `claimRefs` is the number of claimed values of the shape, the
length of `values` that `Fri.verify` requires. -/
theorem soundness_of_curveCA_of_claimRefs (hca : CurveCA K udThreshold)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift (1 - δ)
          ((modelParams m params shape wf).claims (view m params shape (firstMessage (attempt res.1).commitments
            (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches + (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) + (modelParams m params shape wf).verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  refine soundness_of_curveCA m params shape wf hca hheight hδ hrate (le_trans ?_ hα) hβ hq hadv
    attempt
  have hsum : (∑ j ∈ Finset.range (numRounds params shape + 1),
      (((modelParams m params shape wf).numClaims j - 1 : ℕ) : ℝ)) ≤
      ((claimRefs params.logBlowup shape).length : ℝ) := by
    exact_mod_cast sum_numClaims_sub_one_le m params shape wf
  gcongr

end Soundness

end CertiFri.Exec
