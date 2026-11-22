import CertiFriProofs.Exec.SoundnessUnconditional
import CertiFriProofs.Theory.Compiled.TwoAttempts

/-!
# Soundness of the executable verifier for two attempts

`Exec.soundness` (`Exec/Soundness.lean`) is about an adversary that outputs one
attempt: a statement and a proof. Here the adversary outputs two attempts, and
both are verified against the same oracle. The theorems bound the probability
that the executable verifier `Fri.verify` accepts one of the two attempts while
the claims of that attempt fail, where both "accepts" and "the claims fail" are
read on the final log of the experiment, after both verifications. A statement
about two openings of one commitment is a statement of this form.

## Definitions

* `Accepted m params shape wf a l`: the executable verifier accepts the attempt
  `a` on the log `l`. This is the acceptance event of `Exec.soundness`.
* `Fails m params shape wf θ a l`: the claims of the attempt `a` fail at
  agreement `θ` for the functions that the hash queries of `l` commit to. This
  is the failure event of `Exec.soundness`.
* `experiment₂`: the adversary runs; then, for its first attempt and after it
  for its second, the challenge queries of the transcript and the hash queries
  of the verification are made.

## Results

With `N = Q + 2 * ((rounds + 2) + verifierQueries)`, the number of oracle
queries of the experiment for an adversary with at most `Q` queries:

* `soundness₂`: under the proximity hypotheses of `Exec.soundness`, the
  probability that one of the two attempts is accepted on the final log while
  its claims fail on the final log is at most

      2 * (N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|)).

* `soundness₂_uniqueDecoding`: the same at agreement `1 - δ`, for
  `2 * δ + (1 / 2) ^ logBlowup ≤ 1`, with no proximity hypothesis, as
  `Exec.soundness_uniqueDecoding` is to `Exec.soundness`.

## What is assumed

What `Exec/Soundness.lean` lists: the random-oracle model with chained
challenges, ideal primitives, `FieldModel` and `WellFormed`, Merkle commitments
with one path per query, a fixed shape; for `soundness₂`, the proximity
hypotheses `CurveMCA` and `StepMCA`.

## What is not covered

* Any relation between the two attempts. The theorems hold for every pair; that
  two attempts open the same commitments is for the statement that uses them.
* More than two attempts.
* Everything `Exec/Soundness.lean` lists as not covered.
-/

namespace CertiFri.Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)
  [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-! ## The events -/

/-- **The executable verifier accepts the attempt `a` on the log `l`.** Some
total answer function `f` that agrees with `l` makes `Fri.verify` return `true`
on the attempt, when its commitment schemes are Merkle trees over the hash
functions of `f` and its challenger is the idealised challenger over `f`
(`accepts`). A log that extends `l` allows fewer such functions. -/
def Accepted (a : Attempt F EF D) (l : Log (OracleAnswer (D := D) m params shape wf)) : Prop :=
  ∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
    (∀ x y, l.dlookup x = some y → f x = y) ∧ accepts m params shape wf f a = true

/-- **The claims of the attempt `a` fail on the log `l`, at agreement `θ`.**
The claims are those of the statement of `a` for the model parameters, about
the functions that the hash queries of `l` open under the commitments of `a`
(`Compiled.Params.claims` with `Oracle.committedRow`). They fail when at some
level there is no set of at least `θ` of the coset on which every claimed
function of the level agrees, except possibly at its opening point, with a
polynomial of the degree bound of the level that takes the claimed value at the
opening point (`PcsRbr.ClaimsFail`). The doc comment of `Exec.soundness` spells
this out. -/
def Fails (θ : ℝ) (a : Attempt F EF D) (l : Log (OracleAnswer (D := D) m params shape wf)) :
    Prop :=
  ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
    ((modelParams m params shape wf).claims
      (view m params shape (firstMessage a.commitments a.points a.values)) (committedRow l))

omit [Fintype K] [Fintype D] in
/-- Acceptance on a log implies acceptance on every prefix of it. -/
theorem Accepted.of_prefix {a : Attempt F EF D}
    {l l' : Log (OracleAnswer (D := D) m params shape wf)} (h : Accepted m params shape wf a l')
    (hl : l <+: l') : Accepted m params shape wf a l := by
  obtain ⟨f, hf, hacc⟩ := h
  exact ⟨f, fun x y hxy => hf x y (dlookup_of_prefix hxy hl), hacc⟩

omit [Fintype K] [Fintype D] in
/-- **Refinement, on a log.** If the executable verifier accepts an attempt on
a log, the model verifier accepts, on that log, the proof data and the raw
messages of the attempt. -/
theorem acceptsLog_of_accepted {a : Attempt F EF D}
    {l : Log (OracleAnswer (D := D) m params shape wf)} (h : Accepted m params shape wf a l) :
    (modelParams m params shape wf).AcceptsLog (powBits params shape) (view m params shape)
      (modelProof m params shape a.proof) (a.messages params shape) l := by
  obtain ⟨f, hf, hacc⟩ := h
  exact ⟨f, hf, run_model_of_accepts m params shape wf f a hacc⟩

/-! ## The experiment -/

/-- **The experiment for two attempts.** The adversary runs and returns `a`.
Then, for `attempt₁ a` and after it for `attempt₂ a`: the challenge of every
round of the attempt's transcript is queried, and the hash queries of its
verification are made, by running the model verifier. All queries go to the
same oracle. The result is `a` and the model verifier's two verdicts. -/
noncomputable def experiment₂ {A : Type*}
    (adv : OracleComp (OracleAnswer (D := D) m params shape wf) A)
    (attempt₁ attempt₂ : A → Attempt F EF D) :
    OracleComp (OracleAnswer (D := D) m params shape wf) (A × Bool × Bool) :=
  (modelParams m params shape wf).experimentGrindView₂ (powBits params shape)
    (view m params shape) adv (fun a => (attempt₁ a).messages params shape)
    (fun a => (attempt₂ a).messages params shape)
    (fun a => modelProof m params shape (attempt₁ a).proof)
    (fun a => modelProof m params shape (attempt₂ a).proof)

omit [Fintype K] [Fintype D] in
/-- The experiment for two attempts makes the adversary's queries and, for each
attempt, one query per round of the transcript and the queries of the model
verifier. -/
theorem queryBound_experiment₂ {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt₁ attempt₂ : A → Attempt F EF D) :
    (experiment₂ m params shape wf adv attempt₁ attempt₂).QueryBound
      (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
        (modelParams m params shape wf).verifierQueries)) :=
  (modelParams m params shape wf).queryBound_experimentGrindView₂ _ _ hadv _ _ _ _

/-! ## Soundness -/

/-- **Soundness of the executable verifier for two attempts, in the
random-oracle model.**

*Statement.* Fix the parameters and the shape of the claims. Whatever the
adversary, as long as it makes at most `Q` oracle queries and outputs two
attempts: the probability that the executable verifier accepts one of the two
attempts while the claims of that attempt fail is at most

    2 * (N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|)),

where `N = Q + 2 * ((rounds + 2) + P.verifierQueries)` counts the oracle
queries of the experiment `experiment₂`, with `batches`, `rounds` and
`P.verifierQueries` as in `Exec.soundness`.

*The final log.* Both events, for both attempts, are about the final log `l` of
the experiment, which holds the answers to the adversary's queries and to the
challenge queries and the hash queries of both verifications. "Accepts" is
`Accepted`: some total answer function that agrees with `l` makes `Fri.verify`
return `true`. "The claims fail" is `Fails`: the claimed functions of the
attempt are read from the hash queries of `l`.

*Assumptions.* Those of `Exec.soundness`: `0 ≤ θ`; the batching hypothesis
`hmca` and the folding hypothesis `hstep` for the model parameters; `εmax`
bounds the error of every round: `∑ j ≤ rounds, εα j` for the batching round,
`εβ i / 2 ^ commitPowBits` for folding round `i`, and
`θ ^ numQueries / 2 ^ queryPowBits` for the query round. The module
documentation of `Exec/Soundness.lean` lists what is assumed of the fields and
of the primitives. -/
theorem soundness₂ {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds,
      CurveMCA
        ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          j).image ((modelParams m params shape wf).shift * ·))
        (2 ^ ((modelParams m params shape wf).rounds - j) *
          (modelParams m params shape wf).finalDegree)
        ((modelParams m params shape wf).numClaims j) θ (εα j))
    (hstep : ∀ i < (modelParams m params shape wf).rounds,
      StepMCA
        (twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n i)
        (twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          (i + 1))
        (2 ^ ((modelParams m params shape wf).rounds - (i + 1)) *
          (modelParams m params shape wf).finalDegree) θ (εβ i))
    (hα : ∑ j ∈ Finset.range ((modelParams m params shape wf).rounds + 1), εα j ≤ εmax)
    (hβ : ∀ i < (modelParams m params shape wf).rounds, εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt₁ attempt₂ : A → Attempt F EF D) :
    prob (fun res l =>
        (Accepted m params shape wf (attempt₁ res.1) l ∧
          Fails m params shape wf θ (attempt₁ res.1) l) ∨
        (Accepted m params shape wf (attempt₂ res.1) l ∧
          Fails m params shape wf θ (attempt₂ res.1) l))
      (experiment₂ m params shape wf adv attempt₁ attempt₂) [] ≤
      2 * ((Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) ^ 2 / (4 * Fintype.card D)) := by
  have h := (modelParams m params shape wf).soundness_grind_view₂ (powBits params shape)
    (view m params shape) hθ (εmax := εmax) hmca hstep
    (by rw [powBits_zero, pow_zero, div_one]; exact hα)
    (fun i hi => by rw [powBits_succ_of_lt params shape hi]; exact hβ i hi)
    (by rw [show (modelParams m params shape wf).rounds = numRounds params shape from rfl,
      powBits_last]; exact hq)
    hadv (fun a => (attempt₁ a).messages params shape)
    (fun a => (attempt₂ a).messages params shape)
    (fun a => modelProof m params shape (attempt₁ a).proof)
    (fun a => modelProof m params shape (attempt₂ a).proof)
  refine le_trans (prob_mono (fun res l hres => ?_) _ _) h
  exact hres.imp (fun h₁ => ⟨acceptsLog_of_accepted m params shape wf h₁.1, h₁.2⟩)
    fun h₂ => ⟨acceptsLog_of_accepted m params shape wf h₂.1, h₂.2⟩

/-- **Soundness of the executable verifier for two attempts up to the
unique-decoding radius, with no proximity hypothesis.**

Let no committed column be shorter than the final height, and let `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup ≤ 1`. Whatever the adversary, as long as it makes
at most `Q` oracle queries and outputs two attempts, the probability that
`Fri.verify` accepts one of the two attempts while the claims of that attempt
fail at agreement `1 - δ` is at most

    2 * (N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|)),

with `N = Q + 2 * ((rounds + 2) + verifierQueries)`, provided `εmax` bounds the
error of every round. With `n = logMaxHeight params.logBlowup shape` and
`c = (1 + δ) * 2 ^ n`, these are
`(number of claimed values) * c / |K|` for the batching round,
`c / |K| / 2 ^ commitPowBits` for a folding round, and
`(1 - δ) ^ numQueries / 2 ^ queryPowBits` for the query round.

The experiment and the events, both read on the final log, are those of
`soundness₂`; the error hypotheses are those of
`Exec.soundness_uniqueDecoding`. -/
theorem soundness₂_uniqueDecoding
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt₁ attempt₂ : A → Attempt F EF D) :
    prob (fun res l =>
        (Accepted m params shape wf (attempt₁ res.1) l ∧
          Fails m params shape wf (1 - δ) (attempt₁ res.1) l) ∨
        (Accepted m params shape wf (attempt₂ res.1) l ∧
          Fails m params shape wf (1 - δ) (attempt₂ res.1) l))
      (experiment₂ m params shape wf adv attempt₁ attempt₂) [] ≤
      2 * ((Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) ^ 2 / (4 * Fintype.card D)) := by
  have hθ : (0 : ℝ) ≤ 1 - δ := by
    have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) params.logBlowup
    linarith
  have hn : (modelParams m params shape wf).n =
      (modelParams m params shape wf).rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : (modelParams m params shape wf).finalDegree = 2 ^ params.logFinalPolyLen := rfl
  have hsum : (∑ j ∈ Finset.range (numRounds params shape + 1),
      (((modelParams m params shape wf).numClaims j - 1 : ℕ) : ℝ)) ≤
      ((claimRefs params.logBlowup shape).length : ℝ) := by
    exact_mod_cast sum_numClaims_sub_one_le m params shape wf
  refine soundness₂ m params shape wf hθ
    (εα := fun j => (((modelParams m params shape wf).numClaims j - 1 : ℕ) : ℝ) *
      ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K)
    (fun j hj => (modelParams m params shape wf).curveMCA_of_rate_of_curveCA
      (curveCA_udThreshold K) hn hfinal hδ hrate hj ((modelParams m params shape wf).numClaims j))
    (fun i hi => (modelParams m params shape wf).stepMCA_of_rate_of_curveCA
      (curveCA_udThreshold K) hn hfinal hδ hrate hi)
    (le_trans ?_ hα) (fun _ _ => hβ) hq hadv attempt₁ attempt₂
  rw [← Finset.sum_div, ← Finset.sum_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsum (by positivity))
    (Nat.cast_nonneg _)

end CertiFri.Exec
