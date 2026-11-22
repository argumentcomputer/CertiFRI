import CertiFriProofs.Exec.Extract
import CertiFriProofs.Exec.TwoAttempts

/-!
# Binding of the commitment scheme

A commitment cannot be opened at one point to two values: the probability
that an adversary produces two statements with proofs, both accepted by
`Fri.verify`, that claim two different values for the same column of the same
commitment at the same opening point is small.

## The experiment and the event

`experiment₂` (`Exec/TwoAttempts.lean`): the adversary outputs two attempts of
the fixed shape; for each, the challenge queries of its transcript and the hash
queries of its verification are made.

`Conflict a₁ a₂`: a claim of the first attempt and a claim of the second name
the same column (same batch, matrix and column), the two attempts have the same
commitment for that batch, the two claims have the same opening point, and
their claimed values differ. Points and values are compared as elements of the
field `K`.

## Results

* `binding`: the probability that both attempts are accepted and conflict is
  at most twice the bound of `Exec.soundness_uniqueDecoding`, with the queries
  of both verifications counted.
* `binding_of_rate`: the same with the margin of unique decoding in executable
  terms.

The proof: outside the event of `soundness₂_uniqueDecoding`, the claims of both
attempts hold against the final log. Then each claimed value is the value, at
its opening point, of the polynomial extracted for its column
(`eval_extractColumn_of_not_claimsFail`), and the two claims have the same
extracted polynomial (`extractColumn_congr`,
`extractColumn_congr_commitments`).

## What is assumed

What `Exec.knowledge_soundness` assumes, including the margin of unique
decoding `DecodeMargin` at every level that has a claim.

## Not covered

Two openings of different shapes. Columns on cosets too small for the margin.
-/

namespace CertiFri.Exec

open Oracle OracleComp Fri
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [DecidableEq D] [Inhabited D] in
/-- Two claims of a shape about the same matrix are about columns of the same
length. -/
theorem logHeight_eq_of_mem_claimRefs {lb : ℕ} {shape : ClaimShape} {c c' : ClaimRef}
    (hc : c ∈ claimRefs lb shape) (hc' : c' ∈ claimRefs lb shape) (hb : c.batch = c'.batch)
    (hm : c.matrix = c'.matrix) : c.logHeight = c'.logHeight := by
  obtain ⟨p, hp, hpb, hpm, hph, -⟩ := mem_claimRefs hc
  obtain ⟨p', hp', hpb', hpm', hph', -⟩ := mem_claimRefs hc'
  obtain ⟨mats, ms, hmats, hms, hlog, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  obtain ⟨mats', ms', hmats', hms', hlog', -⟩ := mem_pointRefs (List.mem_of_getElem? hp')
  rw [← hpb, hb, hpb'] at hmats
  obtain rfl : mats = mats' := Option.some.inj (hmats.symm.trans hmats')
  rw [← hpm, hm, hpm'] at hms
  obtain rfl : ms = ms' := Option.some.inj (hms.symm.trans hms')
  rw [hph, hph', hlog, hlog']

/-- **Two attempts conflict**: a claim of the first and a claim of the second
are about the same column of a batch that has the same commitment in both
attempts, at the same opening point, with different claimed values. -/
def Conflict (a₁ a₂ : Attempt F EF D) : Prop :=
  ∃ c₁ ∈ claimRefs params.logBlowup shape, ∃ c₂ ∈ claimRefs params.logBlowup shape,
    c₁.batch = c₂.batch ∧ c₁.matrix = c₂.matrix ∧ c₁.col = c₂.col ∧
    a₁.commitments.getD c₁.batch default = a₂.commitments.getD c₂.batch default ∧
    m.ext.toModel (a₁.points.getD c₁.pointIdx 0) = m.ext.toModel (a₂.points.getD c₂.pointIdx 0) ∧
    m.ext.toModel (a₁.values.getD c₁.valueIdx 0) ≠ m.ext.toModel (a₂.values.getD c₂.valueIdx 0)

variable [DecidableEq F] [DecidableEq EF]

/-- Two accepted attempts whose claims hold against one log do not conflict. -/
theorem not_conflict_of_not_fails {θ : ℝ} {a₁ a₂ : Attempt F EF D}
    {l : Log (OracleAnswer (D := D) m params shape wf)}
    (hmargin : ∀ j ≤ numRounds params shape, (modelParams m params shape wf).numClaims j ≠ 0 →
      DecodeMargin
        ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          j).image ((modelParams m params shape wf).shift * ·))
        ((modelParams m params shape wf).ldt.degree j) θ)
    (hacc₁ : Accepted m params shape wf a₁ l) (hacc₂ : Accepted m params shape wf a₂ l)
    (h₁ : ¬ Fails m params shape wf θ a₁ l) (h₂ : ¬ Fails m params shape wf θ a₂ l) :
    ¬ Conflict m params shape a₁ a₂ := by
  rintro ⟨c₁, hc₁, c₂, hc₂, hb, hmat, hcol, hroot, hz, hy⟩
  obtain ⟨f₁, -, hf₁⟩ := hacc₁
  obtain ⟨f₂, -, hf₂⟩ := hacc₂
  have e₁ := eval_extractColumn_of_not_claimsFail m params shape wf
    (shapeOk_of_accepts m params shape wf hf₁) hmargin h₁ hc₁
  have e₂ := eval_extractColumn_of_not_claimsFail m params shape wf
    (shapeOk_of_accepts m params shape wf hf₂) hmargin h₂ hc₂
  have hpoly : extractColumn m params shape wf θ a₁.commitments l c₁ =
      extractColumn m params shape wf θ a₂.commitments l c₂ := by
    rw [extractColumn_congr m params shape wf hb hmat hcol
      (logHeight_eq_of_mem_claimRefs hc₁ hc₂ hb hmat)]
    exact extractColumn_congr_commitments m params shape wf (hb ▸ hroot)
  exact hy (by rw [← e₁, ← e₂, hpoly, hz])

variable [Fintype K] [Fintype D]

/-- **Binding.** Fix the parameters and the shape. Let no committed column be
shorter than the final height, let `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup ≤ 1`, and let the margin of unique decoding hold at
agreement `1 - δ` at every level that has a claim. Whatever the adversary, as
long as it makes at most `Q` oracle queries: the probability that both of its
attempts are accepted by `Fri.verify` and conflict is at most

    2 * (N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)),

with `N = Q + 2 * ((rounds + 2) + verifierQueries)`, the number of oracle
queries of the experiment, and `εmax` bounding the round errors of
`Exec.soundness_uniqueDecoding`.

"Accepted" is `Accepted`: some total answer function agreeing with the final
log makes `Fri.verify` return `true`. "Conflict" is `Conflict`: the two
attempts claim different values, at one opening point, for one column of a
batch with the same commitment in both. -/
theorem binding
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1)
    (hmargin : ∀ j ≤ numRounds params shape, (modelParams m params shape wf).numClaims j ≠ 0 →
      DecodeMargin
        ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          j).image ((modelParams m params shape wf).shift * ·))
        ((modelParams m params shape wf).ldt.degree j) (1 - δ))
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt₁ attempt₂ : A → Attempt F EF D) :
    prob (fun res l =>
        Accepted m params shape wf (attempt₁ res.1) l ∧
          Accepted m params shape wf (attempt₂ res.1) l ∧
          Conflict m params shape (attempt₁ res.1) (attempt₂ res.1))
      (experiment₂ m params shape wf adv attempt₁ attempt₂) [] ≤
      2 * ((Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) * εmax +
        (((modelParams m params shape wf).batches + 1) *
            ((modelParams m params shape wf).rounds + 2) + 3) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) - 1) / (2 * Fintype.card D)) := by
  refine (prob_mono (fun res l hE => ?_) _ _).trans
    (soundness₂_uniqueDecoding m params shape wf hheight hδ hrate hα hβ hq hadv attempt₁ attempt₂)
  obtain ⟨hacc₁, hacc₂, hconf⟩ := hE
  by_contra hnot
  rw [not_or, not_and, not_and] at hnot
  exact not_conflict_of_not_fails m params shape wf hmargin hacc₁ hacc₂ (hnot.1 hacc₁)
    (hnot.2 hacc₂) hconf

/-- **Binding, with the margin in executable terms.** `binding` where the margin
of unique decoding is the inequality
`2 * δ + (1 / 2) ^ logBlowup + 3 / 2 ^ (logMaxHeight - j) ≤ 1` at every level
`j` that has a claim. -/
theorem binding_of_rate
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1)
    (hmargin : ∀ j ≤ numRounds params shape, (modelParams m params shape wf).numClaims j ≠ 0 →
      2 * δ + (1 / 2) ^ params.logBlowup +
        3 / 2 ^ (logMaxHeight params.logBlowup shape - j) ≤ 1)
    {εmax : ℝ}
    (hα : ((claimRefs params.logBlowup shape).length : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (OracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt₁ attempt₂ : A → Attempt F EF D) :
    prob (fun res l =>
        Accepted m params shape wf (attempt₁ res.1) l ∧
          Accepted m params shape wf (attempt₂ res.1) l ∧
          Conflict m params shape (attempt₁ res.1) (attempt₂ res.1))
      (experiment₂ m params shape wf adv attempt₁ attempt₂) [] ≤
      2 * ((Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) * εmax +
        (((modelParams m params shape wf).batches + 1) *
            ((modelParams m params shape wf).rounds + 2) + 3) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries)) *
          (Q + 2 * (((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) - 1) / (2 * Fintype.card D)) :=
  binding m params shape wf hheight hδ hrate
    (fun j hj hne => decodeMargin_of_rate m params shape wf hheight hj (hmargin j hj hne))
    hα hβ hq hadv attempt₁ attempt₂

end CertiFri.Exec
