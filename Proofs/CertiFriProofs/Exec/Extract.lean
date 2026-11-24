import CertiFriProofs.Theory.PcsRbr.Decode
import CertiFriProofs.Exec.SoundnessUnconditional

/-!
# Knowledge soundness of the executable verifier

`Exec.soundness_uniqueDecoding` (`Exec/SoundnessUnconditional.lean`) bounds the
probability that `Fri.verify` accepts an attempt whose claims fail. This file
turns it into knowledge soundness: there is an extractor that reads a
polynomial for every committed column off the commitments and the query log,
and the probability that `Fri.verify` accepts an attempt one of whose claimed
values is not the value of the extracted polynomial at the opening point is at
most the same bound.

## The extractor

`extractColumn m params shape wf θ commitments l c` is the polynomial of the
column that the claim `c` names: column `c.col` of matrix `c.matrix` of batch
`c.batch`, whose codeword has `2 ^ c.logHeight` entries.

* It is a function of the commitments and of a log `l` of oracle queries, and
  of nothing else: no opening point, no claimed value, no proof. In the
  theorems `l` is the final log of the experiment: the adversary's queries, the
  challenge queries of the transcript and the hash queries of the verification.
* It reads the column as the function on the coset of its level whose value at
  the point of index `i` is the entry `c.col` of the row `i` that the hash
  queries of `l` open under the commitment of the batch (`committedColumn`,
  built on `Oracle.committedRow`), and decodes that function
  (`decode`, `Theory/PcsRbr/Decode.lean`) at agreement `θ`.
* It depends on a claim only through its column (`extractColumn_congr`) and on
  the commitments only through the commitment of the batch
  (`extractColumn_congr_commitments`). So two claims about one column, in two
  attempts with the same commitment of the batch, have the same extracted
  polynomial against a given log.
* It is not computable as defined: both the committed row and the decoded
  polynomial are choices. Its efficiency is not addressed.
* The extracted polynomial has degree at most `2 ^ (c.logHeight - logBlowup)`
  (`degree_extractColumn_le`): the degree bound of `ClaimsHoldOff`, one more
  than the degree of an honest polynomial.

## Results

* `extractColumn_levelClaims`: for the `k`-th claim of a level, the extracted
  polynomial is the decoded polynomial of the function of that claim in the
  model (`Compiled.Params.claims`).
* `eval_extractColumn_of_not_claimsFail`: if the statement and the proof pass
  the shape checks and the claims do not fail, every claimed value is the value
  of the extracted polynomial of its column at its opening point.
* `shapeOk_of_accepts`: an accepted attempt passes the shape checks.
* `knowledge_soundness`: the probability that `Fri.verify` accepts an attempt
  while some claimed value is not the value of the extracted polynomial at the
  opening point is at most the bound of `Exec.soundness_uniqueDecoding`.
* `decodeMargin_of_rate`, `knowledge_soundness_of_rate`: the margin of unique
  decoding in executable terms, and knowledge soundness with it.

## What is assumed

* What `Exec.soundness_uniqueDecoding` assumes: the random-oracle model with
  chained challenges, ideal primitives, `FieldModel` and `WellFormed`, Merkle
  commitments with one path per query, a shape fixed before the adversary runs.
* `DecodeMargin` on the coset of every level that has a claim: the agreement
  `1 - δ` is far enough inside the unique-decoding radius for two sets that
  each miss one point of a `1 - δ` fraction to share more points than the
  degree bound. In executable terms, at level `j`:
  `2 * δ + (1 / 2) ^ logBlowup + 3 / 2 ^ (logMaxHeight - j) ≤ 1`.

## What is not covered

* An efficient extractor, or one that works from the adversary's queries alone
  before the verification runs.
* Agreement beyond the unique-decoding radius, where a column may be close to
  several polynomials.
* Zero knowledge, and everything `Exec/Soundness.lean` lists as not covered.
-/

namespace CertiFri.Exec

open Oracle OracleComp Fri Polynomial
open PcsRbr (ClaimsFail)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)
  [DecidableEq F] [DecidableEq EF]

/-! ## The extractor -/

/-- The function that the hash queries of `l` commit to under `root` for the
column of the claim `c`: on the coset of `2 ^ c.logHeight` points, its value at
the point of index `i` is the entry `c.col` of row `i` of matrix `c.matrix`
under `root`, for the dimensions of batch `c.batch`. It is zero where no row is
committed, where the row is too short, and off the coset. -/
noncomputable def committedColumn (root : D) (l : Log (OracleAnswer (D := D) m params shape wf))
    (c : ClaimRef) : K → K :=
  Compiled.ofIndexed (2 ^ c.logHeight)
    (fun i => (modelParams m params shape wf).shift *
      pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
        c.logHeight i)
    fun i => Compiled.entry
      (committedRow l root (batchDims params.logBlowup (shape.getD c.batch [])) c.matrix i) c.col

/-- The polynomial that column `col` of matrix `matrix` of batch `batch`
decodes to: the function the hash queries of `l` commit to under the commitment
of the batch, decoded on the coset of the column's level. It does not depend on
any opening point, claimed value or proof. -/
noncomputable def extractColumn (θ : ℝ) (commitments : Array D)
    (l : Log (OracleAnswer (D := D) m params shape wf)) (c : ClaimRef) : K[X] :=
  decode
    ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
      ((modelParams m params shape wf).n - c.logHeight)).image
        ((modelParams m params shape wf).shift * ·))
    ((modelParams m params shape wf).ldt.degree ((modelParams m params shape wf).n - c.logHeight))
    θ (committedColumn m params shape wf (commitments.getD c.batch default) l c)

variable {θ : ℝ} {commitments : Array D} {l : Log (OracleAnswer (D := D) m params shape wf)}

/-- The extracted polynomial depends on a claim only through its column: the
batch, the matrix, the column and the height. -/
theorem extractColumn_congr {c c' : ClaimRef} (hb : c.batch = c'.batch)
    (hm : c.matrix = c'.matrix) (hc : c.col = c'.col) (hh : c.logHeight = c'.logHeight) :
    extractColumn m params shape wf θ commitments l c =
      extractColumn m params shape wf θ commitments l c' := by
  simp only [extractColumn, committedColumn, hb, hm, hc, hh]

/-- The extracted polynomial depends on the commitments only through the
commitment of the batch of the column. -/
theorem extractColumn_congr_commitments {commitments' : Array D} {c : ClaimRef}
    (h : commitments.getD c.batch default = commitments'.getD c.batch default) :
    extractColumn m params shape wf θ commitments l c =
      extractColumn m params shape wf θ commitments' l c := by
  simp only [extractColumn, h]

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The root of an input batch in the statement, read through `view`, is the
commitment of the batch. -/
private theorem inputRoots_firstMessage (commitments : Array D) (points values : Array EF)
    (b : Fin (modelParams m params shape wf).batches) :
    @Compiled.Msg.inputRoots K D (modelParams m params shape wf).batches
        (view m params shape (firstMessage (F := F) commitments points values)) b =
      commitments.getD b.val default := by
  show (view m params shape (firstMessage (F := F) commitments points values)).inputRoots b = _
  simp only [view, Checks.digestsIn_firstMessage, List.getD_eq_getElem?_getD,
    Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **The extractor and the claims of the model.** For the `k`-th claim of
level `j`, the extracted polynomial is the polynomial that the function of that
claim in the model decodes to, on the coset of level `j` with the degree bound
of level `j`. The function of the claim does not depend on the opening points
or on the claimed values of the statement. -/
theorem extractColumn_levelClaims (θ : ℝ) (commitments : Array D) (points values : Array EF)
    (l : Log (OracleAnswer (D := D) m params shape wf)) {j : ℕ}
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    extractColumn m params shape wf θ commitments l
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k) =
      decode
        ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          j).image ((modelParams m params shape wf).shift * ·))
        ((modelParams m params shape wf).ldt.degree j) θ
        (((modelParams m params shape wf).claims
          (view m params shape (firstMessage commitments points values)) (committedRow l) j
            k).f) := by
  have hlog := logHeight_of_mem_levelClaims (List.get_mem
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j) k)
  have hj : (modelParams m params shape wf).n -
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
        k).logHeight = j := by
    show logMaxHeight params.logBlowup shape - _ = j
    omega
  have hn : (modelParams m params shape wf).n - j =
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
        k).logHeight := by
    show logMaxHeight params.logBlowup shape - j = _
    omega
  unfold extractColumn
  rw [hj]
  congr 1
  unfold committedColumn Compiled.Params.claims
  simp only [hn, inputRoots_firstMessage]
  rfl

/-- The extracted polynomial has degree at most the bound of the level of its
column. -/
theorem degree_extractColumn_lt (θ : ℝ) (commitments : Array D)
    (l : Log (OracleAnswer (D := D) m params shape wf)) (c : ClaimRef) :
    (extractColumn m params shape wf θ commitments l c).degree <
      ((modelParams m params shape wf).ldt.degree
        ((modelParams m params shape wf).n - c.logHeight) + 1 : ℕ) :=
  degree_decode_lt _ _ _ _

/-- The extracted polynomial of a column of height between the final height
and the height of the first domain has degree at most
`2 ^ (c.logHeight - logBlowup)`, the number of coefficients of an honest
polynomial of that column. -/
theorem degree_extractColumn_le (θ : ℝ) (commitments : Array D)
    (l : Log (OracleAnswer (D := D) m params shape wf)) {c : ClaimRef}
    (hfinal : params.logFinalHeight ≤ c.logHeight)
    (hle : c.logHeight ≤ logMaxHeight params.logBlowup shape) :
    (extractColumn m params shape wf θ commitments l c).degree ≤
      (2 ^ (c.logHeight - params.logBlowup) : ℕ) := by
  have hdeg : (modelParams m params shape wf).ldt.degree
      ((modelParams m params shape wf).n - c.logHeight) =
      2 ^ (c.logHeight - params.logBlowup) := by
    show 2 ^ (numRounds params shape - (logMaxHeight params.logBlowup shape - c.logHeight)) *
      2 ^ params.logFinalPolyLen = _
    rw [← pow_add]
    congr 1
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have h := degree_extractColumn_lt m params shape wf θ commitments l c
  rw [hdeg] at h
  exact Order.le_of_lt_succ (by exact_mod_cast h)

/-! ## Claims that hold are evaluations of the extracted polynomials -/

namespace Extract

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
/-- No claimed column of a shape is taller than the first domain. -/
theorem logHeight_le_logMaxHeight {lb : ℕ} {c : ClaimRef} (hc : c ∈ claimRefs lb shape) :
    c.logHeight ≤ logMaxHeight lb shape := by
  obtain ⟨p, hp, -, -, hh, -⟩ := mem_claimRefs hc
  obtain ⟨mats, ms, hmats, hms, hph, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  rw [hh, hph]
  exact le_logMaxHeight
    (List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩)

omit [FieldOps EF] [ExtensionOps F EF] [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  [DecidableEq F] [DecidableEq EF] in
/-- In a shape that passes the shape checks, no claimed column is shorter than
the final height. -/
theorem logFinalHeight_le_logHeight {InputProof CommitProof : Type} {points values : Array EF}
    {proof : FriProof F EF D InputProof CommitProof}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) {c : ClaimRef}
    (hc : c ∈ claimRefs params.logBlowup shape) : params.logFinalHeight ≤ c.logHeight := by
  obtain ⟨p, hp, -, -, hh, -⟩ := mem_claimRefs hc
  obtain ⟨mats, ms, hmats, hms, hph, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
  have hall := List.all_eq_true.mp hshape.1.1.1.1.1.1.1.1.1.1.1.2 ms
    (List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩)
  rw [Bool.and_eq_true, decide_eq_true_eq] at hall
  rw [hh, hph]
  exact hall.2

end Extract

omit [DecidableEq F] [DecidableEq EF] in
/-- An attempt that the executable verifier accepts passes the shape checks. -/
theorem shapeOk_of_accepts {f : ∀ x, OracleAnswer (D := D) m params shape wf x}
    {a : Attempt F EF D} (h : accepts m params shape wf f a = true) :
    shapeOk (F := F) params shape a.commitments a.points a.values a.proof = true := by
  unfold accepts Fri.verify at h
  rw [Bool.and_eq_true] at h
  exact h.1

/-- **Claims that hold are evaluations of the extracted polynomials.** Let the
statement and the proof of an attempt pass the shape checks, and let the margin
of unique decoding hold on the coset of every level that has a claim. If the
claims of the attempt, read from the log `l`, do not fail at agreement `θ`,
then for every claim of the shape the claimed value is the value, at the
opening point of the claim, of the polynomial extracted for its column from the
commitments and `l`. -/
theorem eval_extractColumn_of_not_claimsFail {a : Attempt F EF D}
    (hshape : shapeOk (F := F) params shape a.commitments a.points a.values a.proof = true)
    (hmargin : ∀ j ≤ numRounds params shape, (modelParams m params shape wf).numClaims j ≠ 0 →
      DecodeMargin
        ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
          j).image ((modelParams m params shape wf).shift * ·))
        ((modelParams m params shape wf).ldt.degree j) θ)
    (h : ¬ ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
      ((modelParams m params shape wf).claims
        (view m params shape (firstMessage a.commitments a.points a.values)) (committedRow l)))
    {c : ClaimRef} (hc : c ∈ claimRefs params.logBlowup shape) :
    (extractColumn m params shape wf θ a.commitments l c).eval
        (m.ext.toModel (a.points.getD c.pointIdx 0)) =
      m.ext.toModel (a.values.getD c.valueIdx 0) := by
  have hle := Extract.logHeight_le_logMaxHeight shape hc
  have hfin := Extract.logFinalHeight_le_logHeight params shape hshape hc
  obtain ⟨j, hlog⟩ : ∃ j, c.logHeight + j = logMaxHeight params.logBlowup shape :=
    ⟨logMaxHeight params.logBlowup shape - c.logHeight, by omega⟩
  have hj : j ≤ numRounds params shape := by
    unfold numRounds
    omega
  have hmem : c ∈ levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j :=
    List.mem_filter.mpr ⟨hc, beq_iff_eq.mpr hlog⟩
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmem
  have hag : Agrees m params shape a.commitments a.points a.values a.proof
      (⟨0, #[], true, #[]⟩ : Challenges EF)
      (fun j => view m params shape
        (messages params shape a.commitments a.points a.values a.proof j))
      (m.ext.toModel 0) (fun i => m.ext.toModel ((#[] : Array EF).getD i 0))
      (fun t => (#[] : Array ℕ).getD t.val 0) :=
    { msg := fun _ _ => rfl
      alpha := rfl
      beta := fun _ _ => rfl
      index := fun _ => rfl }
  have hpt := point_msg_zero m params shape wf hshape hag hj k
  have hval := value_msg_zero m params shape wf hshape hag hj k
  have hext := extracts_of_not_claimsFail hmargin h j hj k
  have hpoly := extractColumn_levelClaims m params shape wf θ a.commitments a.points a.values l k
  rw [hk] at hpt hval hpoly
  rw [hpoly, ← hpt, ← hval]
  exact hext

/-! ## The margin in executable terms -/

omit [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
/-- **The margin of unique decoding in executable terms.** Let no committed
column be shorter than the final height. At a level `j` up to the last round,
the coset has `2 ^ (logMaxHeight - j)` points and the degree bound is that
times the rate `2 ^ (-logBlowup)`. So the margin holds at agreement `1 - δ` as
soon as `2 * δ + (1 / 2) ^ logBlowup + 3 / 2 ^ (logMaxHeight - j) ≤ 1`. -/
theorem decodeMargin_of_rate
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} {j : ℕ}
    (hj : j ≤ numRounds params shape)
    (h : 2 * δ + (1 / 2) ^ params.logBlowup +
      3 / 2 ^ (logMaxHeight params.logBlowup shape - j) ≤ 1) :
    DecodeMargin
      ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
        j).image ((modelParams m params shape wf).shift * ·))
      ((modelParams m params shape wf).ldt.degree j) (1 - δ) := by
  have hn : (modelParams m params shape wf).n =
      (modelParams m params shape wf).rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hcard : ((twoAdicDomain (modelParams m params shape wf).ω (modelParams m params shape wf).n
      j).image ((modelParams m params shape wf).shift * ·)).card =
      2 ^ (logMaxHeight params.logBlowup shape - j) := by
    rw [Finset.card_image_of_injective _
      (mul_right_injective₀ (modelParams m params shape wf).shift_ne),
      card_twoAdicDomain (modelParams m params shape wf).prim
        (hj.trans (modelParams m params shape wf).rounds_le)]
    rfl
  have hdeg : (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j) =
      2 ^ params.logBlowup * ((modelParams m params shape wf).ldt.degree j : ℝ) := by
    have h := Compose.card_twoAdicDomain_eq_mul_degree hn (modelParams m params shape wf).prim
      (i := j) hj
    rw [card_twoAdicDomain (modelParams m params shape wf).prim
      (hj.trans (modelParams m params shape wf).rounds_le)] at h
    have h' : (2 : ℕ) ^ (logMaxHeight params.logBlowup shape - j) =
        2 ^ params.logBlowup * (modelParams m params shape wf).ldt.degree j := h
    exact_mod_cast h'
  unfold DecodeMargin
  rw [hcard]
  push_cast
  have hX : (0 : ℝ) < 2 ^ (logMaxHeight params.logBlowup shape - j) := by positivity
  have hhalf : (1 / 2 : ℝ) ^ params.logBlowup * 2 ^ params.logBlowup = 1 := by
    rw [← mul_pow]
    norm_num
  have hd : (1 / 2 : ℝ) ^ params.logBlowup * 2 ^ (logMaxHeight params.logBlowup shape - j) =
      ((modelParams m params shape wf).ldt.degree j : ℝ) := by
    rw [hdeg, ← mul_assoc, hhalf, one_mul]
  have key := mul_le_mul_of_nonneg_right h hX.le
  rw [add_mul, add_mul, div_mul_cancel₀ _ hX.ne', hd] at key
  linarith

/-! ## Knowledge soundness -/

section Soundness

variable [Fintype K] [Fintype D]

/-- **Knowledge soundness of the executable verifier, up to the unique-decoding
radius.**

*Statement.* Fix the parameters and the shape of the claims. Whatever the
adversary, as long as it makes at most `Q` oracle queries: the probability that
`Fri.verify` accepts its attempt while, for some claim `c` of the shape, the
claimed value `values[c.valueIdx]` is not the value at the opening point
`points[c.pointIdx]` of the polynomial extracted for the column of `c`, is at
most the bound of `Exec.soundness_uniqueDecoding`,

    N * εmax + (max (batches + rounds) 3 + 3) * N ^ 2 / (4 * |D|),

with `N = Q + (rounds + 2) + verifierQueries`.

*The extractor.* `extractColumn` at agreement `1 - δ`: a function of the
commitments of the attempt and of the final log `l` of the experiment, which
holds the adversary's queries, the challenge queries of the transcript and the
hash queries of the verification. It does not see the opening points, the
claimed values or the proof, and its polynomial has degree at most
`2 ^ (c.logHeight - logBlowup)` (`degree_extractColumn_le`). It is not
computable as defined.

*Assumptions.* Those of `Exec.soundness_uniqueDecoding`, where `εmax` bounds
the error of every round, and `hmargin`: the margin of unique decoding at
agreement `1 - δ` on the coset of every level that has a claim
(`decodeMargin_of_rate` gives it in executable terms). The experiment and
"`Fri.verify` accepts" are those of `Exec.soundness`. -/
theorem knowledge_soundness
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
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ∃ c ∈ claimRefs params.logBlowup shape,
          (extractColumn m params shape wf (1 - δ) (attempt res.1).commitments l c).eval
              (m.ext.toModel ((attempt res.1).points.getD c.pointIdx 0)) ≠
            m.ext.toModel ((attempt res.1).values.getD c.valueIdx 0))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  refine (prob_mono (fun res l hE => ?_) _ _).trans
    (soundness_uniqueDecoding m params shape wf hheight hδ hrate hα hβ hq hadv attempt)
  obtain ⟨⟨f, hf, hacc⟩, c, hc, hne⟩ := hE
  refine ⟨⟨f, hf, hacc⟩, ?_⟩
  by_contra hfail
  exact hne (eval_extractColumn_of_not_claimsFail m params shape wf
    (shapeOk_of_accepts m params shape wf hacc) hmargin hfail hc)

/-- **Knowledge soundness, with the margin in executable terms.**
`knowledge_soundness` where the margin of unique decoding is the inequality
`2 * δ + (1 / 2) ^ logBlowup + 3 / 2 ^ (logMaxHeight - j) ≤ 1` at every level
`j` that has a claim. -/
theorem knowledge_soundness_of_rate
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
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, OracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            accepts m params shape wf f (attempt res.1) = true) ∧
        ∃ c ∈ claimRefs params.logBlowup shape,
          (extractColumn m params shape wf (1 - δ) (attempt res.1).commitments l c).eval
              (m.ext.toModel ((attempt res.1).points.getD c.pointIdx 0)) ≠
            m.ext.toModel ((attempt res.1).values.getD c.valueIdx 0))
      (experiment m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) :=
  knowledge_soundness m params shape wf hheight hδ hrate
    (fun j hj hne => decodeMargin_of_rate m params shape wf hheight hj (hmargin j hj hne))
    hα hβ hq hadv attempt

end Soundness

end CertiFri.Exec
