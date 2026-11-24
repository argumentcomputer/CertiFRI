import CertiFriProofs.Exec.Honest
import CertiFriProofs.Exec.Checks

/-!
# Completeness: an honest proof passes every check of the executable verifier

The executable verifier `Fri.verify` accepts an honest proof of an honest
statement (`HonestStatement`, `HonestProof` of `Exec/Honest.lean`), given what
the arithmetic of the model yields on such a proof.

* `verify_of_honest_aux`: the verifier returns `true`.

The steps are in `CertiFri.Exec.CompletenessChecks`:

* `length_sampleIndices`, `size_indices`: the challenger hands out one index
  per query.
* `inputChecks_of_open`, `commitChecks_of_open`: the commitment checks of the
  verifier, from the check of every batch and of every round.
* `verifyWith_of_checks`: `Fri.verifyWith` from its six conjuncts.
* `agrees`: the messages, challenges and indices of a run, read in the model,
  form an instance of `Agrees`, so that the lemmas of `Exec/Arith.lean` apply.
* `ne_cosetPoint`: no opening point of an honest statement is a query point.
* `queryResult_ok`: the checks of one query pass.
* `rows_eq_rep`: the rows the fold chain reconstructs are the committed rows.

## What is assumed

* `FieldModel` and `WellFormed`, as everywhere in `Exec/`.
* The abstraction map of the extension field is injective (`hinj`). The honest
  codeword of a round is committed as the elements `rep` picks; the verifier
  hashes the elements it computes. The two are the same elements only when a
  value of the model has one representation.
* Four facts about the model, as hypotheses of `verify_of_honest_aux`. With
  `P` the parameters of the model, `G i` the honest polynomial of level `i`
  (`honestWord`) and `idx t` the index of query `t`:
  * `hred`: the reduced opening of level `j` is the value of `inputPoly … j`
    at the point of the query in the domain of that level;
  * `hzero`: `inputPoly` of the last level is zero when the final polynomial
    is a constant;
  * `hfold`: the fold chain of the model ends at the value of `G numRounds`;
  * `hrow`: the row of round `i` in the model holds the two values of `G i`
    at the points of the query's pair.

Nothing is assumed about the hash functions or the challenger.

## What is not covered

The four facts above are not proved here. Nothing is said about a prover
program, nor about how the Merkle openings of an honest proof come to verify:
that is a field of `HonestProof`.
-/

namespace CertiFri.Exec

open Fri Polynomial

namespace CompletenessChecks

/-! ## The query indices -/

section Indices

variable {σ F EF D : Type}

/-- The challenger hands out as many indices as it is asked for. -/
theorem length_sampleIndices (chal : Challenger σ F EF D) (bits : ℕ) :
    ∀ (count : ℕ) (s : σ), (chal.sampleIndices bits count s).length = count
  | 0, _ => rfl
  | count + 1, s => by
    rw [Challenger.sampleIndices, List.length_cons, length_sampleIndices chal bits count]

/-- The transcript of a run holds one query index per query. -/
theorem size_indices [FieldOps F] [Inhabited D] (chal : Challenger σ F EF D) (init : σ)
    (params : FriParams) (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) :
    (transcript chal init params shape commitments points values proof).indices.size =
      params.numQueries := by
  simp only [transcript, transcriptTail, List.size_toArray, length_sampleIndices]

end Indices

/-! ## The commitment checks, from the check of each commitment -/

section Commitments

variable {F EF D : Type} [FieldOps EF]

/-- The executable commitment checks of the input batches pass when every
batch has a commitment and an opening that the commitment scheme accepts. -/
theorem inputChecks_of_open (inputMmcs : Mmcs F D) {params : FriParams} {shape : ClaimShape}
    {commitments : Array D} {inputOpenings : Array (BatchOpening F inputMmcs.MultiProof)}
    {indices : Array ℕ}
    (hopen : ∀ b < shape.length, ∃ (root : D) (opening : BatchOpening F inputMmcs.MultiProof),
      commitments[b]? = some root ∧ inputOpenings[b]? = some opening ∧
      inputMmcs.verifyMultiBatch root (batchDims params.logBlowup (shape.getD b []))
        (Array.ofFn (n := params.numQueries) fun t => indices.getD t.val 0 >>>
          (logMaxHeight params.logBlowup shape -
            Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))
        opening.openedValues opening.openingProof = true) :
    inputChecks inputMmcs params shape commitments inputOpenings indices = true := by
  simp only [inputChecks, List.all_eq_true, List.mem_range]
  intro b hb
  obtain ⟨root, opening, hroot, ho, hv⟩ := hopen b hb
  rw [hroot, ho]
  exact hv

/-- The executable commitment checks of the folding rounds pass when every
round has a commitment and an opening for which the commitment scheme accepts
the rows of the queries. -/
theorem commitChecks_of_open (friMmcs : Mmcs EF D) {numQueries n rounds : ℕ}
    {commits : Array D} {openings : Array (CommitPhaseStep EF friMmcs.MultiProof)}
    {indices : Array ℕ} {rows : Array (List (EF × EF))}
    (hopen : ∀ i < rounds, ∃ (root : D) (opening : CommitPhaseStep EF friMmcs.MultiProof),
      commits[i]? = some root ∧ openings[i]? = some opening ∧
      friMmcs.verifyMultiBatch root #[⟨2, n - i - 1⟩]
        (Array.ofFn (n := numQueries) fun t => indices.getD t.val 0 >>> (i + 1))
        (Array.ofFn (n := numQueries) fun t =>
          #[#[((rows.getD t.val []).getD i (0, 0)).1, ((rows.getD t.val []).getD i (0, 0)).2]])
        opening.openingProof = true) :
    commitChecks friMmcs numQueries n rounds commits openings indices rows = true := by
  simp only [commitChecks, List.all_eq_true, List.mem_range]
  intro i hi
  obtain ⟨root, opening, hroot, ho, hv⟩ := hopen i hi
  rw [hroot, ho]
  exact hv

end Commitments

/-! ## The checks of the verifier, from its conjuncts -/

section Assembly

variable {F EF D : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [DecidableEq D] (params : FriParams) (shape : ClaimShape)
  {hIn : MerkleHasher F D} {hFri : MerkleHasher EF D} {commitments : Array D}
  {points values : Array EF} {proof : FriProof F EF D (Array (List D)) (Array (List D))}
  {ch : Challenges EF}

/-- The checks of the executable verifier pass when each of them does: the
proof-of-work checks, the number and the range of the query indices, the
commitment checks of the input batches, the checks of every query, and the
commitment checks of the folding rounds on the rows the queries reconstruct. -/
theorem verifyWith_of_checks (hpow : ch.powOk = true)
    (hsize : ch.indices.size = params.numQueries)
    (hlt : ∀ t < params.numQueries,
      ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape)
    (hin : inputChecks (merkleMmcs hIn) params shape commitments proof.inputOpenings
      ch.indices = true)
    (hok : ∀ t : Fin params.numQueries,
      (queryResult (F := F) params shape points values proof ch t.val).ok = true)
    (hcommit : commitChecks (merkleMmcs hFri) params.numQueries
      (logMaxHeight params.logBlowup shape) (numRounds params shape) proof.commitPhaseCommits
      proof.commitPhaseOpenings ch.indices
      ((Array.ofFn fun t : Fin params.numQueries =>
        queryResult (F := F) params shape points values proof ch t.val).map (·.rows)) = true) :
    verifyWith (merkleMmcs hIn) (merkleMmcs hFri) params shape commitments points values proof
      ch = true := by
  show (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun t =>
        decide (ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs hIn) params shape commitments proof.inputOpenings ch.indices
      && (Array.ofFn fun t : Fin params.numQueries =>
        queryResult (F := F) params shape points values proof ch t.val).all (·.ok)
      && commitChecks (merkleMmcs hFri) params.numQueries
        (logMaxHeight params.logBlowup shape) (numRounds params shape) proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun t : Fin params.numQueries =>
          queryResult (F := F) params shape points values proof ch t.val).map (·.rows)))
      = true
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨hpow, hsize⟩, hlt⟩, hin⟩, ?_⟩, hcommit⟩
  rw [Array.all_eq_true]
  intro t ht
  rw [Array.size_ofFn] at ht
  simpa using hok ⟨t, ht⟩

end Assembly

/-! ## One query -/

section Query

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

omit [TwoAdicOps F] in
/-- The messages, the challenges and the query indices of a run of the
executable verifier, read in the model, are those of the run. -/
theorem agrees (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (ch : Challenges EF) :
    Agrees m params shape commitments points values proof ch
      (fun j => view m params shape (messages params shape commitments points values proof j))
      (m.ext.toModel ch.alpha) (fun r => m.ext.toModel (ch.betas.getD r 0))
      (fun t : Fin params.numQueries => ch.indices.getD t.val 0) :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- No committed column of an opening point is taller than the first domain. -/
theorem logHeight_le {p : PointRef} {pointIdx : ℕ}
    (hp : (pointRefs params.logBlowup shape)[pointIdx]? = some p) :
    p.logHeight ≤ logMaxHeight params.logBlowup shape := by
  obtain ⟨mats, ms, hmats, hms, hh, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  rw [hh]
  exact le_logMaxHeight
    (List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩)

variable {w : Committed F K} {commitments : Array D} {points values : Array EF}

/-- An opening point of an honest statement is not a query point of its
matrix: the difference the verifier tests against zero is not zero. -/
theorem ne_cosetPoint (hst : HonestStatement m params shape wf w points values) {p : PointRef}
    {pointIdx : ℕ} (hp : (pointRefs params.logBlowup shape)[pointIdx]? = some p) (index : ℕ) :
    (points.getD pointIdx 0 -
      cosetPoint (F := F) (logMaxHeight params.logBlowup shape)
        (logMaxHeight params.logBlowup shape - p.logHeight) index == 0) = false := by
  rw [← Bool.not_eq_true, m.ext.beq_iff, m.ext.map_sub, m.ext.map_zero, sub_eq_zero,
    toModel_cosetPoint m params shape wf (Nat.sub_le _ _),
    Nat.sub_sub_self (logHeight_le params shape hp)]
  exact hst.off_domain p pointIdx hp index

variable {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : Challenges EF}

/-- **The checks of one query pass** for an honest statement, when in the model
the reduced opening of the last level is zero for a constant final polynomial
(`hconst`), and the fold chain ends at the value of the final polynomial of the
proof (`hfinal`). -/
theorem queryResult_ok (hst : HonestStatement m params shape wf w points values)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (t : Fin params.numQueries)
    (hconst : params.logFinalPolyLen = 0 →
      (modelParams m params shape wf).reduced
        (view m params shape (firstMessage commitments points values))
        ((modelParams m params shape wf).opened (modelProof m params shape proof) t)
        (m.ext.toModel ch.alpha) (ch.indices.getD t.val 0) (numRounds params shape) = 0)
    (hfinal : (modelParams m params shape wf).folded (modelProof m params shape proof)
        (view m params shape (firstMessage commitments points values)) (m.ext.toModel ch.alpha)
        (fun r => m.ext.toModel (ch.betas.getD r 0)) (ch.indices.getD t.val 0) t
        (numRounds params shape) =
      (polyOfCoeffs (proof.finalPoly.toList.map m.ext.toModel)).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - numRounds params shape)
          (ch.indices.getD t.val 0 >>> numRounds params shape))) :
    (queryResult (F := F) params shape points values proof ch t.val).ok = true := by
  have hag := agrees m params shape commitments points values proof ch
  simp only [queryResult, checkQuery, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    rintro ⟨p, pointIdx⟩ hmem
    have hp : (pointRefs params.logBlowup shape)[pointIdx]? = some p :=
      List.mem_zipIdx_iff_getElem?.mp hmem
    simp only [ne_cosetPoint m params shape wf hst hp, Bool.not_false]
  · rw [Bool.or_eq_true]
    by_cases h0 : params.logFinalPolyLen = 0
    · right
      rw [m.ext.beq_iff, toModel_reducedOpenings m params shape wf hshape hag le_rfl t,
        m.ext.map_zero]
      exact hconst h0
    · left
      simpa using h0
  · rw [m.ext.beq_iff, toModel_foldChain_fst m params shape wf hshape hag t _ le_rfl,
      m.ext.horner_eq_eval, m.embed,
      toModel_domainPoint m params shape wf (j := numRounds params shape) (Nat.sub_le _ _)]
    exact hfinal

/-- **The rows of a query are the committed rows.** If the row of round `i` of
the model holds the values `a` and `b`, and the abstraction map of the
extension field is injective, the row the executable fold chain reconstructs
holds the representations `rep a` and `rep b`. -/
theorem rows_eq_rep (hinj : Function.Injective m.ext.toModel)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (t : Fin params.numQueries) {i : ℕ} (hi : i < numRounds params shape) {a b : K}
    (hrow : (modelParams m params shape wf).commitRow (modelProof m params shape proof)
        (view m params shape (firstMessage commitments points values)) (m.ext.toModel ch.alpha)
        (fun r => m.ext.toModel (ch.betas.getD r 0)) (ch.indices.getD t.val 0) t i = (a, b)) :
    (queryResult (F := F) params shape points values proof ch t.val).rows.getD i (0, 0) =
      (rep m a, rep m b) := by
  have h := (rows_queryResult m params shape wf hshape
    (agrees m params shape commitments points values proof ch) t hi).trans hrow
  rw [Prod.mk.injEq] at h
  exact Prod.ext (hinj (h.1.trans (toModel_rep m a).symm))
    (hinj (h.2.trans (toModel_rep m b).symm))

end Query

end CompletenessChecks

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- **An honest proof passes every check of the executable verifier.**

The statement is honest for the committed data `w`, the proof is honest for the
hash functions `hIn` and `hFri` and the challenger `chal` started at `init`,
and the abstraction map of the extension field is injective. With the
challenges the verifier derives from the proof, the model satisfies:

* `hred`: the reduced opening of every level up to the last round is the value
  of `inputPoly` of the level at the point of the query in that level;
* `hzero`: when the final polynomial is a constant, `inputPoly` of the last
  level is zero;
* `hfold`: the fold chain of every query ends at the value of `honestWord` of
  the last level;
* `hrow`: the row of every query in every round holds the values of
  `honestWord` of the round at the two points of the query's pair.

Then `Fri.verify`, with the Merkle commitment schemes over `hIn` and `hFri`,
accepts. -/
theorem verify_of_honest_aux (hinj : Function.Injective m.ext.toModel)
    {hIn : MerkleHasher F D} {hFri : MerkleHasher EF D} {chal : Challenger σ F EF D} {init : σ}
    {w : Committed F K} {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))}
    (hst : HonestStatement m params shape wf w points values)
    (hpf : HonestProof m params shape wf hIn hFri chal init w commitments points values proof)
    (hred : ∀ (t : Fin params.numQueries) (j : ℕ), j ≤ numRounds params shape →
      (modelParams m params shape wf).reduced
          (view m params shape (firstMessage commitments points values))
          ((modelParams m params shape wf).opened (modelProof m params shape proof) t)
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          ((transcript chal init params shape commitments points values proof).indices.getD
            t.val 0) j =
        (inputPoly m params shape wf w points values
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          j).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - j)
            ((transcript chal init params shape commitments points values proof).indices.getD
              t.val 0 >>> j)))
    (hzero : params.logFinalPolyLen = 0 →
      inputPoly m params shape wf w points values
        (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
        (numRounds params shape) = 0)
    (hfold : ∀ t : Fin params.numQueries,
      (modelParams m params shape wf).folded (modelProof m params shape proof)
          (view m params shape (firstMessage commitments points values))
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          (fun r => m.ext.toModel
            ((transcript chal init params shape commitments points values proof).betas.getD r 0))
          ((transcript chal init params shape commitments points values proof).indices.getD
            t.val 0) t (numRounds params shape) =
        (honestWord m params shape wf w points values
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          (fun r => m.ext.toModel
            ((transcript chal init params shape commitments points values proof).betas.getD r 0))
          (numRounds params shape)).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - numRounds params shape)
            ((transcript chal init params shape commitments points values proof).indices.getD
              t.val 0 >>> numRounds params shape)))
    (hrow : ∀ (t : Fin params.numQueries) (i : ℕ), i < numRounds params shape →
      (modelParams m params shape wf).commitRow (modelProof m params shape proof)
          (view m params shape (firstMessage commitments points values))
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          (fun r => m.ext.toModel
            ((transcript chal init params shape commitments points values proof).betas.getD r 0))
          ((transcript chal init params shape commitments points values proof).indices.getD
            t.val 0) t i =
        ((honestWord m params shape wf w points values
            (m.ext.toModel
              (transcript chal init params shape commitments points values proof).alpha)
            (fun r => m.ext.toModel
              ((transcript chal init params shape commitments points values proof).betas.getD r
                0)) i).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - i)
            (2 * ((transcript chal init params shape commitments points values
              proof).indices.getD t.val 0 >>> (i + 1)))),
         (honestWord m params shape wf w points values
            (m.ext.toModel
              (transcript chal init params shape commitments points values proof).alpha)
            (fun r => m.ext.toModel
              ((transcript chal init params shape commitments points values proof).betas.getD r
                0)) i).eval
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - i)
            (2 * ((transcript chal init params shape commitments points values
              proof).indices.getD t.val 0 >>> (i + 1)) + 1)))) :
    Fri.verify (merkleMmcs hIn) (merkleMmcs hFri) chal init params shape commitments points values
      proof = true := by
  have hshape := hpf.shape_ok
  have hwith : verifyWith (merkleMmcs hIn) (merkleMmcs hFri) params shape commitments points
      values proof (transcript chal init params shape commitments points values proof) = true := by
    refine CompletenessChecks.verifyWith_of_checks params shape hpf.pow
      (CompletenessChecks.size_indices chal init params shape commitments points values proof)
      hpf.index_lt (CompletenessChecks.inputChecks_of_open (merkleMmcs hIn) hpf.input_open)
      (fun t => ?_) ?_
    · refine CompletenessChecks.queryResult_ok m params shape wf hst hshape t (fun h0 => ?_) ?_
      · rw [hred t _ le_rfl, hzero h0, eval_zero]
      · rw [hfold t, hpf.final]
    · refine CompletenessChecks.commitChecks_of_open (merkleMmcs hFri) fun i hi => ?_
      obtain ⟨root, opening, hroot, ho, hv⟩ := hpf.round_open i hi
      refine ⟨root, opening, hroot, ho, ?_⟩
      simp only [Checks.getD_map_ofFn,
        fun t => CompletenessChecks.rows_eq_rep m params shape wf hinj hshape t hi (hrow t i hi)]
      exact hv
  exact Bool.and_eq_true_iff.mpr ⟨hshape, hwith⟩

end CertiFri.Exec
