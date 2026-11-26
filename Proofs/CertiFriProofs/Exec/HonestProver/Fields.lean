import CertiFriProofs.Exec.HonestProver.Prover
import CertiFriProofs.Exec.HonestArith

/-!
# The honest prover's proof, property by property

What `HonestProof` (`Exec/Honest.lean`) asks of a proof, for the pieces the
honest prover of `Exec/HonestProver/Prover.lean` builds its proof from. The
lemmas are stated for arbitrary challenges and query indices, so that none
mentions the transcript; `Exec/HonestProver.lean` applies them to the
challenges of the prover. All of them are in the namespace `HonestProver`.

* `sampleIndices_lt`, `getD_lt`: the query indices are indices of the first
  domain.
* `dimsOf_inputMatrices`, `verifyOpenings_inputOpening`: the committed matrices
  of a batch have the dimensions the verifier computes, and the Merkle check
  accepts the opening of the batch (`Merkle.verifyOpenings_tree`).
* `openedEntry_inputOpening`: the opened entries are the entries of the rows
  of `w`.
* `verifyOpenings_roundOpening`: the Merkle check accepts, under the commitment
  of a round, the rows of the word of the round.
* `sibling_roundOpening`: the sibling values are the values of the word.
* `polyOfCoeffs_rep`, `degree_word_lt`: the final polynomial is the word after
  the last round.
* `shapeOk_of_sizes`, `shape_roundOpening`, `shape_inputOpening`: the shape
  checks of the verifier.
* `powOk_run`: the proof-of-work checks of the folding rounds, when the search
  succeeds in every state.

## What is assumed

Each lemma states what it needs. Together: the statement has the shape the
verifier requires (`StatementShape`); every batch has a matrix and the
committed rows of `w` have the widths of their matrices (the Merkle check
rejects an opening otherwise); the query indices are below the size of the
first domain; for the degree of the final polynomial, the statement is honest
(`HonestStatement`). Nothing is assumed about the hash functions.

## Not covered

The transcript (`transcript_honestProof` of `Exec/HonestProver/Prover.lean`),
and the assembly into `HonestProof` (`Exec/HonestProver.lean`).
-/

namespace CertiFri.Exec

open Fri Polynomial

namespace HonestProver

/-! ## Indices -/

/-- An index of the first domain, shifted to a shorter height, is an index of
that height. -/
theorem shiftRight_sub_lt {index n h : ℕ} (hindex : index < 2 ^ n) (hle : h ≤ n) :
    index >>> (n - h) < 2 ^ h := by
  have hn : h + (n - h) = n := by omega
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)), ← Nat.pow_add,
    hn]
  exact hindex

section Challenger

variable {σ F EF D : Type}

/-- A challenger whose sampled integers are in range hands out indices in
range. -/
theorem sampleIndices_lt {chal : Challenger σ F EF D}
    (hbits : ∀ s bits, (chal.sampleBits s bits).1 < 2 ^ bits) (bits : ℕ) :
    ∀ (count : ℕ) (s : σ), ∀ x ∈ chal.sampleIndices bits count s, x < 2 ^ bits
  | 0, _, x, hx => by cases hx
  | count + 1, s, x, hx => by
    rw [Challenger.sampleIndices, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hbits s bits
    · exact sampleIndices_lt hbits bits count _ x hx

/-- An entry of an array of numbers in range, read with the default zero, is in
range. -/
theorem getD_lt {indices : Array ℕ} {n : ℕ} (h : ∀ x ∈ indices, x < 2 ^ n) (t : ℕ) :
    indices.getD t 0 < 2 ^ n := by
  rw [Array.getD_eq_getD_getElem?]
  rcases hx : indices[t]? with _ | x
  · exact Nat.two_pow_pos n
  · exact h x (Array.mem_of_getElem? hx)

end Challenger

/-! ## The input matrices -/

section Inputs

variable {F K D : Type} [Field K] (params : FriParams) (shape : ClaimShape) (w : Committed F K)

/-- The matrix at position `mi` of batch `b`. -/
theorem getElem?_inputMatrices (b mi : ℕ) :
    (inputMatrices params shape w b)[mi]? = (shape.getD b [])[mi]?.map fun ms =>
      { logHeight := ms.logDegree + params.logBlowup, width := ms.width, row := w.row b mi } := by
  rw [inputMatrices, List.getElem?_map, List.getElem?_zipIdx, Option.map_map]
  rcases (shape.getD b [])[mi]? with _ | ms
  · rfl
  · simp only [Option.map_some, Function.comp_apply, Nat.zero_add]

/-- A batch has one committed matrix per matrix of the shape. -/
theorem length_inputMatrices (b : ℕ) :
    (inputMatrices params shape w b).length = (shape.getD b []).length := by
  rw [inputMatrices, List.length_map, List.length_zipIdx]

/-- The dimensions of the committed matrices of a batch are those the verifier
computes from the shape. -/
theorem dimsOf_inputMatrices (b : ℕ) :
    Merkle.dimsOf (inputMatrices params shape w b) =
      batchDims params.logBlowup (shape.getD b []) := by
  rw [Merkle.dimsOf, batchDims]
  refine congrArg List.toArray (List.ext_getElem? fun mi => ?_)
  rw [List.getElem?_map, getElem?_inputMatrices, Option.map_map, List.getElem?_map]
  rfl

variable {params shape w}

/-- A batch of the shape that is not empty has a committed matrix. -/
theorem inputMatrices_ne_nil (hbatch : ∀ mats ∈ shape, mats ≠ []) {b : ℕ}
    (hb : b < shape.length) : inputMatrices params shape w b ≠ [] := by
  intro h
  have hlen := length_inputMatrices params shape w b
  rw [h, List.length_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb,
    Option.getD_some] at hlen
  exact hbatch _ (List.getElem_mem hb) (List.eq_nil_of_length_eq_zero hlen.symm)

/-- The rows of the committed matrices have the widths of the matrices, when
the rows of `w` do. -/
theorem width_inputMatrices
    (hwidth : ∀ (b mi : ℕ) (mats : List MatrixShape) (ms : MatrixShape),
      shape[b]? = some mats → mats[mi]? = some ms →
        ∀ i < 2 ^ (ms.logDegree + params.logBlowup), (w.row b mi i).size = ms.width)
    (b : ℕ) :
    ∀ M ∈ inputMatrices params shape w b, ∀ i < 2 ^ M.logHeight, (M.row i).size = M.width := by
  intro M hM i hi
  obtain ⟨mi, hmi⟩ := List.mem_iff_getElem?.mp hM
  rw [getElem?_inputMatrices, List.getD_eq_getElem?_getD] at hmi
  rcases hmats : shape[b]? with _ | mats
  · rw [hmats] at hmi
    simp at hmi
  · rw [hmats, Option.getD_some] at hmi
    rcases hms : mats[mi]? with _ | ms
    · rw [hms] at hmi
      simp at hmi
    · rw [hms, Option.map_some, Option.some.injEq] at hmi
      subst hmi
      exact hwidth b mi mats ms hmats hms i hi

/-- **The openings of an input batch verify.** For query indices of the first
domain, the Merkle check accepts the opening of batch `b`, under the root of
the tree of the batch. -/
theorem verifyOpenings_inputOpening [DecidableEq D] (hIn : MerkleHasher F D)
    (hbatch : ∀ mats ∈ shape, mats ≠ [])
    (hwidth : ∀ (b mi : ℕ) (mats : List MatrixShape) (ms : MatrixShape),
      shape[b]? = some mats → mats[mi]? = some ms →
        ∀ i < 2 ^ (ms.logDegree + params.logBlowup), (w.row b mi i).size = ms.width)
    {indices : Array ℕ}
    (hidx : ∀ t, indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape) {b : ℕ}
    (hb : b < shape.length) :
    Merkle.verifyOpenings hIn (Merkle.root hIn (inputMatrices params shape w b))
      (batchDims params.logBlowup (shape.getD b []))
      (Array.ofFn (n := params.numQueries) fun t =>
        indices.getD t.val 0 >>> (logMaxHeight params.logBlowup shape -
          Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))
      (inputOpening params shape hIn w indices b).openedValues
      (inputOpening params shape hIn w indices b).openingProof = true := by
  have h := Merkle.verifyOpenings_tree hIn (inputMatrices_ne_nil hbatch hb)
    (width_inputMatrices hwidth b)
    (Array.ofFn (n := params.numQueries) fun t =>
      indices.getD t.val 0 >>> (logMaxHeight params.logBlowup shape -
        Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))
    (by
      intro x hx
      obtain ⟨t, rfl⟩ := Array.mem_ofFn.mp hx
      rw [dimsOf_inputMatrices]
      exact shiftRight_sub_lt (hidx t.val) (maxLogHeight_batchDims_le b))
  rw [dimsOf_inputMatrices] at h
  exact h

/-- The row of a matrix that the tree of its batch opens at a query index,
shifted to the tallest matrix of the batch: the row of `w` at the index shifted
to the height of the matrix. -/
theorem getD_rowsAt_inputMatrices {b mi : ℕ} {mats : List MatrixShape} {ms : MatrixShape}
    (hmats : shape[b]? = some mats) (hms : mats[mi]? = some ms) (index : ℕ) :
    (Merkle.rowsAt (inputMatrices params shape w b)
        (index >>> (logMaxHeight params.logBlowup shape -
          Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))).getD mi
        #[] =
      w.row b mi
        (index >>> (logMaxHeight params.logBlowup shape - (ms.logDegree + params.logBlowup))) := by
  have hget : shape.getD b [] = mats := by
    rw [List.getD_eq_getElem?_getD, hmats, Option.getD_some]
  have htop : Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList ≤
      logMaxHeight params.logBlowup shape := maxLogHeight_batchDims_le b
  have hle : ms.logDegree + params.logBlowup ≤
      Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList := by
    rw [hget]
    exact Merkle.le_maxLogHeight (d := ⟨ms.width, ms.logDegree + params.logBlowup⟩)
      (List.mem_map.mpr ⟨ms, List.mem_of_getElem? hms, rfl⟩)
  have hsum : logMaxHeight params.logBlowup shape -
        Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList +
      (Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList -
        (ms.logDegree + params.logBlowup)) =
      logMaxHeight params.logBlowup shape - (ms.logDegree + params.logBlowup) := by
    omega
  rw [Array.getD_eq_getD_getElem?, Merkle.getElem?_rowsAt, getElem?_inputMatrices,
    dimsOf_inputMatrices, hget, hms, Option.map_some, Option.map_some, Option.getD_some,
    ← Nat.shiftRight_add, ← hget, hsum]

end Inputs

/-! ## The opened rows of a query -/

section Rows

variable {F EF D K : Type} [FieldOps F] [Field K] {params : FriParams} {shape : ClaimShape}
  {hIn : MerkleHasher F D} {w : Committed F K} {indices : Array ℕ}
  {proof : FriProof F EF D (Array (List D)) (Array (List D))}

/-- **The opened entries are the committed ones.** In a proof whose input
openings are those of the prover for the query indices `indices`, the opened
entry of a claim for query `t` is the entry of the row of `w` at the index of
the query, shifted to the height of the claim's matrix. -/
theorem openedEntry_inputOpening
    (hpf : proof.inputOpenings = Array.ofFn (n := shape.length) fun b =>
      inputOpening params shape hIn w indices b.val)
    {c : ClaimRef} (hc : c ∈ claimRefs params.logBlowup shape) {t : ℕ}
    (ht : t < params.numQueries) :
    openedEntry (queryRows proof t) c =
      (w.row c.batch c.matrix
        (indices.getD t 0 >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD
        c.col 0 := by
  obtain ⟨p, hp, hb, hmat, hh, -⟩ := mem_claimRefs hc
  obtain ⟨mats, ms, hmats, hms, hph, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  have hbl : c.batch < shape.length := batch_lt_of_mem_claimRefs hc
  have hrows : (queryRows proof t).getD c.batch #[] =
      Merkle.rowsAt (inputMatrices params shape w c.batch)
        (indices.getD t 0 >>> (logMaxHeight params.logBlowup shape -
          Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD c.batch [])).toList)) := by
    simp [queryRows, hpf, inputOpening, hbl, ht]
  rw [← hb] at hmats
  rw [← hmat] at hms
  rw [openedEntry, hrows, getD_rowsAt_inputMatrices hmats hms, hh, hph]

end Rows

/-! ## The folding rounds -/

section Rounds

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hFri : MerkleHasher EF D) (w : Committed F K)
  (points values : Array EF)

/-- **The openings of a folding round verify.** For query indices of the first
domain, the Merkle check accepts, under the commitment of round `i` for the
challenges `ch`, the rows of the word of the round at the rows of the queries:
row `p` holds the values at the points of the indices `2 * p` and `2 * p + 1`
of level `i`. -/
theorem verifyOpenings_roundOpening [DecidableEq D] (ch : Challenges EF) {i : ℕ}
    (hi : i < logMaxHeight params.logBlowup shape)
    (hidx : ∀ t, ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape) :
    Merkle.verifyOpenings hFri
      (roundCommit m params shape wf hFri w points values ch.alpha ch.betas i)
      #[⟨2, logMaxHeight params.logBlowup shape - i - 1⟩]
      (Array.ofFn (n := params.numQueries) fun t => ch.indices.getD t.val 0 >>> (i + 1))
      (Array.ofFn (n := params.numQueries) fun t =>
        #[#[rep m ((word m params shape wf w points values ch.alpha ch.betas i).eval
              (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
                (logMaxHeight params.logBlowup shape - i)
                (2 * (ch.indices.getD t.val 0 >>> (i + 1))))),
            rep m ((word m params shape wf w points values ch.alpha ch.betas i).eval
              (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
                (logMaxHeight params.logBlowup shape - i)
                (2 * (ch.indices.getD t.val 0 >>> (i + 1)) + 1)))]])
      (roundOpening m params shape wf hFri w points values ch i).openingProof = true := by
  have h := Merkle.verifyOpenings_tree hFri
    (ms := [roundMatrix m params shape wf
      (word m params shape wf w points values ch.alpha ch.betas i) i])
    (List.cons_ne_nil _ _)
    (by
      intro M hM p _
      rw [List.mem_singleton.mp hM]
      rfl)
    (Array.ofFn (n := params.numQueries) fun t => ch.indices.getD t.val 0 >>> (i + 1))
    (by
      intro x hx
      obtain ⟨t, rfl⟩ := Array.mem_ofFn.mp hx
      rw [Merkle.maxLogHeight_dimsOf_singleton]
      have hlt := shiftRight_sub_lt (hidx t.val)
        (Nat.sub_le (logMaxHeight params.logBlowup shape) (i + 1))
      have hsub : logMaxHeight params.logBlowup shape -
          (logMaxHeight params.logBlowup shape - (i + 1)) = i + 1 := by omega
      rw [hsub] at hlt
      exact hlt)
  rw [Array.map_ofFn] at h
  simp only [Function.comp_def, Merkle.rowsAt_singleton] at h
  exact h

variable {m params shape wf hFri w points values}

/-- The sibling value of a query in a round, in a proof whose openings of the
rounds are those of the prover for the challenges `ch`: the representation of
the value of the word of the round at the other point of the query's pair. -/
theorem sibling_roundOpening {ch : Challenges EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))}
    (hpf : proof.commitPhaseOpenings = Array.ofFn (n := numRounds params shape) fun i =>
      roundOpening m params shape wf hFri w points values ch i.val)
    {i : ℕ} (hi : i < numRounds params shape) {t : ℕ} (ht : t < params.numQueries) :
    sibling proof i t =
      rep m ((word m params shape wf w points values ch.alpha ch.betas i).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          (logMaxHeight params.logBlowup shape - i) ((ch.indices.getD t 0 >>> i) ^^^ 1))) := by
  simp [sibling, hpf, roundOpening, hi, ht]

end Rounds

/-! ## The final polynomial -/

section Final

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K)

omit [TwoAdicOps F] in
/-- The array of representations of the first `n` coefficients of a polynomial
of degree below `n`, read in `K`, is the polynomial. -/
theorem polyOfCoeffs_rep {G : K[X]} {n : ℕ} (hG : G.degree < n) :
    polyOfCoeffs ((Array.ofFn (n := n) fun k => rep m (G.coeff k.val)).toList.map
      m.ext.toModel) = G := by
  ext k
  rw [coeff_polyOfCoeffs, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_ofFn]
  by_cases hk : k < n
  · simp only [hk, ↓reduceDIte, Option.map_some, Option.getD_some, toModel_rep]
  · simp only [hk, ↓reduceDIte, Option.map_none, Option.getD_none]
    exact (coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hG (Nat.cast_le.mpr (Nat.le_of_not_lt hk)))).symm

variable (params : FriParams) (shape : ClaimShape) (wf : WellFormed m params shape)
  {w : Committed F K} {points values : Array EF}

/-- For an honest statement, the word after the last round has degree below
the length of the final polynomial, whatever the challenges. -/
theorem degree_word_lt (hst : HonestStatement m params shape wf w points values) (alpha : EF)
    (betas : Array EF) :
    (word m params shape wf w points values alpha betas (numRounds params shape)).degree <
      params.finalPolyLen := by
  classical
  have h : (word m params shape wf w points values alpha betas (numRounds params shape)).degree <
      ((2 ^ (numRounds params shape - numRounds params shape) * params.finalPolyLen : ℕ) :
        WithBot ℕ) :=
    degree_honestPoly_lt (modelParams m params shape wf).ldt _
      (fun i _ => degree_inputPoly_lt m params shape wf hst (m.ext.toModel alpha) i)
      (numRounds params shape) le_rfl
  rwa [Nat.sub_self, pow_zero, one_mul] at h

end Final

/-! ## The lengths -/

section Shape

variable {F EF D : Type} [FieldOps F] [TwoAdicOps F] {InputProof CommitProof : Type}
  {params : FriParams} {shape : ClaimShape} {commitments : Array D} {points values : Array EF}
  {proof : FriProof F EF D InputProof CommitProof}

/-- **The shape checks of the verifier pass** when the statement has the shape
the verifier requires and every array of the proof has the length the
parameters and the shape fix. -/
theorem shapeOk_of_sizes (hst : StatementShape F params shape points values)
    (hcomm : commitments.size = shape.length)
    (hcommits : proof.commitPhaseCommits.size = numRounds params shape)
    (hwitnesses : proof.commitPowWitnesses.size = numRounds params shape)
    (hopenings : proof.commitPhaseOpenings.size = numRounds params shape)
    (hrounds : ∀ o ∈ proof.commitPhaseOpenings, o.logArity = 1 ∧
      o.siblingValues.size = params.numQueries ∧ ∀ v ∈ o.siblingValues, v.size = 1)
    (hfinal : proof.finalPoly.size = params.finalPolyLen)
    (hinputs : proof.inputOpenings.size = shape.length)
    (hrows : ∀ b < shape.length, ∃ o, proof.inputOpenings[b]? = some o ∧
      o.openedValues.size = params.numQueries ∧
        ∀ v ∈ o.openedValues, v.size = (shape.getD b []).length) :
    shapeOk (F := F) params shape commitments points values proof = true := by
  simp only [shapeOk, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    Array.all_eq_true_iff_forall_mem, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hst.numQueries_ne, hst.maxLogArity_ne⟩, hst.flatten_ne⟩,
    fun ms hms => ⟨hst.numPoints_ne ms hms, hst.finalHeight_le ms hms⟩⟩, hst.le_twoAdicity⟩,
    hcomm⟩, hst.size_points⟩, hst.size_values⟩, hcommits⟩, hwitnesses⟩, hopenings⟩,
    fun o ho => ?_⟩, hfinal⟩, hinputs⟩, fun b hb => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hrounds o ho
    exact ⟨⟨h1, h2⟩, h3⟩
  · obtain ⟨o, ho, h1, h2⟩ := hrows b hb
    rw [ho]
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem]
    exact ⟨h1, h2⟩

end Shape

section OpeningShapes

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hIn : MerkleHasher F D) (hFri : MerkleHasher EF D)
  (w : Committed F K) (points values : Array EF)

/-- The opening of a folding round folds by two and holds one sibling value
per query. -/
theorem shape_roundOpening (ch : Challenges EF) (i : ℕ) :
    (roundOpening m params shape wf hFri w points values ch i).logArity = 1 ∧
      (roundOpening m params shape wf hFri w points values ch i).siblingValues.size =
        params.numQueries ∧
      ∀ v ∈ (roundOpening m params shape wf hFri w points values ch i).siblingValues,
        v.size = 1 := by
  refine ⟨rfl, Array.size_ofFn, fun v hv => ?_⟩
  obtain ⟨t, rfl⟩ := Array.mem_ofFn.mp hv
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] in
/-- The opening of an input batch holds, for every query, one row per matrix
of the batch. -/
theorem shape_inputOpening (indices : Array ℕ) (b : ℕ) :
    (inputOpening params shape hIn w indices b).openedValues.size = params.numQueries ∧
      ∀ v ∈ (inputOpening params shape hIn w indices b).openedValues,
        v.size = (shape.getD b []).length := by
  refine ⟨by rw [inputOpening, Array.size_map, Array.size_ofFn], fun v hv => ?_⟩
  obtain ⟨x, -, rfl⟩ := Array.mem_map.mp hv
  rw [Merkle.size_rowsAt, length_inputMatrices]

end OpeningShapes

/-! ## The proof-of-work checks -/

section Pow

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hFri : MerkleHasher EF D) {chal : Challenger σ F EF D}
  (w : Committed F K) (points values : Array EF) {grind : σ → ℕ → F}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] in
/-- At zero difficulty every witness passes when the challenger state is valid. -/
theorem checkWitness_zero (chal : Challenger σ F EF D) (s : σ) (x : F) (hok : chal.ok s = true) :
    (chal.checkWitness s 0 x).1 = true := by
  simp [Challenger.checkWitness, hok]

/-- If the search finds a passing witness for the difficulty of the folding
rounds in every state, every witness of the prover's folding rounds passes. -/
theorem powOk_run
    (hgrind : ∀ s,
      (chal.checkWitness s params.commitPowBits (grind s params.commitPowBits)).1 = true)
    (alpha : EF) (s : σ) :
    ∀ i, (run m params shape wf hFri chal w points values grind alpha s i).powOk = true
  | 0 => rfl
  | i + 1 => by
    change ((run m params shape wf hFri chal w points values grind alpha s i).powOk &&
      (chal.checkWitness _ params.commitPowBits (grind _ params.commitPowBits)).1) = true
    rw [powOk_run hgrind alpha s i, hgrind, Bool.and_self]

end Pow

end HonestProver

end CertiFri.Exec
