import CertiFriProofs.Exec.Setup
import CertiFriProofs.Exec.MerkleMap

/-!
# The commitment checks, and the assembly of the verdict

The checks of the executable verifier (`Fri.verifyWith`), run with the Merkle
commitment schemes over the hash functions of the model, imply the verdict of
the model verifier (`modelChecks`).

* `inputChecks_model`: the executable commitment checks of the input batches
  are those of the model.
* `commitChecks_model`: the executable commitment checks of the folding rounds
  are those of the model, given that the rows the executable fold chain
  reconstructs are the rows of the model.
* `modelChecks_of_verifyWith_aux`: the assembly. If the executable checks pass,
  every proof-of-work check passed and the verdict of the model verifier is
  `true`.

The steps are in `CertiFri.Exec.Checks`: what an accepted Merkle check says
about sizes (`size_of_verifyOpenings`), the executable checks unfolded for a
Merkle scheme (`inputChecks_merkle`, `commitChecks_merkle`), the roots in the
messages of the model (`inputRoots_eq`, `commitRoot_eq`), the rows and paths of
the model's proof (`ofFn_inputRows`, `ofFn_inputPaths`, `ofFn_commitPaths`),
and the Merkle check of the two executable schemes as the Merkle check of the
model (`verifyOpenings_inputHasher`, `verifyOpenings_friHasher`).

## What is assumed

The arithmetic of one query is not treated here. The assembly takes two facts
about it as hypotheses: a query that passes its own checks has a model fold
chain that ends at the value of the final polynomial (`hfinal`), and the rows
of the executable fold chain are, as elements of the model field, the rows of
the model (`hrows`).

The messages, the challenges and the query indices of the model are those of
the run (`Agrees`). The proof data of the model is that of the executable proof
(`modelProof`), whose commitment proofs hold one Merkle path per query.
Nothing is assumed about the hash functions.

## What is not covered

How the challenges come out of a challenger, the arithmetic of one query, and
soundness.
-/

namespace CertiFri.Exec

open Fri

namespace Checks

/-! ## Sizes -/

/-- An accepted Merkle check has one group of opened rows and one path per
index. -/
theorem size_of_verifyOpenings {T D : Type} [DecidableEq D] {h : MerkleHasher T D} {root : D}
    {dims : Array Dimensions} {indices : Array ℕ} {rows : Array (Array (Array T))}
    {paths : Array (List D)} (hv : Merkle.verifyOpenings h root dims indices rows paths = true) :
    rows.size = indices.size ∧ paths.size = indices.size := by
  simp only [Merkle.verifyOpenings, Bool.and_eq_true, beq_iff_eq] at hv
  exact ⟨hv.1.1, hv.1.2⟩

/-- The images of the entries of an array, each read with a default, are the
image of the array. -/
theorem ofFn_map_getD {α β : Type} (f : α → β) (arr : Array α) (d : α) {q : ℕ}
    (h : arr.size = q) : (Array.ofFn fun t : Fin q => f (arr.getD t.val d)) = arr.map f := by
  subst h
  refine Array.ext (by simp) fun i _ _ => ?_
  simp

/-- An array is the array of its entries, each read with a default. -/
theorem ofFn_getD {α : Type} (arr : Array α) (d : α) {q : ℕ} (h : arr.size = q) :
    (Array.ofFn fun t : Fin q => arr.getD t.val d) = arr :=
  (ofFn_map_getD id arr d h).trans (Array.map_id arr)

/-- An entry of the image of an array given by a function. -/
theorem getD_map_ofFn {α β : Type} (f : α → β) {q : ℕ} (r : Fin q → α) (d : β) (t : Fin q) :
    ((Array.ofFn r).map f).getD t.val d = f (r t) := by
  simp

/-- The image of an array of single rows of two entries. -/
theorem map_ofFn_pair {α β : Type} (g : α → β) {q : ℕ} (a b : Fin q → α) :
    ((Array.ofFn fun t => #[#[a t, b t]]).map fun r => r.map fun row => row.map g) =
      Array.ofFn fun t => #[#[g (a t), g (b t)]] := by
  simp [Function.comp_def]

/-! ## The executable checks for a Merkle scheme -/

section Merkle

variable {F EF D : Type} [FieldOps EF] [DecidableEq D]

/-- The executable commitment check of an input batch, for the Merkle scheme
over a hasher: the batch has a commitment and an opening, and the Merkle check
of the opened rows passes. -/
theorem inputChecks_merkle (h : MerkleHasher F D) {params : FriParams} {shape : ClaimShape}
    {commitments : Array D} {inputOpenings : Array (BatchOpening F (Array (List D)))}
    {indices : Array ℕ}
    (hin : inputChecks (merkleMmcs h) params shape commitments inputOpenings indices = true)
    {b : ℕ} (hb : b < shape.length) :
    ∃ (root : D) (opening : BatchOpening F (Array (List D))),
      commitments[b]? = some root ∧ inputOpenings[b]? = some opening ∧
      Merkle.verifyOpenings h root (batchDims params.logBlowup (shape.getD b []))
        (Array.ofFn (n := params.numQueries) fun t => indices.getD t.val 0 >>>
          (logMaxHeight params.logBlowup shape -
            Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))
        opening.openedValues opening.openingProof = true := by
  simp only [inputChecks, List.all_eq_true, List.mem_range] at hin
  have hb := hin b hb
  split at hb
  · next root opening hroot ho => exact ⟨root, opening, hroot, ho, hb⟩
  · exact absurd hb (by simp)

/-- The executable commitment check of a folding round, for the Merkle scheme
over a hasher: the round has a commitment and an opening, and the Merkle check
of the rows of the queries passes. -/
theorem commitChecks_merkle (h : MerkleHasher EF D) {numQueries n rounds : ℕ}
    {commits : Array D} {openings : Array (CommitPhaseStep EF (Array (List D)))}
    {indices : Array ℕ} {rows : Array (List (EF × EF))}
    (hc : commitChecks (merkleMmcs h) numQueries n rounds commits openings indices rows = true)
    {i : ℕ} (hi : i < rounds) :
    ∃ (root : D) (opening : CommitPhaseStep EF (Array (List D))),
      commits[i]? = some root ∧ openings[i]? = some opening ∧
      Merkle.verifyOpenings h root #[⟨2, n - i - 1⟩]
        (Array.ofFn (n := numQueries) fun t => indices.getD t.val 0 >>> (i + 1))
        (Array.ofFn (n := numQueries) fun t =>
          #[#[((rows.getD t.val []).getD i (0, 0)).1, ((rows.getD t.val []).getD i (0, 0)).2]])
        opening.openingProof = true := by
  simp only [commitChecks, List.all_eq_true, List.mem_range] at hc
  have hi := hc i hi
  split at hi
  · next root opening hroot ho => exact ⟨root, opening, hroot, ho, hi⟩
  · exact absurd hi (by simp)

end Merkle

/-! ## The roots of the messages -/

/-- The digests of the statement are the commitments. -/
theorem digestsIn_firstMessage {F EF D : Type} (commitments : Array D) (points values : Array EF) :
    digestsIn (firstMessage (F := F) commitments points values) = commitments.toList := by
  simp [digestsIn, firstMessage, List.filterMap_append, List.filterMap_map]

section Messages

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  {commitments : Array D} {points values : Array EF} {InputProof CommitProof : Type}
  {proof : FriProof F EF D InputProof CommitProof} {ch : Challenges EF}
  {msg : ℕ → Compiled.Msg K D shape.length} {α : K} {β : ℕ → K}
  {index : Fin params.numQueries → ℕ}

/-- The root of an input batch in the model's first message is the commitment
of the batch. -/
theorem inputRoots_eq
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (b : Fin shape.length) {root : D} (hroot : commitments[b.val]? = some root) :
    (msg 0).inputRoots b = root := by
  rw [hag.msg 0 (Nat.zero_le _)]
  simp only [view, messages, ite_true, digestsIn_firstMessage, List.getD_eq_getElem?_getD,
    Array.getElem?_toList, hroot, Option.getD_some]

/-- The root of a folding round in the model's message of that round is the
commitment of the round. -/
theorem commitRoot_eq
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    {i : ℕ} (hi : i < numRounds params shape) {root : D}
    (hroot : proof.commitPhaseCommits[i]? = some root) :
    (msg (i + 1)).commitRoot = root := by
  rw [hag.msg (i + 1) (by omega)]
  simp [view, messages, digestsIn, hroot, hi]

end Messages

/-! ## The proof data -/

section ProofData

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  {proof : FriProof F EF D (Array (List D)) (Array (List D))}

/-- The opened rows of an input batch in the model's proof are the opened rows
of the executable proof, as elements of the model field. -/
theorem ofFn_inputRows (b : Fin shape.length) {opening : BatchOpening F (Array (List D))}
    (ho : proof.inputOpenings[b.val]? = some opening)
    (hsize : opening.openedValues.size = params.numQueries) :
    Array.ofFn ((modelProof m params shape proof).inputRows b) =
      opening.openedValues.map fun r => r.map fun row => row.map m.base.toModel := by
  rw [← ofFn_map_getD (fun r => r.map fun row => row.map m.base.toModel) opening.openedValues
    #[] hsize]
  congr 1
  funext t
  simp [modelProof, queryRows, ho]

/-- The paths of an input batch in the model's proof are those of the
executable proof. -/
theorem ofFn_inputPaths (b : Fin shape.length) {opening : BatchOpening F (Array (List D))}
    (ho : proof.inputOpenings[b.val]? = some opening)
    (hsize : opening.openingProof.size = params.numQueries) :
    Array.ofFn ((modelProof m params shape proof).inputPaths b) = opening.openingProof := by
  rw [← ofFn_getD opening.openingProof [] hsize]
  congr 1
  funext t
  simp only [modelProof, ho]

/-- The paths of a folding round in the model's proof are those of the
executable proof. -/
theorem ofFn_commitPaths (i : ℕ) {opening : CommitPhaseStep EF (Array (List D))}
    (ho : proof.commitPhaseOpenings[i]? = some opening)
    (hsize : opening.openingProof.size = params.numQueries) :
    Array.ofFn ((modelProof m params shape proof).commitPaths i) = opening.openingProof := by
  rw [← ofFn_getD opening.openingProof [] hsize]
  congr 1
  funext t
  simp only [modelProof, ho]

end ProofData

/-! ## The hashers -/

section Hashers

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  [DecidableEq D] (m : FieldModel F EF K) (H : MerkleHasher K D) (root : D)
  (dims : Array Dimensions) (indices : Array ℕ) (paths : Array (List D))

/-- The Merkle check of the input scheme is the Merkle check of the model on
the opened rows as elements of the model field. -/
theorem verifyOpenings_inputHasher (rows : Array (Array (Array F))) :
    Merkle.verifyOpenings (inputHasher m H) root dims indices rows paths =
      Merkle.verifyOpenings H root dims indices
        (rows.map fun r => r.map fun row => row.map m.base.toModel) paths :=
  verifyOpenings_map m.base.toModel H root dims indices rows paths

/-- The Merkle check of the scheme of the folding rounds is the Merkle check of
the model on the opened rows as elements of the model field. -/
theorem verifyOpenings_friHasher (rows : Array (Array (Array EF))) :
    Merkle.verifyOpenings (friHasher m H) root dims indices rows paths =
      Merkle.verifyOpenings H root dims indices
        (rows.map fun r => r.map fun row => row.map m.ext.toModel) paths :=
  verifyOpenings_map m.ext.toModel H root dims indices rows paths

end Hashers

end Checks

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)
  {commitments : Array D} {points values : Array EF}
  {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : Challenges EF}
  {msg : ℕ → Compiled.Msg K D shape.length} {α : K} {β : ℕ → K}
  {index : Fin params.numQueries → ℕ}

/-! ## The input batches -/

omit [DecidableEq K] in
/-- **The commitment checks of the input batches.** If the executable checks of
the input batches pass for the Merkle scheme over the hash functions of the
model, then the Merkle checks of the input batches of the model verifier
pass. -/
theorem inputChecks_model (H : MerkleHasher K D)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (hin : inputChecks (merkleMmcs (inputHasher m H)) params shape commitments
      proof.inputOpenings ch.indices = true) :
    (List.finRange (modelParams m params shape wf).batches).all (fun b =>
      Merkle.verifyOpenings H ((msg 0).inputRoots b) ((modelParams m params shape wf).dims b)
        (Array.ofFn fun t => index t >>> ((modelParams m params shape wf).n -
          Merkle.maxLogHeight ((modelParams m params shape wf).dims b).toList))
        (Array.ofFn ((modelProof m params shape proof).inputRows b))
        (Array.ofFn ((modelProof m params shape proof).inputPaths b))) = true := by
  rw [List.all_eq_true]
  intro b _
  obtain ⟨root, opening, hroot, ho, hv⟩ := Checks.inputChecks_merkle _ hin b.isLt
  obtain ⟨hrows, hpaths⟩ := Checks.size_of_verifyOpenings hv
  rw [Array.size_ofFn] at hrows hpaths
  rw [Checks.verifyOpenings_inputHasher] at hv
  rw [Checks.inputRoots_eq m params shape hag b hroot,
    Checks.ofFn_inputRows m params shape b ho hrows,
    Checks.ofFn_inputPaths m params shape b ho hpaths]
  simp only [hag.index]
  exact hv

/-! ## The folding rounds -/

omit [DecidableEq K] in
/-- **The commitment checks of the folding rounds.** If the executable checks
of the folding rounds pass for the Merkle scheme over the hash functions of the
model, and the rows of the executable fold chains are, as elements of the model
field, the rows of the model, then the Merkle checks of the folding rounds of
the model verifier pass. -/
theorem commitChecks_model (H : MerkleHasher K D)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (hrows : ∀ (t : Fin params.numQueries) (i : ℕ), i < numRounds params shape →
      (m.ext.toModel
          (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).1),
        m.ext.toModel
          (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).2)) =
      (modelParams m params shape wf).commitRow (modelProof m params shape proof) (msg 0) α β
        (index t) t i)
    (hcommit : commitChecks (merkleMmcs (friHasher m H)) params.numQueries
      (logMaxHeight params.logBlowup shape) (numRounds params shape) proof.commitPhaseCommits
      proof.commitPhaseOpenings ch.indices
      ((Array.ofFn fun t : Fin params.numQueries =>
        queryResult (F := F) params shape points values proof ch t.val).map (·.rows)) = true) :
    (List.range (modelParams m params shape wf).rounds).all (fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot
        ((modelParams m params shape wf).commitDims i)
        (Array.ofFn fun t => index t >>> (i + 1))
        (Array.ofFn fun t =>
          #[#[((modelParams m params shape wf).commitRow (modelProof m params shape proof)
              (msg 0) α β (index t) t i).1,
            ((modelParams m params shape wf).commitRow (modelProof m params shape proof)
              (msg 0) α β (index t) t i).2]])
        (Array.ofFn ((modelProof m params shape proof).commitPaths i))) = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi : i < numRounds params shape := List.mem_range.mp hi
  obtain ⟨root, opening, hroot, ho, hv⟩ := Checks.commitChecks_merkle _ hcommit hi
  obtain ⟨-, hpaths⟩ := Checks.size_of_verifyOpenings hv
  rw [Array.size_ofFn] at hpaths
  rw [Checks.verifyOpenings_friHasher, Checks.map_ofFn_pair] at hv
  simp only [Checks.getD_map_ofFn] at hv
  rw [Checks.commitRoot_eq m params shape hag hi hroot,
    Checks.ofFn_commitPaths m params shape i ho hpaths]
  simp only [← hrows _ i hi]
  simp only [hag.index]
  exact hv

/-! ## The assembly -/

/-- **The executable checks imply the verdict of the model.** If the checks of
the executable verifier pass, with the Merkle commitment schemes over the hash
functions `H` of the model, then every proof-of-work check passed and the
model verifier accepts against `H`: its Merkle checks of the input batches
pass, every fold chain ends at the value of the final polynomial, and its
Merkle checks of the folding rounds pass.

The two hypotheses about the arithmetic of one query are `hfinal`, for a query
that passes its own checks, and `hrows`, for the rows of the fold chain. The
shape check `_hshape` is not used: the lengths this proof needs follow from the
accepted Merkle checks. -/
theorem modelChecks_of_verifyWith_aux (H : MerkleHasher K D)
    (_hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (hfinal : ∀ t : Fin params.numQueries,
      (queryResult (F := F) params shape points values proof ch t.val).ok = true →
      (modelParams m params shape wf).folded (modelProof m params shape proof) (msg 0) α β
          (index t) t (modelParams m params shape wf).rounds =
        Compiled.hornerEval
          ((msg ((modelParams m params shape wf).rounds + 1)).finalCoeffs.take
            (modelParams m params shape wf).finalDegree)
          (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - (modelParams m params shape wf).rounds)
            (index t >>> (modelParams m params shape wf).rounds)))
    (hrows : ∀ (t : Fin params.numQueries) (i : ℕ), i < numRounds params shape →
      (m.ext.toModel
          (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).1),
        m.ext.toModel
          (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).2)) =
      (modelParams m params shape wf).commitRow (modelProof m params shape proof) (msg 0) α β
        (index t) t i)
    (h : verifyWith (merkleMmcs (inputHasher m H)) (merkleMmcs (friHasher m H)) params shape
      commitments points values proof ch = true) :
    ch.powOk = true ∧
      modelChecks (modelParams m params shape wf) H (modelProof m params shape proof) msg α β
        index = true := by
  have h' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun t =>
        decide (ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs (inputHasher m H)) params shape commitments
        proof.inputOpenings ch.indices
      && (Array.ofFn fun t : Fin params.numQueries =>
        queryResult (F := F) params shape points values proof ch t.val).all (·.ok)
      && commitChecks (merkleMmcs (friHasher m H)) params.numQueries
        (logMaxHeight params.logBlowup shape) (numRounds params shape) proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun t : Fin params.numQueries =>
          queryResult (F := F) params shape points values proof ch t.val).map (·.rows)))
      = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hpow, -⟩, -⟩, hin⟩, hok⟩, hcommit⟩ := h'
  refine ⟨hpow, ?_⟩
  have hfin : (modelParams m params shape wf).FinalCheck (modelProof m params shape proof) msg
      α β index := fun t => hfinal t (by
    have := Array.all_eq_true.mp hok t.val (by rw [Array.size_ofFn]; exact t.isLt)
    simpa using this)
  simp only [modelChecks, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨inputChecks_model m params shape wf H hag hin, hfin⟩,
    commitChecks_model m params shape wf H hag hrows hcommit⟩

end CertiFri.Exec
