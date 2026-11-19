import CertiFri.Verifier
import CertiFriProofs.Refines
import CertiFriProofs.Theory.Compiled.Verifier

/-!
# The executable verifier and the model: definitions

The security theory (`Theory/Compiled/`) is about a model verifier over one
mathematical field, whose messages are records and whose challenges are the
answers of a random oracle. The executable verifier (`CertiFri/Verifier.lean`)
computes over two executable fields, reads flat arrays, and takes its
challenges from a challenger. This file defines how the one is read as the
other. The theorems are in the sibling modules.

* `FieldModel F EF K`: the two executable fields implement one field `K`, the
  base field inside it.
* `modelParams`: the parameters of the model protocol for executable parameters
  and a shape of claims. Level `j` of the model holds the claims
  `levelClaims … j` of the shape, in their order.
* `messages`: what the executable verifier absorbs in each round, as the raw
  prover message of that round. `view` reads a raw message as a message of the
  model.
* `modelProof`: the proof data of the model for an executable proof whose
  commitment proofs are one Merkle path per query.
* `inputHasher`, `friHasher`: the hashers of the two commitment schemes when
  the hash functions are those of the model, applied to the modelled values of
  a row.
* `freeChallenger`: the challenger whose challenges are the answers of the
  model's random oracle to everything absorbed so far.
* `modelChecks`: what the model verifier computes against a fixed hasher
  (the right-hand side of `Compiled.Params.run_verifyWith`).
* `Agrees`: the messages, challenges and query indices of the model are those
  of a run of the executable verifier.

## The idealised challenger

`freeChallenger` keeps what was absorbed, split into rounds: an absorption
after a squeeze starts a new round. Every squeeze of a round reads the one
answer of the oracle to the rounds so far and the absorptions of the current
round: the proof-of-work bits are its first component, a field challenge its
second, and the `k`-th query index is the index of its `k`-th query point. So
the proof-of-work bits and the challenge of a round are independent uniform
values, as in `Theory/PcsRbr/Grinding.lean`.
-/

namespace CertiFri.Exec

open Oracle Fri
open PcsRbr (Chal GrindChal)

/-! ## The claims of a shape -/

section Shape

variable {lb : ℕ} {shape : ClaimShape}

/-- An opening point of a shape belongs to a matrix of the shape. -/
theorem mem_pointRefs {p : PointRef} (h : p ∈ pointRefs lb shape) :
    ∃ mats m, shape[p.batch]? = some mats ∧ mats[p.matrix]? = some m ∧
      p.logHeight = m.logDegree + lb ∧ p.width = m.width := by
  simp only [pointRefs, List.mem_flatMap, List.mem_zipIdx_iff_getElem?, List.mem_replicate] at h
  obtain ⟨⟨mats, b⟩, hb, ⟨m, mi⟩, hm, -, rfl⟩ := h
  exact ⟨mats, m, hb, hm, rfl, rfl⟩

/-- A claim of a shape is about a column of the matrix of one of the opening
points, the one at the position `pointIdx`. -/
theorem mem_claimRefs {c : ClaimRef} (h : c ∈ claimRefs lb shape) :
    ∃ p, (pointRefs lb shape)[c.pointIdx]? = some p ∧ c.batch = p.batch ∧
      c.matrix = p.matrix ∧ c.logHeight = p.logHeight ∧ c.col < p.width := by
  simp only [claimRefs, List.mem_map, List.mem_zipIdx_iff_getElem?] at h
  obtain ⟨⟨⟨p, pi, col⟩, vi⟩, hx, rfl⟩ := h
  have hmem := List.mem_of_getElem? hx
  simp only [List.mem_flatMap, List.mem_zipIdx_iff_getElem?, List.mem_map, List.mem_range] at hmem
  obtain ⟨⟨p', pi'⟩, hp, col', hcol, heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨p', hp, rfl, rfl, rfl, hcol⟩

/-- A claim of a shape is at the position `valueIdx` of the list of claims. -/
theorem getElem?_claimRefs_valueIdx {c : ClaimRef} (h : c ∈ claimRefs lb shape) :
    (claimRefs lb shape)[c.valueIdx]? = some c := by
  simp only [claimRefs, List.mem_map, List.mem_zipIdx_iff_getElem?] at h
  obtain ⟨⟨⟨p, pi, col⟩, vi⟩, hx, rfl⟩ := h
  simp only [claimRefs, List.getElem?_map, List.getElem?_zipIdx, hx, Option.map_some, Nat.zero_add]

/-- The batch of a claim is a batch of the shape. -/
theorem batch_lt_of_mem_claimRefs {c : ClaimRef} (h : c ∈ claimRefs lb shape) :
    c.batch < shape.length := by
  obtain ⟨p, hp, hb, -⟩ := mem_claimRefs h
  obtain ⟨mats, m, hmats, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  rw [hb]
  exact (List.getElem?_eq_some_iff.mp hmats).1

/-- A claim of a level is a claim of the shape. -/
theorem mem_claimRefs_of_mem_levelClaims {n j : ℕ} {c : ClaimRef}
    (h : c ∈ levelClaims lb shape n j) : c ∈ claimRefs lb shape :=
  (List.mem_filter.mp h).1

/-- A claim of level `j` is about a column of `2 ^ (n - j)` entries. -/
theorem logHeight_of_mem_levelClaims {n j : ℕ} {c : ClaimRef}
    (h : c ∈ levelClaims lb shape n j) : c.logHeight + j = n := by
  simpa using (List.mem_filter.mp h).2

private theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

private theorem maxLogHeight_le {dims : List Dimensions} {N : ℕ}
    (h : ∀ d ∈ dims, d.logHeight ≤ N) : Merkle.maxLogHeight dims ≤ N := by
  induction dims with
  | nil => exact Nat.zero_le _
  | cons d l ih =>
    simp only [Merkle.maxLogHeight]
    exact Nat.max_le.mpr
      ⟨h d List.mem_cons_self, ih fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

/-- No matrix of a shape is taller than the first domain. -/
theorem le_logMaxHeight {m : MatrixShape} (h : m ∈ shape.flatten) :
    m.logDegree + lb ≤ logMaxHeight lb shape :=
  le_foldr_max (List.mem_map_of_mem (f := fun m : MatrixShape => m.logDegree + lb) h)

/-- The tree of a batch is no deeper than the first domain is large. -/
theorem maxLogHeight_batchDims_le (b : ℕ) :
    Merkle.maxLogHeight (batchDims lb (shape.getD b [])).toList ≤ logMaxHeight lb shape := by
  refine maxLogHeight_le fun d hd => ?_
  simp only [batchDims, List.toList_toArray, List.mem_map] at hd
  obtain ⟨m, hm, rfl⟩ := hd
  refine le_logMaxHeight ?_
  rw [List.getD_eq_getElem?_getD] at hm
  rcases hb : shape[b]? with _ | mats
  · rw [hb] at hm
    cases hm
  · rw [hb] at hm
    exact List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hb, hm⟩

end Shape

/-! ## The fields -/

/-- The executable fields `F` and `EF` implement one mathematical field `K`:
`EF` all of it, and `F` a subfield, through the embedding of `F` in `EF`. -/
structure FieldModel (F EF K : Type) [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    [Field K] where
  /-- The base field, read in `K`. -/
  base : Refines F K
  /-- The extension field. -/
  ext : Refines EF K
  /-- The embedding of the base field is the inclusion. -/
  embed : ∀ a : F, ext.toModel (ExtensionOps.embed a) = base.toModel a
  /-- Every element of `K` has a representation. -/
  surj : Function.Surjective ext.toModel

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K]

/-- What the model needs of the two-adic structure of the executable base
field, for the first domain of a shape: the generator of that domain is a
primitive root of unity of its order, and the coset shift is not zero. -/
structure WellFormed (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) :
    Prop where
  /-- The generator of the first domain is a primitive root of unity. -/
  prim : IsPrimitiveRoot
    (m.base.toModel (TwoAdicOps.twoAdicGenerator (logMaxHeight params.logBlowup shape)))
    (2 ^ logMaxHeight params.logBlowup shape)
  /-- The coset shift is not zero. -/
  shift_ne : m.base.toModel TwoAdicOps.cosetShift ≠ 0

/-! ## The parameters of the model -/

/-- The parameters of the model protocol for executable parameters and a shape
of claims. The first domain has log-size `logMaxHeight`, there are `numRounds`
folding rounds, and level `j` holds the claims `levelClaims … j`, each about
the column its `ClaimRef` names. -/
def modelParams (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (wf : WellFormed m params shape) : Compiled.Params K where
  ω := m.base.toModel (TwoAdicOps.twoAdicGenerator (logMaxHeight params.logBlowup shape))
  n := logMaxHeight params.logBlowup shape
  rounds := numRounds params shape
  finalDegree := params.finalPolyLen
  shift := m.base.toModel TwoAdicOps.cosetShift
  queries := params.numQueries
  batches := shape.length
  dims := fun b => batchDims params.logBlowup (shape.getD b.val [])
  numClaims := fun j =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length
  slot := fun j k =>
    ⟨⟨((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k).batch,
        batch_lt_of_mem_claimRefs (mem_claimRefs_of_mem_levelClaims (List.get_mem _ k))⟩,
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k).matrix,
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k).col⟩
  prim := wf.prim
  rounds_le := Nat.sub_le _ _
  shift_ne := wf.shift_ne
  height_le := fun b => maxLogHeight_batchDims_le b.val
  slot_dims := by
    intro j _ k
    have hmem := List.get_mem
      (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j) k
    obtain ⟨p, hp, hb, hmat, hh, hcol⟩ := mem_claimRefs (mem_claimRefs_of_mem_levelClaims hmem)
    obtain ⟨mats, ms, hmats, hms, hph, hpw⟩ := mem_pointRefs (List.mem_of_getElem? hp)
    have hj := logHeight_of_mem_levelClaims hmem
    refine ⟨⟨ms.width, ms.logDegree + params.logBlowup⟩, ?_, ?_, ?_⟩
    · simp only [batchDims, List.getD_eq_getElem?_getD, hb, hmats, Option.getD_some, hmat,
        List.getElem?_toArray, List.getElem?_map, hms, Option.map_some]
    · simp only
      omega
    · simp only
      omega

/-! ## Messages -/

/-- A raw prover message: what the verifier absorbs in one round. -/
abbrev RawMsg (F EF D : Type) : Type := List (Observation F EF D)

/-- The digests of a raw message, in order. -/
def digestsIn (msg : RawMsg F EF D) : List D :=
  msg.filterMap fun
    | .digest d => some d
    | _ => none

/-- The extension-field elements of a raw message, in order, as elements of `K`. -/
def extsIn (m : FieldModel F EF K) (msg : RawMsg F EF D) : List K :=
  msg.filterMap fun
    | .ext e => some (m.ext.toModel e)
    | _ => none

/-- The raw message of round `j` of a run of the executable verifier: what
`transcript` absorbs before the squeeze of that round. Round `0` is the
statement. Round `1 + i`, for `i < numRounds`, is the commitment of folding
round `i`, followed by its proof-of-work witness when there is a check. The
last round is the final polynomial and the arities, followed by the last
witness when there is a check. -/
def messages [Inhabited D] (params : FriParams) (shape : ClaimShape) (commitments : Array D)
    (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (j : ℕ) : RawMsg F EF D :=
  if j = 0 then firstMessage commitments points values
  else if j ≤ numRounds params shape then
    .digest (proof.commitPhaseCommits.getD (j - 1) default) ::
      (if params.commitPowBits = 0 then [] else [.base (proof.commitPowWitnesses.getD (j - 1) 0)])
  else
    finalMessage (numRounds params shape) proof.finalPoly ++
      (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness])

/-- The number of proof-of-work bits of each round of the transcript: none
before the batching challenge, `commitPowBits` before each folding challenge,
`queryPowBits` before the query indices. -/
def powBits (params : FriParams) (shape : ClaimShape) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i ≤ numRounds params shape then params.commitPowBits
  else params.queryPowBits

/-- A raw message, read as a message of the model.

* The root of input batch `b` is the `b`-th digest, and the root of a folding
  round is the first digest.
* The opening point of a claim is the extension-field element at the position
  `pointIdx` of the claim, and its claimed value the one at the position
  `valueIdx` after the opening points. In the statement, the opening points
  come first and the claimed values after them.
* The coefficients of the final polynomial are the extension-field elements.

A missing digest reads as the default digest and a missing element as zero. -/
def view [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (msg : RawMsg F EF D) : Compiled.Msg K D shape.length where
  inputRoots := fun b => (digestsIn msg).getD b.val default
  points := (List.range (numRounds params shape + 1)).map fun j =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).map fun c =>
      (extsIn m msg).getD c.pointIdx 0
  values := (List.range (numRounds params shape + 1)).map fun j =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).map fun c =>
      (extsIn m msg).getD ((pointRefs params.logBlowup shape).length + c.valueIdx) 0
  commitRoot := (digestsIn msg).getD 0 default
  finalCoeffs := extsIn m msg
  witness := 0

/-! ## Proofs -/

/-- The proof data of the model for an executable proof whose commitment
proofs hold one Merkle path per query: the opened rows and the sibling values,
as elements of `K`, and the paths. Missing data reads as empty or zero. -/
def modelProof (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (proof : FriProof F EF D (Array (List D)) (Array (List D))) :
    Compiled.Proof K D shape.length params.numQueries where
  inputRows := fun b t => ((queryRows proof t.val).getD b.val #[]).map (·.map m.base.toModel)
  inputPaths := fun b t =>
    match proof.inputOpenings[b.val]? with
    | some o => o.openingProof.getD t.val []
    | none => []
  siblings := fun i t => m.ext.toModel (sibling proof i t.val)
  commitPaths := fun i t =>
    match proof.commitPhaseOpenings[i]? with
    | some o => o.openingProof.getD t.val []
    | none => []

/-! ## Hashers -/

/-- The hasher of the input commitments when the hash functions are `H`: a row
of base-field elements is hashed as the row of its values in `K`. -/
def inputHasher (m : FieldModel F EF K) (H : MerkleHasher K D) : MerkleHasher F D where
  hashRows xs := H.hashRows (xs.map m.base.toModel)
  compress := H.compress

/-- The hasher of the commitments of the folding rounds when the hash
functions are `H`: a row of extension-field elements is hashed as the row of
its values in `K`. -/
def friHasher (m : FieldModel F EF K) (H : MerkleHasher K D) : MerkleHasher EF D where
  hashRows xs := H.hashRows (xs.map m.ext.toModel)
  compress := H.compress

/-! ## What the model verifier computes -/

/-- The verdict of the model verifier against the hasher `H`: the Merkle checks
of the input batches, the comparison of every fold chain with the final
polynomial, and the Merkle checks of the folding rounds. For `H = hasherOf f`
this is `(P.verifyWith pf msg α β index).run f`
(`Compiled.Params.run_verifyWith`). -/
def modelChecks [DecidableEq K] [DecidableEq D] (P : Compiled.Params K) (H : MerkleHasher K D)
    (pf : Compiled.Proof K D P.batches P.queries) (msg : ℕ → Compiled.Msg K D P.batches) (α : K)
    (β : ℕ → K) (index : Fin P.queries → ℕ) : Bool :=
  ((List.finRange P.batches).all fun b =>
      Merkle.verifyOpenings H ((msg 0).inputRoots b) (P.dims b)
        (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
        (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
    decide (P.FinalCheck pf msg α β index) &&
    (List.range P.rounds).all fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot (P.commitDims i)
        (Array.ofFn fun t => index t >>> (i + 1))
        (Array.ofFn fun t => #[#[(P.commitRow pf (msg 0) α β (index t) t i).1,
          (P.commitRow pf (msg 0) α β (index t) t i).2]])
        (Array.ofFn (pf.commitPaths i))

/-! ## The data of one run, on both sides -/

/-- The claims of each level, as `Fri.verifyWith` hands them to the queries:
`levelClaims` of the level, read from an array with one entry per level up to
the last round. -/
def levelsOf (params : FriParams) (shape : ClaimShape) : ℕ → List ClaimRef := fun j =>
  (Array.ofFn (n := numRounds params shape + 1) fun j =>
    levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j.val).getD j []

/-- What `Fri.verifyWith` computes for query `t`. -/
def queryResult (params : FriParams) (shape : ClaimShape) (points values : Array EF)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof)
    (ch : Challenges EF) (t : ℕ) : QueryResult EF :=
  checkQuery (F := F) params shape (levelsOf params shape) points values proof ch t
    (ch.indices.getD t 0)

/-- The model's messages, challenges and query indices are those of a run of
the executable verifier: the message of each round is the raw message of the
round read through `view`, and the challenges are the executable challenges as
elements of `K`. -/
structure Agrees [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (ch : Challenges EF)
    (msg : ℕ → Compiled.Msg K D shape.length) (α : K) (β : ℕ → K)
    (index : Fin params.numQueries → ℕ) : Prop where
  /-- The messages of the rounds of the protocol. -/
  msg : ∀ j ≤ numRounds params shape + 1,
    msg j = view m params shape (messages params shape commitments points values proof j)
  /-- The batching challenge. -/
  alpha : α = m.ext.toModel ch.alpha
  /-- The folding challenges. -/
  beta : ∀ i < numRounds params shape, β i = m.ext.toModel (ch.betas.getD i 0)
  /-- The query indices. -/
  index : ∀ t, index t = ch.indices.getD t.val 0

/-! ## The idealised challenger -/

/-- The state of the idealised challenger: the number of closed rounds, their
raw messages, the absorptions of the current round, and the number of squeezes
made in the current round. -/
structure FreeState (F EF D : Type) where
  /-- The number of closed rounds. -/
  round : ℕ
  /-- The raw messages of the closed rounds. -/
  hist : ℕ → RawMsg F EF D
  /-- What was absorbed in the current round. -/
  cur : RawMsg F EF D
  /-- The number of squeezes made in the current round. -/
  nsamp : ℕ

/-- The state before anything is absorbed. -/
def FreeState.init : FreeState F EF D := ⟨0, fun _ => [], [], 0⟩

section Free

variable [DecidableEq K] (P : Compiled.Params K) (bits : ℕ → ℕ)
  (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) K D x)

/-- The answer of the oracle `f` for the current round of a state: its answer
to the transcript of the closed rounds and the absorptions of the current
round. -/
def freeAnswer (s : FreeState F EF D) : GrindChal bits (Chal P.ldt P.queries) s.round :=
  f (.chal (fsTranscript f s.hist s.round) s.cur)

/-- The `k`-th query point of a challenge; zero when there is none. -/
def queryPoint {i : ℕ} (c : Chal P.ldt P.queries i) (k : ℕ) : K :=
  if h : k < P.queries then c.points ⟨k, h⟩ else 0

/-- **The idealised challenger**: its challenges are the answers of the oracle
`f` to everything absorbed so far.

* An absorption after a squeeze closes the current round and starts the next.
* `sampleExt` returns a representation of the field challenge of the round's
  answer.
* The first `sampleBits` of a round with a proof-of-work check returns the
  proof-of-work bits of the round's answer. Every other `sampleBits` returns
  the index of the next query point of the round's answer. -/
noncomputable def freeChallenger (m : FieldModel F EF K) :
    Challenger (FreeState F EF D) F EF D where
  observe s o :=
    if s.nsamp = 0 then { s with cur := s.cur ++ [o] }
    else ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩
  sampleExt s :=
    (Function.surjInv m.surj (freeAnswer P bits f s).2.field, { s with nsamp := s.nsamp + 1 })
  sampleBits s _ :=
    (if s.nsamp = 0 ∧ bits s.round ≠ 0 then ((freeAnswer P bits f s).1 : ℕ)
      else P.indexOf (queryPoint P (freeAnswer P bits f s).2
        (s.nsamp - if bits s.round = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

end Free

end CertiFri.Exec
