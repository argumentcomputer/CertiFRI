import CertiFriProofs.Exec.Honest
import CertiFriProofs.Merkle.Tree

/-!
# The honest prover

`HonestProof` (`Exec/Honest.lean`) says what a proof that follows the protocol
looks like, in terms of the challenges the verifier derives from that proof.
This file defines a prover as a mathematical function and shows that the
verifier derives from its proof the challenges the prover itself used.

Nothing here is a program: the prover picks representations of field elements
with `rep`, so it is not computable, and no prover program is certified.

## The prover

The prover is given the committed data `w : Committed F K`, the opening points,
the claimed values, the two hash functions, the challenger with its initial
state, and a witness search `grind`: from a state of the challenger and a
number of bits, a proof-of-work witness. It runs the challenger as the verifier
does.

1. `honestCommitments`: for each batch, the Merkle root of its matrices
   (`HonestProver.inputMatrices`), whose rows are the rows of `w`.
2. `HonestProver.batching`: it absorbs the commitments, the opening points and
   the claimed values, and squeezes the batching challenge.
3. `HonestProver.run`: the folding rounds. In round `i` the prover commits to
   `honestWord` of level `i` for the challenges it holds (`HonestProver.word`),
   as the matrix of width two whose row `p` holds the values at the points of
   the indices `2 * p` and `2 * p + 1` (`HonestProver.roundMatrix`). It absorbs
   the commitment, searches a witness, runs the proof-of-work check and
   squeezes the folding challenge (`HonestProver.step`).
4. `HonestProver.finalPoly`: the coefficients of `honestWord` after the last
   round.
5. `HonestProver.queryPow`: it absorbs the final polynomial and the arities,
   searches a witness and runs the proof-of-work check. Then it squeezes the
   query indices.
6. `HonestProver.inputOpening`, `HonestProver.roundOpening`: it opens every
   input batch and the matrix of every round at the query indices, with the
   rows and the paths of the Merkle trees (`Merkle/Tree.lean`).

`honestChallenges` holds the challenges of this run and whether every witness
the search returned passed its check; `honestProof` is the proof.
`StatementShape` is the part of `Fri.shapeOk` that is about the statement; the
sibling modules assume it.

## What is proved

* `HonestProver.honestWord_congr`: `honestWord` of level `i` depends on the
  folding challenges of the rounds before `i` only.
* `HonestProver.commitPhase_run`: on the commitments and witnesses of the
  prover, the commit phase of the verifier's transcript goes through the
  states of the prover.
* `transcript_honestProof`: the challenges the verifier derives from the
  honest proof are `honestChallenges`.

## What is assumed

`FieldModel` and `WellFormed`, which the definitions of `Exec/Honest.lean`
take. Nothing else: the theorems hold for every challenger, every pair of hash
functions, every witness search and every statement.

## Not covered

That the honest proof satisfies `HonestProof` and is accepted: the modules
`Exec/HonestProver/Fields.lean` and `Exec/HonestProver.lean`. Zero-knowledge,
and any statement about a prover program.
-/

namespace CertiFri.Exec

open Fri Polynomial

/-- **The statement has the shape the verifier requires**: the part of
`Fri.shapeOk` that is about the parameters, the shape of the claims, and the
numbers of opening points and claimed values. -/
structure StatementShape (F : Type) {EF : Type} [FieldOps F] [TwoAdicOps F] (params : FriParams)
    (shape : ClaimShape) (points values : Array EF) : Prop where
  /-- There is a query. -/
  numQueries_ne : params.numQueries ≠ 0
  /-- Folding by two is allowed. -/
  maxLogArity_ne : params.maxLogArity ≠ 0
  /-- Some matrix is committed. -/
  flatten_ne : shape.flatten ≠ []
  /-- Every matrix is opened at a point. -/
  numPoints_ne : ∀ ms ∈ shape.flatten, ms.numPoints ≠ 0
  /-- No committed column is shorter than the final height. -/
  finalHeight_le : ∀ ms ∈ shape.flatten, params.logFinalHeight ≤ ms.logDegree + params.logBlowup
  /-- The first domain exists in the field. -/
  le_twoAdicity : logMaxHeight params.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F)
  /-- There is one opening point per opening point of the shape. -/
  size_points : points.size = (pointRefs params.logBlowup shape).length
  /-- There is one claimed value per claim of the shape. -/
  size_values : values.size = (claimRefs params.logBlowup shape).length

namespace HonestProver

/-! ## Arrays built by appending -/

section Push

variable {α : Type}

/-- A sequence of arrays that starts empty and grows by one entry at each step
has `j` entries at step `j`, and its entries do not change once written. -/
theorem push_seq {A : ℕ → Array α} (h0 : A 0 = #[]) (hs : ∀ i, ∃ x, A (i + 1) = (A i).push x) :
    (∀ j, (A j).size = j) ∧ ∀ i j, i ≤ j → ∀ k < i, (A j)[k]? = (A i)[k]? := by
  have hsize : ∀ j, (A j).size = j := by
    intro j
    induction j with
    | zero => rw [h0]; rfl
    | succ j ih =>
      obtain ⟨x, hx⟩ := hs j
      rw [hx, Array.size_push, ih]
  refine ⟨hsize, fun i j hij k hk => ?_⟩
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    obtain ⟨x, hx⟩ := hs j
    rw [hx, Array.getElem?_push, hsize j, ite_eq_right (by omega), ih]

end Push

/-! ## The polynomials of the prover depend on the earlier challenges only -/

section Word

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (w : Committed F K) (points values : Array EF)

/-- `honestWord` of level `i` depends on the folding challenges of the rounds
before `i` only. -/
theorem honestWord_congr (α : K) {β β' : ℕ → K} {i : ℕ} (h : ∀ r < i, β r = β' r) :
    honestWord m params shape wf w points values α β i =
      honestWord m params shape wf w points values α β' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change foldPoly (β i) (honestWord m params shape wf w points values α β i) +
        C (β i ^ 2) * inputPoly m params shape wf w points values α (i + 1) =
      foldPoly (β' i) (honestWord m params shape wf w points values α β' i) +
        C (β' i ^ 2) * inputPoly m params shape wf w points values α (i + 1)
    rw [ih fun r hr => h r (Nat.lt_succ_of_lt hr), h i (Nat.lt_succ_self i)]

/-- The polynomial the prover commits to in round `i`, given the batching
challenge and the folding challenges it holds: `honestWord` of level `i` for
these challenges, read in `K`. -/
noncomputable def word (alpha : EF) (betas : Array EF) (i : ℕ) : K[X] :=
  honestWord m params shape wf w points values (m.ext.toModel alpha)
    (fun r => m.ext.toModel (betas.getD r 0)) i

/-- The word of round `i` is the same for two arrays of folding challenges that
agree before `i`. -/
theorem word_congr (alpha : EF) {betas betas' : Array EF} {i : ℕ}
    (h : ∀ r < i, betas[r]? = betas'[r]?) :
    word m params shape wf w points values alpha betas i =
      word m params shape wf w points values alpha betas' i :=
  honestWord_congr m params shape wf w points values _ fun r hr => by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, h r hr]

end Word

/-! ## The matrices the prover commits to -/

section Matrices

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]

/-- The matrices of input batch `b`, as committed: the matrix at position `mi`
has the dimensions the shape gives it, after the blowup, and the rows of `w`. -/
def inputMatrices (params : FriParams) (shape : ClaimShape) (w : Committed F K) (b : ℕ) :
    List (Merkle.Matrix F) :=
  (shape.getD b []).zipIdx.map fun x =>
    { logHeight := x.1.logDegree + params.logBlowup, width := x.1.width, row := w.row b x.2 }

variable (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- The matrix of a folding round, for the polynomial `G` of level `i`: width
two and log-height `n - i - 1`. Row `p` holds representations of the values of
`G` at the points of the indices `2 * p` and `2 * p + 1` of level `i`. -/
noncomputable def roundMatrix (G : K[X]) (i : ℕ) : Merkle.Matrix EF where
  logHeight := logMaxHeight params.logBlowup shape - i - 1
  width := 2
  row p :=
    #[rep m (G.eval (pointOfIndex (modelParams m params shape wf).ω
        (modelParams m params shape wf).n (logMaxHeight params.logBlowup shape - i) (2 * p))),
      rep m (G.eval (pointOfIndex (modelParams m params shape wf).ω
        (modelParams m params shape wf).n (logMaxHeight params.logBlowup shape - i) (2 * p + 1)))]

end Matrices

/-! ## The folding rounds -/

/-- What the prover holds after some folding rounds. -/
structure Run (σ F EF D : Type) where
  /-- The state of the challenger. -/
  state : σ
  /-- The commitments of the rounds so far. -/
  commits : Array D
  /-- The proof-of-work witnesses of the rounds so far. -/
  witnesses : Array F
  /-- The folding challenges of the rounds so far. -/
  betas : Array EF
  /-- Whether every witness so far passed its check. -/
  powOk : Bool

section Rounds

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hFri : MerkleHasher EF D) (chal : Challenger σ F EF D)
  (w : Committed F K) (points values : Array EF) (grind : σ → ℕ → F)

/-- The commitment of round `i`, given the challenges the prover holds: the
Merkle root of the matrix of the word of the round. -/
noncomputable def roundCommit (alpha : EF) (betas : Array EF) (i : ℕ) : D :=
  Merkle.root hFri
    [roundMatrix m params shape wf (word m params shape wf w points values alpha betas i) i]

/-- Round `i` of the prover: commit to the word of the round, absorb the
commitment, search a witness, run the proof-of-work check, squeeze the folding
challenge. -/
noncomputable def step (alpha : EF) (i : ℕ) (r : Run σ F EF D) : Run σ F EF D :=
  let commit := roundCommit m params shape wf hFri w points values alpha r.betas i
  let s := chal.observe r.state (.digest commit)
  let witness := grind s params.commitPowBits
  let pow := chal.checkWitness s params.commitPowBits witness
  let beta := chal.sampleExt pow.2
  { state := beta.2
    commits := r.commits.push commit
    witnesses := r.witnesses.push witness
    betas := r.betas.push beta.1
    powOk := r.powOk && pow.1 }

/-- The prover after `i` folding rounds, started with the batching challenge
`alpha` and the challenger in state `s`. -/
noncomputable def run (alpha : EF) (s : σ) : ℕ → Run σ F EF D
  | 0 => { state := s, commits := #[], witnesses := #[], betas := #[], powOk := true }
  | i + 1 => step m params shape wf hFri chal w points values grind alpha i
      (run alpha s i)

/-- After `i` rounds the prover holds `i` commitments. -/
theorem size_commits (alpha : EF) (s : σ) (i : ℕ) :
    (run m params shape wf hFri chal w points values grind alpha s i).commits.size = i :=
  (push_seq (A := fun i => (run m params shape wf hFri chal w points values grind alpha s
    i).commits) rfl fun _ => ⟨_, rfl⟩).1 i

/-- After `i` rounds the prover holds `i` witnesses. -/
theorem size_witnesses (alpha : EF) (s : σ) (i : ℕ) :
    (run m params shape wf hFri chal w points values grind alpha s i).witnesses.size = i :=
  (push_seq (A := fun i => (run m params shape wf hFri chal w points values grind alpha s
    i).witnesses) rfl fun _ => ⟨_, rfl⟩).1 i

/-- The folding challenges of the rounds before `i` do not change after round
`i`. -/
theorem getElem?_betas (alpha : EF) (s : σ) {i j : ℕ} (hij : i ≤ j) {k : ℕ} (hk : k < i) :
    (run m params shape wf hFri chal w points values grind alpha s j).betas[k]? =
      (run m params shape wf hFri chal w points values grind alpha s i).betas[k]? :=
  (push_seq (A := fun i => (run m params shape wf hFri chal w points values grind alpha s
    i).betas) rfl fun _ => ⟨_, rfl⟩).2 i j hij k hk

/-- The word of round `i` for the challenges the prover holds after a later
round is the word it committed to in round `i`. -/
theorem word_run (alpha : EF) (s : σ) {i j : ℕ} (hij : i ≤ j) :
    word m params shape wf w points values alpha
        (run m params shape wf hFri chal w points values grind alpha s j).betas i =
      word m params shape wf w points values alpha
        (run m params shape wf hFri chal w points values grind alpha s i).betas i :=
  word_congr m params shape wf w points values alpha fun _ hr =>
    getElem?_betas m params shape wf hFri chal w points values grind alpha s hij hr

/-- The commitment of round `i`, in the array of commitments the prover holds
after a later round. -/
theorem getElem?_commits (alpha : EF) (s : σ) {i j : ℕ} (hij : i < j) :
    (run m params shape wf hFri chal w points values grind alpha s j).commits[i]? =
      some (roundCommit m params shape wf hFri w points values alpha
        (run m params shape wf hFri chal w points values grind alpha s i).betas i) := by
  rw [(push_seq (A := fun i => (run m params shape wf hFri chal w points values grind alpha s
    i).commits) rfl fun _ => ⟨_, rfl⟩).2 (i + 1) j hij i (Nat.lt_succ_self i)]
  change (Array.push _ _)[i]? = _
  rw [Array.getElem?_push, size_commits, ite_eq_left rfl]

/-- The witness of round `i`, in the array of witnesses the prover holds after
a later round: the one the search returns for the state after the commitment of
the round is absorbed. -/
theorem getElem?_witnesses (alpha : EF) (s : σ) {i j : ℕ} (hij : i < j) :
    (run m params shape wf hFri chal w points values grind alpha s j).witnesses[i]? =
      some (grind (chal.observe
        (run m params shape wf hFri chal w points values grind alpha s i).state
        (.digest (roundCommit m params shape wf hFri w points values alpha
          (run m params shape wf hFri chal w points values grind alpha s i).betas i)))
        params.commitPowBits) := by
  rw [(push_seq (A := fun i => (run m params shape wf hFri chal w points values grind alpha s
    i).witnesses) rfl fun _ => ⟨_, rfl⟩).2 (i + 1) j hij i (Nat.lt_succ_self i)]
  change (Array.push _ _)[i]? = _
  rw [Array.getElem?_push, size_witnesses, ite_eq_left rfl]

/-- **The verifier's commit phase follows the prover.** On the commitments and
the witnesses the prover holds after `j` rounds, the commit phase of the
verifier's transcript, run for `i ≤ j` rounds from the state the prover started
in, returns the folding challenges of the prover's first `i` rounds, whether
the witnesses of these rounds passed, and the prover's state after them. -/
theorem commitPhase_run [Inhabited D] (alpha : EF) (s : σ) (j : ℕ) :
    ∀ i ≤ j, commitPhase chal params.commitPowBits
        (run m params shape wf hFri chal w points values grind alpha s j).commits
        (run m params shape wf hFri chal w points values grind alpha s j).witnesses i s =
      ((run m params shape wf hFri chal w points values grind alpha s i).betas,
        (run m params shape wf hFri chal w points values grind alpha s i).powOk,
        (run m params shape wf hFri chal w points values grind alpha s i).state)
  | 0, _ => rfl
  | i + 1, hi => by
    rw [commitPhase, commitPhase_run alpha s j i (Nat.le_of_succ_le hi),
      Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      getElem?_commits m params shape wf hFri chal w points values grind alpha s hi,
      getElem?_witnesses m params shape wf hFri chal w points values grind alpha s hi]
    rfl

end Rounds

end HonestProver

/-! ## The prover -/

section Prover

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hIn : MerkleHasher F D) (hFri : MerkleHasher EF D)
  (chal : Challenger σ F EF D) (init : σ) (w : Committed F K) (points values : Array EF)
  (grind : σ → ℕ → F)

/-- **The commitments of the honest prover**: for each batch of the shape, the
root of the Merkle tree over the matrices of the batch, whose rows are the rows
of the committed data `w`. -/
def honestCommitments : Array D :=
  Array.ofFn (n := shape.length) fun b =>
    Merkle.root hIn (HonestProver.inputMatrices params shape w b.val)

namespace HonestProver

/-- The batching challenge of the prover, and the state of the challenger after
it: the prover absorbs its commitments, the opening points and the claimed
values, and squeezes. -/
def batching : EF × σ :=
  chal.sampleExt (chal.observeAll init
    (firstMessage (honestCommitments params shape hIn w) points values))

/-- The prover after the last folding round. -/
noncomputable def commitRun : Run σ F EF D :=
  run m params shape wf hFri chal w points values grind
    (batching params shape hIn chal init w points values).1
    (batching params shape hIn chal init w points values).2 (numRounds params shape)

/-- The final polynomial of the prover: representations of the coefficients of
the word after the last round. -/
noncomputable def finalPoly : Array EF :=
  Array.ofFn (n := params.finalPolyLen) fun k =>
    rep m ((word m params shape wf w points values
      (batching params shape hIn chal init w points values).1
      (commitRun m params shape wf hIn hFri chal init w points values grind).betas
      (numRounds params shape)).coeff k.val)

/-- The state of the challenger after the prover absorbs the final polynomial
and the arities of the rounds. -/
noncomputable def queryState : σ :=
  chal.observeAll (commitRun m params shape wf hIn hFri chal init w points values grind).state
    (finalMessage (numRounds params shape)
      (finalPoly m params shape wf hIn hFri chal init w points values grind))

/-- The witness the search returns before the query indices. -/
noncomputable def queryWitness : F :=
  grind (queryState m params shape wf hIn hFri chal init w points values grind)
    params.queryPowBits

/-- The last proof-of-work check of the prover: whether the witness passes, and
the state of the challenger after the check. -/
noncomputable def queryPow : Bool × σ :=
  chal.checkWitness (queryState m params shape wf hIn hFri chal init w points values grind)
    params.queryPowBits (queryWitness m params shape wf hIn hFri chal init w points values grind)

end HonestProver

/-- **The challenges of the honest prover**: the batching challenge and the
folding challenges it squeezed, whether every witness its search returned
passed the proof-of-work check, and the query indices it squeezed. -/
noncomputable def honestChallenges : Challenges EF where
  alpha := (HonestProver.batching params shape hIn chal init w points values).1
  betas := (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).betas
  powOk :=
    (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).powOk &&
      (HonestProver.queryPow m params shape wf hIn hFri chal init w points values grind).1
  indices := (chal.sampleIndices (logMaxHeight params.logBlowup shape) params.numQueries
    (HonestProver.queryPow m params shape wf hIn hFri chal init w points values grind).2).toArray

namespace HonestProver

/-- The opening of input batch `b` at the query indices `indices`: for each
query, the rows and the path of the Merkle tree of the batch at the index of
the query, shifted to the tallest matrix of the batch. -/
def inputOpening (indices : Array ℕ) (b : ℕ) : BatchOpening F (Array (List D)) where
  openedValues :=
    (Array.ofFn (n := params.numQueries) fun t =>
      indices.getD t.val 0 >>> (logMaxHeight params.logBlowup shape -
        Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList)).map
      (Merkle.rowsAt (inputMatrices params shape w b))
  openingProof :=
    (Array.ofFn (n := params.numQueries) fun t =>
      indices.getD t.val 0 >>> (logMaxHeight params.logBlowup shape -
        Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList)).map
      (Merkle.pathAt hIn (inputMatrices params shape w b))

/-- The opening of folding round `i` for the challenges `ch`: for each query,
a representation of the value of the word of the round at the other point of
the query's pair, and the path of the Merkle tree of the round at the row of
the pair. -/
noncomputable def roundOpening (ch : Challenges EF) (i : ℕ) :
    CommitPhaseStep EF (Array (List D)) where
  logArity := 1
  siblingValues := Array.ofFn (n := params.numQueries) fun t =>
    #[rep m ((word m params shape wf w points values ch.alpha ch.betas i).eval
      (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
        (logMaxHeight params.logBlowup shape - i) ((ch.indices.getD t.val 0 >>> i) ^^^ 1)))]
  openingProof :=
    (Array.ofFn (n := params.numQueries) fun t => ch.indices.getD t.val 0 >>> (i + 1)).map
      (Merkle.pathAt hFri
        [roundMatrix m params shape wf (word m params shape wf w points values ch.alpha ch.betas i)
          i])

end HonestProver

/-- **The proof of the honest prover.** The commitments and the witnesses of
the folding rounds, the openings of the input batches and of the rounds at the
query indices, the final polynomial, and the last witness. -/
noncomputable def honestProof : FriProof F EF D (Array (List D)) (Array (List D)) where
  commitPhaseCommits :=
    (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).commits
  commitPowWitnesses :=
    (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).witnesses
  inputOpenings := Array.ofFn (n := shape.length) fun b =>
    HonestProver.inputOpening params shape hIn w
      (honestChallenges m params shape wf hIn hFri chal init w points values grind).indices b.val
  commitPhaseOpenings := Array.ofFn (n := numRounds params shape) fun i =>
    HonestProver.roundOpening m params shape wf hFri w points values
      (honestChallenges m params shape wf hIn hFri chal init w points values grind) i.val
  finalPoly := HonestProver.finalPoly m params shape wf hIn hFri chal init w points values grind
  queryPowWitness :=
    HonestProver.queryWitness m params shape wf hIn hFri chal init w points values grind

/-- **The verifier derives, from the honest proof, the challenges the prover
used.** The transcript of the verifier on the honest commitments and the honest
proof is `honestChallenges`: the same batching challenge, folding challenges
and query indices, and its proof-of-work checks pass exactly when the witnesses
of the prover's search did. This holds for every challenger, every pair of hash
functions and every witness search. -/
theorem transcript_honestProof [Inhabited D] :
    transcript chal init params shape (honestCommitments params shape hIn w) points values
        (honestProof m params shape wf hIn hFri chal init w points values grind) =
      honestChallenges m params shape wf hIn hFri chal init w points values grind := by
  have h : commitPhase chal params.commitPowBits
      (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).commits
      (HonestProver.commitRun m params shape wf hIn hFri chal init w points values
        grind).witnesses (numRounds params shape)
      (chal.sampleExt (chal.observeAll init
        (firstMessage (honestCommitments params shape hIn w) points values))).2 =
      ((HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).betas,
        (HonestProver.commitRun m params shape wf hIn hFri chal init w points values grind).powOk,
        (HonestProver.commitRun m params shape wf hIn hFri chal init w points values
          grind).state) :=
    HonestProver.commitPhase_run m params shape wf hFri chal w points values grind
      (HonestProver.batching params shape hIn chal init w points values).1
      (HonestProver.batching params shape hIn chal init w points values).2 (numRounds params shape)
      (numRounds params shape) le_rfl
  unfold transcript transcriptTail
  simp only [honestProof, h]
  rfl

end Prover

end CertiFri.Exec
