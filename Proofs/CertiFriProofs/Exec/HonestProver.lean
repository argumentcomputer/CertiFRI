import CertiFriProofs.Exec.HonestProver.Fields
import CertiFriProofs.Exec.Completeness

/-!
# Completeness, with the prover

`Exec.completeness` says that `Fri.verify` accepts every proof that satisfies
`HonestProof`, a specification in terms of the challenges the verifier derives
from the proof. This file shows that such a proof exists: the proof of the
honest prover of `Exec/HonestProver/Prover.lean`, which commits to each round
after deriving the challenges of the rounds before it.

* `honestProof_honest`: the honest prover's proof satisfies `HonestProof`.
* `completeness_honestProver`: for an honest statement, `Fri.verify` accepts
  the honest prover's commitments and proof.
* `completeness_honestProver_of_grind`: the same, when the witness search
  succeeds in every state.
* `honestChallenges_powOk_of_grind`, `honestChallenges_powOk_of_bits_eq_zero`:
  the witnesses of the prover pass when the search succeeds in every state,
  and when there is no proof of work.

The prover is a mathematical function, not a program: nothing here certifies a
prover implementation.

## What is assumed

* `FieldModel` and `WellFormed`, as everywhere in `Exec/`.
* `HonestStatement`: behind the commitments are polynomials of the allowed
  degree, the rows of `w` are their evaluations, the claimed values are their
  values at the opening points, and no opening point lies on the coset of its
  matrix.
* `StatementShape`: the parameters, the shape and the numbers of opening
  points and claimed values are ones `Fri.shapeOk` accepts.
* `hbatch`: every batch of the shape has a matrix. The Merkle check rejects an
  opening of an empty batch.
* `hwidth`: every row of `w` that is committed has the width of its matrix.
* `hbits`: the challenger samples integers below `2 ^ bits`, as its interface
  says.
* `hpow`: every witness the search returned in the prover's run passed its
  proof-of-work check (`honestChallenges … .powOk`). A witness is found by
  search and need not exist; with no proof of work this holds for every search.
* For `completeness_honestProver` only: every element of `K` has one
  representation in the executable extension field
  (`Function.Injective m.ext.toModel`), as in `Exec.completeness`.

The hash functions and the challenger are otherwise arbitrary, and no random
oracle is involved.

## Not covered

Zero-knowledge; a prover program; Plonky3's pruned Merkle proofs; the hash
functions and the challenger of `CertiFriP3`.
-/

namespace CertiFri.Exec

open Fri

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) (hIn : MerkleHasher F D) (hFri : MerkleHasher EF D)
  (chal : Challenger σ F EF D) (init : σ) (w : Committed F K) (points values : Array EF)
  (grind : σ → ℕ → F)

namespace HonestProver

omit [DecidableEq D] [Inhabited D] in
/-- The commitment of round `i` in the honest proof is the root of the tree
over the matrix of the word of the round, for the challenges of the prover. -/
theorem getElem?_commitPhaseCommits {i : ℕ} (hi : i < numRounds params shape) :
    (honestProof m params shape wf hIn hFri chal init w points values
        grind).commitPhaseCommits[i]? =
      some (roundCommit m params shape wf hFri w points values
        (honestChallenges m params shape wf hIn hFri chal init w points values grind).alpha
        (honestChallenges m params shape wf hIn hFri chal init w points values grind).betas i) := by
  have hword := word_run m params shape wf hFri chal w points values grind
    (batching params shape hIn chal init w points values).1
    (batching params shape hIn chal init w points values).2 hi.le
  refine (getElem?_commits m params shape wf hFri chal w points values grind
    (batching params shape hIn chal init w points values).1
    (batching params shape hIn chal init w points values).2 hi).trans (congrArg some ?_)
  unfold roundCommit
  rw [← hword]
  rfl

omit [DecidableEq D] [Inhabited D] in
/-- The query indices of the prover are indices of the first domain, when the
challenger samples integers in range. -/
theorem getD_indices_lt (hbits : ∀ s bits, (chal.sampleBits s bits).1 < 2 ^ bits) (t : ℕ) :
    (honestChallenges m params shape wf hIn hFri chal init w points values grind).indices.getD
        t 0 < 2 ^ logMaxHeight params.logBlowup shape :=
  getD_lt (fun x hx => sampleIndices_lt hbits _ _ _ x (List.mem_toArray.mp hx)) t

omit [DecidableEq D] [Inhabited D] in
/-- If the search finds a passing witness in every state, for the difficulty
of the folding rounds and for that of the queries, every witness of the prover
passes. -/
theorem powOk_of_checks
    (hcommit : ∀ s,
      (chal.checkWitness s params.commitPowBits (grind s params.commitPowBits)).1 = true)
    (hquery : ∀ s,
      (chal.checkWitness s params.queryPowBits (grind s params.queryPowBits)).1 = true) :
    (honestChallenges m params shape wf hIn hFri chal init w points values grind).powOk =
      true := by
  change ((commitRun m params shape wf hIn hFri chal init w points values grind).powOk &&
    (chal.checkWitness _ params.queryPowBits (grind _ params.queryPowBits)).1) = true
  rw [hquery, Bool.and_true]
  exact powOk_run m params shape wf hFri w points values hcommit _ _ _

end HonestProver

variable {hIn hFri chal init w points values grind}

omit [DecidableEq D] [Inhabited D] in
/-- **The witnesses of the prover pass when the search succeeds.** If in every
state and for every difficulty the search returns a witness that passes the
proof-of-work check, every witness of the honest prover passes. -/
theorem honestChallenges_powOk_of_grind
    (hgrind : ∀ s bits, (chal.checkWitness s bits (grind s bits)).1 = true) :
    (honestChallenges m params shape wf hIn hFri chal init w points values grind).powOk = true :=
  HonestProver.powOk_of_checks m params shape wf hIn hFri chal init w points values grind
    (fun s => hgrind s _) (fun s => hgrind s _)

omit [DecidableEq D] [Inhabited D] in
/-- **Without proof of work, the witnesses of the prover pass** on any valid
challenger, whatever the search returns. -/
theorem honestChallenges_powOk_of_bits_eq_zero (hcommit : params.commitPowBits = 0)
    (hquery : params.queryPowBits = 0) (hok : ∀ s, chal.ok s = true) :
    (honestChallenges m params shape wf hIn hFri chal init w points values grind).powOk = true :=
  HonestProver.powOk_of_checks m params shape wf hIn hFri chal init w points values grind
    (fun s => by rw [hcommit]; exact HonestProver.checkWitness_zero chal s _ (hok s))
    (fun s => by rw [hquery]; exact HonestProver.checkWitness_zero chal s _ (hok s))

open HonestProver in
/-- **The honest prover's proof follows the protocol.**

Let the statement be honest for the committed data `w` and have the shape the
verifier requires, let every batch have a matrix and the committed rows of `w`
the widths of their matrices, let the challenger sample integers in range, and
let every witness the prover's search returned pass its check. Then the proof
of the honest prover satisfies `HonestProof` for the commitments of the honest
prover, with the hash functions and the challenger the prover ran. -/
theorem honestProof_honest (hst : HonestStatement m params shape wf w points values)
    (hshape : StatementShape F params shape points values)
    (hbatch : ∀ mats ∈ shape, mats ≠ [])
    (hwidth : ∀ (b mi : ℕ) (mats : List MatrixShape) (ms : MatrixShape),
      shape[b]? = some mats → mats[mi]? = some ms →
        ∀ i < 2 ^ (ms.logDegree + params.logBlowup), (w.row b mi i).size = ms.width)
    (hbits : ∀ s bits, (chal.sampleBits s bits).1 < 2 ^ bits)
    (hpow : (honestChallenges m params shape wf hIn hFri chal init w points values
      grind).powOk = true) :
    HonestProof m params shape wf hIn hFri chal init w (honestCommitments params shape hIn w)
      points values (honestProof m params shape wf hIn hFri chal init w points values grind) := by
  have hidx := getD_indices_lt m params shape wf hIn hFri chal init w points values grind hbits
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine shapeOk_of_sizes hshape Array.size_ofFn
      (size_commits m params shape wf hFri chal w points values grind _ _ _)
      (size_witnesses m params shape wf hFri chal w points values grind _ _ _)
      Array.size_ofFn (fun o ho => ?_) Array.size_ofFn Array.size_ofFn (fun b hb => ?_)
    · obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp ho
      exact shape_roundOpening m params shape wf hFri w points values _ i.val
    · refine ⟨_, ?_, shape_inputOpening params shape hIn w
        (honestChallenges m params shape wf hIn hFri chal init w points values grind).indices b⟩
      simp [honestProof, hb]
  · rw [transcript_honestProof]
    exact hpow
  · rw [transcript_honestProof]
    exact fun t _ => hidx t
  · rw [transcript_honestProof]
    intro b hb
    exact ⟨_, _, by simp [honestCommitments, hb], by simp [honestProof, hb],
      verifyOpenings_inputOpening hIn hbatch hwidth hidx hb⟩
  · rw [transcript_honestProof]
    exact fun c hc t ht => openedEntry_inputOpening rfl hc ht
  · rw [transcript_honestProof]
    intro i hi
    exact ⟨_, _, getElem?_commitPhaseCommits m params shape wf hIn hFri chal init w points values
        grind hi, by simp [honestProof, hi],
      verifyOpenings_roundOpening m params shape wf hFri w points values _
        (lt_of_lt_of_le hi (Nat.sub_le _ _)) hidx⟩
  · rw [transcript_honestProof]
    intro i hi t ht
    rw [sibling_roundOpening rfl hi ht, toModel_rep]
    rfl
  · rw [transcript_honestProof]
    exact polyOfCoeffs_rep m (degree_word_lt m params shape wf hst _ _)

/-- **Completeness, with the prover.** For every honest statement, the honest
prover's proof is accepted.

Let the executable fields implement a field with one representation per
element. If the statement is honest for the committed data `w`
(`HonestStatement`) and has the shape the verifier requires (`StatementShape`),
every batch has a matrix, the committed rows of `w` have the widths of their
matrices, the challenger samples integers in range, and every witness the
prover's search returned passes its check, then `Fri.verify`, with the Merkle
commitment schemes over `hIn` and `hFri` and the challenger `chal` started at
`init`, accepts the commitments and the proof of the honest prover. The hash
functions and the challenger are otherwise arbitrary. -/
theorem completeness_honestProver (hinj : Function.Injective m.ext.toModel)
    (hst : HonestStatement m params shape wf w points values)
    (hshape : StatementShape F params shape points values)
    (hbatch : ∀ mats ∈ shape, mats ≠ [])
    (hwidth : ∀ (b mi : ℕ) (mats : List MatrixShape) (ms : MatrixShape),
      shape[b]? = some mats → mats[mi]? = some ms →
        ∀ i < 2 ^ (ms.logDegree + params.logBlowup), (w.row b mi i).size = ms.width)
    (hbits : ∀ s bits, (chal.sampleBits s bits).1 < 2 ^ bits)
    (hpow : (honestChallenges m params shape wf hIn hFri chal init w points values
      grind).powOk = true) :
    Fri.verify (merkleMmcs hIn) (merkleMmcs hFri) chal init params shape
      (honestCommitments params shape hIn w) points values
      (honestProof m params shape wf hIn hFri chal init w points values grind) = true :=
  completeness m params shape wf hinj hst
    (honestProof_honest m params shape wf hst hshape hbatch hwidth hbits hpow)

/-- **Completeness, with a prover whose witness search succeeds.** The
hypotheses of `completeness_honestProver`, with the last one replaced: in every
state and for every difficulty, the search returns a witness that passes the
proof-of-work check. Then `Fri.verify` accepts the commitments and the proof of
the honest prover. -/
theorem completeness_honestProver_of_grind (hinj : Function.Injective m.ext.toModel)
    (hst : HonestStatement m params shape wf w points values)
    (hshape : StatementShape F params shape points values)
    (hbatch : ∀ mats ∈ shape, mats ≠ [])
    (hwidth : ∀ (b mi : ℕ) (mats : List MatrixShape) (ms : MatrixShape),
      shape[b]? = some mats → mats[mi]? = some ms →
        ∀ i < 2 ^ (ms.logDegree + params.logBlowup), (w.row b mi i).size = ms.width)
    (hbits : ∀ s bits, (chal.sampleBits s bits).1 < 2 ^ bits)
    (hgrind : ∀ s bits, (chal.checkWitness s bits (grind s bits)).1 = true) :
    Fri.verify (merkleMmcs hIn) (merkleMmcs hFri) chal init params shape
      (honestCommitments params shape hIn w) points values
      (honestProof m params shape wf hIn hFri chal init w points values grind) = true :=
  completeness_honestProver m params shape wf hinj hst hshape hbatch hwidth hbits
    (honestChallenges_powOk_of_grind m params shape wf hgrind)

end CertiFri.Exec
