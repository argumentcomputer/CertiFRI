import CertiFriProofs.Exec.HonestArith
import CertiFriProofs.Exec.CompletenessChecks

/-!
# Completeness of the executable verifier

`Fri.verify` accepts every proof that follows the protocol.

`completeness`: if the statement is honest (`HonestStatement`) and the proof is
honest (`HonestProof`), both defined in `Exec/Honest.lean`, then `Fri.verify`
returns `true`, with the Merkle commitment schemes over any two hash functions
and with any challenger.

## What is assumed

* `FieldModel` and `WellFormed`, as for soundness, and that every element of the
  field has only one executable representation
  (`Function.Injective m.ext.toModel`). The verifier hashes the elements it
  computes; without this an honest prover and the verifier could hold two
  representations of one value, with different hashes.
* What `HonestStatement` and `HonestProof` say, including: no opening point
  lies on the coset its matrix is committed on (the verifier rejects a query
  that hits one); the proof-of-work checks pass (a witness is found by search
  and need not exist); the challenger returns indices of the first domain; the
  Merkle openings verify (for a tree built as in `Merkle/Tree.lean` they do:
  `Merkle.verifyOpenings_tree`).

No random oracle is involved: the hash functions and the challenger are
arbitrary.

## Not covered

* That an honest proof exists. `Exec/HonestProver.lean` constructs one, round
  by round, and proves it honest (`completeness_honestProver`).
* Completeness for Plonky3's pruned Merkle proofs, and for the hash functions
  and the challenger of `CertiFriP3` as such: the theorem holds for any, and
  nothing is proved about those. The fields of `CertiFriP3` are a `FieldModel`
  (`P3/GoldilocksModel.lean`).
-/

namespace CertiFri.Exec

open Fri

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- **Completeness.** An honest proof of an honest statement is accepted.

Let the executable fields implement a field with one representation per
element. If behind the commitments there are polynomials of the allowed degree
whose evaluations are the committed rows, the claimed values are their values
at the opening points, no opening point lies on the coset of its matrix
(`HonestStatement`), and the proof follows the protocol for the challenges the
verifier derives from it (`HonestProof`), then `Fri.verify` returns `true`.
The hash functions `hIn`, `hFri` and the challenger `chal` are arbitrary. -/
theorem completeness (hinj : Function.Injective m.ext.toModel)
    {hIn : MerkleHasher F D} {hFri : MerkleHasher EF D} {chal : Challenger σ F EF D} {init : σ}
    {w : Committed F K} {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))}
    (hst : HonestStatement m params shape wf w points values)
    (hpf : HonestProof m params shape wf hIn hFri chal init w commitments points values proof) :
    Fri.verify (merkleMmcs hIn) (merkleMmcs hFri) chal init params shape commitments points values
      proof = true :=
  verify_of_honest_aux m params shape wf hinj hst hpf
    (fun t _ hj => reduced_eq_eval_inputPoly m params shape wf hst hpf.shape_ok _ t
      (fun c hc => hpf.input_rows c hc t.val t.isLt) (hpf.index_lt t.val t.isLt) hj)
    (fun hlfp => inputPoly_numRounds_eq_zero m params shape wf hst hlfp _)
    (fun t => folded_eq_eval_honestWord m params shape wf hst hpf.shape_ok _ _ t
      (fun c hc => hpf.input_rows c hc t.val t.isLt) (hpf.index_lt t.val t.isLt) le_rfl
      (fun r hr => hpf.sibling_eval r hr t.val t.isLt))
    (fun t _ hi => commitRow_eq_eval_honestWord m params shape wf hst hpf.shape_ok _ _ t
      (fun c hc => hpf.input_rows c hc t.val t.isLt) (hpf.index_lt t.val t.isLt) hi
      (fun r hr => hpf.sibling_eval r (lt_of_le_of_lt hr hi) t.val t.isLt))

end CertiFri.Exec
