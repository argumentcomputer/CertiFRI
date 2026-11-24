import CertiFriProofs.Exec.Stark.GoodLog
import CertiFriProofs.Exec.Stark.Run
import CertiFriProofs.Theory.Oracle.Adaptive
import CertiFriProofs.Theory.Compiled.AcceptsCom

/-!
# The chain of one proof

The queries the verification of one proof (one shard of a batch) makes to the
random oracle of the STARK experiment: the challenge queries along its
Fiat–Shamir chain, and the hash queries of the Merkle checks of its opening
proof.

## Contents

* `lastField`: the field challenge of the last round of a transcript.
* `nextMsg M sys proof m0 mid i t`: the raw message of round `i` of the chain
  of `proof`, given the transcript `t` of the rounds before it. `m0` is the
  first message and `mid` what the entry point absorbs between the second
  lookup challenge and the commitment to the lookup traces (nothing for
  `Stark.verify`, the position of the shard for `Stark.verifyBatch`). The
  messages of rounds `1`, `2` and `4` depend on the challenge before them: the
  lookup challenges are absorbed back, and the opening claims are made at the
  out-of-domain point.
* `shardComp M sys proof m0 mid`: the computation that makes the queries of the
  verification of `proof`: it derives the chain (`deriveA`), then runs the
  model verifier of the opening protocol (`Compiled.Params.verifyWith`) on the
  challenges of the chain. It returns the verdict of the model verifier. For a
  proof whose first domain does not exist in the field it makes no query.
* `queryBound_shardComp`: the number of queries it makes.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ}

/-- The field challenge of the last round of a transcript; zero for the empty
transcript. -/
def lastField {Msg : Type} : {i : ℕ} → Transcript Msg (UChal K slots width) i → K
  | _, .nil => 0
  | _, .snoc _ _ c => c.field

section Chain

variable (M : StarkModel F EF K) (sys : System F D)
  (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)

/-- The raw message of round `i` of the chain of a proof, given the transcript
of the rounds before it. -/
noncomputable def nextMsg :
    (i : ℕ) → Transcript (RawMsg F EF D) (UChal K slots width) i → RawMsg F EF D
  | 0, _ => m0
  | 1, t => [.ext (rep M (lastField t))]
  | 2, t => .ext (rep M (lastField t)) :: (mid ++ secondMessage proof)
  | 3, _ => [.digest proof.quotientCommit]
  | 4, t => (claimValues (openingClaims sys proof (rep M (lastField t)))).toList.map .ext
  | j + 5, _ => messages sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
      #[] #[] #[] proof.openingProof (j + 1)

/-- **The queries of the verification of one proof**: the challenge queries of
its chain, then the hash queries of the model verifier of the opening protocol
on the challenges of the chain. The result is the verdict of the model
verifier. -/
noncomputable def shardComp : OracleComp (SAns F EF D K slots width) Bool :=
  if h : logMaxHeight sys.fri.logBlowup (starkShape sys M.extData.d proof.active proof.logDegrees)
      ≤ TwoAdicOps.twoAdicity (F := F) then
    (deriveA (fun _ : HashQuery K D => D) (nextMsg M sys proof m0 mid)
      (4 + ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ h)).rounds + 2))).bind fun t =>
      (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ h)).verifyWith
        (modelProof M.toFieldModel sys.fri
          (starkShape sys M.extData.d proof.active proof.logDegrees) proof.openingProof)
        (fun j => view M.toFieldModel sys.fri
          (starkShape sys M.extData.d proof.active proof.logDegrees)
          (messages sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
            ((openingClaims sys proof (rep M (fieldAt (chalsOf t) 3))).map (·.commitment))
            (claimPoints (openingClaims sys proof (rep M (fieldAt (chalsOf t) 3))))
            (claimValues (openingClaims sys proof (rep M (fieldAt (chalsOf t) 3))))
            proof.openingProof j))
        (fieldAt (chalsOf t) 4)
        (fun i => if i < (modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d proof.active proof.logDegrees)
            (M.wellFormed sys.fri _ h)).rounds then fieldAt (chalsOf t) (5 + i) else 0)
        (fun k => (ansAt (chalsOf t) (5 + (modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d proof.active proof.logDegrees)
            (M.wellFormed sys.fri _ h)).rounds)).bits
          (k.val + if sys.fri.queryPowBits = 0 then 0 else 1)
          (modelParams M.toFieldModel sys.fri
            (starkShape sys M.extData.d proof.active proof.logDegrees)
            (M.wellFormed sys.fri _ h)).n)
  else .pure false

/-- A bound on the number of queries of the verification of a proof whose
matrices have log-height at most `n`: one per round of the chain, and the hash
queries of the model verifier. -/
def shardQueries (sys : System F D) (n : ℕ) : ℕ :=
  4 + (n + 2) + (4 + n) * (sys.fri.numQueries * (3 * n + 1))

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] in
/-- The opening claims of a proof are about at most four commitments. -/
private theorem length_starkShape_le (d : ℕ) (active : Array Bool) (logDegrees : Array ℕ) :
    (starkShape sys d active logDegrees).length ≤ 4 := by
  unfold starkShape
  cases sys.preprocessedCommit <;> exact Nat.le_of_ble_eq_true rfl

omit [DecidableEq F] [DecidableEq EF] in
/-- The verification of a proof makes at most `shardQueries sys n` queries,
when the first domain of its opening has log-size at most `n`. -/
theorem queryBound_shardComp {n : ℕ}
    (hn : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ n) :
    (shardComp (slots := slots) (width := width) M sys proof m0 mid).QueryBound
      (shardQueries sys n) := by
  unfold shardComp
  split
  · next h =>
    have hrounds := (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ h)).rounds_le
    have hbatches := length_starkShape_le sys M.extData.d proof.active proof.logDegrees
    refine QueryBound.mono ((queryBound_deriveA _ _).bind fun t =>
      Compiled.Params.queryBound_verifyWith _ _ _ _ _ _) ?_
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_right (hrounds.trans hn) 2) 4)
      (Nat.mul_le_mul (Nat.add_le_add hbatches (hrounds.trans hn))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 1)))
  · exact queryBound_pure _ _

end Chain

end CertiFri.Exec.Stark
