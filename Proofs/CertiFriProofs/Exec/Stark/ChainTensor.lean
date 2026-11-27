import CertiFriProofs.Exec.Stark.GoodLogTensor
import CertiFriProofs.Exec.Stark.RunTensor
import CertiFriProofs.Exec.Stark.Chain
import CertiFriProofs.Theory.Oracle.Adaptive
import CertiFriProofs.Theory.Compiled.AcceptsComTensor

/-!
# The Fiat–Shamir chain and verifier queries of one tensor-batched STARK shard

Tensor-batched counterpart of `Exec/Stark/Chain.lean`. Derives the adaptive
Fiat–Shamir chain of one shard over `UTensorChal`, then executes
`Compiled.Params.verifyWithTensor` on the derived tensor schedule, folding
challenges, and query indices (with identical query bound `shardQueries sys n`).
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-- The primary field challenge of the last round of a tensor STARK transcript. -/
def tLastField {Msg : Type} : {i : ℕ} → Transcript Msg (UTensorChal K fslots slots width) i → K
  | _, .nil => 0
  | _, .snoc _ _ c => c.field

section ChainTensor

variable (M : StarkModel F EF K) (sys : System F D)
  (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)

/-- Raw message of round `i` of a tensor-batched STARK shard chain. -/
noncomputable def nextMsgTensor :
    (i : ℕ) → Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) i → RawMsg F EF D
  | 0, _ => m0
  | 1, t => [.ext (rep M (tLastField t))]
  | 2, t => .ext (rep M (tLastField t)) :: (mid ++ secondMessage proof)
  | 3, _ => [.digest proof.quotientCommit]
  | 4, t => (claimValues (openingClaims sys proof (rep M (tLastField t)))).toList.map .ext
  | j + 5, _ => messages sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
      #[] #[] #[] proof.openingProof (j + 1)

/-- Read the 2D tensor batching schedule `(rCol, rOpen)` off a multi-slot answer `u`. -/
def tensorChalOfAns (W Mopen : ℕ) (u : UTensorAns K fslots slots width) :
    PcsRbr.TensorChal K W Mopen :=
  (fun b => u.fieldAt b.val, fun b => u.fieldAt (tensorNumChallenges W + b.val))

/-- **The oracle queries of the verification of one tensor-batched shard:**
the challenge queries of its chain, then the Merkle hash queries of
`Compiled.Params.verifyWithTensor`. -/
noncomputable def shardCompTensor : OracleComp (STAns F EF D K fslots slots width) Bool :=
  if h : logMaxHeight sys.fri.logBlowup (starkShape sys M.extData.d proof.active proof.logDegrees)
      ≤ TwoAdicOps.twoAdicity (F := F) then
    let shape := starkShape sys M.extData.d proof.active proof.logDegrees
    let P := modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ h)
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
    (deriveA (fun _ : HashQuery K D => D) (nextMsgTensor M sys proof m0 mid)
      (4 + (P.rounds + 2))).bind fun t =>
      P.verifyWithTensor W Mopen (tensorCoord sys.fri shape)
        (modelProof M.toFieldModel sys.fri shape proof.openingProof)
        (fun j => view M.toFieldModel sys.fri shape
          (messages sys.fri shape
            ((openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))).map (·.commitment))
            (claimPoints (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
            (claimValues (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
            proof.openingProof j))
        (tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4))
        (fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0)
        (fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
          (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n)
  else .pure false

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] in
private theorem length_starkShape_leT (d : ℕ) (active : Array Bool) (logDegrees : Array ℕ) :
    (starkShape sys d active logDegrees).length ≤ 4 := by
  unfold starkShape
  cases sys.preprocessedCommit <;> exact Nat.le_of_ble_eq_true rfl

omit [DecidableEq F] [DecidableEq EF] in
/-- The tensor-batched verification of a shard makes at most `shardQueries sys n` queries. -/
theorem queryBound_shardCompTensor {n : ℕ}
    (hn : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ n) :
    (shardCompTensor (fslots := fslots) (slots := slots) (width := width) M sys proof m0 mid).QueryBound
      (shardQueries sys n) := by
  unfold shardCompTensor
  split
  · next h =>
    dsimp only
    have hrounds := (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ h)).rounds_le
    have hbatches := length_starkShape_leT sys M.extData.d proof.active proof.logDegrees
    refine QueryBound.mono ((queryBound_deriveA _ _).bind fun t =>
      Compiled.Params.queryBound_verifyWithTensor _ _ _ _ _ _ _ _ _) ?_
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_right (hrounds.trans hn) 2) 4)
      (Nat.mul_le_mul (Nat.add_le_add hbatches (hrounds.trans hn))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 1)))
  · exact queryBound_pure _ _

end ChainTensor

end CertiFri.Exec.Stark
