import CertiFriProofs.Exec.MultiArity.StarkState
import CertiFriProofs.Exec.Stark.PrunedTensor

/-!
# Soundness of multi-arity tensor-batched STARKs (unpruned `merkleMmcs` & Plonky3 `prunedMmcs`)

Extends `Exec/Stark/{RunTensor,ChainTensor,ShardGoodTensor,SoundnessTensor,PrunedTensor}.lean`
from binary folding (`logArity = 1`) to variable per-round multi-arity folding
(`CertiFri.Stark.verifyTensorMultiArity` and `CertiFri.Stark.verifyBatchTensorMultiArity`,
using `Fri.scheduleOfShape` covering `logArity ∈ {1, 2, 3, …}`, fold factors `2, 4, 8, …`).

## Main results

1. **Transcript & check refinement (`transcriptTailTensorMulti_ufreeTensor`,
   `checkAfterChallengesTensorMultiArity_ufreeTensor`,
   `modelChecksTensorMulti_of_verifyWithTensorMulti_exec`, `rows_queryResultTensorMulti`).**
2. **Deterministic multi-arity shard soundness (`shard_goodTensorMulti_of_derive_verify`,
   `shard_goodTensorMulti`, `shard_goodTensorMultiPruned`):**
   shared by both unpruned `merkleMmcs` and Plonky3's `CertiFri.P3.prunedMmcs`.
3. **Unconditional unique-decoding ROM soundness (unpruned `merkleMmcs`):**
   * `soundness_verifyTensorMultiArity_ud`
   * `soundness_verifyBatchTensorMultiArity_ud`
   * `soundness_verifyTensorMultiArity_lookups_ud`
   * `soundness_verifyBatchTensorMultiArity_lookups_ud`
4. **Unconditional unique-decoding ROM soundness (`CertiFri.P3.prunedMmcs`):**
   * `soundness_verifyTensorMultiArityPruned_ud`
   * `soundness_verifyBatchTensorMultiArityPruned_ud`
   * `soundness_verifyTensorMultiArityPruned_lookups_ud`
   * `soundness_verifyBatchTensorMultiArityPruned_lookups_ud`
-/

namespace CertiFri.Exec.Stark

open CertiFri CertiFri.P3 CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri
  CertiFri.Oracle CertiFri.Oracle.MerkleRO CertiFri.PcsRbr OracleComp Polynomial
open CertiFri.Exec.Transcript (answer)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-! ## 1. Multi-arity transcript and check refinement with `uChallengerTensor` -/

section RunTensorMulti

omit [TwoAdicOps F] [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- **The challenges of `Fri.transcriptTailTensorMulti` with `uChallengerTensor`.** -/
theorem transcriptTailTensorMulti_ufreeTensor
    (f : ∀ x : FSQuery (RawMsg F EF D) (UTensorChal K fslots slots width) (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (UTensorChal K fslots slots width) K D x)
    (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) (i₀ : ℕ)
    {ms : ℕ → RawMsg F EF D} {s : UStateTensor F EF D}
    (h : UAtTensor ms s i₀ (ms i₀) false 0 0)
    (hpos : 0 < tensorNumChallenges (maxWidth shape) +
      tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (hmC : ∀ i < arities.length,
      ms (i₀ + 1 + i) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]))
    (hmF : ms (i₀ + 1 + arities.length) =
      finalMessageMulti arities proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]))
    (hfinal : proof.finalPoly.size ≠ 0) :
    let ch := transcriptTailTensorMulti (uChallengerTensor f m) s params shape arities proof
    ch.schedule.colChallenges =
        ((List.range (tensorNumChallenges (maxWidth shape))).map fun k =>
          Function.surjInv m.surj ((answer f ms i₀).fieldAt k)).toArray ∧
      ch.schedule.openChallenges =
        ((List.range (tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape))).map fun k =>
          Function.surjInv m.surj ((answer f ms i₀).fieldAt
            (tensorNumChallenges (maxWidth shape) + k))).toArray ∧
      ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges (maxWidth shape) ∧
      ch.schedule.openWeights = tensorWeights ch.schedule.openChallenges
        (maxOpeningsPerHeight params.logBlowup shape) ∧
      ch.betas =
        ((List.range arities.length).map fun i =>
          Function.surjInv m.surj (answer f ms (i₀ + 1 + i)).field).toArray ∧
      (ch.powOk = true →
        (params.commitPowBits ≠ 0 → ∀ i < arities.length,
          (answer f ms (i₀ + 1 + i)).bits 0 params.commitPowBits = 0) ∧
        (params.queryPowBits ≠ 0 →
          (answer f ms (i₀ + 1 + arities.length)).bits 0 params.queryPowBits = 0)) ∧
      ch.indices =
        ((List.range params.numQueries).map fun t =>
          (answer f ms (i₀ + 1 + arities.length)).bits
            (t + if params.queryPowBits = 0 then 0 else 1)
            (logMaxHeight params.logBlowup shape)).toArray := by
  have e : i₀ + arities.length + 1 = i₀ + 1 + arities.length :=
    Nat.add_right_comm i₀ arities.length 1
  have hne : finalMessageMulti (F := F) (D := D) arities proof.finalPoly ≠ [] := by
    intro h0
    have hlen := congrArg List.length h0
    simp only [finalMessageMulti, List.length_append, List.length_map, Array.length_toList,
      List.length_nil] at hlen
    omega
  obtain ⟨hcol, hopen, hcolW, hopenW, h1⟩ :=
    tensorSchedule_ufreeTensor f m (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      i₀ hpos h
  obtain ⟨hβ, hpowC, nf, nb, h2⟩ := commitPhase_ufreeTensor f m params.commitPowBits
    proof.commitPhaseCommits proof.commitPowWitnesses arities.length i₀ hmC h1
  have h3 := h2.observeAll_next f m hne
  rw [e] at h3
  obtain ⟨hpowQ, h4⟩ := h3.checkWitness f m params.queryPowBits proof.queryPowWitness hmF
  have hidx := h4.sampleIndices f m (logMaxHeight params.logBlowup shape) params.numQueries
  refine ⟨hcol, hopen, hcolW, hopenW, hβ, fun hpow => ?_, ?_⟩
  · obtain ⟨hpow₁, hpow₂⟩ := Bool.and_eq_true_iff.mp hpow
    exact ⟨hpowC hpow₁, hpowQ hpow₂⟩
  · exact congrArg List.toArray
      (hidx.trans (List.map_congr_left fun t _ => by rw [Nat.add_comm _ t]))

omit [FieldOps EF] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem mem_claimValuesTM {claims : Array (CommitmentOpening EF D)}
    {c : CommitmentOpening EF D} {m : MatrixOpening EF} {po : PointOpening EF} {x : EF}
    (hc : c ∈ claims.toList) (hm : m ∈ c.matrices.toList) (hpo : po ∈ m.points.toList)
    (hx : x ∈ po.values.toList) : x ∈ (claimValues claims).toList := by
  simp only [claimValues, List.mem_flatMap]
  exact ⟨c, hc, m, hm, po, hpo, hx⟩

omit [FieldOps EF] [DecidableEq F] [DecidableEq EF] in
private theorem exists_value_matrixOpeningTM (k : ℕ) (ζ : EF) {rows : Array (Array EF)} {w : ℕ}
    (hw : 0 < w) (h : rowsOk rows 1 w = true) :
    ∃ po ∈ (matrixOpening k [ζ] rows).points.toList, ∃ x, x ∈ po.values.toList := by
  obtain ⟨rs⟩ := rows
  simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨hsize, hall⟩ := h
  cases rs with
  | nil => cases hsize
  | cons r rs =>
    have hr : r.size = w := hall r (Array.mem_toList_iff.mp List.mem_cons_self)
    exact ⟨⟨ζ, r⟩, List.mem_cons_self, r[0]'(by omega), Array.getElem_mem_toList _⟩

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem claimValues_openingClaims_ne_nilTM {InputProof CommitProof : Type}
    (sys : System F D) (proof : Proof F EF D InputProof CommitProof)
    (hshape : Stark.shapeOk sys proof = true) (hd : 0 < ExtensionOps.degree (F := F) (EF := EF))
    (ζ : EF) : (claimValues (openingClaims sys proof ζ)).toList ≠ [] := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hne⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := hshape
  cases hact : activeIndices proof.active with
  | nil => rw [hact] at hne; cases hne
  | cons ci rest =>
    have hp : (ci, 0) ∈ (activeIndices proof.active).zipIdx := by
      rw [hact, List.zipIdx_cons]; exact List.mem_cons_self
    obtain ⟨-, hq⟩ := hall (ci, 0) hp
    obtain ⟨po, hpo, x, hx⟩ := exists_value_matrixOpeningTM (proof.logDegrees.getD 0 0) ζ
      (Nat.mul_pos (Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)) hd) hq
    refine List.ne_nil_of_mem (mem_claimValuesTM
      (c := ⟨proof.quotientCommit, ((activeIndices proof.active).zipIdx.map fun p : ℕ × ℕ =>
        matrixOpening (proof.logDegrees.getD p.2 0) [ζ]
          (proof.quotientOpened.getD p.2 #[])).toArray⟩) ?_ ?_ hpo hx)
    · simp only [openingClaims, Array.toList_append]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_map.mpr ⟨(ci, 0), hp, rfl⟩

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- **The checks after the lookup challenges for `checkAfterChallengesTensorMultiArity`.** -/
theorem checkAfterChallengesTensorMultiArity_ufreeTensor (M : StarkModel F EF K)
    (f : ∀ x : FSQuery (RawMsg F EF D) (UTensorChal K fslots slots width) (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (UTensorChal K fslots slots width) K D x)
    (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (sys : System F D)
    (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof)
    (hshape : Stark.shapeOk sys proof = true) {ms : ℕ → RawMsg F EF D}
    {s : UStateTensor F EF D} {cur : RawMsg F EF D} (β γ acc : EF)
    (hs : UAtTensor ms s 2 cur false 0 0)
    (h2 : ms 2 = cur ++ secondMessage proof) (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map .ext)
    (hC : ∀ i < (scheduleOfShape sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field)))).length,
      ms (5 + i) = .digest (proof.openingProof.commitPhaseCommits.getD i default) ::
        (if sys.fri.commitPowBits = 0 then []
          else [.base (proof.openingProof.commitPowWitnesses.getD i 0)]))
    (hF : ms (5 + (scheduleOfShape sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field)))).length) =
      finalMessageMulti (scheduleOfShape sys.fri (claimShape (openingClaims sys proof
          (Function.surjInv M.surj (answer f ms 3).field)))) proof.openingProof.finalPoly ++
        (if sys.fri.queryPowBits = 0 then [] else [.base proof.openingProof.queryPowWitness]))
    (h : checkAfterChallengesTensorMultiArity inputMmcs friMmcs
      (uChallengerTensor f M.toFieldModel) sys proof s β γ acc = true) :
    let ζ := Function.surjInv M.surj (answer f ms 3).field
    let sh := claimShape (openingClaims sys proof ζ)
    let arities := scheduleOfShape sys.fri sh
    zetaOk proof ζ = true ∧
      constraintsOk sys proof β γ acc (Function.surjInv M.surj (answer f ms 2).field) ζ = true ∧
      widthsUniform (openingClaims sys proof ζ) = true ∧
      Fri.shapeOkMultiArity arities sys.fri sh ((openingClaims sys proof ζ).map (·.commitment))
        (claimPoints (openingClaims sys proof ζ)) (claimValues (openingClaims sys proof ζ))
        proof.openingProof = true ∧
      ∃ ch : TensorChallenges EF,
        ch = transcriptFromTensorMulti (uChallengerTensor f M.toFieldModel)
          (mainChallenges (uChallengerTensor f M.toFieldModel) s proof).state sys.fri sh arities
          (claimValues (openingClaims sys proof ζ)) proof.openingProof ∧
        verifyWithTensorMulti inputMmcs friMmcs sys.fri sh arities
          ((openingClaims sys proof ζ).map (·.commitment))
          (claimPoints (openingClaims sys proof ζ)) (claimValues (openingClaims sys proof ζ))
          proof.openingProof ch = true ∧
        ch.schedule.colChallenges =
          ((List.range (tensorNumChallenges (maxWidth sh))).map fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt k)).toArray ∧
        ch.schedule.openChallenges =
          ((List.range (tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup sh))).map fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt
              (tensorNumChallenges (maxWidth sh) + k))).toArray ∧
        ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges (maxWidth sh) ∧
        ch.schedule.openWeights = tensorWeights ch.schedule.openChallenges
          (maxOpeningsPerHeight sys.fri.logBlowup sh) ∧
        ch.betas = ((List.range arities.length).map fun i =>
          Function.surjInv M.surj (answer f ms (5 + i)).field).toArray ∧
        (ch.powOk = true →
          (sys.fri.commitPowBits ≠ 0 → ∀ i < arities.length,
            (answer f ms (5 + i)).bits 0 sys.fri.commitPowBits = 0) ∧
          (sys.fri.queryPowBits ≠ 0 →
            (answer f ms (5 + arities.length)).bits 0 sys.fri.queryPowBits = 0)) ∧
        ch.indices = ((List.range sys.fri.numQueries).map fun t =>
          (answer f ms (5 + arities.length)).bits
            (t + if sys.fri.queryPowBits = 0 then 0 else 1)
            (logMaxHeight sys.fri.logBlowup sh)).toArray := by
  have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage proof))
      2 (ms 2) false 0 0 := by
    rw [h2]; exact hs.observeAll f M.toFieldModel _
  obtain ⟨hα, a2'⟩ := a2.sampleExt_zero f M.toFieldModel
  have a3 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observe
      ((uChallengerTensor f M.toFieldModel).sampleExt
        ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage proof))).2
      (.digest proof.quotientCommit)) 3 (ms 3) false 0 0 := by
    rw [h3]; exact a2'.observe_next f M.toFieldModel _
  obtain ⟨hζ, a3'⟩ := a3.sampleExt_zero f M.toFieldModel
  simp only [checkAfterChallengesTensorMultiArity, mainChallenges, Bool.and_eq_true] at h
  rw [hα, hζ] at h
  obtain ⟨⟨hz, hv⟩, hc⟩ := h
  rw [verifyClaimsFromTensorMultiArity, Bool.and_eq_true] at hv
  obtain ⟨hu, hvf⟩ := hv
  rw [verifyFromTensorMultiArity, verifyFromTensorWithSchedule, Bool.and_eq_true] at hvf
  obtain ⟨hsh, hw⟩ := hvf
  have hne : (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map
        (Observation.ext (F := F) (D := D)) ≠ [] := fun h0 =>
    claimValues_openingClaims_ne_nilTM sys proof hshape (M.degree_eq ▸ M.extData.d_pos) _
      (List.map_eq_nil_iff.mp h0)
  have a4 := a3'.observeAll_next f M.toFieldModel hne
  have a4' : UAtTensor ms _ 4 (ms 4) false 0 0 :=
    ⟨a4.round, a4.hist, a4.cur.trans h4.symm, a4.squeezed, a4.nfields, a4.nbits⟩
  have hfinal : proof.openingProof.finalPoly.size ≠ 0 := by
    have hsh' := hsh
    simp only [Fri.shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hsh'
    rw [hsh'.1.1.2]
    exact (Nat.two_pow_pos _).ne'
  have hact_ne : ¬ (activeIndices proof.active).isEmpty := by
    have h := hshape
    simp only [Stark.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact Bool.eq_false_iff.mp h.1.1.1.1.1.1.1.1.1.2
  have hpos : 0 < tensorNumChallenges (maxWidth (claimShape (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field)))) +
      tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup (claimShape (openingClaims sys
        proof (Function.surjInv M.surj (answer f ms 3).field)))) := by
    rw [claimShape_openingClaims sys proof hshape, ← M.degree_eq]
    exact pos_tensorChallenges_starkShape sys M.extData.d hact_ne proof.logDegrees
  obtain ⟨tcol, topen, tcolW, topenW, tβ, tpow, tidx⟩ :=
    transcriptTailTensorMulti_ufreeTensor f M.toFieldModel sys.fri
      (claimShape (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
      (scheduleOfShape sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field))))
      proof.openingProof 4 a4' hpos hC hF hfinal
  exact ⟨hz, hc, hu, hsh, _, rfl, hw, tcol, topen, tcolW, topenW, tβ, tpow, tidx⟩

omit [DecidableEq F] [DecidableEq EF] in
/-- **Accepted executable `verifyWithTensorMulti` implies `modelChecksTensorMulti` (and `powOk`).** -/
theorem modelChecksTensorMulti_of_verifyWithTensorMulti_exec (m : FieldModel F EF K)
    (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (wf : WellFormed m params shape) (hpos : ∀ a ∈ arities, 0 < a)
    (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    {Msg : Type} {Chal : ℕ → Type}
    (f : ∀ x : FSQuery Msg Chal (HashQuery K D), MerkleAnswer Msg Chal K D x)
    {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    (hshape : Fri.shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hcolSize : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape))
    (hopenSize : ch.schedule.openChallenges.size =
      tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (hcolW : ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges (maxWidth shape))
    (hopenW : ch.schedule.openWeights =
      tensorWeights ch.schedule.openChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (h : verifyWithTensorMulti (merkleMmcs (inputHasher m (hasherOf f)))
      (merkleMmcs (friHasher m (hasherOf f))) params shape arities commitments points values proof
      ch = true) :
    let r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) :=
      (fun b => m.ext.toModel (ch.schedule.colChallenges.getD b.val 0),
       fun b => m.ext.toModel (ch.schedule.openChallenges.getD b.val 0))
    ch.powOk = true ∧
      modelChecksTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (tensorCoordMulti params shape arities) (hasherOf f)
        (modelProofMulti m params shape proof)
        (fun j => viewMulti m params shape arities
          (messagesMulti params arities commitments points values proof j))
        r (fun i => m.ext.toModel (ch.betas.getD i 0))
        (fun t => ch.indices.getD t.val 0) = true := by
  let r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) :=
    (fun b => m.ext.toModel (ch.schedule.colChallenges.getD b.val 0),
     fun b => m.ext.toModel (ch.schedule.openChallenges.getD b.val 0))
  have hag : AgreesTensorMulti m params shape arities commitments points values proof ch
      (fun j => viewMulti m params shape arities
        (messagesMulti params arities commitments points values proof j))
      r (fun i => m.ext.toModel (ch.betas.getD i 0))
      (fun t => ch.indices.getD t.val 0) :=
    { msg := fun _ _ => rfl
      colSize := hcolSize
      openSize := hopenSize
      colWeights := hcolW
      openWeights := hopenW
      colChals := fun b => by
        show m.ext.toModel (ch.schedule.colChallenges.getD b.val 0) =
          m.ext.toModel ch.schedule.colChallenges[b.val]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hcolSize]; exact b.isLt),
          Option.getD_some]
      openChals := fun b => by
        show m.ext.toModel (ch.schedule.openChallenges.getD b.val 0) =
          m.ext.toModel ch.schedule.openChallenges[b.val]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [hopenSize]; exact b.isLt),
          Option.getD_some]
      beta := fun _ _ => rfl
      index := fun _ => rfl }
  exact modelChecksTensorMulti_of_verifyWithTensorMulti m params shape arities wf hpos hsum
    (hasherOf f) hshape hag h

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- Each round's reconstructed `2 ^ a`-entry row from `queryResultTensorMulti` maps under
`m.ext.toModel` to `Compiled.MultiParams.commitRowTensor`. -/
theorem rows_queryResultTensorMulti (m : FieldModel F EF K) (params : FriParams)
    (shape : ClaimShape) (arities : List ℕ) (wf : WellFormed m params shape)
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    (t : Fin params.numQueries)
    (hok : (queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).ok = true)
    {i : ℕ} (hi : i < arities.length) :
    ((queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).rows.getD
        i #[]).map m.ext.toModel =
      (modelParamsMulti m params shape arities wf hpos hsum).commitRowTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
        (modelProofMulti m params shape proof) (msg 0) r β (index t) t i := by
  have hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width := by
    intro o ho
    simp only [queryResultTensorMulti, checkQueryTensorMulti, Bool.and_eq_true,
      List.all_eq_true, beq_iff_eq] at hok
    exact hok.1.1.1 o ho
  have hrow := (toModel_foldChainMulti m params shape arities wf hpos hsum hshape hag
    t (index t) hwidths arities.length le_rfl).2.2 i hi
  rw [hag.index t] at hrow
  simpa [queryResultTensorMulti, checkQueryTensorMulti, hag.index t] using hrow

end RunTensorMulti

/-! ## 2. Multi-arity shard chain and verification computation (`shardCompTensorMulti`) -/

section ChainTensorMulti

variable (M : StarkModel F EF K) (sys : System F D)
  (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)

/-- Raw message of round `i` of a multi-arity tensor-batched STARK shard chain. -/
noncomputable def nextMsgTensorMulti :
    (i : ℕ) → Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) i → RawMsg F EF D
  | 0, _ => m0
  | 1, t => [.ext (rep M (tLastField t))]
  | 2, t => .ext (rep M (tLastField t)) :: (mid ++ secondMessage proof)
  | 3, _ => [.digest proof.quotientCommit]
  | 4, t => (claimValues (openingClaims sys proof (rep M (tLastField t)))).toList.map .ext
  | j + 5, _ => messagesMulti sys.fri
      (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
      #[] #[] #[] proof.openingProof (j + 1)

/-- **The oracle queries of verifying one multi-arity tensor-batched shard:**
the challenge queries of its chain, then the Merkle hash queries of
`Compiled.MultiParams.verifyWithTensor`. -/
noncomputable def shardCompTensorMulti (hcap : 0 < sys.fri.maxLogArity) :
    OracleComp (STAns F EF D K fslots slots width) Bool :=
  if h : logMaxHeight sys.fri.logBlowup (starkShape sys M.extData.d proof.active proof.logDegrees)
      ≤ TwoAdicOps.twoAdicity (F := F) then
    let shape := starkShape sys M.extData.d proof.active proof.logDegrees
    let arities := scheduleOfShape sys.fri shape
    let P := modelParamsMulti M.toFieldModel sys.fri shape arities (M.wellFormed sys.fri _ h)
      (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
    (deriveA (fun _ : HashQuery K D => D) (nextMsgTensorMulti M sys proof m0 mid)
      (4 + (P.rounds + 2))).bind fun t =>
      P.verifyWithTensor W Mopen (tensorCoordMulti sys.fri shape arities)
        (modelProofMulti M.toFieldModel sys.fri shape proof.openingProof)
        (fun j => viewMulti M.toFieldModel sys.fri shape arities
          (messagesMulti sys.fri arities
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
private theorem length_starkShape_leTM (d : ℕ) (active : Array Bool) (logDegrees : Array ℕ) :
    (starkShape sys d active logDegrees).length ≤ 4 := by
  unfold starkShape
  cases sys.preprocessedCommit <;> exact Nat.le_of_ble_eq_true rfl

omit [DecidableEq F] [DecidableEq EF] in
/-- Multi-arity verification of a shard satisfies the exact same `shardQueries sys n` bound. -/
theorem queryBound_shardCompTensorMulti (hcap : 0 < sys.fri.maxLogArity) {n : ℕ}
    (hn : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ n) :
    (shardCompTensorMulti (fslots := fslots) (slots := slots) (width := width)
      M sys proof m0 mid hcap).QueryBound (shardQueries sys n) := by
  unfold shardCompTensorMulti
  split
  · next h =>
    dsimp only
    have hrounds := (modelParamsMulti M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
      (M.wellFormed sys.fri _ h) (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)).rounds_le
    have hbatches := length_starkShape_leTM sys M.extData.d proof.active proof.logDegrees
    refine QueryBound.mono ((queryBound_deriveA _ _).bind fun t =>
      Compiled.MultiParams.queryBound_verifyWithTensor _ _ _ _ _ _ _ _ _) ?_
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.add_le_add_right (hrounds.trans hn) 2) 4)
      (Nat.mul_le_mul (Nat.add_le_add hbatches (hrounds.trans hn))
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hn) 1)))
  · exact queryBound_pure _ _

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_shardCompTensorMulti_twoAdicity (hcap : 0 < sys.fri.maxLogArity) :
    (shardCompTensorMulti (fslots := fslots) (slots := slots) (width := width)
      M sys proof m0 mid hcap).QueryBound (shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  by_cases h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F)
  · exact queryBound_shardCompTensorMulti M sys proof m0 mid hcap h
  · rw [shardCompTensorMulti, dite_eq_right h]
    exact queryBound_pure _ _

end ChainTensorMulti

/-! ## 3. Deterministic multi-arity shard soundness (`shard_goodTensorMulti`) -/

section ShardGoodMulti

section BuildTM

variable {Msg Msg' : Type} {C : ℕ → Type}

private def mkTTM (m : ℕ → Msg) (c : ∀ j, C j) : (i : ℕ) → Transcript Msg C i
  | 0 => .nil
  | i + 1 => (mkTTM m c i).snoc (m i) (c i)

private theorem msgs_mkTTM (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkTTM m c i).msgs = (List.range i).map m := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkTTM, Transcript.msgs_snoc, ih, List.range_succ, List.map_append, List.map_singleton]

private theorem mapIdx_mkTTM (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkTTM m c i).mapIdx g = mkTTM (fun j => g j (m j)) c i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [mkTTM, Transcript.mapIdx_snoc, ih, mkTTM]

private theorem msgAt_mkTTM (m : ℕ → Msg) (c : ∀ j, C j) (i j : ℕ) :
    Compiled.msgAt (mkTTM m c (i + 1)) j = m (min j i) := by
  rw [mkTTM, Compiled.msgAt, msgs_mkTTM, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge j i with h | h
  · rw [List.getElem?_range h, min_eq_left h.le]; rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h), min_eq_right h]; rfl

private theorem getElem?_msgs_mapIdx_mkTTM (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j)
    {i j : ℕ} (hj : j < i) : ((mkTTM m c i).mapIdx g).msgs[j]? = some (g j (m j)) := by
  rw [mapIdx_mkTTM, msgs_mkTTM, List.getElem?_map, List.getElem?_range hj]; rfl

private theorem mentions_of_supports_mkTTM {X' : Type} {Y' : X' → Type}
    [DecidableEq (FSQuery Msg C X')] {l : Log (FSAnswer (Msg := Msg) C Y')} {m : ℕ → Msg}
    {c : ∀ j, C j} : ∀ {i : ℕ}, Supports l (mkTTM m c i) → ∀ j < i, Mentions l j (m j)
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i + 1, h, j, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact mentions_of_supports_mkTTM h.1 j hlt
    · refine ⟨_, List.of_mem_dlookup h.2, ?_⟩
      have hlast := List.getElem?_concat_length (l := (mkTTM m c j).msgs) (a := m j)
      rwa [Transcript.length_msgs] at hlast

private theorem fsTranscript_eq_mkTTM {X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg C X', FSAnswer C Y' x) (ms : ℕ → Msg) (i : ℕ) :
    fsTranscript f ms i = mkTTM ms (answer f ms) i := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun t => t.snoc (ms i) (answer f ms i)) ih

private theorem chalsOf_mkTTM {U : Type} (m : ℕ → Msg) (c : ℕ → U) (i : ℕ) :
    chalsOf (mkTTM (C := fun _ => U) m c i) = (List.range i).map c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkTTM, chalsOf, ih, List.range_succ, List.map_append, List.map_singleton]

variable {nc : ℕ → ℕ} {S : MultiLdtInstance K} {W M q : ℕ}

omit [DecidableEq K] in
private theorem claimsOf_mkTTM (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i : ℕ) :
    claimsOf (mkTTM m c (i + 1)) = (m 0).claims := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

omit [DecidableEq K] in
private theorem wordsOf_mkTTM (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i k : ℕ) :
    wordsOf (mkTTM m c i) k = if k + 1 < i then (m (k + 1)).word else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkTTM, PcsRbr.wordsOf_snoc_succ]
      by_cases hk : k = i
      · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

omit [DecidableEq K] in
private theorem tensorOfMulti_mkTTM (m : ℕ → Msg) (c : ∀ j, ChalTensorMulti S W M q j) (i : ℕ) :
    tensorOfMulti (mkTTM m c (i + 1)) = (c 0).tensor := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

omit [DecidableEq K] in
private theorem betasOfTensorMulti_mkTTM (m : ℕ → Msg) (c : ∀ j, ChalTensorMulti S W M q j)
    (i k : ℕ) :
    betasOfTensorMulti (mkTTM m c i) k = if k + 1 < i then (c (k + 1)).field else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkTTM, PcsRbr.betasOfTensorMulti_snoc_succ]
      by_cases hk : k = i
      · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

omit [DecidableEq K] in
private theorem queriesOfTensorMulti_mkTTM (m : ℕ → Msg) (c : ∀ j, ChalTensorMulti S W M q j)
    (i : ℕ) : queriesOfTensorMulti (mkTTM m c (i + 1)) = (c i).points := rfl

omit [DecidableEq K] in
private theorem acceptsTensorMulti_mkTTM_congr
    {coord : ∀ j, Fin (nc j) → Fin M × Fin W} {m m' : ℕ → PcsRbr.Msg K nc}
    {c : ∀ j, ChalTensorMulti S W M q j} {i : ℕ} {s : K} (h0 : (m' 0).claims = (m 0).claims)
    (hw : ∀ k < i, (m' (k + 1)).word = (m (k + 1)).word)
    (h : AcceptsTensorMulti S s coord (mkTTM m c (i + 1))) :
    AcceptsTensorMulti S s coord (mkTTM m' c (i + 1)) := by
  have hc : claimsOf (mkTTM m' c (i + 1)) = claimsOf (mkTTM m c (i + 1)) := by
    rw [claimsOf_mkTTM, claimsOf_mkTTM, h0]
  have hwo : wordsOf (mkTTM m' c (i + 1)) = wordsOf (mkTTM m c (i + 1)) := by
    funext k
    rw [wordsOf_mkTTM, wordsOf_mkTTM]
    by_cases hk : k + 1 < i + 1
    · rw [ite_eq_left hk, ite_eq_left hk, hw k (by omega)]
    · rw [ite_eq_right hk, ite_eq_right hk]
  have hr : tensorOfMulti (mkTTM m' c (i + 1)) = tensorOfMulti (mkTTM m c (i + 1)) := by
    rw [tensorOfMulti_mkTTM, tensorOfMulti_mkTTM]
  have hβ : betasOfTensorMulti (mkTTM m' c (i + 1)) = betasOfTensorMulti (mkTTM m c (i + 1)) := by
    funext k; rw [betasOfTensorMulti_mkTTM, betasOfTensorMulti_mkTTM]
  unfold AcceptsTensorMulti
  rw [hc, hwo, hr, hβ, queriesOfTensorMulti_mkTTM]
  exact h

end BuildTM

omit [DecidableEq K] in
private theorem tLastField_fsTranscriptAM {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UTensorChal K fslots slots width) X',
      FSAnswer (UTensorChal K fslots slots width) Y' x)
    (next : ∀ i, Transcript Msg (UTensorChal K fslots slots width) i → Msg) (j : ℕ) :
    tLastField (fsTranscriptA f next (j + 1)) =
      (answer f (fun i => next i (fsTranscriptA f next i)) j).field := by
  show UTensorAns.field (f (.chal (fsTranscriptA f next j) (next j (fsTranscriptA f next j)))) =
    UTensorAns.field (f (.chal (fsTranscript f (fun i => next i (fsTranscriptA f next i)) j)
      (next j (fsTranscriptA f next j))))
  rw [← fsTranscriptA_eq_fsTranscript]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem rawAt_interpTensorM (B : Bounds) (r : ℕ)
    (l : Log (STAns F EF D K fslots slots width)) (m : ℕ → RawMsg F EF D)
    (c : ℕ → UTensorAns K fslots slots width) {i j : ℕ} (hj : j < i) :
    rawAt ((mkTTM (C := UTensorChal K fslots slots width) m c i).mapIdx
      (interpTensor B r l)).msgs j = m j := by
  rw [rawAt, getElem?_msgs_mapIdx_mkTTM _ _ _ hj]; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem comAt_interpTensorM (B : Bounds) (r : ℕ)
    (l : Log (STAns F EF D K fslots slots width)) (m : ℕ → RawMsg F EF D)
    (c : ℕ → UTensorAns K fslots slots width) {i j : ℕ} (hj : j < i) (hr : j < r) :
    comAt ((mkTTM (C := UTensorChal K fslots slots width) m c i).mapIdx
      (interpTensor B r l)).msgs j = (readMsg B (m j) (committedRow l)).2 := by
  rw [comAt, getElem?_msgs_mapIdx_mkTTM _ _ _ hj, interpTensor, ite_eq_left hr]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_chalsOf_mkTTM {Msg : Type} (m : ℕ → Msg)
    (c : ℕ → UTensorAns K fslots slots width) {i j : ℕ} (hj : j < i) :
    tAnsAt (chalsOf (mkTTM (C := UTensorChal K fslots slots width) m c i)) j = c j := by
  rw [chalsOf_mkTTM, tAnsAt, List.getElem?_map, List.getElem?_range hj]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_chalsOf_fsTranscriptAM {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UTensorChal K fslots slots width) X',
      FSAnswer (UTensorChal K fslots slots width) Y' x)
    (next : ∀ i, Transcript Msg (UTensorChal K fslots slots width) i → Msg) {i j : ℕ} (hj : j < i) :
    tAnsAt (chalsOf (fsTranscriptA f next i)) j =
      answer f (fun i => next i (fsTranscriptA f next i)) j := by
  rw [fsTranscriptA_eq_fsTranscript, fsTranscript_eq_mkTTM]
  exact tAnsAt_chalsOf_mkTTM _ _ hj

omit [Field K] [DecidableEq K] in
private theorem tBits_eq_zeroM (u : UTensorAns K fslots slots width) (k : ℕ) {b : ℕ} (hb : b = 0) :
    u.bits k b = 0 := by
  subst hb; exact Nat.lt_one_iff.mp (u.bits_lt k 0)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private theorem readMsg_snd_of_memTM (B : Bounds) {m : RawMsg F EF D}
    (com : Compiled.Committed K D) {root : D} (h : root ∈ digestsOf B m) :
    (readMsg B m com).2 root = com root :=
  ite_eq_left h

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem getD_zero_mem_digestsOfTM (B : Bounds) {m : RawMsg F EF D} (h : digestsIn m ≠ []) :
    (digestsIn m).getD 0 default ∈ digestsOf B m := by
  unfold digestsOf
  cases hd : digestsIn m with
  | nil => exact absurd hd h
  | cons d ds => exact List.mem_cons_self (a := d) (l := List.take B.shards ds)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem committedRow_of_mentionsTM (B : Bounds) (r : ℕ)
    {l l₁ : Log (STAns F EF D K fslots slots width)} (hl₁ : l₁ <+: l)
    (hno : ¬ HasBad (Hit (fun _ => digestsOf (F := F) (EF := EF) B) r) l) {j : ℕ}
    {m : RawMsg F EF D} (hm : Mentions l₁ j m) (hj : j < r) {root : D}
    (hroot : root ∈ digestsOf B m) :
    committedRow l root = committedRow l₁ root := by
  obtain ⟨s, rfl⟩ := hl₁
  funext dims
  exact committedRow_append_of_not_hit (present_of_mentions hm hj hroot)
    (fun h => hno h.hasBad) dims

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem digestsIn_of_baseTM {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) : digestsIn mid = [] := by
  rw [digestsIn, List.filterMap_eq_nil_iff]
  intro o ho; obtain ⟨a, rfl⟩ := hmid o ho; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_of_baseTM {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) : extsOf mid = [] := by
  rw [extsOf, List.filterMap_eq_nil_iff]
  intro o ho; obtain ⟨a, rfl⟩ := hmid o ho; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_map_extTM (l : List EF) :
    extsOf (l.map (Observation.ext (F := F) (D := D))) = l := by
  simp [extsOf, List.filterMap_map]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem digestsIn_secondTM {InputProof CommitProof : Type} (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    digestsIn (.ext γ :: (mid ++ secondMessage proof)) = [proof.stage2Commit] := by
  have h := digestsIn_of_baseTM hmid
  simp only [digestsIn] at h
  simp [digestsIn, secondMessage, List.filterMap_append, List.filterMap_map, h]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_secondTM {InputProof CommitProof : Type} (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    extsOf (.ext γ :: (mid ++ secondMessage proof)) =
      γ :: proof.intermediateAccumulators.toList := by
  have h := extsOf_of_baseTM hmid
  simp only [extsOf] at h
  simp [extsOf, secondMessage, List.filterMap_append, List.filterMap_map, h]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messagesMulti_succ_of_lt {InputProof CommitProof : Type} (params : FriParams)
    (arities : List ℕ) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) {i : ℕ} (hi : i < arities.length) :
    messagesMulti params arities commitments points values proof (i + 1) =
      .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]) := by
  rw [messagesMulti, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
    Nat.add_sub_cancel]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messagesMulti_of_gt {InputProof CommitProof : Type} (params : FriParams)
    (arities : List ℕ) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) {j : ℕ} (hj : arities.length < j) :
    messagesMulti params arities commitments points values proof j =
      finalMessageMulti arities proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
  rw [messagesMulti, ite_eq_right (by omega), ite_eq_right (by omega)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messagesMulti_succ_congr {InputProof CommitProof : Type} (params : FriParams)
    (arities : List ℕ) (commitments commitments' : Array D) (points points' values values' : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) (j : ℕ) :
    messagesMulti params arities commitments points values proof (j + 1) =
      messagesMulti params arities commitments' points' values' proof (j + 1) := by
  rw [messagesMulti, messagesMulti, ite_eq_right (Nat.succ_ne_zero j),
    ite_eq_right (Nat.succ_ne_zero j)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messagesMulti_min {InputProof CommitProof : Type} (params : FriParams)
    (arities : List ℕ) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) (j : ℕ) :
    messagesMulti params arities commitments points values proof (min j (arities.length + 1)) =
      messagesMulti params arities commitments points values proof j := by
  rcases Nat.lt_or_ge (arities.length + 1) j with h | h
  · rw [min_eq_right h.le, messagesMulti_of_gt _ _ _ _ _ _ (Nat.lt_succ_self _),
      messagesMulti_of_gt _ _ _ _ _ _ (by omega)]
  · rw [min_eq_left h]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem digestsIn_messagesMulti_ne_nil {InputProof CommitProof : Type} (params : FriParams)
    (arities : List ℕ) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) {i : ℕ} (hi : i < arities.length) :
    digestsIn (messagesMulti params arities commitments points values proof (i + 1)) ≠ [] := by
  rw [messagesMulti_succ_of_lt _ _ _ _ _ _ hi]
  exact List.cons_ne_nil (proof.commitPhaseCommits.getD i default) _

omit [DecidableEq F] [DecidableEq EF] in
private theorem run_of_checkTensorMulti (M : StarkModel F EF K) (sys : System F D)
    (hcap : 0 < sys.fri.maxLogArity)
    (f : ∀ x, STAns F EF D K fslots slots width x)
    (proof : Proof F EF D (Array (List D)) (Array (List D)))
    (hshape : Stark.shapeOk sys proof = true) {shape : ClaimShape}
    (hsh : ∀ ζ, claimShape (openingClaims sys proof ζ) = shape)
    {ms : ℕ → RawMsg F EF D} {s : UStateTensor F EF D} {cur : RawMsg F EF D} (β γ acc : EF)
    {α ζ : EF}
    (hα : α = Function.surjInv M.surj (answer f ms 2).field)
    (hζ : ζ = Function.surjInv M.surj (answer f ms 3).field)
    (hs : UAtTensor ms s 2 cur false 0 0) (h2 : ms 2 = cur ++ secondMessage proof)
    (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof ζ)).toList.map .ext)
    (h5 : ∀ j, ms (5 + j) =
      messagesMulti sys.fri (scheduleOfShape sys.fri shape) #[] #[] #[] proof.openingProof (j + 1))
    (hcheck : checkAfterChallengesTensorMultiArity
      (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    let arities := scheduleOfShape sys.fri shape
    ∃ htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F),
      (∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup) ∧
      zetaOk proof ζ = true ∧ constraintsOk sys proof β γ acc α ζ = true ∧
      ((modelParamsMulti M.toFieldModel sys.fri shape arities (M.wellFormed sys.fri shape htwo)
          (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)).verifyWithTensor
        (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)
        (tensorCoordMulti sys.fri shape arities)
        (modelProofMulti M.toFieldModel sys.fri shape proof.openingProof)
        (fun j => viewMulti M.toFieldModel sys.fri shape arities (messagesMulti sys.fri arities
          ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
          (claimValues (openingClaims sys proof ζ)) proof.openingProof j))
        (tensorChalOfAns (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)
          (answer f ms 4))
        (fun i => if i < arities.length then (answer f ms (5 + i)).field else 0)
        (fun k => (answer f ms (5 + arities.length)).bits
          (k.val + if sys.fri.queryPowBits = 0 then 0 else 1)
          (logMaxHeight sys.fri.logBlowup shape))).run f = true ∧
      (sys.fri.commitPowBits ≠ 0 → ∀ i < arities.length,
        (answer f ms (5 + i)).bits 0 sys.fri.commitPowBits = 0) ∧
      (sys.fri.queryPowBits ≠ 0 →
        (answer f ms (5 + arities.length)).bits 0 sys.fri.queryPowBits = 0) := by
  subst hα hζ
  have hsh' : claimShape (openingClaims
      (InputProof := (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))).MultiProof)
      (CommitProof := (merkleMmcs (friHasher M.toFieldModel (hasherOf f))).MultiProof) sys proof
      (Function.surjInv M.surj (answer f ms 3).field)) = shape := hsh _
  obtain ⟨hz, hc, -, hfs, ch, -, hw, hcol, hopen, hcolW, hopenW, hβ, hpow, hidx⟩ :=
    checkAfterChallengesTensorMultiArity_ufreeTensor M f
      (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys proof hshape β γ acc hs h2 h3 h4
      (fun i hi => by
        rw [hsh'] at hi
        rw [h5 i, messagesMulti_succ_of_lt _ _ _ _ _ _ hi])
      (by rw [hsh', h5, messagesMulti_of_gt _ _ _ _ _ _ (Nat.lt_succ_self _)]) hcheck
  rw [hsh'] at hfs hw hcol hopen hcolW hopenW hβ hpow hidx
  obtain ⟨htwo, hfinal⟩ : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F) ∧
      ∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup := by
    have h := hfs
    simp only [Fri.shapeOkMultiArity, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.2, fun m hm => (h.1.1.1.1.1.1.1.1.1.1.1.1.2 m hm).2⟩
  have hcolSz : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape) := by
    rw [hcol, List.size_toArray, List.length_map, List.length_range]
  have hopenSz : ch.schedule.openChallenges.size =
      tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup shape) := by
    rw [hopen, List.size_toArray, List.length_map, List.length_range]
  obtain ⟨hpowOk, hmc⟩ := modelChecksTensorMulti_of_verifyWithTensorMulti_exec M.toFieldModel
    sys.fri shape (scheduleOfShape sys.fri shape) (M.wellFormed sys.fri shape htwo)
    (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap) f hfs hcolSz hopenSz hcolW hopenW hw
  refine ⟨htwo, hfinal, hz, hc, ?_, (hpow hpowOk).1, (hpow hpowOk).2⟩
  refine Eq.trans (congrArg (OracleComp.run f) ?_)
    (((modelParamsMulti M.toFieldModel sys.fri shape (scheduleOfShape sys.fri shape) _ _
        _).run_verifyWithTensor _ _ _ f _ _ _ _ _).trans hmc)
  congr 1
  · refine Prod.ext (funext fun b => ?_) (funext fun b => ?_)
    · dsimp only [tensorChalOfAns]
      rw [hcol, Transcript.getD_map_range, ite_eq_left b.isLt, Function.surjInv_eq M.surj]
    · dsimp only [tensorChalOfAns]
      rw [hopen, Transcript.getD_map_range, ite_eq_left b.isLt, Function.surjInv_eq M.surj]
  · funext i
    rw [hβ, Transcript.getD_map_range, apply_ite M.ext.toModel, M.ext.map_zero,
      Function.surjInv_eq M.surj]
  · funext k
    rw [hidx, Transcript.getD_map_range,
      ite_eq_left (show k.val < sys.fri.numQueries from k.isLt)]

private def forgetProofsTM {InputProof CommitProof : Type}
    (proof : Proof F EF D InputProof CommitProof) : Proof F EF D Unit Unit where
  active := proof.active
  stage1Commit := proof.stage1Commit
  stage2Commit := proof.stage2Commit
  quotientCommit := proof.quotientCommit
  intermediateAccumulators := proof.intermediateAccumulators
  logDegrees := proof.logDegrees
  quotientOpened := proof.quotientOpened
  preprocessedOpened := proof.preprocessedOpened
  stage1Opened := proof.stage1Opened
  stage2Opened := proof.stage2Opened
  openingProof := ⟨#[], #[], #[], #[], #[], 0⟩

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem check_of_proofTM {InputProof CommitProof : Type} (M : StarkModel F EF K)
    (sys : System F D) (v : ShardView F EF D K) (proof : Proof F EF D InputProof CommitProof)
    (h1 : proof.active = v.hdr.active) (h2 : proof.stage1Commit = v.hdr.stage1Commit)
    (h3 : proof.stage2Commit = v.stage2) (h4 : proof.quotientCommit = v.quot)
    (h5 : proof.intermediateAccumulators = v.accs) (h6 : proof.logDegrees = v.hdr.logDegrees)
    (hshape : Stark.shapeOk sys proof = true)
    (hc : constraintsOk sys proof (rep M v.β) (rep M v.γ) v.acc0 (rep M v.α) (rep M v.ζ) = true)
    (hz : zetaOk proof (rep M v.ζ) = true) :
    v.Check M sys (claimValues (openingClaims sys proof (rep M v.ζ))) :=
  ⟨forgetProofsTM proof, h1, h2, h3, h4, h5, h6, hshape, rfl, hc, hz⟩

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem baseRows_congrSGM (M : StarkModel F EF K) {com com' : Compiled.Committed K D}
    {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i; unfold StarkModel.baseRows; rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem colPoly_congrSGM (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ)
    {com com' : Compiled.Committed K D} {root : D} (h : com root = com' root)
    (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord; rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem constraintFail_congrSGM {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {com com' : Compiled.Committed K D} {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs ↔
      ConstraintFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  have hvals : rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
    funext pos ci x; unfold rowVals pointRow
    have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
        (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
      funext fun j => colPoly_congrSGM M _ _ h1 _ _ _ _
    have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
        (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
      funext fun j => colPoly_congrSGM M _ _ h2 _ _ _ _
    have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
        (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
      funext j; unfold shardCols; dsimp only
      cases hpc : sys.preprocessedCommit with
      | none => rfl
      | some root => exact colPoly_congrSGM M _ _ (h3 root hpc) _ _ _ _
    rw [hmain, hstage2, hpre]
  unfold ConstraintFail; rw [hvals]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem mem_commitmentsTM {sys : System F D} {v : ShardView F EF D K} {root : D}
    (hroot : root ∈ (v.commitments sys).toList) :
    root = v.hdr.stage1Commit ∨ root = v.stage2 ∨ root = v.quot ∨
      sys.preprocessedCommit = some root := by
  unfold ShardView.commitments at hroot
  cases hpc : sys.preprocessedCommit with
  | none =>
    rw [hpc] at hroot
    simp only [Array.append_empty, List.mem_cons, List.not_mem_nil, or_false] at hroot
    tauto
  | some c =>
    rw [hpc] at hroot
    simp only [Array.toList_append, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hroot
    rcases hroot with (h | h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (h ▸ rfl)))

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private theorem comOf_eqTM {sys : System F D} {msgs : List (IMsg F EF D K)}
    {v : ShardView F EF D K} {c : Compiled.Committed K D}
    (h0 : ∀ root, root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root →
      comAt msgs 0 root = c root)
    (h2 : comAt msgs 2 v.stage2 = c v.stage2) (h3 : comAt msgs 3 v.quot = c v.quot) {root : D}
    (hroot : root = v.hdr.stage1Commit ∨ root = v.stage2 ∨ root = v.quot ∨
      sys.preprocessedCommit = some root) : comOf sys v msgs root = c root := by
  unfold comOf
  by_cases h : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root
  · rw [ite_eq_left h]; exact h0 root h
  · rw [ite_eq_right h]
    by_cases h' : root = v.stage2
    · rw [ite_eq_left h', h']; exact h2
    · rw [ite_eq_right h']
      obtain rfl : root = v.quot := by tauto
      exact h3

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem inputRoots_mem_commitmentsTM (M : StarkModel F EF K) {sys : System F D}
    (v : ShardView F EF D K) (arities : List ℕ) (points values : Array EF)
    (b : Fin (v.shape M sys).length) :
    (viewMulti M.toFieldModel sys.fri (v.shape M sys) arities
      (firstMessage (F := F) (v.commitments sys) points values)).inputRoots b ∈
        (v.commitments sys).toList := by
  have hsize : (v.commitments sys).toList.length = (v.shape M sys).length := by
    unfold ShardView.commitments ShardView.shape starkShape
    cases sys.preprocessedCommit <;> rfl
  show (digestsIn (firstMessage (F := F) (v.commitments sys) points values)).getD b.val default ∈ _
  rw [Checks.digestsIn_firstMessage, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [hsize]; exact b.isLt), Option.getD_some]
  exact List.getElem_mem _

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem commitments_openingClaimsTM {InputProof CommitProof : Type} {sys : System F D}
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) :
    (openingClaims sys proof ζ).map (·.commitment) =
      #[proof.stage1Commit, proof.stage2Commit, proof.quotientCommit] ++
        match sys.preprocessedCommit with
        | some c => #[c]
        | none => #[] := by
  unfold openingClaims
  cases sys.preprocessedCommit <;> simp

omit [Inhabited D] in
private theorem baseRows_of_opensTM (M : StarkModel F EF K)
    {l l₁ : Log (STAns F EF D K fslots slots width)} (hl₁ : l₁ <+: l)
    (hl : ¬ LogCollision hashObs l) {com : Compiled.Committed K D} {root : D}
    (hcom : com root = committedRow l root) {dims : Array Dimensions} {index : ℕ}
    {rows : Array (Array F)}
    (h : Opens l₁ root dims index (rows.map (·.map M.base.toModel))) {m : ℕ} {d : Dimensions}
    (hd : dims[m]? = some d) :
    M.baseRows com root dims m (index >>> (Merkle.maxLogHeight dims.toList - d.logHeight)) =
      committedRow l₁ root dims m
        (index >>> (Merkle.maxLogHeight dims.toList - d.logHeight)) := by
  have h₁ := committedRow_of_opens (fun hcol => hl (hcol.of_prefix hl₁)) h hd
  have h₂ := committedRow_of_opens hl (h.of_prefix hl₁) hd
  unfold StarkModel.baseRows
  rw [hcom, h₂, h₁, Array.getElem?_map]
  cases rows[m]? with
  | none => rfl
  | some row =>
    rw [Option.map_some, Option.bind_some]
    refine ite_eq_left fun x hx => ?_
    rw [Array.toList_map, List.mem_map] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact Set.mem_range_self a

omit [DecidableEq F] [DecidableEq EF] in
private theorem ungrind_pcsTTensorMulti {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {msgs : List (IMsg F EF D K)} {chals : List (UTensorAns K fslots slots width)}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) (j : ℕ) :
    ungrind (pcsTTensorMulti msgs chals hs hcap j) =
      mkTTM (pcsMsgMulti msgs hs hcap) (fun i =>
        (pcsChalTensorMulti (hs.paramsMulti hcap) (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
          (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys))) i
          (tAnsAt chals (4 + i))).2) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pcsTTensorMulti, PcsRbr.ungrind_snoc, ih, mkTTM]

omit [DecidableEq F] [DecidableEq EF] in
private theorem powPasses_pcsTTensorMulti {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {msgs : List (IMsg F EF D K)} {chals : List (UTensorAns K fslots slots width)}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) (j : ℕ) :
    PowPasses (pcsTTensorMulti msgs chals hs hcap j) ↔
      ∀ i < j, (tAnsAt chals (4 + i)).bits 0
        (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)) i) = 0 := by
  induction j with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩
  | succ j ih =>
    rw [pcsTTensorMulti, PcsRbr.powPasses_snoc, ih]
    constructor
    · rintro ⟨h, hj⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hj
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)⟩

omit [DecidableEq F] [DecidableEq EF] in
private theorem accepts_pcsTTensorMulti {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {msgs : List (IMsg F EF D K)} {chals : List (UTensorAns K fslots slots width)}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity)
    {Mq : Type} {Cq : ℕ → Type} [DecidableEq (FSQuery Mq Cq (HashQuery K D))]
    {pf : Compiled.MultiProof K D (hs.paramsMulti hcap).batches (hs.paramsMulti hcap).queries}
    {l' l₁ : Log (MerkleAnswer Mq Cq K D)} (pm : ℕ → RawMsg F EF D)
    (ans : ℕ → UTensorAns K fslots slots width)
    (hans : ∀ j < 4 + ((hs.paramsMulti hcap).rounds + 2), tAnsAt chals j = ans j)
    (hmin : ∀ j, pm (min j ((hs.paramsMulti hcap).rounds + 1)) = pm j)
    (h0 : pm 0 = firstMessage (v.commitments sys)
      (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs))
    (hraw : ∀ k ≤ (hs.paramsMulti hcap).rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1))
    (hrun : Outcome ((hs.paramsMulti hcap).verifyWithTensor (M' := Mq) (C := Cq)
      (maxWidth (v.shape M sys)) (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
      (starkTensorCoordMulti M sys hs hcap) pf
      (fun j => viewMulti M.toFieldModel sys.fri (v.shape M sys)
        (scheduleOfShape sys.fri (v.shape M sys)) (pm j))
      (tensorChalOfAns (maxWidth (v.shape M sys))
        (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) (ans 4))
      (fun i => if i < (hs.paramsMulti hcap).rounds then (ans (5 + i)).field else 0)
      (fun k => (ans (5 + (hs.paramsMulti hcap).rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) (hs.paramsMulti hcap).n)) l' true l₁)
    (hl : ¬ LogCollision hashObs l₁)
    (hc : ∀ (b : Fin (hs.paramsMulti hcap).batches) (k : Fin (hs.paramsMulti hcap).queries)
        (mi : ℕ) (d : Dimensions), ((hs.paramsMulti hcap).dims b)[mi]? = some d →
      M.baseRows (comOf sys v msgs)
          ((viewMulti M.toFieldModel sys.fri (v.shape M sys)
            (scheduleOfShape sys.fri (v.shape M sys)) (pm 0)).inputRoots b)
          ((hs.paramsMulti hcap).dims b) mi
          ((ans (5 + (hs.paramsMulti hcap).rounds)).bits
            (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) (hs.paramsMulti hcap).n >>>
              ((hs.paramsMulti hcap).n - d.logHeight)) =
        committedRow l₁ ((viewMulti M.toFieldModel sys.fri (v.shape M sys)
            (scheduleOfShape sys.fri (v.shape M sys)) (pm 0)).inputRoots b)
          ((hs.paramsMulti hcap).dims b) mi
          ((ans (5 + (hs.paramsMulti hcap).rounds)).bits
            (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) (hs.paramsMulti hcap).n >>>
              ((hs.paramsMulti hcap).n - d.logHeight)))
    (hw : ∀ k < (hs.paramsMulti hcap).rounds,
      comAt msgs (4 + (k + 1))
          (viewMulti M.toFieldModel sys.fri (v.shape M sys)
            (scheduleOfShape sys.fri (v.shape M sys)) (pm (k + 1))).commitRoot =
        committedRow l₁ (viewMulti M.toFieldModel sys.fri (v.shape M sys)
          (scheduleOfShape sys.fri (v.shape M sys)) (pm (k + 1))).commitRoot) :
    AcceptsTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
      (starkTensorCoordMulti M sys hs hcap)
      (ungrind (pcsTTensorMulti msgs chals hs hcap ((hs.paramsMulti hcap).rounds + 2))) := by
  let P := hs.paramsMulti hcap
  have hP_rounds : P.rounds = (hs.paramsMulti hcap).rounds := rfl
  let arities := scheduleOfShape sys.fri (v.shape M sys)
  let W := maxWidth (v.shape M sys)
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)
  have hr : tensorOfMulti (mkTTM pm (fun i =>
      (pcsChalTensorMulti P W Mopen (powBitsMulti sys.fri arities) i
        (tAnsAt chals (4 + i))).2)
      (P.rounds + 2)) = tensorChalOfAns W Mopen (ans 4) := by
    rw [tensorOfMulti_mkTTM, tensor_pcsChalTensorMulti _ _ _ _ _ _ rfl, hans (4 + 0) (by omega)]
    rfl
  have hβ : betasOfTensorMulti (mkTTM pm (fun i =>
      (pcsChalTensorMulti P W Mopen (powBitsMulti sys.fri arities) i
        (tAnsAt chals (4 + i))).2)
      (P.rounds + 2)) =
      fun i => if i < P.rounds then (ans (5 + i)).field else 0 := by
    funext i
    rw [betasOfTensorMulti_mkTTM]
    rcases Nat.lt_trichotomy i P.rounds with hi | rfl | hi
    · rw [ite_eq_left (by omega), ite_eq_left hi,
        field_pcsChalTensorMulti _ _ _ _ _ _ (Nat.succ_ne_zero _) (Nat.succ_le_of_lt hi),
        hans (4 + (i + 1)) (by omega), show 4 + (i + 1) = 5 + i by omega]
    · rw [ite_eq_left (Nat.lt_succ_self _), ite_eq_right (Nat.lt_irrefl _),
        field_pcsChalTensorMulti_of_not_le _ _ _ _ _ _ (Nat.not_succ_le_self _)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hq : (fun k => P.indexOf (queriesOfTensorMulti (mkTTM pm (fun i =>
      (pcsChalTensorMulti P W Mopen (powBitsMulti sys.fri arities) i
        (tAnsAt chals (4 + i))).2)
      (P.rounds + 2)) k)) =
      fun k => (ans (5 + P.rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n := by
    funext k
    rw [queriesOfTensorMulti_mkTTM, indexOf_points_pcsChalTensorMulti _ _ _ _ _ _
        (Nat.not_succ_le_self _),
      show powBitsMulti sys.fri arities (P.rounds + 1) = sys.fri.queryPowBits from
        powBitsMulti_last sys.fri arities,
      hans (4 + (P.rounds + 1)) (by omega),
      show 4 + (P.rounds + 1) = 5 + P.rounds by omega]
  have hmsg : (fun j => viewMulti M.toFieldModel sys.fri (v.shape M sys) arities
      (Compiled.msgAt (mkTTM pm (fun i =>
        (pcsChalTensorMulti P W Mopen (powBitsMulti sys.fri arities) i
          (tAnsAt chals (4 + i))).2)
        (P.rounds + 2)) j)) =
      fun j => viewMulti M.toFieldModel sys.fri (v.shape M sys) arities (pm j) := by
    funext j
    rw [msgAt_mkTTM, hmin]
  have hacc := P.acceptsTensorMulti_of_outcome_verifyWithTensor_view_com
    (W := W) (M := Mopen) (coord := starkTensorCoordMulti M sys hs hcap) (pf := pf)
    (l := l') (l' := l₁)
    (viewMulti M.toFieldModel sys.fri (v.shape M sys) arities)
    (mkTTM pm (fun i =>
      (pcsChalTensorMulti P W Mopen (powBitsMulti sys.fri arities) i
        (tAnsAt chals (4 + i))).2)
      (P.rounds + 2))
    (by rw [hmsg, hr, hβ, hq]; exact hrun) hl (M.baseRows (comOf sys v msgs))
    (fun b k mi d hd => by
      rw [congrFun hq k, msgAt_mkTTM, Nat.zero_min]
      exact hc b k mi d hd)
  rw [mapIdx_mkTTM] at hacc
  rw [ungrind_pcsTTensorMulti]
  refine acceptsTensorMulti_mkTTM_congr ?_ (fun k hk => ?_) hacc
  · show (P.read 0 (viewMulti M.toFieldModel sys.fri (v.shape M sys) arities (firstMessage
      (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs)))
      (M.baseRows (comOf sys v msgs))).claims = _
    rw [← h0]; rfl
  · show (P.read (k + 1) (viewMulti M.toFieldModel sys.fri (v.shape M sys) arities
      (rawAt msgs (4 + (k + 1)))) (comAt msgs (4 + (k + 1)))).word =
      (P.read (k + 1) (viewMulti M.toFieldModel sys.fri (v.shape M sys) arities (pm (k + 1)))
        (committedRow l₁)).word
    rw [hraw k (Nat.le_of_lt_succ hk)]
    rcases Nat.lt_or_ge k P.rounds with hlt | hge
    · exact ((P.read_word_of_lt hlt _ _).trans
        (congrArg (fun c => P.commitWord k (c (P.commitDims k) 0))
          (hw k hlt))).trans (P.read_word_of_lt hlt _ _).symm
    · obtain rfl : k = P.rounds := by omega
      exact (P.read_word_last _ _).trans (P.read_word_last _ _).symm

private theorem shard_goodTensorMulti_aux (M : StarkModel F EF K) (sys : System F D)
    (hcap : 0 < sys.fri.maxLogArity) (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap V θ B r l)
    {f : ∀ x, STAns F EF D K fslots slots width x}
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    {l' l₁ : Log (STAns F EF D K fslots slots width)}
    (hl₁ : l₁ <+: l) (hf : ∀ x y, l₁.dlookup x = some y → f x = y)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {ms : ℕ → RawMsg F EF D} {claims : Array (Array F)}
    (hhdr : pre.headers[V.shard (ms 2)]? =
      some ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    {shape : ClaimShape} (hsh : shape = starkShape sys M.extData.d proof.active proof.logDegrees)
    (htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F))
    {R : ℕ} (hR : R = (scheduleOfShape sys.fri shape).length)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hsup : Supports l₁ (fsTranscript f ms (4 + (R + 2))))
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D) {ζ : EF}
    (hβ : β = Function.surjInv M.surj (answer f ms 0).field)
    (hγ : γ = Function.surjInv M.surj (answer f ms 1).field)
    (hζ : ζ = Function.surjInv M.surj (answer f ms 3).field) (h0 : ms 0 = m0)
    (h2 : ms 2 = .ext γ :: (mid ++ secondMessage proof))
    (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof ζ)).toList.map .ext)
    (h5 : ∀ j, ms (5 + j) =
      messagesMulti sys.fri (scheduleOfShape sys.fri shape) #[] #[] #[] proof.openingProof (j + 1))
    (hs : UAtTensor ms s 2 (.ext γ :: mid) false 0 0) (hacc : acc = (claimsAccumulator β γ claims).2)
    (hcheck : checkAfterChallengesTensorMultiArity
      (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true)
    {b : Bool}
    {rT : TensorChal K (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)}
    {bF : ℕ → K} {idx : Fin sys.fri.numQueries → ℕ}
    (hrT : rT = tensorChalOfAns (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)
      (answer f ms 4))
    (hbF : ∀ i, bF i = if i < R then (answer f ms (5 + i)).field else 0)
    (hidx : ∀ k, idx k = (answer f ms (5 + R)).bits
      (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) (logMaxHeight sys.fri.logBlowup shape))
    (hrun : Outcome ((modelParamsMulti M.toFieldModel sys.fri shape (scheduleOfShape sys.fri shape)
        (M.wellFormed sys.fri shape htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).verifyWithTensor
      (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)
      (tensorCoordMulti sys.fri shape (scheduleOfShape sys.fri shape))
      (modelProofMulti M.toFieldModel sys.fri shape proof.openingProof)
      (fun j => viewMulti M.toFieldModel sys.fri shape (scheduleOfShape sys.fri shape)
        (messagesMulti sys.fri (scheduleOfShape sys.fri shape)
          ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
          (claimValues (openingClaims sys proof ζ)) proof.openingProof j)) rT bF idx) l' b l₁) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  have hr' : 4 + (R + 2) ≤ r := by
    have hle : R ≤ logMaxHeight sys.fri.logBlowup shape :=
      hR ▸ scheduleOfShape_length_le_logMaxHeight hcap
    omega
  have hd := sdoomedTensorMulti_of_goodLogTensorMulti hgood _ hr' (hsup.of_prefix hl₁)
  rw [fsTranscript_eq_mkTTM] at hd hsup
  obtain ⟨msgs, chals, hlen, hraw, hcom, hans, hment, hdl⟩ :
      ∃ (msgs : List (IMsg F EF D K)) (chals : List (UTensorAns K fslots slots width)),
        msgs.length = 4 + (R + 2) ∧ (∀ j < msgs.length, rawAt msgs j = ms j) ∧
        (∀ j < msgs.length, comAt msgs j = (readMsg B (ms j) (committedRow l)).2) ∧
        (∀ j < msgs.length, tAnsAt chals j = answer f ms j) ∧
        (∀ j < msgs.length, Mentions l₁ j (ms j)) ∧
        sdoomedTensorMultiL M sys hcap V θ B msgs chals := by
    have hlen := Transcript.length_msgs
      ((mkTTM (C := UTensorChal K fslots slots width) ms (answer f ms) (4 + (R + 2))).mapIdx
        (interpTensor B r l))
    exact ⟨_, _, hlen, fun j hj => rawAt_interpTensorM B r l ms _ (hlen ▸ hj),
      fun j hj => comAt_interpTensorM B r l ms _ (hlen ▸ hj) (by omega),
      fun j hj => by
        rw [mapIdx_mkTTM]
        exact tAnsAt_chalsOf_mkTTM _ _ (hlen ▸ hj),
      fun j hj => mentions_of_supports_mkTTM hsup j (hlen ▸ hj), hd⟩
  clear hd hsup
  have hfield : ∀ j < msgs.length, tFieldAt chals j = (answer f ms j).field := fun j hj =>
    congrArg UTensorAns.field (hans j hj)
  have hβ' : β = rep M (tFieldAt chals 0) := by rw [hβ, hfield 0 (by omega)]; rfl
  have hγ' : γ = rep M (tFieldAt chals 1) := by rw [hγ, hfield 1 (by omega)]; rfl
  have hζ' : ζ = rep M (tFieldAt chals 3) := by rw [hζ, hfield 3 (by omega)]; rfl
  have hα : rep M (tFieldAt chals 2) = Function.surjInv M.surj (answer f ms 2).field := by
    rw [hfield 2 (by omega)]; rfl
  subst hsh hR hrT hβ' hγ' hζ' hacc
  obtain rfl : bF = _ := funext hbF
  obtain rfl : idx = _ := funext hidx
  obtain ⟨_, hfinal, hz, hc, hrunf, hpowC, hpowQ⟩ := run_of_checkTensorMulti M sys hcap f proof
    hshape (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) _ _ _ hα hζ
    hs h2 h3 h4 h5 hcheck
  obtain rfl : b = true := (hrun.run_eq hf).symm.trans hrunf
  have hheight := logMaxHeight_starkShape_le hheightOk hshape M.extData.d
  have hmargin : ∀ m ∈ (starkShape sys M.extData.d proof.active proof.logDegrees).flatten,
      StrictMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ :=
    fun m hm => M.strictMargin_coset ((CertiFri.Exec.le_logMaxHeight hm).trans htwo) hθ
  have hactive : proof.active.size = sys.circuits.size := by
    have h := hshape
    simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1.2
  have hsv : Supported M sys θ (tViewOf M msgs chals
      ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) :=
    ⟨htwo, hfinal, hmargin, hactive, hheight⟩
  have hlen' : msgs.length = 4 + ((hsv.paramsMulti hcap).rounds + 2) := hlen
  have hv2 : proof.stage2Commit = (digestsIn (rawAt msgs 2)).getD 0 default := by
    rw [hraw 2 (by omega), h2, digestsIn_secondTM _ hmid proof]; rfl
  have hv3 : proof.quotientCommit = (digestsIn (rawAt msgs 3)).getD 0 default := by
    rw [hraw 3 (by omega), h3]; rfl
  have hva : proof.intermediateAccumulators = ((extsOf (rawAt msgs 2)).drop 1).toArray := by
    rw [hraw 2 (by omega), h2, extsOf_secondTM _ hmid proof]; rfl
  have hvals : valuesOf msgs =
      claimValues (openingClaims sys proof (rep M (tFieldAt chals 3))) := by
    rw [valuesOf, hraw 4 (by omega), h4, extsOf_map_extTM]
  have hcol : ¬ LogCollision hashObs l := not_logCollision_of_not_hasBad_hit hgood.2
  have hc0 : ∀ root, root = proof.stage1Commit ∨ sys.preprocessedCommit = some root →
      comAt msgs 0 root = committedRow l root := by
    intro root hroot
    rw [hcom 0 (by omega), h0]
    exact readMsg_snd_of_memTM B _ (hroot.elim (fun h => h ▸ hdig) (hdigFixed root))
  have hc2 : comAt msgs 2 ((digestsIn (rawAt msgs 2)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 2)).getD 0 default) := by
    rw [hcom 2 (by omega), hraw 2 (by omega)]
    exact readMsg_snd_of_memTM B _ (getD_zero_mem_digestsOfTM B
      (by rw [h2, digestsIn_secondTM _ hmid proof]; exact List.cons_ne_nil _ _))
  have hc3 : comAt msgs 3 ((digestsIn (rawAt msgs 3)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 3)).getD 0 default) := by
    rw [hcom 3 (by omega), hraw 3 (by omega)]
    exact readMsg_snd_of_memTM B _ (getD_zero_mem_digestsOfTM B
      (by rw [h3]; exact List.cons_ne_nil proof.quotientCommit []))
  have hcomOf : ∀ root, (root = proof.stage1Commit ∨ root = _ ∨ root = _ ∨
      sys.preprocessedCommit = some root) → comOf sys (tViewOf M msgs chals
        ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) msgs root =
        committedRow l root := fun root h => comOf_eqTM hc0 hc2 hc3 h
  obtain ⟨pm, hpm⟩ : ∃ pm : ℕ → RawMsg F EF D, pm = messagesMulti sys.fri
      (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
      ((openingClaims sys proof (rep M (tFieldAt chals 3))).map (·.commitment))
      (claimPoints (openingClaims sys proof (rep M (tFieldAt chals 3))))
      (claimValues (openingClaims sys proof (rep M (tFieldAt chals 3)))) proof.openingProof :=
    ⟨_, rfl⟩
  rw [← hpm] at hrun
  have hpm0 : pm 0 = firstMessage (ShardView.commitments sys (tViewOf M msgs chals
      ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩))
      (shapePoints (F := F) (starkShape sys M.extData.d proof.active proof.logDegrees)
        (rep M (tFieldAt chals 3))) (valuesOf msgs) := by
    rw [hpm]
    refine (ite_eq_left rfl).trans ?_
    rw [commitments_openingClaimsTM, claimPoints_openingClaims sys proof hshape, ← M.degree_eq,
      ← hvals, hv2, hv3]
    rfl
  have hpmraw : ∀ k ≤ (hsv.paramsMulti hcap).rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1) :=
    fun k hk => by
      rw [hraw _ (by omega), show 4 + (k + 1) = 5 + k by omega, h5 k, hpm]
      exact messagesMulti_succ_congr _ _ _ _ _ _ _ _ _ _
  have hpmmin : ∀ j, pm (min j ((hsv.paramsMulti hcap).rounds + 1)) = pm j := fun j => by
    rw [hpm]; exact messagesMulti_min _ _ _ _ _ _ j
  have hacc := accepts_pcsTTensorMulti hsv hcap pm (answer f ms) (fun j hj => hans j (by omega))
    hpmmin hpm0 hpmraw hrun (fun h => hcol (h.of_prefix hl₁))
    (fun b k mi d hd => by
      have hopen := ((hsv.paramsMulti hcap).outcome_verifyWithTensor hrun).1 b k
      rw [hpm0] at hopen ⊢
      have h := baseRows_of_opensTM M hl₁ hcol
        (hcomOf _ (mem_commitmentsTM (inputRoots_mem_commitmentsTM M _ _ _ _ b))) hopen hd
      have hle := Merkle.le_maxLogHeight
        (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hd))
      have hH := (hsv.paramsMulti hcap).height_le b
      rw [← Nat.shiftRight_add, show (hsv.paramsMulti hcap).n -
          Merkle.maxLogHeight ((hsv.paramsMulti hcap).dims b).toList +
        (Merkle.maxLogHeight ((hsv.paramsMulti hcap).dims b).toList - d.logHeight) =
          (hsv.paramsMulti hcap).n - d.logHeight by omega] at h
      exact h)
    (fun k hk => by
      have hj : 4 + (k + 1) < msgs.length := by omega
      have hms : ms (4 + (k + 1)) = pm (k + 1) := (hraw _ hj).symm.trans (hpmraw k hk.le)
      have hmem := getD_zero_mem_digestsOfTM B (m := pm (k + 1))
        (by rw [hpm]; exact digestsIn_messagesMulti_ne_nil _ _ _ _ _ _ hk)
      rw [hcom _ hj, hms]
      refine (readMsg_snd_of_memTM B _ hmem).trans ?_
      exact committedRow_of_mentionsTM B r hl₁ hgood.2 (hms ▸ hment _ hj) (by omega) hmem)
  have hpow : PowPasses (pcsTTensorMulti msgs chals hsv hcap
      ((hsv.paramsMulti hcap).rounds + 2)) := by
    refine (powPasses_pcsTTensorMulti hsv hcap _).mpr fun i hi => ?_
    rw [hans (4 + i) (by omega)]
    rcases i with _ | i
    · exact tBits_eq_zeroM _ _ (powBitsMulti_zero sys.fri _)
    · rcases Nat.lt_or_ge i (hsv.paramsMulti hcap).rounds with hlt | hge
      · refine (congrArg (UTensorAns.bits _ 0) (powBitsMulti_succ_of_lt sys.fri _ hlt)).trans ?_
        by_cases hb : sys.fri.commitPowBits = 0
        · exact tBits_eq_zeroM _ _ hb
        · have h := hpowC hb i hlt
          rwa [show 5 + i = 4 + (i + 1) by omega] at h
      · obtain rfl : i = (hsv.paramsMulti hcap).rounds := by omega
        refine (congrArg (UTensorAns.bits _ 0) (powBitsMulti_last sys.fri _)).trans ?_
        by_cases hb : sys.fri.queryPowBits = 0
        · exact tBits_eq_zeroM _ _ hb
        · have h : (answer f ms (5 + (hsv.paramsMulti hcap).rounds)).bits 0
              sys.fri.queryPowBits = 0 := hpowQ hb
          rwa [show 5 + (hsv.paramsMulti hcap).rounds =
            4 + ((hsv.paramsMulti hcap).rounds + 1) by omega] at h
  have hdec' : V.dec0 (rawAt msgs 0) = some pre := by rw [hraw 0 (by omega), h0]; exact hdec
  have e0 : M.ext.toModel (rep M (tFieldAt chals 0)) = tFieldAt chals 0 :=
    Function.surjInv_eq M.surj _
  have e1 : M.ext.toModel (rep M (tFieldAt chals 1)) = tFieldAt chals 1 :=
    Function.surjInv_eq M.surj _
  have hgl := good_of_sdoomedTensorMultiL hfixed hdl hdec' hpre
    (by rw [hraw 2 (by omega)]; exact hhdr) hsv hlen'
    (by
      rw [hvals]
      exact check_of_proofTM M sys _ proof rfl rfl hv2 hv3 hva rfl hshape hc hz)
    hpow hacc
  refine ⟨fun hfail => hgl ?_, fun hbal => ?_⟩
  · rw [e0, e1, hv2, hv3, hva] at hfail
    exact (constraintFail_congrSGM
      (baseRows_congrSGM M (hcomOf _ (.inl rfl)).symm)
      (baseRows_congrSGM M (hcomOf _ (.inr (.inl rfl))).symm)
      fun root hroot => baseRows_congrSGM M (hcomOf _ (.inr (.inr (.inr hroot)))).symm).mp hfail
  · rw [e0, e1]
    have h := balance_of_sdoomedTensorMultiL hdl hdec' hpre (by omega)
      (by rw [hcom 0 (by omega), h0]; exact hbal)
    rwa [hcom 0 (by omega), h0] at h

/-- **Deterministic multi-arity shard soundness from separated `deriveA` and `verifyWithTensor`
outcomes.** Shared directly by both unpruned `merkleMmcs` and pruned `prunedMmcs`! -/
theorem shard_goodTensorMulti_of_derive_verify (M : StarkModel F EF K) (sys : System F D)
    (hcap : 0 < sys.fri.maxLogArity) (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap V θ B r l)
    {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F))
    {l₀ l' l'' l₁ : Log (STAns F EF D K fslots slots width)}
    {t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds + 2))}
    {b : Bool}
    (hder : Outcome (deriveA (fun _ : HashQuery K D => D)
      (nextMsgTensorMulti M sys proof m0 mid)
      (4 + ((modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds + 2))) l₀ t l')
    (hl' : l' <+: l'')
    (hver : Outcome ((modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).verifyWithTensor
      (maxWidth (starkShape sys M.extData.d proof.active proof.logDegrees))
      (maxOpeningsPerHeight sys.fri.logBlowup
        (starkShape sys M.extData.d proof.active proof.logDegrees))
      (tensorCoordMulti sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)))
      (modelProofMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees) proof.openingProof)
      (fun j => viewMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (messagesMulti sys.fri
          (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
          ((openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))).map (·.commitment))
          (claimPoints (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
          (claimValues (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
          proof.openingProof j))
      (tensorChalOfAns (maxWidth (starkShape sys M.extData.d proof.active proof.logDegrees))
        (maxOpeningsPerHeight sys.fri.logBlowup
          (starkShape sys M.extData.d proof.active proof.logDegrees)) (tAnsAt (chalsOf t) 4))
      (fun i => if i < (modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds then tFieldAt (chalsOf t) (5 + i) else 0)
      (fun k => (tAnsAt (chalsOf t) (5 + (modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1)
        (modelParamsMulti M.toFieldModel sys.fri
          (starkShape sys M.extData.d proof.active proof.logDegrees)
          (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
          (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
          (scheduleOfShape_sum_le hcap)).n)) l'' b l₁)
    (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensorMulti M sys proof m0 mid 2
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = proof.active) (hstage1 : hdr.stage1Commit = proof.stage1Commit)
    (hlogs : hdr.logDegrees = proof.logDegrees)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensorMulti M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) s 2 (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensorMultiArity
      (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  obtain ⟨act, stage1, logs, claims⟩ := hdr
  dsimp only at hactive hstage1 hlogs hacc
  subst hactive hstage1 hlogs
  have hlast := tLastField_fsTranscriptAM f (nextMsgTensorMulti M sys proof m0 mid)
  have hfl₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y h =>
    hf x y (dlookup_of_prefix h hl₁)
  have hl'₁ : l' <+: l₁ := hl'.trans hver.prefix
  obtain rfl := hder.eq_fsTranscriptA fun x y h => hfl₁ x y (dlookup_of_prefix h hl'₁)
  have hsup := (supports_of_outcome_deriveA hder).of_prefix hl'₁
  rw [fsTranscriptA_eq_fsTranscript] at hsup
  let P := modelParamsMulti M.toFieldModel sys.fri
    (starkShape sys M.extData.d proof.active proof.logDegrees)
    (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
    (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
  have hP_rounds : P.rounds =
      (scheduleOfShape sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)).length := rfl
  have hans : ∀ j < 4 + (P.rounds + 2),
      tAnsAt (chalsOf (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) (4 + (P.rounds + 2)))) j =
        answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
          (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) j := fun j hj =>
    tAnsAt_chalsOf_fsTranscriptAM f _ hj
  have hfield : ∀ j < 4 + (P.rounds + 2),
      tFieldAt (chalsOf (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) (4 + (P.rounds + 2)))) j =
        (answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
          (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) j).field := fun j hj =>
    congrArg UTensorAns.field (hans j hj)
  refine shard_goodTensorMulti_aux M sys hcap V θ B r hfixed hheightOk hθ hgood proof m0 mid hmid
    hl₁ hfl₁ hdec hpre
    (ms := fun j => nextMsgTensorMulti M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j))
    hhdr hdig hdigFixed rfl htwo rfl hr hsup hshape β γ acc s hβ hγ
    (congrArg (rep M) (hfield 3 (by omega))) rfl ?_ rfl ?_ (fun j => ?_) hs hacc hcheck
    (congrArg (tensorChalOfAns _ _) (hans 4 (by omega)))
    (fun i => ite_congr rfl (fun hi => hfield (5 + i) (by omega)) fun _ => rfl)
    (fun k => congrArg (fun u : UTensorAns K fslots slots width => u.bits _ _)
      (hans (5 + P.rounds) (by omega)))
    hver
  · show Observation.ext (rep M (tLastField (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 2)))
      :: (mid ++ secondMessage proof) = _
    rw [hlast 1, hγ]; rfl
  · show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (tLastField
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 4))))).toList = _
    rw [hlast 3, hfield 3 (by omega)]
  · rw [Nat.add_comm 5 j]; rfl

/-- **An accepted unpruned multi-arity tensor STARK proof in a good log has no failing constraint.** -/
theorem shard_goodTensorMulti (M : StarkModel F EF K) (sys : System F D)
    (hcap : 0 < sys.fri.maxLogArity) (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap V θ B r l)
    {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    {l₀ l₁ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorMulti M sys proof m0 mid hcap) l₀ b l₁) (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensorMulti M sys proof m0 mid 2
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = proof.active) (hstage1 : hdr.stage1Commit = proof.stage1Commit)
    (hlogs : hdr.logDegrees = proof.logDegrees)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensorMulti M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) j)) s 2 (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensorMultiArity
      (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  have hlast := tLastField_fsTranscriptAM f (nextMsgTensorMulti M sys proof m0 mid)
  obtain ⟨htwo, -⟩ := run_of_checkTensorMulti M sys hcap f proof hshape
    (shape := starkShape sys M.extData.d proof.active proof.logDegrees)
    (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) β γ acc rfl rfl hs
    (show Observation.ext (rep M (tLastField (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 2)))
        :: (mid ++ secondMessage proof) = _ by
      rw [hlast 1, hγ]; rfl)
    rfl
    (show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (tLastField
        (fsTranscriptA f (nextMsgTensorMulti M sys proof m0 mid) 4))))).toList = _ by
      rw [hlast 3]; rfl)
    (fun j => by rw [Nat.add_comm 5 j]; rfl) hcheck
  unfold shardCompTensorMulti at hout
  rw [dite_eq_left htwo, outcome_bind] at hout
  obtain ⟨t, l', hder, hver⟩ := hout
  exact shard_goodTensorMulti_of_derive_verify M sys hcap V θ B r hfixed hheightOk hθ hgood hf
    proof m0 mid hmid htwo hder (List.prefix_refl l') hver hl₁ hdec hpre hhdr hactive hstage1 hlogs
    hdig hdigFixed hr hshape β γ acc s hβ hγ hs hacc hcheck

end ShardGoodMulti

/-! ## 4. Unpruned multi-arity STARK soundness (`verifyTensorMultiArity` & `verifyBatchTensorMultiArity`) -/

section UnprunedMulti

variable (M : StarkModel F EF K) (sys : System F D) (hcap : 0 < sys.fri.maxLogArity)
  (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyTensorMultiArity` against an oracle (unpruned `merkleMmcs`).** -/
noncomputable def verifyTensorMultiArityAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : SAttempt F EF D) : Bool :=
  Stark.verifyTensorMultiArity (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a.claims a.proof

/-- Soundness experiment for `Stark.verifyTensorMultiArity` (unpruned `merkleMmcs`). -/
noncomputable def experimentTensorMultiStark {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → SAttempt F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardCompTensorMulti M sys (attempt a).proof
      (firstMessage sys (attempt a).proof (attempt a).claims) [] hcap).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_experimentTensorMultiStark {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    (experimentTensorMultiStark M sys hcap adv attempt).QueryBound
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    (queryBound_shardCompTensorMulti_twoAdicity M sys _ _ _ hcap).bind fun _ =>
      queryBound_pure _ 0

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerOk_of_shapeOkTM {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true)
    {claims : Array (Array F)} (hclaims : claims.size ≤ B.claims)
    (hlen : ∀ c ∈ claims, c.size ≤ B.len) :
    HeaderOk sys B ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩ := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, hlogs⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hact⟩ := hshape
  refine ⟨hsize, hlogs, fun pos => ?_, hclaims, hlen⟩
  show proof.logDegrees.getD pos 0 ≤ sys.maxLogDegree
  by_cases hpos : pos < (activeIndices proof.active).length
  · have hmem : ((activeIndices proof.active)[pos], pos) ∈ (activeIndices proof.active).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem hpos
    exact (hact _ hmem).1.1.1.1.1.1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    exact Nat.zero_le _

theorem verifyTensorMultiArity_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttempt F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorMulti M sys a.proof (firstMessage sys a.proof a.claims) [] hcap)
      l₀ b l)
    (hacc : verifyTensorMultiArityAccepts M sys f a = true) (hcov : Covered B a) :
    ¬ ViolatesTensor M sys θ l f a ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩)).eval
            (Polynomial.C (M.ext.toModel (lookupOfTensor M sys f a).1))).eval
          (M.ext.toModel (lookupOfTensor M sys f a).2) ≠ 0) := by
  simp only [verifyTensorMultiArityAccepts, Stark.verifyTensorMultiArity, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, -⟩, -, hcheck⟩ := hacc
  have hhdr := headerOk_of_shapeOkTM sys B hshape hcov.claims hcov.claim_len
  have hdec : (singleVariant (EF := EF) sys B).dec0 (firstMessage sys a.proof a.claims) =
      some ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ := by
    rw [firstMessage_eq]
    exact singleVariant_dec0 M.base hN hcast hhdr
  have hpre : PreOk sys B
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ :=
    ⟨hshards, fun h hh => by rwa [List.mem_singleton.mp (Array.mem_toList_iff.mpr hh)],
      Nat.zero_le _, fun m hm => absurd hm (Array.not_mem_empty m)⟩
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  have a0 : UAtTensor (fun j => nextMsgTensorMulti M sys a.proof
        (firstMessage sys a.proof a.claims) [] j
        (fsTranscriptA f (nextMsgTensorMulti M sys a.proof (firstMessage sys a.proof a.claims) []) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims)) 0 (firstMessage sys a.proof a.claims) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (firstMessage sys a.proof a.claims)
    (ms := fun j => nextMsgTensorMulti M sys a.proof (firstMessage sys a.proof a.claims) [] j
      (fsTranscriptA f (nextMsgTensorMulti M sys a.proof (firstMessage sys a.proof a.claims) []) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  exact shard_goodTensorMulti M sys hcap (singleVariant sys B) θ B (maxRounds F) hfixed hheightOk
    hθ hgood hf a.proof (firstMessage sys a.proof a.claims) []
    (fun o ho => absurd ho List.not_mem_nil) hout (List.prefix_refl l) hdec hpre
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩) rfl rfl rfl rfl
    (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self)
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyTensorMultiArity` (unpruned `merkleMmcs`).** -/
theorem soundness_verifyTensorMultiArity_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorMultiArityAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ViolatesTensor M sys (1 - δ) l f (attempt out.1))
      (experimentTensorMultiStark M sys hcap adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := singleVariant sys B) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorMultiStark M sys hcap hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyTensorMultiArity_good M sys hcap (1 - δ) B hfixed hheightOk hshards hN hcast
    (by linarith) hgood hf (attempt a) hcomp hacc hcov).1 hviol

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyTensorMultiArity`.** -/
theorem soundness_verifyTensorMultiArity_lookups_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorMultiArityAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ¬ LookupsBalancedTensor M sys (1 - δ) B l (attempt out.1))
      (experimentTensorMultiStark M sys hcap adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := singleVariant sys B) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorMultiStark M sys hcap hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hviol, hbal⟩ := verifyTensorMultiArity_good M sys hcap (1 - δ) B hfixed hheightOk
    hshards hN hcast (by linarith) hgood hf (attempt a) hcomp hacc hcov
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  simp only [verifyTensorMultiArityAccepts, Stark.verifyTensorMultiArity, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, hres⟩, hclaims, -⟩ := hacc
  have hitems : allItems M sys (1 - δ)
      (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
        (committedRow l)).2)
      ⟨#[⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
        (attempt a).claims⟩], #[]⟩ =
      headerItems M sys (1 - δ)
        (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
          (committedRow l)).2)
        ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
          (attempt a).claims⟩ := by
    rw [allItems]; exact (List.append_nil _).trans (List.flatMap_singleton _ _)
  rw [hitems] at hne hsum
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards (attempt a).proof (attempt a).claims
  have hlast := toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l))
    (hdr := ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit,
      (attempt a).proof.logDegrees, (attempt a).claims⟩)
    (β := (lookupOfTensor M sys f (attempt a)).1)
    (γ := (lookupOfTensor M sys f (attempt a)).2)
    hplain h2 hshape rfl rfl rfl
    (baseRows_readMsgT M B _ (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self))
    (fun root hroot => baseRows_readMsgT M B _
      (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
    htwo hclaims hviol hne
  exact hsum (hlast.symm.trans (((M.ext.beq_iff _ _).mp hres).trans M.ext.map_zero))

/-- **`Stark.verifyBatchTensorMultiArity` against an oracle (unpruned `merkleMmcs`).** -/
noncomputable def batchTensorMultiArityAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : BAttempt F EF D) : Bool :=
  Stark.verifyBatchTensorMultiArity (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a

/-- Sequential verification of unpruned multi-arity shards. -/
noncomputable def shardsCompTensorMulti (m0 : RawMsg F EF D) :
    List (Proof F EF D (Array (List D)) (Array (List D))) → ℕ →
      OracleComp (STAns F EF D K fslots slots width) Bool
  | [], _ => .pure true
  | proof :: rest, i =>
    (shardCompTensorMulti M sys proof m0 [observeNat i] hcap).bind fun b =>
      (shardsCompTensorMulti m0 rest (i + 1)).bind fun b' => .pure (b && b')

/-- Soundness experiment for `Stark.verifyBatchTensorMultiArity` (unpruned `merkleMmcs`). -/
noncomputable def batchExperimentTensorMultiStark {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → BAttempt F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardsCompTensorMulti M sys hcap (batchFirstMessage sys (attempt a).preamble)
      ((attempt a).proofs.toList.take B.shards) 0).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
private theorem queryBound_shardsCompTensorMulti (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i : ℕ) :
    (shardsCompTensorMulti (fslots := fslots) (slots := slots) (width := width)
      M sys hcap m0 proofs i).QueryBound
      (proofs.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  induction proofs generalizing i with
  | nil => exact queryBound_pure _ _
  | cons proof rest ih =>
    have h : (shardsCompTensorMulti (fslots := fslots) (slots := slots) (width := width)
        M sys hcap m0 (proof :: rest) i).QueryBound
        (shardQueries sys (TwoAdicOps.twoAdicity (F := F)) +
          (rest.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
      (queryBound_shardCompTensorMulti_twoAdicity M sys proof m0 _ hcap).bind fun _ =>
        (ih (i + 1)).bind fun _ => queryBound_pure _ _
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_batchExperimentTensorMultiStark {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    (batchExperimentTensorMultiStark M sys hcap B adv attempt).QueryBound
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    ((queryBound_shardsCompTensorMulti M sys hcap _ _ 0).mono
      (Nat.mul_le_mul_right _ (List.length_take_le _ _))).bind fun _ => queryBound_pure _ 0

private theorem outcome_shardsCompTensorMulti (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i₀ : ℕ)
    {l l' : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (h : Outcome (shardsCompTensorMulti M sys hcap m0 proofs i₀) l b l') (k : ℕ)
    {proof : Proof F EF D (Array (List D)) (Array (List D))} (hk : proofs[k]? = some proof) :
    ∃ (l₀ : Log (STAns F EF D K fslots slots width)) (b' : Bool)
      (l₁ : Log (STAns F EF D K fslots slots width)),
      Outcome (shardCompTensorMulti M sys proof m0 [observeNat (i₀ + k)] hcap) l₀ b' l₁ ∧
        l₁ <+: l' := by
  induction proofs generalizing i₀ l b k with
  | nil => exact absurd hk (by simp)
  | cons p rest ih =>
    rw [shardsCompTensorMulti] at h
    obtain ⟨b₁, l₁, h₁, h⟩ := outcome_bind.mp h
    obtain ⟨b₂, l₂, h₂, h₃⟩ := outcome_bind.mp h
    obtain ⟨-, rfl⟩ := h₃
    cases k with
    | zero =>
      obtain rfl : p = proof := by simpa using hk
      exact ⟨l, b₁, l₁, h₁, h₂.prefix⟩
    | succ k =>
      obtain ⟨l₀, b', l₁', h', hp⟩ := ih (i₀ + 1) h₂ k (by simpa using hk)
      have e : i₀ + 1 + k = i₀ + (k + 1) := by omega
      rw [e] at h'
      exact ⟨l₀, b', l₁', h', hp⟩

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerOk_of_shardOkTM {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true)
    {hdr : ShardHeader F D} (hactive : hdr.active = proof.active)
    (hlogs : hdr.logDegrees = proof.logDegrees) (hclaims : hdr.claims.size ≤ B.claims)
    (hlen : ∀ c ∈ hdr.claims, c.size ≤ B.len) : HeaderOk sys B hdr := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, hlogs'⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hact⟩ := hshape
  refine ⟨by rw [hactive]; exact hsize, by rw [hlogs, hactive]; exact hlogs', fun pos => ?_,
    hclaims, hlen⟩
  rw [hlogs]
  by_cases hpos : pos < (activeIndices proof.active).length
  · have hmem : ((activeIndices proof.active)[pos], pos) ∈ (activeIndices proof.active).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      exact List.getElem?_eq_getElem hpos
    exact (hact _ hmem).1.1.1.1.1.1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none]
    exact Nat.zero_le _

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
theorem shardOkTensorMultiArity_of_batchAccepts {f : ∀ x, STAns F EF D K fslots slots width x}
    {a : BAttempt F EF D} (hacc : batchTensorMultiArityAccepts M sys f a = true) :
    a.preamble.headers.size = a.proofs.size ∧
      ∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (Array (List D)) (Array (List D))),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        Stark.shapeOk sys proof = true ∧ hdr.active = proof.active ∧
          hdr.stage1Commit = proof.stage1Commit ∧ hdr.logDegrees = proof.logDegrees ∧
          checkAfterChallengesTensorMultiArity
            (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (merkleMmcs (friHasher M.toFieldModel (hasherOf f)))
            (uChallengerTensor f M.toFieldModel) sys proof
            ((uChallengerTensor f M.toFieldModel).observe
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.2 (observeNat i))
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).1
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).2.1
            (claimsAccumulator
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).1
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.1 hdr.claims).2 = true := by
  simp only [batchTensorMultiArityAccepts, Stark.verifyBatchTensorMultiArity, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hacc
  obtain ⟨⟨-, hsz⟩, ⟨-, hall⟩, -⟩ := hacc
  refine ⟨hsz, fun i hdr proof hhdr hproof => ?_⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensorMultiArity, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, -, hcheck⟩ := h
  exact ⟨hshape, hactive, hstage1, hlogs, hcheck⟩

theorem verifyBatchTensorMultiArity_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttempt F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardsCompTensorMulti M sys hcap (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchTensorMultiArityAccepts M sys f a = true) (hcov : BatchCovered B a) {i : ℕ}
    {hdr : ShardHeader F D} {proof : Proof F EF D (Array (List D)) (Array (List D))}
    (hhdr : a.preamble.headers[i]? = some hdr) (hproof : a.proofs[i]? = some proof) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit
        (M.ext.toModel (batchLookupOfTensor M sys f a).1)
        (M.ext.toModel (batchLookupOfTensor M sys f a).2)
        (M.ext.toModel (claimsAccumulator (batchLookupOfTensor M sys f a).1
          (batchLookupOfTensor M sys f a).2 hdr.claims).2)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble)).eval
            (Polynomial.C (M.ext.toModel (batchLookupOfTensor M sys f a).1))).eval
          (M.ext.toModel (batchLookupOfTensor M sys f a).2) ≠ 0) := by
  obtain ⟨hsz, hall⟩ := shardOkTensorMultiArity_of_batchAccepts M sys hacc
  obtain ⟨hshape, hactive, hstage1, hlogs, hcheck⟩ := hall i hdr proof hhdr hproof
  have hmem : hdr ∈ a.preamble.headers := Array.mem_of_getElem? hhdr
  have hi : i < B.shards :=
    lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hhdr).1 hcov.shards
  have hpre : PreOk sys B a.preamble := by
    refine ⟨hcov.shards, fun h hh => ?_, hcov.messages, hcov.message_len⟩
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hh
    have hklt : k < a.proofs.size := hsz ▸ (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨hshape', hactive', -, hlogs', -⟩ :=
      hall k h a.proofs[k] hk (Array.getElem?_eq_getElem hklt)
    exact headerOk_of_shardOkTM sys B hshape' hactive' hlogs' (hcov.claims h hh).1
      (hcov.claims h hh).2
  have hdec := batchVariant_dec0 (EF := EF) M.base hN hcast hpre
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hk : (a.proofs.toList.take B.shards)[i]? = some proof := by
    rw [List.getElem?_take_of_lt hi, Array.getElem?_toList]; exact hproof
  obtain ⟨l₀', b', l₁, hcomp, hl₁⟩ := outcome_shardsCompTensorMulti M sys hcap _ _ 0 hout i hk
  rw [Nat.zero_add] at hcomp
  have a0 : UAtTensor (fun j => nextMsgTensorMulti M sys proof
        (batchFirstMessage sys a.preamble) [observeNat i] j
        (fsTranscriptA f
          (nextMsgTensorMulti M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble)) 0 (batchFirstMessage sys a.preamble) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (batchFirstMessage sys a.preamble)
    (ms := fun j => nextMsgTensorMulti M sys proof (batchFirstMessage sys a.preamble) [observeNat i] j
      (fsTranscriptA f
        (nextMsgTensorMulti M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  have hs' := hs.observe f M.toFieldModel (observeNat i)
  have hshard : (batchVariant (EF := EF) sys B N).shard
      (nextMsgTensorMulti M sys proof (batchFirstMessage sys a.preamble) [observeNat i] 2
        (fsTranscriptA f
          (nextMsgTensorMulti M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) 2)) = i :=
    batchVariant_shard M.base sys B hcast _ (hi.le.trans hN.shards) _
  exact shard_goodTensorMulti M sys hcap (batchVariant sys B N) θ B (maxRounds F) hfixed hheightOk
    hθ hgood hf proof (batchFirstMessage sys a.preamble) [observeNat i]
    (fun o ho => ⟨_, List.mem_singleton.mp ho⟩) hcomp hl₁ hdec hpre (hdr := hdr)
    (by rw [hshard]; exact hhdr) hactive hstage1 hlogs
    (by
      rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩))
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs' rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyBatchTensorMultiArity` (unpruned).** -/
theorem soundness_verifyBatchTensorMultiArity_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorMultiArityAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          BatchViolatesTensor M sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStark M sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := batchVariant sys B N) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorMultiStark M sys hcap B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, i, hdr, proof, hhdr, hproof, hfail⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyBatchTensorMultiArity_good M sys hcap (1 - δ) B hfixed hheightOk hN hcast
    (by linarith) hgood hf (attempt a) hcomp hacc hcov hhdr hproof).1 hfail

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyBatchTensorMultiArity`.** -/
theorem soundness_verifyBatchTensorMultiArity_lookups_ud [Fintype K] [Fintype D] {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorMultiArityAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalancedTensor M sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStark M sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := batchVariant sys B N) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorMultiStark M sys hcap B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  have hacc' := hacc
  simp only [batchTensorMultiArityAccepts, Stark.verifyBatchTensorMultiArity, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hacc'
  obtain ⟨⟨hne0, hsz⟩, ⟨hmsgs, hall⟩, hfold⟩ := hacc'
  have hpos0 : 0 < (attempt a).preamble.headers.size :=
    Nat.pos_of_ne_zero (by simpa using hne0)
  obtain ⟨-, hbal⟩ := verifyBatchTensorMultiArity_good M sys hcap (1 - δ) B hfixed hheightOk hN
    hcast (by linarith) hgood hf (attempt a) hcomp hacc hcov
    (Array.getElem?_eq_getElem hpos0) (Array.getElem?_eq_getElem (hsz ▸ hpos0))
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  obtain ⟨-, hinit⟩ := messagesAccumulator_model M (batchLookupOfTensor M sys f (attempt a)).1
    (batchLookupOfTensor M sys f (attempt a)).2 _ hmsgs
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards (pre := (attempt a).preamble)
  have hshard_res : ∀ (i : ℕ) (hdr : ShardHeader F D)
      (proof : Proof F EF D (Array (List D)) (Array (List D))),
      (attempt a).preamble.headers.toList[i]? = some hdr →
      (attempt a).proofs.toList[i]? = some proof →
      M.ext.toModel (Stark.residual proof) =
        lookupSum (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).1)
          (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).2)
          (headerItems M sys (1 - δ)
            (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
              (committedRow l)).2) hdr) := by
    intro i hdr proof hhdr hproof
    rw [Array.getElem?_toList] at hhdr hproof
    have hmem : ((hdr, proof), i) ∈
        ((attempt a).preamble.headers.toList.zip (attempt a).proofs.toList).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
        Array.getElem?_toList]
      exact ⟨hhdr, hproof⟩
    have hs := hall _ hmem
    simp only [Stark.shardOkTensorMultiArity, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, hclaims, -⟩ := hs
    have hcf := (verifyBatchTensorMultiArity_good M sys hcap (1 - δ) B hfixed hheightOk hN hcast
      (by linarith) hgood hf (attempt a) hcomp hacc hcov hhdr hproof).1
    have hmem_hdr : hdr ∈ (attempt a).preamble.headers.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? hhdr)
    exact toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l))
      hplain h2 hshape hactive hstage1 hlogs
      (baseRows_readMsgT M B _ (by
        rw [hdigs, ← hstage1]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨hdr, hmem_hdr, rfl⟩)))
      (fun root hroot => baseRows_readMsgT M B _
        (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
      htwo hclaims hcf fun it hit =>
        hne it (by rw [allItems]; exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨hdr, hmem_hdr, hit⟩))
  have hfl := toModel_foldl_residualT M (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).1)
    (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).2)
    (headerItems M sys (1 - δ)
      (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
        (committedRow l)).2))
    (attempt a).preamble.headers.toList (attempt a).proofs.toList hsz hshard_res
    (messagesAccumulator (batchLookupOfTensor M sys f (attempt a)).1
      (batchLookupOfTensor M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2
  have hzero : M.ext.toModel ((attempt a).proofs.foldl (fun total proof => total + Stark.residual proof)
      (messagesAccumulator (batchLookupOfTensor M sys f (attempt a)).1
        (batchLookupOfTensor M sys f (attempt a)).2
        ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2) = 0 :=
    ((M.ext.beq_iff _ _).mp hfold).trans M.ext.map_zero
  rw [Array.foldl_toList] at hfl
  rw [hfl, hinit] at hzero
  have hmap : ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity)).map
      (fun msg => (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) =
      (attempt a).preamble.messages.toList.map fun m =>
        (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel) := by
    rw [List.map_map]; rfl
  rw [hmap] at hzero
  rw [allItems, lookupSum_append, add_comm] at hsum
  exact hsum hzero

end UnprunedMulti

/-! ## 5. Pruned-MMCS (`CertiFri.P3.prunedMmcs`) multi-arity STARK soundness -/

section PrunedMulti

variable (M : StarkModel F EF K) (sys : System F D) (hcap : 0 < sys.fri.maxLogArity)

/-- Monadic multi-arity path restoration for one pruned STARK shard: restores the
unpruned per-query authentication paths for every input batch and every variable-arity
folding round (`P.commitDims i = #[⟨2 ^ P.logArity i, P.n - P.cum (i + 1)⟩]`). -/
noncomputable def restoreShardPathsMultiM
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F))
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds + 2))) :
    OracleComp (STAns F EF D K fslots slots width)
      (Option (Array (Array (List D)) × Array (Array (List D)))) :=
  let shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
  let arities := scheduleOfShape sys.fri shape
  let P := modelParamsMulti M.toFieldModel sys.fri shape arities (M.wellFormed sys.fri _ htwo)
    (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
  let W := maxWidth shape
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  let p0 := pproof.withPaths #[] #[]
  let pf0 := modelProofMulti M.toFieldModel sys.fri shape p0.openingProof
  let ζ := rep M (tFieldAt (chalsOf t) 3)
  let msg0 := viewMulti M.toFieldModel sys.fri shape arities
    (messagesMulti sys.fri arities
      ((openingClaims sys pproof ζ).map (·.commitment))
      (claimPoints (openingClaims sys pproof ζ))
      (claimValues (openingClaims sys pproof ζ))
      pproof.openingProof 0)
  let rT := tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4)
  let βM := fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0
  let idxM : Fin P.queries → ℕ := fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
    (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n
  (mapM_oc (fun b : Fin P.batches =>
      let pruned := match pproof.openingProof.inputOpenings[b.val]? with
        | some o => o.openingProof
        | none => ⟨#[]⟩
      restorePathsM (Msg := RawMsg F EF D) (Chal := UTensorChal K fslots slots width)
        (P.dims b)
        (Array.ofFn fun k : Fin P.queries =>
          idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
        (Array.ofFn (pf0.inputRows b))
        pruned)
    (List.finRange P.batches)).bind fun inOpts =>
    (mapM_oc (fun i : ℕ =>
        let pruned := match pproof.openingProof.commitPhaseOpenings[i]? with
          | some o => o.openingProof
          | none => ⟨#[]⟩
        restorePathsM (Msg := RawMsg F EF D) (Chal := UTensorChal K fslots slots width)
          (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[P.commitRowTensor W Mopen (tensorCoordMulti sys.fri shape arities)
                pf0 msg0 rT βM (idxM k) k i])
          pruned)
      (List.range P.rounds)).bind fun comOpts =>
      match inOpts.mapM id, comOpts.mapM id with
      | some inL, some comL => .pure (some (inL.toArray, comL.toArray))
      | _, _ => .pure none

/-- **Oracle queries of verifying one pruned multi-arity tensor STARK shard:**
`deriveA`, then `restoreShardPathsMultiM`, then `Compiled.MultiParams.verifyWithTensor`. -/
noncomputable def shardCompTensorMultiPruned
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D) :
    OracleComp (STAns F EF D K fslots slots width) Bool :=
  if h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F) then
    let shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
    let arities := scheduleOfShape sys.fri shape
    let P := modelParamsMulti M.toFieldModel sys.fri shape arities (M.wellFormed sys.fri _ h)
      (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
    (deriveA (fun _ : HashQuery K D => D)
      (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) (4 + (P.rounds + 2))).bind fun t =>
      (restoreShardPathsMultiM M sys hcap pproof h t).bind fun opt =>
        match opt with
        | some (inPaths, comPaths) =>
          let proof := pproof.withPaths inPaths comPaths
          P.verifyWithTensor W Mopen (tensorCoordMulti sys.fri shape arities)
            (modelProofMulti M.toFieldModel sys.fri shape proof.openingProof)
            (fun j => viewMulti M.toFieldModel sys.fri shape arities
              (messagesMulti sys.fri arities
                ((openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))).map (·.commitment))
                (claimPoints (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
                (claimValues (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
                proof.openingProof j))
            (tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4))
            (fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0)
            (fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
              (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n)
        | none => .pure false
  else .pure false

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem queryBound_restoreShardPathsMultiM
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F))
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).rounds + 2))) :
    (restoreShardPathsMultiM M sys hcap pproof htwo t).QueryBound
      (modelParamsMulti M.toFieldModel sys.fri
        (starkShape sys M.extData.d pproof.active pproof.logDegrees)
        (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
        (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
        (scheduleOfShape_sum_le hcap)).verifierQueries := by
  unfold restoreShardPathsMultiM
  dsimp only
  set P := modelParamsMulti M.toFieldModel sys.fri
    (starkShape sys M.extData.d pproof.active pproof.logDegrees)
    (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
    (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
  refine (QueryBound.bind
    (n := P.batches * (P.queries * (3 * P.n + 1)))
    (m := P.rounds * (P.queries * (3 * P.n + 1)) + 0)
    ?_ fun inOpts =>
      QueryBound.bind (n := P.rounds * (P.queries * (3 * P.n + 1))) (m := 0)
        ?_ fun comOpts => ?_).mono ?_
  · refine (queryBound_mapM_oc (q := P.queries * (3 * P.n + 1))
      (fun b => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        have hle := P.height_le b
        dsimp only [P] at hle ⊢
        exact Nat.mul_le_mul_left _ (by omega))
      (List.finRange _)).mono ?_
    rw [List.length_finRange]
  · refine (queryBound_mapM_oc (q := P.queries * (3 * P.n + 1))
      (fun i => by
        refine (queryBound_restorePathsM _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        have hdim : Merkle.maxLogHeight (P.commitDims i).toList ≤ P.n := by
          simp only [Compiled.MultiParams.commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        dsimp only [P] at hdim ⊢
        exact Nat.mul_le_mul_left _ (by omega))
      (List.range _)).mono ?_
    rw [List.length_range]
  · split <;> exact queryBound_pure _ 0
  · dsimp only [P]; simp only [Compiled.MultiParams.verifierQueries]; ring_nf; omega

omit [DecidableEq F] [DecidableEq EF] in
/-- Multi-arity pruned verification satisfies the exact same `shardQueriesPruned` bound. -/
theorem queryBound_shardCompTensorMultiPruned
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D) :
    (shardCompTensorMultiPruned (fslots := fslots) (slots := slots) (width := width)
      M sys hcap pproof m0 mid).QueryBound
      (shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) := by
  unfold shardCompTensorMultiPruned
  split
  · next h =>
    dsimp only
    let P := modelParamsMulti M.toFieldModel sys.fri
      (starkShape sys M.extData.d pproof.active pproof.logDegrees)
      (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
      (M.wellFormed sys.fri _ h) (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
    have hrounds : P.rounds ≤ TwoAdicOps.twoAdicity (F := F) := P.rounds_le.trans h
    have hbatches : P.batches ≤ 4 :=
      length_starkShape_leTM sys M.extData.d pproof.active pproof.logDegrees
    have hvq : P.verifierQueries ≤
        (4 + TwoAdicOps.twoAdicity (F := F)) *
          (sys.fri.numQueries * (3 * TwoAdicOps.twoAdicity (F := F) + 1)) := by
      unfold Compiled.MultiParams.verifierQueries
      exact Nat.mul_le_mul (Nat.add_le_add hbatches hrounds)
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 3 h) 1))
    refine QueryBound.mono
      (QueryBound.bind (m := P.verifierQueries + P.verifierQueries)
        (queryBound_deriveA _ _) fun t =>
          QueryBound.bind (m := P.verifierQueries)
            (queryBound_restoreShardPathsMultiM M sys hcap pproof h t) fun opt => ?_) ?_
    · cases opt with
      | none => exact queryBound_pure _ P.verifierQueries
      | some ps => exact Compiled.MultiParams.queryBound_verifyWithTensor _ _ _ _ _ _ _ _ _
    · dsimp only [P] at hrounds hvq ⊢
      unfold shardQueriesPruned
      omega
  · exact queryBound_pure _ _

/-! ### Unpruning refinement for `checkAfterChallengesTensorMultiArity` with `prunedMmcs` -/

omit [FieldOps EF] [ExtensionOps F EF] [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_friShapeOkMultiArity (arities : List ℕ) (params : FriParams)
    (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (inPaths comPaths : Array (Array (List D))) :
    Fri.shapeOkMultiArity (F := F) arities params shape commitments points values
        (pproof.withPaths inPaths comPaths).openingProof =
      Fri.shapeOkMultiArity (F := F) arities params shape commitments points values
        pproof.openingProof := by
  unfold Fri.shapeOkMultiArity
  dsimp only
  simp only [Proof.withPaths, Array.size_mapIdx]
  refine congrArg₂ (· && ·) (congrArg₂ (· && ·) (congrArg₂ (· && ·) ?_ rfl) rfl) ?_
  · refine congrArg₂ (· && ·) rfl (congrArg (List.all _) (funext fun i => ?_))
    rw [Array.getElem?_mapIdx]
    cases pproof.openingProof.commitPhaseOpenings[i]? <;> rfl
  · refine congrArg (List.all _) (funext fun b => ?_)
    rw [Array.getElem?_mapIdx]
    cases pproof.openingProof.inputOpenings[b]? <;> rfl

omit [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_queryResultTensorMulti (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (points values : Array EF)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (inPaths comPaths : Array (Array (List D))) (ch : TensorChallenges EF) (t : ℕ) :
    queryResultTensorMulti (F := F) params shape arities points values
        (pproof.withPaths inPaths comPaths).openingProof ch t =
      queryResultTensorMulti (F := F) params shape arities points values
        pproof.openingProof ch t := by
  have hqr : Fri.queryRows (pproof.withPaths inPaths comPaths).openingProof t =
      Fri.queryRows pproof.openingProof t := by
    unfold Fri.queryRows
    simp only [Proof.withPaths]
    apply Array.ext
    · simp
    · intro i hi1 hi2
      simp [Array.getElem_map, Array.getElem_mapIdx]
  have hsib : (fun i => Fri.siblingsMulti (pproof.withPaths inPaths comPaths).openingProof i t) =
      (fun i => Fri.siblingsMulti pproof.openingProof i t) := by
    funext i
    unfold Fri.siblingsMulti
    simp only [Proof.withPaths, Array.getElem?_mapIdx]
    cases pproof.openingProof.commitPhaseOpenings[i]? <;> rfl
  unfold queryResultTensorMulti Fri.checkQueryTensorMulti
  rw [hqr, hsib]
  rfl

private lemma mapM_id_eq_some_of_forallM {α : Type*} (l : List (Option α)) (r : List α)
    (hlen : l.length = r.length)
    (h : ∀ i (hi : i < r.length), l[i]'(hlen ▸ hi) = some r[i]) :
    l.mapM id = some r := by
  induction l generalizing r with
  | nil =>
    cases r with
    | nil => rfl
    | cons _ _ => cases hlen
  | cons a as ih =>
    cases r with
    | nil => cases hlen
    | cons b bs =>
      have h0 : a = some b := h 0 (Nat.zero_lt_succ _)
      subst h0
      have htail := ih bs (Nat.succ.inj hlen) fun i hi => h (i + 1) (Nat.succ_lt_succ hi)
      simp only [List.mapM_cons, id_eq, Option.bind_eq_bind, Option.bind_some, htail,
        Option.pure_def]

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private lemma withPaths_nextMsgTensorMulti (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (m0 mid : RawMsg F EF D) (inPaths comPaths : Array (Array (List D))) :
    nextMsgTensorMulti (fslots := fslots) (slots := slots) (width := width) M sys
        (pproof.withPaths inPaths comPaths) m0 mid =
      nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid := by
  funext i t
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
          cases i with
          | zero => rfl
          | succ j => rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem commitChecksMulti_of_open (friMmcs : Mmcs EF D) {numQueries n : ℕ}
    {arities : List ℕ} {commits : Array D}
    {openings : Array (CommitPhaseStep EF friMmcs.MultiProof)}
    {indices : Array ℕ} {rows : Array (List (Array EF))}
    (h : ∀ i < arities.length,
      ∃ (root : D) (o : CommitPhaseStep EF friMmcs.MultiProof),
        commits[i]? = some root ∧ openings[i]? = some o ∧
        friMmcs.verifyMultiBatch root #[⟨2 ^ arities.getD i 1, n - cumLogArity arities (i + 1)⟩]
          (Array.ofFn (n := numQueries) fun t => indices.getD t.val 0 >>> cumLogArity arities (i + 1))
          (Array.ofFn (n := numQueries) fun t => #[(rows.getD t.val []).getD i #[]])
          o.openingProof = true) :
    commitChecksMulti friMmcs numQueries n arities commits openings indices rows = true := by
  simp only [commitChecksMulti, List.all_eq_true, List.mem_range]
  intro i hi
  obtain ⟨root, o, hroot, ho, hv⟩ := h i hi
  rw [hroot, ho]
  exact hv

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
private theorem unprune_verifyWithTensorMulti_pruned
    (f : ∀ x, STAns F EF D K fslots slots width x)
    (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    (htwo : logMaxHeight params.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F))
    (coms : Array D) (pts vals : Array EF)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D))
    (ch : TensorChallenges EF)
    (msgM : ℕ → Compiled.Msg K D shape.length)
    (rT : PcsRbr.TensorChal K (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape))
    (βM : ℕ → K)
    (idxM : Fin (modelParamsMulti M.toFieldModel params shape arities
      (M.wellFormed params shape htwo) hpos hsum).queries → ℕ)
    (hfs : Fri.shapeOkMultiArity (F := F) arities params shape coms pts vals pproof.openingProof = true)
    (hag0 : AgreesTensorMulti M.toFieldModel params shape arities coms pts vals
      (pproof.withPaths #[] #[]).openingProof ch msgM rT βM idxM)
    (hw : verifyWithTensorMulti (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) params shape arities coms pts vals
      pproof.openingProof ch = true) :
    let P := modelParamsMulti M.toFieldModel params shape arities
      (M.wellFormed params shape htwo) hpos hsum
    let W := maxWidth shape
    let Mopen := maxOpeningsPerHeight params.logBlowup shape
    let p0 := pproof.withPaths #[] #[]
    ∃ (inPaths comPaths : Array (Array (List D))),
      ((List.finRange P.batches).map fun b =>
        restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProofMulti M.toFieldModel params shape p0.openingProof).inputRows b))
          (match pproof.openingProof.inputOpenings[b.val]? with
            | some o => o.openingProof | none => ⟨#[]⟩)).mapM id = some inPaths.toList ∧
      ((List.range P.rounds).map fun i =>
        restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1))
          (Array.ofFn fun k : Fin P.queries =>
            #[P.commitRowTensor W Mopen (tensorCoordMulti params shape arities)
                (modelProofMulti M.toFieldModel params shape p0.openingProof) (msgM 0) rT βM
                (idxM k) k i])
          (match pproof.openingProof.commitPhaseOpenings[i]? with
            | some o => o.openingProof | none => ⟨#[]⟩)).mapM id = some comPaths.toList ∧
      verifyWithTensorMulti (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) params shape arities coms pts vals
        (pproof.withPaths inPaths comPaths).openingProof ch = true := by
  intro P W Mopen p0
  let comRow (i : ℕ) (k : Fin P.queries) : Array K :=
    P.commitRowTensor W Mopen (tensorCoordMulti params shape arities)
      (modelProofMulti M.toFieldModel params shape p0.openingProof) (msgM 0) rT βM (idxM k) k i
  have hfs0 : Fri.shapeOkMultiArity (F := F) arities params shape coms pts vals p0.openingProof = true := by
    rw [withPaths_friShapeOkMultiArity]; exact hfs
  have hw' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun k =>
        decide (ch.indices.getD k 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (prunedMmcs (inputHasher M.toFieldModel (hasherOf f))) params shape
        coms pproof.openingProof.inputOpenings ch.indices
      && (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensorMulti (F := F) params shape arities pts vals pproof.openingProof ch k.val).all (·.ok)
      && commitChecksMulti (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) params.numQueries
        (logMaxHeight params.logBlowup shape) arities
        pproof.openingProof.commitPhaseCommits pproof.openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensorMulti (F := F) params shape arities pts vals pproof.openingProof ch k.val).map
          (·.rows))) = true := hw
  simp only [Bool.and_eq_true] at hw'
  obtain ⟨⟨⟨⟨⟨hpowB, hidxSzB⟩, hidxLtB⟩, hinPruned⟩, hqOk⟩, hcomPruned⟩ := hw'
  have hok_all : ∀ k : Fin params.numQueries,
      (queryResultTensorMulti (F := F) params shape arities pts vals p0.openingProof ch k.val).ok = true :=
    fun k => by
      rw [withPaths_queryResultTensorMulti]
      have := Array.all_eq_true.mp hqOk k.val (by rw [Array.size_ofFn]; exact k.isLt)
      simpa using this
  have hinEach : ∀ b : Fin P.batches,
      ∃ (root : D) (o : BatchOpening F (PrunedPaths D)) (paths : Array (List D)),
        coms[b.val]? = some root ∧
        pproof.openingProof.inputOpenings[b.val]? = some o ∧
        restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProofMulti M.toFieldModel params shape p0.openingProof).inputRows b))
          o.openingProof = some paths ∧
        Merkle.verifyOpenings (inputHasher M.toFieldModel (hasherOf f)) root
          (batchDims params.logBlowup (shape.getD b.val []))
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b.val [])).toList))
          o.openedValues paths = true := by
    intro b
    simp only [Fri.inputChecks, List.all_eq_true, List.mem_range] at hinPruned
    have hb := hinPruned b.val b.isLt
    split at hb
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hb
      obtain ⟨hrowsSz, _⟩ := Exec.Checks.size_of_verifyOpenings hver
      rw [Array.size_ofFn] at hrowsSz
      have ho' : pproof.openingProof.inputOpenings[b.val]? =
          some (o : BatchOpening F (PrunedPaths D)) := ho
      have ho0 : p0.openingProof.inputOpenings[b.val]? =
          some { openedValues := o.openedValues, openingProof := #[] } := by
        dsimp only [p0, Proof.withPaths]
        rw [Array.getElem?_mapIdx, ho']; rfl
      have hrowsEq : Array.ofFn
            ((modelProofMulti M.toFieldModel params shape p0.openingProof).inputRows b) =
          o.openedValues.map fun r => r.map fun row => row.map M.base.toModel := by
        refine Array.ext (by simp [hrowsSz]) fun t h1 h2 => ?_
        simp only [Array.getElem_ofFn, Array.getElem_map, modelProofMulti, queryRows]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, ho0, Option.map_some, Option.getD_some,
          Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa [hrowsSz] using h1),
          Option.getD_some]
      have hidx_eq : (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) =
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>>
              (logMaxHeight params.logBlowup shape -
                Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b.val [])).toList)) := by
        congr 1; funext k; rw [hag0.index k]; rfl
      have hrestM : restorePaths (hasherOf f) (P.dims b)
          (Array.ofFn fun k : Fin P.queries =>
            idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
          (Array.ofFn ((modelProofMulti M.toFieldModel params shape p0.openingProof).inputRows b))
          o.openingProof = some paths := by
        rw [hrowsEq, hidx_eq]
        exact (restorePaths_map M.base.toModel (hasherOf f) (P.dims b) _ o.openedValues
          o.openingProof).symm.trans hrest
      exact ⟨root, o, paths, hroot, ho, hrestM, hver⟩
    · exact absurd hb (by simp)
  have hcomEach : ∀ i : ℕ, i < P.rounds →
      ∃ (root : D) (o : CommitPhaseStep EF (PrunedPaths D)) (paths : Array (List D)),
        pproof.openingProof.commitPhaseCommits[i]? = some root ∧
        pproof.openingProof.commitPhaseOpenings[i]? = some o ∧
        restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1))
          (Array.ofFn fun k : Fin P.queries => #[comRow i k])
          o.openingProof = some paths ∧
        Merkle.verifyOpenings (friHasher M.toFieldModel (hasherOf f)) root
          #[⟨2 ^ arities.getD i 1, P.n - cumLogArity arities (i + 1)⟩]
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>> cumLogArity arities (i + 1))
          (Array.ofFn (n := params.numQueries) fun k =>
            #[(queryResultTensorMulti (F := F) params shape arities pts vals pproof.openingProof
                ch k.val).rows.getD i #[]])
          paths = true := by
    intro i hi
    simp only [Fri.commitChecksMulti, List.all_eq_true, List.mem_range] at hcomPruned
    have hci := hcomPruned i hi
    split at hci
    · next root o hroot ho =>
      obtain ⟨paths, hrest, hver⟩ := prunedMmcs_accepts hci
      have hi_ar : i < arities.length := hi
      have ha_eq : arities.getD i 1 = P.logArity i := by
        simp only [P, modelParamsMulti, Compiled.MultiParams.logArity,
          List.getD_eq_getElem _ _ hi_ar]
      have hdims_eq : #[Dimensions.mk (2 ^ arities.getD i 1)
          (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1))] = P.commitDims i := by
        rw [ha_eq]; rfl
      have hrowsEq :
          (Array.ofFn (n := P.queries) fun k =>
            #[(queryResultTensorMulti (F := F) params shape arities pts vals pproof.openingProof
                ch k.val).rows.getD i #[]]).map
            (fun r => r.map fun row => row.map M.ext.toModel) =
          Array.ofFn fun k : Fin P.queries => #[comRow i k] := by
        refine Array.ext (by simp) fun k h1 h2 => ?_
        have hk : k < P.queries := by simpa using h1
        simp only [Array.getElem_map, Array.getElem_ofFn]
        have hqr := rows_queryResultTensorMulti M.toFieldModel params shape arities
          (M.wellFormed params shape htwo) hpos hsum hfs0 hag0 ⟨k, hk⟩ (hok_all ⟨k, hk⟩) hi_ar
        rw [withPaths_queryResultTensorMulti] at hqr
        have hmap1 : ∀ (x : Array EF), Array.map (fun row => Array.map M.ext.toModel row) #[x] =
            #[Array.map M.ext.toModel x] := fun x => by simp
        rw [hmap1]
        exact congrArg (fun x => #[x]) hqr
      have hidx_eq : (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1)) =
          (Array.ofFn (n := params.numQueries) fun k =>
            ch.indices.getD k.val 0 >>> cumLogArity arities (i + 1)) := by
        congr 1; funext k; rw [hag0.index k]; rfl
      have hrestM : restorePaths (hasherOf f) (P.commitDims i)
          (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1))
          (Array.ofFn fun k : Fin P.queries => #[comRow i k])
          o.openingProof = some paths := by
        rw [← hrowsEq, hidx_eq, ← hdims_eq]
        simp only [Exec.Checks.getD_map_ofFn] at hrest
        exact (restorePaths_map M.ext.toModel (hasherOf f) _ _ _ o.openingProof).symm.trans hrest
      simp only [Exec.Checks.getD_map_ofFn] at hver
      exact ⟨root, o, paths, hroot, ho, hrestM, hver⟩
    · exact absurd hci (by simp)
  let inOpt (b : Fin P.batches) : Option (Array (List D)) :=
    restorePaths (hasherOf f) (P.dims b)
      (Array.ofFn fun k : Fin P.queries =>
        idxM k >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
      (Array.ofFn ((modelProofMulti M.toFieldModel params shape p0.openingProof).inputRows b))
      (match pproof.openingProof.inputOpenings[b.val]? with
        | some o => o.openingProof | none => ⟨#[]⟩)
  let comOpt (i : ℕ) : Option (Array (List D)) :=
    restorePaths (hasherOf f) (P.commitDims i)
      (Array.ofFn fun k : Fin P.queries => idxM k >>> P.cum (i + 1))
      (Array.ofFn fun k : Fin P.queries => #[comRow i k])
      (match pproof.openingProof.commitPhaseOpenings[i]? with
        | some o => o.openingProof | none => ⟨#[]⟩)
  let inPaths : Array (Array (List D)) := Array.ofFn fun b : Fin P.batches => (inOpt b).getD #[]
  let comPaths : Array (Array (List D)) := Array.ofFn fun i : Fin P.rounds => (comOpt i.val).getD #[]
  refine ⟨inPaths, comPaths, ?_, ?_, ?_⟩
  · refine mapM_id_eq_some_of_forallM _ inPaths.toList (by simp [inPaths]) fun i hi => ?_
    have hi' : i < P.batches := by simpa [inPaths] using hi
    obtain ⟨root, o, paths, -, ho, hrestM, -⟩ := hinEach ⟨i, hi'⟩
    have hopt : inOpt ⟨i, hi'⟩ = some paths := by
      dsimp only [inOpt]; rw [ho]; exact hrestM
    simp only [List.getElem_map, List.getElem_finRange, Fin.cast_mk, Array.getElem_toList, inPaths,
      Array.getElem_ofFn, hopt, Option.getD_some]
    exact hopt
  · refine mapM_id_eq_some_of_forallM _ comPaths.toList (by simp [comPaths]) fun i hi => ?_
    have hi' : i < P.rounds := by simpa [comPaths] using hi
    obtain ⟨root, o, paths, -, ho, hrestM, -⟩ := hcomEach i hi'
    have hopt : comOpt i = some paths := by
      dsimp only [comOpt]; rw [ho]; exact hrestM
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, comPaths,
      Array.getElem_ofFn, hopt, Option.getD_some]
    exact hopt
  · have hinUnpruned : inputChecks (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) params
        shape coms (pproof.withPaths inPaths comPaths).openingProof.inputOpenings ch.indices = true := by
      refine Exec.CompletenessChecks.inputChecks_of_open
        (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) fun b hb => ?_
      have hb' : b < P.batches := hb
      obtain ⟨root, o, paths, hroot, ho, hrestM, hver⟩ := hinEach ⟨b, hb'⟩
      have hopt : inOpt ⟨b, hb'⟩ = some paths := by
        dsimp only [inOpt]; rw [ho]; exact hrestM
      have hget : inPaths.getD b #[] = paths := by
        simp [inPaths, Array.getD_eq_getD_getElem?, hb', hopt]
      refine ⟨root, { openedValues := o.openedValues, openingProof := paths }, hroot, ?_, hver⟩
      exact ((Array.getElem?_mapIdx ..).trans (congrArg (Option.map _) ho)).trans
        (congrArg (fun p => some (BatchOpening.mk o.openedValues p)) hget)
    have hcomUnpruned : commitChecksMulti (merkleMmcs (friHasher M.toFieldModel (hasherOf f)))
        params.numQueries (logMaxHeight params.logBlowup shape) arities
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseCommits
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensorMulti (F := F) params shape arities pts vals
            (pproof.withPaths inPaths comPaths).openingProof ch k.val).map (·.rows)) = true := by
      refine commitChecksMulti_of_open
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) fun i hi => ?_
      have hi' : i < P.rounds := hi
      obtain ⟨root, o, paths, hroot, ho, hrestM, hver⟩ := hcomEach i hi'
      have hopt : comOpt i = some paths := by
        dsimp only [comOpt]; rw [ho]; exact hrestM
      have hget : comPaths.getD i #[] = paths := by
        simp [comPaths, Array.getD_eq_getD_getElem?, hi', hopt]
      refine ⟨root, { logArity := o.logArity, siblingValues := o.siblingValues, openingProof := paths },
        hroot, ?_, ?_⟩
      · exact ((Array.getElem?_mapIdx ..).trans (congrArg (Option.map _) ho)).trans
          (congrArg (fun p => some (CommitPhaseStep.mk o.logArity o.siblingValues p)) hget)
      · simp only [merkleMmcs, Exec.Checks.getD_map_ofFn, withPaths_queryResultTensorMulti]
        exact hver
    show (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun k =>
        decide (ch.indices.getD k 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))) params shape coms
        (pproof.withPaths inPaths comPaths).openingProof.inputOpenings ch.indices
      && (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensorMulti (F := F) params shape arities pts vals
          (pproof.withPaths inPaths comPaths).openingProof ch k.val).all (·.ok)
      && commitChecksMulti (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) params.numQueries
        (logMaxHeight params.logBlowup shape) arities
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseCommits
        (pproof.withPaths inPaths comPaths).openingProof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun k : Fin params.numQueries =>
          queryResultTensorMulti (F := F) params shape arities pts vals
            (pproof.withPaths inPaths comPaths).openingProof ch k.val).map (·.rows))) = true
    have hqOk' : (Array.ofFn fun k : Fin params.numQueries =>
        queryResultTensorMulti (F := F) params shape arities pts vals
          (pproof.withPaths inPaths comPaths).openingProof ch k.val).all (·.ok) = true := by
      simp only [withPaths_queryResultTensorMulti]; exact hqOk
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨hpowB, hidxSzB⟩, hidxLtB⟩, hinUnpruned⟩, hqOk'⟩, hcomUnpruned⟩

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
/-- **Core pruned-to-unpruned bridge for one multi-arity tensor STARK shard.** -/
theorem unprune_of_checkAfterChallengesTensorMultiArity_pruned
    (f : ∀ x, STAns F EF D K fslots slots width x)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D)
    (hshape : Stark.shapeOk sys pproof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid j
      (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) j)) s 2
      (.ext γ :: mid) false 0 0)
    (hcheck : checkAfterChallengesTensorMultiArity
      (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      pproof s β γ acc = true) :
    ∃ (htwo : logMaxHeight sys.fri.logBlowup
        (starkShape sys M.extData.d pproof.active pproof.logDegrees) ≤
          TwoAdicOps.twoAdicity (F := F))
      (inPaths comPaths : Array (Array (List D))),
      (restoreShardPathsMultiM M sys hcap pproof htwo
        (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid)
          (4 + ((modelParamsMulti M.toFieldModel sys.fri
            (starkShape sys M.extData.d pproof.active pproof.logDegrees)
            (scheduleOfShape sys.fri (starkShape sys M.extData.d pproof.active pproof.logDegrees))
            (M.wellFormed sys.fri _ htwo) (scheduleOfShape_pos hcap)
            (scheduleOfShape_sum_le hcap)).rounds + 2)))).run f =
          some (inPaths, comPaths) ∧
      checkAfterChallengesTensorMultiArity
        (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
        (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
        sys (pproof.withPaths inPaths comPaths) s β γ acc = true := by
  set next := nextMsgTensorMulti (fslots := fslots) (slots := slots) (width := width)
    M sys (pproof.withPaths #[] #[]) m0 mid
  set ms := fun j => next j (fsTranscriptA f next j)
  set shape := starkShape sys M.extData.d pproof.active pproof.logDegrees
  set arities := scheduleOfShape sys.fri shape
  set ζ := Function.surjInv M.surj (answer f ms 3).field
  have hlast : ∀ j, tLastField (fsTranscriptA f next (j + 1)) = (answer f ms j).field := fun j => by
    show UTensorAns.field (f (.chal (fsTranscriptA f next j) (next j (fsTranscriptA f next j)))) =
      UTensorAns.field (f (.chal (fsTranscript f ms j) (next j (fsTranscriptA f next j))))
    rw [← fsTranscriptA_eq_fsTranscript]
  have hsh : claimShape (openingClaims
      (InputProof := (prunedMmcs (inputHasher M.toFieldModel (hasherOf f))).MultiProof)
      (CommitProof := (prunedMmcs (friHasher M.toFieldModel (hasherOf f))).MultiProof)
      sys pproof ζ) = shape := by
    change claimShape (openingClaims sys pproof ζ) = shape
    rw [claimShape_openingClaims sys pproof hshape ζ, ← M.degree_eq]
  have h2 : ms 2 = (.ext γ :: mid) ++ secondMessage pproof := by
    show Observation.ext (rep M (tLastField (fsTranscriptA f next 2))) ::
      (mid ++ secondMessage pproof) = _
    rw [hlast 1, hγ]; rfl
  have h4 : ms 4 = (claimValues (openingClaims sys pproof ζ)).toList.map .ext := by
    show List.map Observation.ext (claimValues (openingClaims sys pproof
      (rep M (tLastField (fsTranscriptA f next 4))))).toList = _
    rw [hlast 3]; rfl
  have hC : ∀ i < arities.length,
      ms (5 + i) = .digest (pproof.openingProof.commitPhaseCommits.getD i default) ::
        (if sys.fri.commitPowBits = 0 then []
          else [.base (pproof.openingProof.commitPowWitnesses.getD i 0)]) := fun i hi => by
    rw [Nat.add_comm 5 i]
    show messagesMulti sys.fri arities #[] #[] #[] (pproof.withPaths #[] #[]).openingProof (i + 1) = _
    rw [messagesMulti, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
      Nat.add_sub_cancel]
    rfl
  have hF : ms (5 + arities.length) =
      finalMessageMulti arities pproof.openingProof.finalPoly ++
        (if sys.fri.queryPowBits = 0 then [] else [.base pproof.openingProof.queryPowWitness]) := by
    rw [Nat.add_comm 5 arities.length]
    show messagesMulti sys.fri arities #[] #[] #[] (pproof.withPaths #[] #[]).openingProof
      (arities.length + 1) = _
    rw [messagesMulti, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.not_succ_le_self _)]
    rfl
  obtain ⟨hz, hc, hu, hfs, ch, hch, hw, hcol, hopen, hcolW, hopenW, hβ, hpow, hidx⟩ :=
    checkAfterChallengesTensorMultiArity_ufreeTensor M f
      (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f)))
      sys pproof hshape β γ acc hs h2 rfl h4 (by rw [hsh]; exact hC) (by rw [hsh]; exact hF)
      hcheck
  rw [hsh] at hfs hch hw hcol hopen hcolW hopenW hβ hpow hidx
  have htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F) := by
    have h := hfs
    simp only [Fri.shapeOkMultiArity, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1.1.2
  set P := modelParamsMulti M.toFieldModel sys.fri shape arities (M.wellFormed sys.fri shape htwo)
    (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)
  set W := maxWidth shape
  set Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  set t := fsTranscriptA f next (4 + (P.rounds + 2))
  have hlen_ch : ∀ {n : ℕ}
      (tr : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) n),
      (chalsOf tr).length = n := by
    intro n tr
    induction tr with
    | nil => rfl
    | snoc _ _ _ ih =>
      show (chalsOf _ ++ [_]).length = _
      rw [List.length_append, ih, List.length_singleton]
  have hch_at : ∀ n (k : ℕ), k < n →
      tAnsAt (chalsOf (fsTranscript f ms n)) k = answer f ms k := by
    intro n
    induction n with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero _)
    | succ n ih =>
      intro k hk
      show ((chalsOf (fsTranscript f ms n) ++ [answer f ms n])[k]?).getD _ = answer f ms k
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | hEq
      · rw [List.getElem?_append_left (by rw [hlen_ch]; exact hlt)]
        exact ih k hlt
      · subst hEq
        have heq := List.getElem?_concat_length (l := chalsOf (fsTranscript f ms k))
          (a := answer f ms k)
        rw [hlen_ch] at heq
        rw [heq]; rfl
  have hans : ∀ j < 4 + (P.rounds + 2), tAnsAt (chalsOf t) j = answer f ms j := fun j hj => by
    rw [show t = fsTranscript f ms (4 + (P.rounds + 2)) from fsTranscriptA_eq_fsTranscript f next _]
    exact hch_at _ j hj
  have hζ_eq : rep M (tFieldAt (chalsOf t) 3) = ζ := by
    show rep M (tAnsAt (chalsOf t) 3).field = _
    rw [hans 3 (by omega)]; rfl
  have hcolSz : ch.schedule.colChallenges.size = tensorNumChallenges W := by
    rw [hcol, List.size_toArray, List.length_map, List.length_range]
  have hopenSz : ch.schedule.openChallenges.size = tensorNumChallenges Mopen := by
    rw [hopen, List.size_toArray, List.length_map, List.length_range]
  set rT := tensorChalOfAns W Mopen (tAnsAt (chalsOf t) 4)
  set βM : ℕ → K := fun i => if i < P.rounds then tFieldAt (chalsOf t) (5 + i) else 0
  set idxM : Fin P.queries → ℕ := fun k => (tAnsAt (chalsOf t) (5 + P.rounds)).bits
    (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) P.n
  set ζt := rep M (tFieldAt (chalsOf t) 3)
  set coms := (openingClaims sys pproof ζt).map (·.commitment)
  set pts := claimPoints (openingClaims sys pproof ζt)
  set vals := claimValues (openingClaims sys pproof ζt)
  set msgM : ℕ → Compiled.Msg K D shape.length :=
    fun j => viewMulti M.toFieldModel sys.fri shape arities
      (messagesMulti sys.fri arities coms pts vals pproof.openingProof j)
  have hfs_t : Fri.shapeOkMultiArity (F := F) arities sys.fri shape coms pts vals
      pproof.openingProof = true := by
    dsimp only [coms, pts, vals]; rw [hζ_eq]; exact hfs
  have hw_t : verifyWithTensorMulti (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri shape arities coms pts vals
      pproof.openingProof ch = true := by
    dsimp only [coms, pts, vals]; rw [hζ_eq]; exact hw
  have hag0 : AgreesTensorMulti M.toFieldModel sys.fri shape arities coms pts vals
      (pproof.withPaths #[] #[]).openingProof ch msgM rT βM idxM :=
    { msg := fun _ _ => rfl
      colSize := hcolSz
      openSize := hopenSz
      colWeights := hcolW
      openWeights := hopenW
      colChals := fun b => by
        dsimp only [rT, tensorChalOfAns]
        rw [hans 4 (by omega)]
        have hlt : b.val < ch.schedule.colChallenges.size := by rw [hcolSz]; exact b.isLt
        have hg : ch.schedule.colChallenges[b.val]'hlt =
            Function.surjInv M.surj ((answer f ms 4).fieldAt b.val) := by
          have := Transcript.getD_map_range (fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt k)) (tensorNumChallenges W) b.val 0
          rw [ite_eq_left b.isLt] at this
          rw [← this, ← hcol, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hg, Function.surjInv_eq M.surj]
      openChals := fun b => by
        dsimp only [rT, tensorChalOfAns]
        rw [hans 4 (by omega)]
        have hlt : b.val < ch.schedule.openChallenges.size := by rw [hopenSz]; exact b.isLt
        have hg : ch.schedule.openChallenges[b.val]'hlt =
            Function.surjInv M.surj ((answer f ms 4).fieldAt (tensorNumChallenges W + b.val)) := by
          have := Transcript.getD_map_range (fun k =>
            Function.surjInv M.surj ((answer f ms 4).fieldAt (tensorNumChallenges W + k)))
            (tensorNumChallenges Mopen) b.val 0
          rw [ite_eq_left b.isLt] at this
          rw [← this, ← hopen, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hg, Function.surjInv_eq M.surj]
      beta := fun i hi => by
        dsimp only [βM]
        have hi' : i < P.rounds := hi
        rw [ite_eq_left hi', tFieldAt, hans (5 + i) (by omega), hβ, Transcript.getD_map_range,
          ite_eq_left hi, Function.surjInv_eq M.surj]
      index := fun k => by
        dsimp only [idxM]
        rw [hans (5 + P.rounds) (by omega), hidx, Transcript.getD_map_range, ite_eq_left k.isLt]
        rfl }
  obtain ⟨inPaths, comPaths, hinMapM, hcomMapM, hwithUnpruned⟩ :=
    unprune_verifyWithTensorMulti_pruned M f sys.fri shape arities
      (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap) htwo coms pts vals pproof ch msgM
      rT βM idxM hfs_t hag0 hw_t
  refine ⟨htwo, inPaths, comPaths, ?_, ?_⟩
  · unfold restoreShardPathsMultiM
    simp only [run_bind, run_mapM_oc, run_restorePathsM]
    rw [hinMapM, hcomMapM]
    simp
  · have hα_s : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).alpha =
        Function.surjInv M.surj (answer f ms 2).field := by
      have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))
          2 (ms 2) false 0 0 := by
        rw [h2]; exact hs.observeAll f M.toFieldModel _
      exact (a2.sampleExt_zero f M.toFieldModel).1
    have hζ_s : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = ζ := by
      have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))
          2 (ms 2) false 0 0 := by
        rw [h2]; exact hs.observeAll f M.toFieldModel _
      obtain ⟨-, a2'⟩ := a2.sampleExt_zero f M.toFieldModel
      have a3 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observe
          ((uChallengerTensor f M.toFieldModel).sampleExt
            ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage pproof))).2
          (.digest pproof.quotientCommit)) 3 (ms 3) false 0 0 := a2'.observe_next f M.toFieldModel _
      exact (a3.sampleExt_zero f M.toFieldModel).1
    have hζ_st : (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = ζt :=
      hζ_s.trans hζ_eq.symm
    have hsh_t : claimShape (openingClaims sys pproof ζt) = shape := by
      rw [hζ_eq]; exact hsh
    have hch_eq : transcriptFromTensorMulti (uChallengerTensor f M.toFieldModel)
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri shape arities
        vals (pproof.withPaths inPaths comPaths).openingProof = ch := by
      dsimp only [vals]; rw [hζ_eq]; exact hch.symm
    simp only [checkAfterChallengesTensorMultiArity, verifyClaimsFromTensorMultiArity,
      verifyFromTensorMultiArity, verifyFromTensorWithSchedule, Bool.and_eq_true]
    change (zetaOk pproof (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = true ∧
        widthsUniform (openingClaims sys pproof
          (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta) = true ∧
        Fri.shapeOkMultiArity
          (scheduleOfShape sys.fri (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta)))
          sys.fri
          (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          ((openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta).map (·.commitment))
          (claimPoints (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (claimValues (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (pproof.withPaths inPaths comPaths).openingProof = true ∧
        verifyWithTensorMulti (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
          (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri
          (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (scheduleOfShape sys.fri (claimShape (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta)))
          ((openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta).map (·.commitment))
          (claimPoints (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (claimValues (openingClaims sys pproof
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
          (pproof.withPaths inPaths comPaths).openingProof
          (transcriptFromTensorMulti (uChallengerTensor f M.toFieldModel)
            (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri
            (claimShape (openingClaims sys pproof
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
            (scheduleOfShape sys.fri (claimShape (openingClaims sys pproof
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta)))
            (claimValues (openingClaims sys pproof
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta))
            (pproof.withPaths inPaths comPaths).openingProof) = true) ∧
      constraintsOk sys pproof β γ acc
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).alpha
        (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).zeta = true
    rw [hα_s, hζ_st]
    refine ⟨⟨by rw [hζ_eq]; exact hz, by rw [hζ_eq]; exact hu, ?_, ?_⟩, by rw [hζ_eq]; exact hc⟩
    · rw [hsh_t, withPaths_friShapeOkMultiArity]; exact hfs_t
    · suffices ∀ sh : ClaimShape, sh = shape →
          verifyWithTensorMulti (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys.fri sh
            (scheduleOfShape sys.fri sh) coms pts vals
            (pproof.withPaths inPaths comPaths).openingProof
            (transcriptFromTensorMulti (uChallengerTensor f M.toFieldModel)
              (mainChallenges (uChallengerTensor f M.toFieldModel) s pproof).state sys.fri sh
              (scheduleOfShape sys.fri sh) vals
              (pproof.withPaths inPaths comPaths).openingProof) = true from
        this _ hsh_t
      rintro sh rfl
      rw [hch_eq]
      exact hwithUnpruned

/-- **Deterministic pruned multi-arity shard soundness in a good log.** -/
theorem shard_goodTensorMultiPruned (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap V θ B r l)
    {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (pproof : Proof F EF D (PrunedPaths D) (PrunedPaths D)) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    {l₀ l₁ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorMultiPruned M sys hcap pproof m0 mid) l₀ b l₁) (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid 2
      (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = pproof.active) (hstage1 : hdr.stage1Commit = pproof.stage1Commit)
    (hlogs : hdr.logDegrees = pproof.logDegrees)
    (hdig : pproof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys pproof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid j
        (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid j
      (fsTranscriptA f (nextMsgTensorMulti M sys (pproof.withPaths #[] #[]) m0 mid) j)) s 2
      (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensorMultiArity
      (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      pproof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) pproof.active pproof.logDegrees
        pproof.stage1Commit pproof.stage2Commit pproof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (pproof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  obtain ⟨htwo, inPaths, comPaths, hrunRest, hcheckUnpruned⟩ :=
    unprune_of_checkAfterChallengesTensorMultiArity_pruned M sys hcap f pproof m0 mid hshape β γ
      acc s hγ hs hcheck
  unfold shardCompTensorMultiPruned at hout
  rw [dite_eq_left htwo, outcome_bind] at hout
  obtain ⟨t, l', hder, hrest_bind⟩ := hout
  obtain ⟨opt, l'', hrest, hver⟩ := outcome_bind.mp hrest_bind
  have hfl₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y h =>
    hf x y (dlookup_of_prefix h hl₁)
  have hfl'' : ∀ x y, l''.dlookup x = some y → f x = y := fun x y h =>
    hfl₁ x y (dlookup_of_prefix h hver.prefix)
  have hfl' : ∀ x y, l'.dlookup x = some y → f x = y := fun x y h =>
    hfl'' x y (dlookup_of_prefix h hrest.prefix)
  obtain rfl := hder.eq_fsTranscriptA hfl'
  have hopt : opt = some (inPaths, comPaths) := (hrest.run_eq hfl'').symm.trans hrunRest
  subst hopt
  dsimp only at hver
  set proof := pproof.withPaths inPaths comPaths
  have hnextEq := withPaths_nextMsgTensorMulti (fslots := fslots) (slots := slots) (width := width)
    M sys pproof m0 mid inPaths comPaths
  rw [← hnextEq] at hder hhdr hβ hγ hs
  exact shard_goodTensorMulti_of_derive_verify M sys hcap V θ B r hfixed hheightOk hθ hgood hf
    proof m0 mid hmid htwo hder hrest.prefix hver hl₁ hdec hpre hhdr hactive hstage1 hlogs hdig
    hdigFixed hr hshape β γ acc s hβ hγ hs hacc hcheckUnpruned

/-! ### Single-shard & batch pruned multi-arity STARK soundness -/

section PrunedMultiSingle

variable (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyTensorMultiArity` with `CertiFri.P3.prunedMmcs` against an oracle `f`.** -/
noncomputable def verifyTensorMultiArityPrunedAccepts
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : SAttemptPruned F EF D) : Bool :=
  Stark.verifyTensorMultiArity (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a.claims a.proof

/-- Soundness experiment for `Stark.verifyTensorMultiArity` with `prunedMmcs`. -/
noncomputable def experimentTensorMultiStarkPruned {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → SAttemptPruned F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardCompTensorMultiPruned M sys hcap (attempt a).proof
      (firstMessage sys (attempt a).proof (attempt a).claims) []).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_experimentTensorMultiStarkPruned {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    (experimentTensorMultiStarkPruned M sys hcap adv attempt).QueryBound
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    (queryBound_shardCompTensorMultiPruned M sys hcap _ _ _).bind fun _ => queryBound_pure _ 0

theorem verifyTensorMultiArityPruned_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttemptPruned F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensorMultiPruned M sys hcap a.proof
      (firstMessage sys a.proof a.claims) []) l₀ b l)
    (hacc : verifyTensorMultiArityPrunedAccepts M sys f a = true) (hcov : CoveredPruned B a) :
    ¬ ViolatesTensorPruned M sys θ l f a ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩)).eval
            (Polynomial.C (M.ext.toModel (lookupOfTensorPruned M sys f a).1))).eval
          (M.ext.toModel (lookupOfTensorPruned M sys f a).2) ≠ 0) := by
  simp only [verifyTensorMultiArityPrunedAccepts, Stark.verifyTensorMultiArity,
    Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, -⟩, -, hcheck⟩ := hacc
  have hhdr := headerOk_of_shapeOkTM sys B hshape hcov.claims hcov.claim_len
  have hdec : (singleVariant (EF := EF) sys B).dec0 (firstMessage sys a.proof a.claims) =
      some ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ := by
    rw [firstMessage_eq]
    exact singleVariant_dec0 M.base hN hcast hhdr
  have hpre : PreOk sys B
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ :=
    ⟨hshards, fun h hh => by rwa [List.mem_singleton.mp (Array.mem_toList_iff.mpr hh)],
      Nat.zero_le _, fun m hm => absurd hm (Array.not_mem_empty m)⟩
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  have a0 : UAtTensor (fun j => nextMsgTensorMulti M sys (a.proof.withPaths #[] #[])
        (firstMessage sys a.proof a.claims) [] j
        (fsTranscriptA f (nextMsgTensorMulti M sys (a.proof.withPaths #[] #[])
          (firstMessage sys a.proof a.claims) []) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims)) 0 (firstMessage sys a.proof a.claims) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (firstMessage sys a.proof a.claims)
    (ms := fun j => nextMsgTensorMulti M sys (a.proof.withPaths #[] #[])
      (firstMessage sys a.proof a.claims) [] j
      (fsTranscriptA f (nextMsgTensorMulti M sys (a.proof.withPaths #[] #[])
        (firstMessage sys a.proof a.claims) []) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  exact shard_goodTensorMultiPruned M sys hcap (singleVariant sys B) θ B (maxRounds F) hfixed
    hheightOk hθ hgood hf a.proof (firstMessage sys a.proof a.claims) []
    (fun o ho => absurd ho List.not_mem_nil) hout (List.prefix_refl l) hdec hpre
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩) rfl rfl rfl rfl
    (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self)
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyTensorMultiArity` with `prunedMmcs`.** -/
theorem soundness_verifyTensorMultiArityPruned_ud [Fintype K] [Fintype D] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorMultiArityPrunedAccepts M sys f (attempt out.1) = true ∧
          CoveredPruned B (attempt out.1) ∧
          ViolatesTensorPruned M sys (1 - δ) l f (attempt out.1))
      (experimentTensorMultiStarkPruned M sys hcap adv attempt) [] ≤
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := singleVariant sys B) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorMultiStarkPruned M sys hcap hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyTensorMultiArityPruned_good M sys hcap (1 - δ) B hfixed hheightOk hshards hN hcast
    (by linarith) hgood hf (attempt a) hcomp hacc hcov).1 hviol

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyTensorMultiArity` with `prunedMmcs`.** -/
theorem soundness_verifyTensorMultiArityPruned_lookups_ud [Fintype K] [Fintype D] {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorMultiArityPrunedAccepts M sys f (attempt out.1) = true ∧
          CoveredPruned B (attempt out.1) ∧
          ¬ LookupsBalancedTensorPruned M sys (1 - δ) B l (attempt out.1))
      (experimentTensorMultiStarkPruned M sys hcap adv attempt) [] ≤
      (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := singleVariant sys B) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_experimentTensorMultiStarkPruned M sys hcap hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hviol, hbal⟩ := verifyTensorMultiArityPruned_good M sys hcap (1 - δ) B hfixed hheightOk
    hshards hN hcast (by linarith) hgood hf (attempt a) hcomp hacc hcov
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  simp only [verifyTensorMultiArityPrunedAccepts, Stark.verifyTensorMultiArity,
    Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, hres⟩, hclaims, -⟩ := hacc
  have hitems : allItems M sys (1 - δ)
      (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
        (committedRow l)).2)
      ⟨#[⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
        (attempt a).claims⟩], #[]⟩ =
      headerItems M sys (1 - δ)
        (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
          (committedRow l)).2)
        ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
          (attempt a).claims⟩ := by
    rw [allItems]; exact (List.append_nil _).trans (List.flatMap_singleton _ _)
  rw [hitems] at hne hsum
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards (attempt a).proof (attempt a).claims
  have hlast := toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l))
    (hdr := ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit,
      (attempt a).proof.logDegrees, (attempt a).claims⟩)
    (β := (lookupOfTensorPruned M sys f (attempt a)).1)
    (γ := (lookupOfTensorPruned M sys f (attempt a)).2)
    hplain h2 hshape rfl rfl rfl
    (baseRows_readMsgT M B _ (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self))
    (fun root hroot => baseRows_readMsgT M B _
      (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
    htwo hclaims hviol hne
  exact hsum (hlast.symm.trans (((M.ext.beq_iff _ _).mp hres).trans M.ext.map_zero))

end PrunedMultiSingle

section PrunedMultiBatch

variable (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyBatchTensorMultiArity` with `CertiFri.P3.prunedMmcs` against an oracle `f`.** -/
noncomputable def batchTensorMultiArityPrunedAccepts
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : BAttemptPruned F EF D) : Bool :=
  Stark.verifyBatchTensorMultiArity (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (prunedMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a

/-- Sequential verification of pruned multi-arity shards. -/
noncomputable def shardsCompTensorMultiPruned (m0 : RawMsg F EF D) :
    List (Proof F EF D (PrunedPaths D) (PrunedPaths D)) → ℕ →
      OracleComp (STAns F EF D K fslots slots width) Bool
  | [], _ => .pure true
  | proof :: rest, i =>
    (shardCompTensorMultiPruned M sys hcap proof m0 [observeNat i]).bind fun b =>
      (shardsCompTensorMultiPruned m0 rest (i + 1)).bind fun b' => .pure (b && b')

/-- Soundness experiment for `Stark.verifyBatchTensorMultiArity` with `prunedMmcs`. -/
noncomputable def batchExperimentTensorMultiStarkPruned {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → BAttemptPruned F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardsCompTensorMultiPruned M sys hcap (batchFirstMessage sys (attempt a).preamble)
      ((attempt a).proofs.toList.take B.shards) 0).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
private theorem queryBound_shardsCompTensorMultiPruned (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (PrunedPaths D) (PrunedPaths D))) (i : ℕ) :
    (shardsCompTensorMultiPruned (fslots := fslots) (slots := slots) (width := width)
      M sys hcap m0 proofs i).QueryBound
      (proofs.length * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) := by
  induction proofs generalizing i with
  | nil => exact queryBound_pure _ _
  | cons proof rest ih =>
    have h : (shardsCompTensorMultiPruned (fslots := fslots) (slots := slots) (width := width)
        M sys hcap m0 (proof :: rest) i).QueryBound
        (shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) +
          (rest.length * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
      (queryBound_shardCompTensorMultiPruned M sys hcap proof m0 _).bind fun _ =>
        (ih (i + 1)).bind fun _ => queryBound_pure _ _
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_batchExperimentTensorMultiStarkPruned {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    (batchExperimentTensorMultiStarkPruned M sys hcap B adv attempt).QueryBound
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    ((queryBound_shardsCompTensorMultiPruned M sys hcap _ _ 0).mono
      (Nat.mul_le_mul_right _ (List.length_take_le _ _))).bind fun _ => queryBound_pure _ 0

private theorem outcome_shardsCompTensorMultiPruned (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (PrunedPaths D) (PrunedPaths D))) (i₀ : ℕ)
    {l l' : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (h : Outcome (shardsCompTensorMultiPruned M sys hcap m0 proofs i₀) l b l') (k : ℕ)
    {proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)} (hk : proofs[k]? = some proof) :
    ∃ (l₀ : Log (STAns F EF D K fslots slots width)) (b' : Bool)
      (l₁ : Log (STAns F EF D K fslots slots width)),
      Outcome (shardCompTensorMultiPruned M sys hcap proof m0 [observeNat (i₀ + k)]) l₀ b' l₁ ∧
        l₁ <+: l' := by
  induction proofs generalizing i₀ l b k with
  | nil => exact absurd hk (by simp)
  | cons p rest ih =>
    rw [shardsCompTensorMultiPruned] at h
    obtain ⟨b₁, l₁, h₁, h⟩ := outcome_bind.mp h
    obtain ⟨b₂, l₂, h₂, h₃⟩ := outcome_bind.mp h
    obtain ⟨-, rfl⟩ := h₃
    cases k with
    | zero =>
      obtain rfl : p = proof := by simpa using hk
      exact ⟨l, b₁, l₁, h₁, h₂.prefix⟩
    | succ k =>
      obtain ⟨l₀, b', l₁', h', hp⟩ := ih (i₀ + 1) h₂ k (by simpa using hk)
      have e : i₀ + 1 + k = i₀ + (k + 1) := by omega
      rw [e] at h'
      exact ⟨l₀, b', l₁', h', hp⟩

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
theorem shardOkTensorMultiArity_of_batchPrunedAccepts
    {f : ∀ x, STAns F EF D K fslots slots width x} {a : BAttemptPruned F EF D}
    (hacc : batchTensorMultiArityPrunedAccepts M sys f a = true) :
    a.preamble.headers.size = a.proofs.size ∧
      ∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        Stark.shapeOk sys proof = true ∧ hdr.active = proof.active ∧
          hdr.stage1Commit = proof.stage1Commit ∧ hdr.logDegrees = proof.logDegrees ∧
          checkAfterChallengesTensorMultiArity
            (prunedMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (prunedMmcs (friHasher M.toFieldModel (hasherOf f)))
            (uChallengerTensor f M.toFieldModel) sys proof
            ((uChallengerTensor f M.toFieldModel).observe
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.2 (observeNat i))
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).1
            (lookupChallenges (uChallengerTensor f M.toFieldModel)
              ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                (batchFirstMessage sys a.preamble))).2.1
            (claimsAccumulator
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).1
              (lookupChallenges (uChallengerTensor f M.toFieldModel)
                ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
                  (batchFirstMessage sys a.preamble))).2.1 hdr.claims).2 = true := by
  simp only [batchTensorMultiArityPrunedAccepts, Stark.verifyBatchTensorMultiArity, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hacc
  obtain ⟨⟨-, hsz⟩, ⟨-, hall⟩, -⟩ := hacc
  refine ⟨hsz, fun i hdr proof hhdr hproof => ?_⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensorMultiArity, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, -, hcheck⟩ := h
  exact ⟨hshape, hactive, hstage1, hlogs, hcheck⟩

theorem verifyBatchTensorMultiArityPruned_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttemptPruned F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardsCompTensorMultiPruned M sys hcap (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchTensorMultiArityPrunedAccepts M sys f a = true) (hcov : BatchCoveredPruned B a)
    {i : ℕ} {hdr : ShardHeader F D} {proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)}
    (hhdr : a.preamble.headers[i]? = some hdr) (hproof : a.proofs[i]? = some proof) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit
        (M.ext.toModel (batchLookupOfTensorPruned M sys f a).1)
        (M.ext.toModel (batchLookupOfTensorPruned M sys f a).2)
        (M.ext.toModel (claimsAccumulator (batchLookupOfTensorPruned M sys f a).1
          (batchLookupOfTensorPruned M sys f a).2 hdr.claims).2)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble)).eval
            (Polynomial.C (M.ext.toModel (batchLookupOfTensorPruned M sys f a).1))).eval
          (M.ext.toModel (batchLookupOfTensorPruned M sys f a).2) ≠ 0) := by
  obtain ⟨hsz, hall⟩ := shardOkTensorMultiArity_of_batchPrunedAccepts M sys hacc
  obtain ⟨hshape, hactive, hstage1, hlogs, hcheck⟩ := hall i hdr proof hhdr hproof
  have hmem : hdr ∈ a.preamble.headers := Array.mem_of_getElem? hhdr
  have hi : i < B.shards :=
    lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hhdr).1 hcov.shards
  have hpre : PreOk sys B a.preamble := by
    refine ⟨hcov.shards, fun h hh => ?_, hcov.messages, hcov.message_len⟩
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hh
    have hklt : k < a.proofs.size := hsz ▸ (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨hshape', hactive', -, hlogs', -⟩ :=
      hall k h a.proofs[k] hk (Array.getElem?_eq_getElem hklt)
    exact headerOk_of_shardOkTM sys B hshape' hactive' hlogs' (hcov.claims h hh).1
      (hcov.claims h hh).2
  have hdec := batchVariant_dec0 (EF := EF) M.base hN hcast hpre
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hk : (a.proofs.toList.take B.shards)[i]? = some proof := by
    rw [List.getElem?_take_of_lt hi, Array.getElem?_toList]; exact hproof
  obtain ⟨l₀', b', l₁, hcomp, hl₁⟩ := outcome_shardsCompTensorMultiPruned M sys hcap _ _ 0 hout i hk
  rw [Nat.zero_add] at hcomp
  have a0 : UAtTensor (fun j => nextMsgTensorMulti M sys (proof.withPaths #[] #[])
        (batchFirstMessage sys a.preamble) [observeNat i] j
        (fsTranscriptA f (nextMsgTensorMulti M sys (proof.withPaths #[] #[])
          (batchFirstMessage sys a.preamble) [observeNat i]) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble)) 0 (batchFirstMessage sys a.preamble) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (batchFirstMessage sys a.preamble)
    (ms := fun j => nextMsgTensorMulti M sys (proof.withPaths #[] #[])
      (batchFirstMessage sys a.preamble) [observeNat i] j
      (fsTranscriptA f (nextMsgTensorMulti M sys (proof.withPaths #[] #[])
        (batchFirstMessage sys a.preamble) [observeNat i]) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  have hs' := hs.observe f M.toFieldModel (observeNat i)
  have hshard : (batchVariant (EF := EF) sys B N).shard
      (nextMsgTensorMulti M sys (proof.withPaths #[] #[]) (batchFirstMessage sys a.preamble)
        [observeNat i] 2
        (fsTranscriptA f (nextMsgTensorMulti M sys (proof.withPaths #[] #[])
          (batchFirstMessage sys a.preamble) [observeNat i]) 2)) = i :=
    batchVariant_shard M.base sys B hcast _ (hi.le.trans hN.shards) _
  exact shard_goodTensorMultiPruned M sys hcap (batchVariant sys B N) θ B (maxRounds F) hfixed
    hheightOk hθ hgood hf proof (batchFirstMessage sys a.preamble) [observeNat i]
    (fun o ho => ⟨_, List.mem_singleton.mp ho⟩) hcomp hl₁ hdec hpre (hdr := hdr)
    (by rw [hshard]; exact hhdr) hactive hstage1 hlogs
    (by
      rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩))
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs' rfl hcheck

/-- **Unconditional unique-decoding soundness of `Stark.verifyBatchTensorMultiArity` with `prunedMmcs`.** -/
theorem soundness_verifyBatchTensorMultiArityPruned_ud [Fintype K] [Fintype D] {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorMultiArityPrunedAccepts M sys f (attempt out.1) = true ∧
          BatchCoveredPruned B (attempt out.1) ∧
          BatchViolatesTensorPruned M sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned M sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := batchVariant sys B N) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorMultiStarkPruned M sys hcap B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, i, hdr, proof, hhdr, hproof, hfail⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyBatchTensorMultiArityPruned_good M sys hcap (1 - δ) B hfixed hheightOk hN hcast
    (by linarith) hgood hf (attempt a) hcomp hacc hcov hhdr hproof).1 hfail

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyBatchTensorMultiArity` with `prunedMmcs`.** -/
theorem soundness_verifyBatchTensorMultiArityPruned_lookups_ud [Fintype K] [Fintype D] {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorMultiArityPrunedAccepts M sys f (attempt out.1) = true ∧
          BatchCoveredPruned B (attempt out.1) ∧
          ¬ BatchLookupsBalancedTensorPruned M sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStarkPruned M sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensorMulti_le (M := M) (sys := sys) (hcap := hcap)
      (V := batchVariant sys B N) (θ := 1 - δ) (B := B) (r := maxRounds F)
      (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
      (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate.le v hs.active hs)
      (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ)
      (queryBound_batchExperimentTensorMultiStarkPruned M sys hcap B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  have hacc' := hacc
  simp only [batchTensorMultiArityPrunedAccepts, Stark.verifyBatchTensorMultiArity, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true] at hacc'
  obtain ⟨⟨hne0, hsz⟩, ⟨hmsgs, hall⟩, hfold⟩ := hacc'
  have hpos0 : 0 < (attempt a).preamble.headers.size :=
    Nat.pos_of_ne_zero (by simpa using hne0)
  obtain ⟨-, hbal⟩ := verifyBatchTensorMultiArityPruned_good M sys hcap (1 - δ) B hfixed hheightOk
    hN hcast (by linarith) hgood hf (attempt a) hcomp hacc hcov
    (Array.getElem?_eq_getElem hpos0) (Array.getElem?_eq_getElem (hsz ▸ hpos0))
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  obtain ⟨-, hinit⟩ := messagesAccumulator_model M (batchLookupOfTensorPruned M sys f (attempt a)).1
    (batchLookupOfTensorPruned M sys f (attempt a)).2 _ hmsgs
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards (pre := (attempt a).preamble)
  have hshard_res : ∀ (i : ℕ) (hdr : ShardHeader F D)
      (proof : Proof F EF D (PrunedPaths D) (PrunedPaths D)),
      (attempt a).preamble.headers.toList[i]? = some hdr →
      (attempt a).proofs.toList[i]? = some proof →
      M.ext.toModel (Stark.residual proof) =
        lookupSum (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).1)
          (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).2)
          (headerItems M sys (1 - δ)
            (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
              (committedRow l)).2) hdr) := by
    intro i hdr proof hhdr hproof
    rw [Array.getElem?_toList] at hhdr hproof
    have hmem : ((hdr, proof), i) ∈
        ((attempt a).preamble.headers.toList.zip (attempt a).proofs.toList).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
        Array.getElem?_toList]
      exact ⟨hhdr, hproof⟩
    have hs := hall _ hmem
    simp only [Stark.shardOkTensorMultiArity, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, hclaims, -⟩ := hs
    have hcf := (verifyBatchTensorMultiArityPruned_good M sys hcap (1 - δ) B hfixed hheightOk hN
      hcast (by linarith) hgood hf (attempt a) hcomp hacc hcov hhdr hproof).1
    have hmem_hdr : hdr ∈ (attempt a).preamble.headers.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? hhdr)
    exact toModel_residualT M sys (1 - δ) (com := M.baseRows (committedRow l))
      hplain h2 hshape hactive hstage1 hlogs
      (baseRows_readMsgT M B _ (by
        rw [hdigs, ← hstage1]
        exact List.mem_append_right _ (List.mem_map.mpr ⟨hdr, hmem_hdr, rfl⟩)))
      (fun root hroot => baseRows_readMsgT M B _
        (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
      htwo hclaims hcf fun it hit =>
        hne it (by rw [allItems]; exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨hdr, hmem_hdr, hit⟩))
  have hfl := toModel_foldl_residualT M
    (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).1)
    (M.ext.toModel (batchLookupOfTensorPruned M sys f (attempt a)).2)
    (headerItems M sys (1 - δ)
      (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
        (committedRow l)).2))
    (attempt a).preamble.headers.toList (attempt a).proofs.toList hsz hshard_res
    (messagesAccumulator (batchLookupOfTensorPruned M sys f (attempt a)).1
      (batchLookupOfTensorPruned M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2
  have hzero : M.ext.toModel ((attempt a).proofs.foldl (fun total proof => total + Stark.residual proof)
      (messagesAccumulator (batchLookupOfTensorPruned M sys f (attempt a)).1
        (batchLookupOfTensorPruned M sys f (attempt a)).2
        ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2) = 0 :=
    ((M.ext.beq_iff _ _).mp hfold).trans M.ext.map_zero
  rw [Array.foldl_toList] at hfl
  rw [hfl, hinit] at hzero
  have hmap : ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity)).map
      (fun msg => (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) =
      (attempt a).preamble.messages.toList.map fun m =>
        (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel) := by
    rw [List.map_map]; rfl
  rw [hmap] at hzero
  rw [allItems, lookupSum_append, add_comm] at hsum
  exact hsum hzero

end PrunedMultiBatch

end PrunedMulti

end CertiFri.Exec.Stark
