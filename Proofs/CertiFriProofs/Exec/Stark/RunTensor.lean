import CertiFriProofs.Exec.Stark.FreeTensor
import CertiFriProofs.Exec.Stark.PcsSoundTensor

/-!
# A run of the tensor-batched STARK verifier with the idealised challenger

Tensor-batched counterpart of `Exec/Stark/Run.lean`. Connects `Stark.lookupChallenges`,
`Stark.checkAfterChallengesTensor`, and `Fri.verifyWithTensor` under `uChallengerTensor`
to the compiled tensor verifier `Compiled.Params.verifyWithTensor` / `modelChecksTensor`.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle
open CertiFri.Exec.Transcript (answer)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] {fslots slots width : ℕ}

section ValuesTensor

omit [FieldOps EF] [Inhabited D] in
private theorem mem_claimValuesT {claims : Array (CommitmentOpening EF D)}
    {c : CommitmentOpening EF D} {m : MatrixOpening EF} {po : PointOpening EF} {x : EF}
    (hc : c ∈ claims.toList) (hm : m ∈ c.matrices.toList) (hpo : po ∈ m.points.toList)
    (hx : x ∈ po.values.toList) : x ∈ (claimValues claims).toList := by
  simp only [claimValues, List.mem_flatMap]
  exact ⟨c, hc, m, hm, po, hpo, hx⟩

omit [FieldOps EF] in
private theorem exists_value_matrixOpeningT (k : ℕ) (ζ : EF) {rows : Array (Array EF)} {w : ℕ}
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

omit [Inhabited D] in
private theorem claimValues_openingClaims_ne_nilT {InputProof CommitProof : Type}
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
    obtain ⟨po, hpo, x, hx⟩ := exists_value_matrixOpeningT (proof.logDegrees.getD 0 0) ζ
      (Nat.mul_pos (Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)) hd) hq
    refine List.ne_nil_of_mem (mem_claimValuesT
      (c := ⟨proof.quotientCommit, ((activeIndices proof.active).zipIdx.map fun p : ℕ × ℕ =>
        matrixOpening (proof.logDegrees.getD p.2 0) [ζ]
          (proof.quotientOpened.getD p.2 #[])).toArray⟩) ?_ ?_ hpo hx)
    · simp only [openingClaims, Array.toList_append]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_map.mpr ⟨(ci, 0), hp, rfl⟩

end ValuesTensor

section ChallengesTensor

variable (M : StarkModel F EF K)
  (f : ∀ x : FSQuery (RawMsg F EF D) (UTensorChal K fslots slots width) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (UTensorChal K fslots slots width) K D x)

omit [DecidableEq K] [Inhabited D] in
/-- **The lookup challenges of a run with `uChallengerTensor`.** -/
theorem lookupChallenges_ufreeTensor (m0 : RawMsg F EF D) {ms : ℕ → RawMsg F EF D}
    (h0 : ms 0 = m0)
    (h1 : ms 1 = [.ext (lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).1]) :
    (lookupChallenges (uChallengerTensor f M.toFieldModel)
        ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).1 =
        Function.surjInv M.surj (answer f ms 0).field ∧
      (lookupChallenges (uChallengerTensor f M.toFieldModel)
        ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).2.1 =
        Function.surjInv M.surj (answer f ms 1).field ∧
      UAtTensor ms (lookupChallenges (uChallengerTensor f M.toFieldModel)
          ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).2.2 2
        [.ext (lookupChallenges (uChallengerTensor f M.toFieldModel)
          ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).2.1]
        false 0 0 := by
  have a0 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)
      0 (ms 0) false 0 0 := by
    rw [h0]
    exact (UAtTensor.init (ms := ms)).observeAll f M.toFieldModel m0
  obtain ⟨hβ, a0'⟩ := a0.sampleExt_zero f M.toFieldModel
  have a1 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observe
      ((uChallengerTensor f M.toFieldModel).sampleExt
        ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).2
      (.ext (lookupChallenges (uChallengerTensor f M.toFieldModel)
        ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init m0)).1))
      1 (ms 1) false 0 0 := by
    rw [h1]
    exact a0'.observe_next f M.toFieldModel _
  obtain ⟨hγ, a1'⟩ := a1.sampleExt_zero f M.toFieldModel
  exact ⟨hβ, hγ, a1'.observe_next f M.toFieldModel _⟩

omit [DecidableEq K] in
/-- **The checks after the lookup challenges for `checkAfterChallengesTensor`.** -/
theorem checkAfterChallengesTensor_ufreeTensor (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (sys : System F D) (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof)
    (hshape : Stark.shapeOk sys proof = true) {ms : ℕ → RawMsg F EF D}
    {s : UStateTensor F EF D} {cur : RawMsg F EF D} (β γ acc : EF)
    (hs : UAtTensor ms s 2 cur false 0 0)
    (h2 : ms 2 = cur ++ secondMessage proof) (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map .ext)
    (hC : ∀ i < numRounds sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field))),
      ms (5 + i) = .digest (proof.openingProof.commitPhaseCommits.getD i default) ::
        (if sys.fri.commitPowBits = 0 then []
          else [.base (proof.openingProof.commitPowWitnesses.getD i 0)]))
    (hF : ms (5 + numRounds sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field)))) =
      finalMessage (numRounds sys.fri (claimShape (openingClaims sys proof
          (Function.surjInv M.surj (answer f ms 3).field)))) proof.openingProof.finalPoly ++
        (if sys.fri.queryPowBits = 0 then [] else [.base proof.openingProof.queryPowWitness]))
    (h : checkAfterChallengesTensor inputMmcs friMmcs (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    let ζ := Function.surjInv M.surj (answer f ms 3).field
    let sh := claimShape (openingClaims sys proof ζ)
    zetaOk proof ζ = true ∧
      constraintsOk sys proof β γ acc (Function.surjInv M.surj (answer f ms 2).field) ζ = true ∧
      widthsUniform (openingClaims sys proof ζ) = true ∧
      Fri.shapeOk sys.fri sh ((openingClaims sys proof ζ).map (·.commitment))
        (claimPoints (openingClaims sys proof ζ)) (claimValues (openingClaims sys proof ζ))
        proof.openingProof = true ∧
      ∃ ch : TensorChallenges EF,
        ch = transcriptFromTensor (uChallengerTensor f M.toFieldModel)
          (mainChallenges (uChallengerTensor f M.toFieldModel) s proof).state sys.fri sh
          (claimValues (openingClaims sys proof ζ)) proof.openingProof ∧
        verifyWithTensor inputMmcs friMmcs sys.fri sh
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
        ch.betas = ((List.range (numRounds sys.fri sh)).map fun i =>
          Function.surjInv M.surj (answer f ms (5 + i)).field).toArray ∧
        (ch.powOk = true →
          (sys.fri.commitPowBits ≠ 0 → ∀ i < numRounds sys.fri sh,
            (answer f ms (5 + i)).bits 0 sys.fri.commitPowBits = 0) ∧
          (sys.fri.queryPowBits ≠ 0 →
            (answer f ms (5 + numRounds sys.fri sh)).bits 0 sys.fri.queryPowBits = 0)) ∧
        ch.indices = ((List.range sys.fri.numQueries).map fun t =>
          (answer f ms (5 + numRounds sys.fri sh)).bits
            (t + if sys.fri.queryPowBits = 0 then 0 else 1)
            (logMaxHeight sys.fri.logBlowup sh)).toArray := by
  -- Round 2: lookup traces and lookup sums, then `α`.
  have a2 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage proof))
      2 (ms 2) false 0 0 := by
    rw [h2]; exact hs.observeAll f M.toFieldModel _
  obtain ⟨hα, a2'⟩ := a2.sampleExt_zero f M.toFieldModel
  -- Round 3: quotient commitment, then `ζ`.
  have a3 : UAtTensor ms ((uChallengerTensor f M.toFieldModel).observe
      ((uChallengerTensor f M.toFieldModel).sampleExt
        ((uChallengerTensor f M.toFieldModel).observeAll s (secondMessage proof))).2
      (.digest proof.quotientCommit)) 3 (ms 3) false 0 0 := by
    rw [h3]; exact a2'.observe_next f M.toFieldModel _
  obtain ⟨hζ, a3'⟩ := a3.sampleExt_zero f M.toFieldModel
  simp only [checkAfterChallengesTensor, mainChallenges, Bool.and_eq_true] at h
  rw [hα, hζ] at h
  obtain ⟨⟨hz, hv⟩, hc⟩ := h
  rw [verifyClaimsFromTensor, Bool.and_eq_true] at hv
  obtain ⟨hu, hvf⟩ := hv
  rw [verifyFromTensor, Bool.and_eq_true] at hvf
  obtain ⟨hsh, hw⟩ := hvf
  -- Round 4: opened values (nonempty).
  have hne : (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map
        (Observation.ext (F := F) (D := D)) ≠ [] := fun h0 =>
    claimValues_openingClaims_ne_nilT sys proof hshape (M.degree_eq ▸ M.extData.d_pos) _
      (List.map_eq_nil_iff.mp h0)
  have a4 := a3'.observeAll_next f M.toFieldModel hne
  have a4' : UAtTensor ms _ 4 (ms 4) false 0 0 :=
    ⟨a4.round, a4.hist, a4.cur.trans h4.symm, a4.squeezed, a4.nfields, a4.nbits⟩
  have hfinal : proof.openingProof.finalPoly.size ≠ 0 := by
    have hsh' := hsh
    simp only [Fri.shapeOk, Bool.and_eq_true, beq_iff_eq] at hsh'
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
    transcriptTailTensor_ufreeTensor f M.toFieldModel sys.fri
      (claimShape (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
      proof.openingProof 4 a4' hpos hC hF hfinal
  exact ⟨hz, hc, hu, hsh, _, rfl, hw, tcol, topen, tcolW, topenW, tβ, tpow, tidx⟩

end ChallengesTensor

section PcsTensor

variable [DecidableEq D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {Msg : Type} {Chal : ℕ → Type}
  (f : ∀ x : FSQuery Msg Chal (HashQuery K D), MerkleAnswer Msg Chal K D x)

/-- **Accepted executable `verifyWithTensor` implies `modelChecksTensor` (and `powOk`).** -/
theorem modelChecksTensor_of_verifyWithTensor_exec {commitments : Array D}
    {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    (hshape : Fri.shapeOk (F := F) params shape commitments points values proof = true)
    (hcolSize : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape))
    (hopenSize : ch.schedule.openChallenges.size =
      tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (hcolW : ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges (maxWidth shape))
    (hopenW : ch.schedule.openWeights =
      tensorWeights ch.schedule.openChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (h : verifyWithTensor (merkleMmcs (inputHasher m (hasherOf f)))
      (merkleMmcs (friHasher m (hasherOf f))) params shape commitments points values proof
      ch = true) :
    let r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) :=
      (fun b => m.ext.toModel (ch.schedule.colChallenges.getD b.val 0),
       fun b => m.ext.toModel (ch.schedule.openChallenges.getD b.val 0))
    ch.powOk = true ∧
      modelChecksTensor (modelParams m params shape wf) (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape) (hasherOf f)
        (modelProof m params shape proof)
        (fun j => view m params shape (messages params shape commitments points values proof j))
        r (fun i => m.ext.toModel (ch.betas.getD i 0))
        (fun t => ch.indices.getD t.val 0) = true := by
  let r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) :=
    (fun b => m.ext.toModel (ch.schedule.colChallenges.getD b.val 0),
     fun b => m.ext.toModel (ch.schedule.openChallenges.getD b.val 0))
  have hag : AgreesTensor m params shape commitments points values proof ch
      (fun j => view m params shape (messages params shape commitments points values proof j))
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
  exact modelChecksTensor_of_verifyWithTensor m params shape wf (hasherOf f) hshape hag h

end PcsTensor

end CertiFri.Exec.Stark
