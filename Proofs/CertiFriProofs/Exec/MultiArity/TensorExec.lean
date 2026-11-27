import CertiFri.MultiArity
import CertiFriProofs.Exec.TensorExec
import CertiFriProofs.Theory.MultiArity.CompiledTensor

/-!
# Executable multi-arity tensor-batched FRI refinement & chained-ROM soundness

Bridges the executable multi-arity tensor-batched FRI verifiers
(`CertiFri.Fri.verifyTensorWithSchedule` and `CertiFri.Fri.verifyTensorMultiArity`
in `CertiFri/MultiArity.lean`) to the compiled multi-arity protocol
(`Theory/MultiArity/CompiledTensor.lean`).

## Main results

1. **Model parameters and equivalence of failing claims:**
   * `modelParamsMulti`, `tensorCoordMulti`, `tensorCoordMulti_injective`
   * `claimsFailMulti_iff_claimsFail`: for any schedule `arities` passing
     `scheduleValid`, failing claims under `MultiLdtInstance` are equivalent to
     failing claims under the binary `LdtInstance` (allowing direct reuse of the
     entire STARK AIR / LogUp / `Link.lean` stack).
2. **Multi-arity arithmetic and check refinement:**
   * `toModel_fieldPowTwo`, `toModel_placeRowMulti`, `toModel_foldRowMulti`,
     `toModel_foldChainMulti`
   * `modelChecksTensorMulti_of_verifyWithTensorMulti`
3. **Transcript refinement & chained-ROM soundness:**
   * `freeChallengerTensorMulti`, `transcriptTensorMulti_free`
   * `run_model_of_acceptsTensorMulti`
   * `Exec.soundnessTensorMulti`, `Exec.soundnessTensorMulti_ud`
-/

namespace CertiFri.Exec

open Fri

/-! ## 1. Multi-arity model parameters, messages, views, and proofs -/

section MultiSetup

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K]

/-- Multi-arity compiled parameters for `(params, shape)` and per-round schedule `arities`. -/
def modelParamsMulti (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (wf : WellFormed m params shape)
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape) :
    Compiled.MultiParams K where
  ω := m.base.toModel (TwoAdicOps.twoAdicGenerator (logMaxHeight params.logBlowup shape))
  n := logMaxHeight params.logBlowup shape
  arities := arities
  finalDegree := params.finalPolyLen
  shift := m.base.toModel TwoAdicOps.cosetShift
  queries := params.numQueries
  batches := shape.length
  dims := fun b => batchDims params.logBlowup (shape.getD b.val [])
  numClaims := fun j =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j)).length
  slot := fun j k =>
    ⟨⟨((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          (cumLogArity arities j)).get k).batch,
        batch_lt_of_mem_claimRefs (mem_claimRefs_of_mem_levelClaims (List.get_mem _ k))⟩,
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          (cumLogArity arities j)).get k).matrix,
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          (cumLogArity arities j)).get k).col⟩
  prim := wf.prim
  arities_pos := hpos
  arities_sum_le := hsum
  shift_ne := wf.shift_ne
  height_le := fun b => maxLogHeight_batchDims_le b.val
  slot_dims := by
    intro j _ k
    have hmem := List.get_mem
      (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
        (cumLogArity arities j)) k
    obtain ⟨p, hp, hb, hmat, hh, hcol⟩ := mem_claimRefs (mem_claimRefs_of_mem_levelClaims hmem)
    obtain ⟨mats, ms, hmats, hms, hph, hpw⟩ := mem_pointRefs (List.mem_of_getElem? hp)
    have hj := logHeight_of_mem_levelClaims hmem
    refine ⟨⟨ms.width, ms.logDegree + params.logBlowup⟩, ?_, ?_, ?_⟩
    · simp only [batchDims, List.getD_eq_getElem?_getD, hb, hmats, Option.getD_some, hmat,
        List.getElem?_toArray, List.getElem?_map, hms, Option.map_some]
    · simp only; omega
    · simp only; omega

/-- 2D tensor coordinate map at round-level `j` (corresponding to cumulative
folded bits `cumLogArity arities j`). -/
def tensorCoordMulti (params : FriParams) (shape : ClaimShape) (arities : List ℕ) (j : ℕ)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j)).length) :
    Fin (maxOpeningsPerHeight params.logBlowup shape) × Fin (maxWidth shape) :=
  tensorCoord params shape (cumLogArity arities j) k

theorem tensorCoordMulti_injective (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (j : ℕ) :
    Function.Injective (tensorCoordMulti params shape arities j) :=
  tensorCoord_injective params shape (cumLogArity arities j)

/-- Raw messages of a multi-arity run: identical to `messages` except rounds are
`arities.length` and the final round uses `finalMessageMulti arities`. -/
def messagesMulti [Inhabited D] (params : FriParams) (arities : List ℕ)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (j : ℕ) : RawMsg F EF D :=
  if j = 0 then firstMessage commitments points values
  else if j ≤ arities.length then
    .digest (proof.commitPhaseCommits.getD (j - 1) default) ::
      (if params.commitPowBits = 0 then []
        else [.base (proof.commitPowWitnesses.getD (j - 1) 0)])
  else
    finalMessageMulti arities proof.finalPoly ++
      (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness])

/-- Proof-of-work bit schedule for multi-arity FRI. -/
def powBitsMulti (params : FriParams) (arities : List ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i ≤ arities.length then params.commitPowBits else params.queryPowBits

theorem powBitsMulti_zero (params : FriParams) (arities : List ℕ) :
    powBitsMulti params arities 0 = 0 := rfl

theorem powBitsMulti_succ_of_lt (params : FriParams) (arities : List ℕ) {i : ℕ}
    (hi : i < arities.length) :
    powBitsMulti params arities (i + 1) = params.commitPowBits := by
  simp [powBitsMulti, hi]

theorem powBitsMulti_last (params : FriParams) (arities : List ℕ) :
    powBitsMulti params arities (arities.length + 1) = params.queryPowBits := by
  simp [powBitsMulti]

/-- Multi-arity view of a raw message, indexing points/values by round-level `r`
(at cumulative level `cumLogArity arities r`). -/
def viewMulti [Inhabited D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (msg : RawMsg F EF D) : Compiled.Msg K D shape.length where
  inputRoots := fun b => (digestsIn msg).getD b.val default
  points := (List.range (arities.length + 1)).map fun r =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities r)).map fun c => (extsIn m msg).getD c.pointIdx 0
  values := (List.range (arities.length + 1)).map fun r =>
    (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities r)).map fun c =>
      (extsIn m msg).getD ((pointRefs params.logBlowup shape).length + c.valueIdx) 0
  commitRoot := (digestsIn msg).getD 0 default
  finalCoeffs := extsIn m msg
  witness := 0

/-- Model proof data for a multi-arity executable proof. -/
def modelProofMulti (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (proof : FriProof F EF D (Array (List D)) (Array (List D))) :
    Compiled.MultiProof K D shape.length params.numQueries where
  inputRows := fun b t => ((queryRows proof t.val).getD b.val #[]).map (·.map m.base.toModel)
  inputPaths := fun b t =>
    match proof.inputOpenings[b.val]? with
    | some o => o.openingProof.getD t.val []
    | none => []
  siblings := fun i t => (siblingsMulti proof i t.val).map m.ext.toModel
  commitPaths := fun i t =>
    match proof.commitPhaseOpenings[i]? with
    | some o => o.openingProof.getD t.val []
    | none => []

/-- Unpack `scheduleValid params shape arities = true`. -/
theorem scheduleValid_iff {params : FriParams} {shape : ClaimShape} {arities : List ℕ} :
    scheduleValid params shape arities = true ↔
      (∀ a ∈ arities, 1 ≤ a ∧ a ≤ params.maxLogArity) ∧
        arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape ∧
        (∀ m ∈ shape.flatten, ∃ r ≤ arities.length,
          m.logDegree + params.logBlowup + cumLogArity arities r =
            logMaxHeight params.logBlowup shape) := by
  unfold scheduleValid
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨hb, hs⟩, hh⟩
    refine ⟨hb, hs, fun m hm => ?_⟩
    obtain ⟨r, hr, heq⟩ := hh m hm
    exact ⟨r, by omega, heq⟩
  · rintro ⟨hb, hs, hh⟩
    refine ⟨⟨hb, hs⟩, fun m hm => ?_⟩
    obtain ⟨r, hr, heq⟩ := hh m hm
    exact ⟨r, by omega, heq⟩

/-- **Equivalence of failing claims between multi-arity and binary LDT instances:**
whenever `arities` is a valid schedule for `(params, shape)` and `θ ≤ 1`,
`ClaimsFailMulti` on `modelParamsMulti` holds iff `ClaimsFail` holds on `modelParams`. -/
theorem claimsFailMulti_iff_claimsFail [DecidableEq K] [Inhabited D]
    (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (wf : WellFormed m params shape)
    (hvalid : scheduleValid params shape arities = true)
    (raw : RawMsg F EF D) (com : Compiled.Committed K D) {θ : ℝ} (hθ : θ ≤ 1) :
    let hpos : ∀ a ∈ arities, 0 < a := fun a ha => by
      have := (scheduleValid_iff.mp hvalid).1 a ha; omega
    let hsum : arities.sum ≤ logMaxHeight params.logBlowup shape := by
      have := (scheduleValid_iff.mp hvalid).2.1; omega
    let Pm := modelParamsMulti m params shape arities wf hpos hsum
    let Pb := modelParams m params shape wf
    PcsRbr.ClaimsFailMulti Pm.ldt Pm.shift θ (Pm.claims (viewMulti m params shape arities raw) com) ↔
      PcsRbr.ClaimsFail Pb.ldt Pb.shift θ (Pb.claims (view m params shape raw) com) := by
  intro hpos hsum Pm Pb
  obtain ⟨-, hsum_eq, hhits⟩ := scheduleValid_iff.mp hvalid
  have hrounds_eq : arities.sum = Pb.rounds := by
    show arities.sum = numRounds params shape
    unfold numRounds; omega
  have hclaims_eq : ∀ (r : ℕ) (hr : r ≤ arities.length),
      Pm.claims (viewMulti m params shape arities raw) com r =
        Pb.claims (view m params shape raw) com (cumLogArity arities r) := by
    intro r hr
    funext k
    have hcum_le : cumLogArity arities r ≤ Pb.rounds := by
      rw [← hrounds_eq]; exact cumLogArity_le_sum arities r
    have hcum_lt : cumLogArity arities r < numRounds params shape + 1 := by
      show cumLogArity arities r < Pb.rounds + 1; omega
    have hpt : (viewMulti m params shape arities raw).point r k.val =
        (view m params shape raw).point (cumLogArity arities r) k.val := by
      simp only [Compiled.Msg.point, viewMulti, view, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hr),
        List.getElem?_range hcum_lt, Option.map_some, Option.getD_some]
    have hval : (viewMulti m params shape arities raw).value r k.val =
        (view m params shape raw).value (cumLogArity arities r) k.val := by
      simp only [Compiled.Msg.value, viewMulti, view, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hr),
        List.getElem?_range hcum_lt, Option.map_some, Option.getD_some]
    show Claim.mk _ ((viewMulti m params shape arities raw).point r k.val)
        ((viewMulti m params shape arities raw).value r k.val) =
      Claim.mk _ ((view m params shape raw).point (cumLogArity arities r) k.val)
        ((view m params shape raw).value (cumLogArity arities r) k.val)
    rw [hpt, hval]
    rfl
  have hdom_eq : ∀ r, (Pm.ldt.domain r).image (Pm.shift * ·) =
      (Pb.ldt.domain (cumLogArity arities r)).image (Pb.shift * ·) := fun _ => rfl
  have hdeg_eq : ∀ r, Pm.ldt.degree r = Pb.ldt.degree (cumLogArity arities r) := fun r => by
    simp only [Compiled.MultiParams.ldt_degree, Compiled.Params.ldt_degree]
    show 2 ^ (arities.sum - cumLogArity arities r) * params.finalPolyLen =
      2 ^ (Pb.rounds - cumLogArity arities r) * params.finalPolyLen
    rw [hrounds_eq]
  constructor
  · rintro ⟨r, hr, hfail⟩
    refine ⟨cumLogArity arities r, ?_, ?_⟩
    · show cumLogArity arities r ≤ Pb.rounds
      rw [← hrounds_eq]; exact cumLogArity_le_sum arities r
    · rw [← hdom_eq r, ← hdeg_eq r, ← hclaims_eq r hr]
      exact hfail
  · rintro ⟨j, hj, hfail⟩
    by_cases hzero : Pb.numClaims j = 0
    · exfalso
      apply hfail
      refine ⟨_, Finset.Subset.refl _, mul_le_of_le_one_left (Nat.cast_nonneg _) hθ, fun k => ?_⟩
      exact absurd (lt_of_lt_of_eq k.isLt hzero) (Nat.not_lt_zero _)
    · have hpos_cl : 0 < Pb.numClaims j := Nat.pos_of_ne_zero hzero
      have hmem : (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j)[0] ∈
          levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j :=
        List.getElem_mem hpos_cl
      have hch := logHeight_of_mem_levelClaims hmem
      obtain ⟨p, hp, -, -, hph, -⟩ := mem_claimRefs (mem_claimRefs_of_mem_levelClaims hmem)
      obtain ⟨mats, ms, hmats, hms, hmh, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
      have hms_flat : ms ∈ shape.flatten :=
        List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩
      obtain ⟨r, hr, hhit⟩ := hhits ms hms_flat
      have hj_eq : cumLogArity arities r = j := by omega
      refine ⟨r, hr, ?_⟩
      subst hj_eq
      rw [hdom_eq r, hdeg_eq r, hclaims_eq r hr]
      exact hfail

end MultiSetup

/-! ## 2. Multi-arity arithmetic and check refinement -/

section MultiArith

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Inhabited D]

omit [FieldOps F] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] in
/-- `fieldPowTwo x k` refines to `toModel x ^ (2 ^ k)`. -/
theorem toModel_fieldPowTwo (r : Refines EF K) (x : EF) :
    ∀ k : ℕ, r.toModel (fieldPowTwo x k) = (r.toModel x) ^ (2 ^ k)
  | 0 => by simp [fieldPowTwo]
  | k + 1 => by
    simp only [fieldPowTwo, r.map_mul, toModel_fieldPowTwo r x k]
    rw [pow_succ, pow_mul, sq]

omit [FieldOps F] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] in
/-- `placeRowMulti` refines to `placeRowMultiM`. -/
theorem toModel_placeRowMulti (r : Refines EF K) (arity : ℕ) (folded : EF)
    (siblings : Array EF) (idxInGroup : ℕ) :
    (placeRowMulti arity folded siblings idxInGroup).map r.toModel =
      Compiled.placeRowMultiM arity (r.toModel folded) (siblings.map r.toModel) idxInGroup := by
  unfold placeRowMulti Compiled.placeRowMultiM
  refine Array.ext (by simp) fun j h1 h2 => ?_
  simp only [Array.getElem_map, Array.getElem_ofFn]
  split_ifs
  · rfl
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases siblings[j]? <;> simp [r.map_zero]
  · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases siblings[j - 1]? <;> simp [r.map_zero]

omit [Inhabited D] in
private theorem toModel_getD_array (r : Refines EF K) (a : Array EF) (i : ℕ) :
    r.toModel (a.getD i 0) = (a.map r.toModel).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> simp [r.map_zero]

omit [Inhabited D] in
/-- `foldRowMulti` refines to `foldRowMultiM`. -/
theorem toModel_foldRowMulti (m : FieldModel F EF K) (n : ℕ) :
    ∀ (a curLevel groupIdx : ℕ) (beta : EF) (evals : Array EF),
      curLevel + a ≤ n →
      m.ext.toModel (foldRowMulti (F := F) n a curLevel groupIdx beta evals) =
        foldRowMultiM (m.base.toModel (TwoAdicOps.twoAdicGenerator n)) n a curLevel groupIdx
          (m.ext.toModel beta) (evals.map m.ext.toModel)
  | 0, _, _, _, evals, _ => by
    simp only [foldRowMulti, foldRowMultiM]
    exact toModel_getD_array m.ext evals 0
  | a + 1, curLevel, groupIdx, beta, evals, hka => by
    unfold foldRowMulti foldRowMultiM
    rw [toModel_foldRowMulti m n a (curLevel + 1) groupIdx (beta * beta) _ (by omega),
      m.ext.map_mul]
    congr 1
    refine Array.ext (by simp) fun r h1 h2 => ?_
    simp only [Array.getElem_map, Array.getElem_ofFn]
    have hfr := Arith.toModel_foldRow m beta
      (domainPoint (F := F) n curLevel (2 * (groupIdx * 2 ^ a + r)))
      (evals.getD (2 * r) 0) (evals.getD (2 * r + 1) 0)
    have hdp : m.base.toModel (domainPoint (F := F) n curLevel (2 * (groupIdx * 2 ^ a + r))) =
        pointOfIndex (m.base.toModel (TwoAdicOps.twoAdicGenerator n)) n (n - curLevel)
          (2 * (groupIdx * 2 ^ a + r)) := by
      unfold domainPoint pointOfIndex
      rw [toModel_fieldPow, toModel_fieldPow, Nat.sub_sub_self (by omega)]
    rw [hfr, hdp, toModel_getD_array, toModel_getD_array]
    rfl

variable (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
  (wf : WellFormed m params shape)
  (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)

/-- Opening-group levels indexed by round `r ≤ arities.length`. -/
def levelOpeningsMultiOf (params : FriParams) (shape : ClaimShape) (arities : List ℕ) :
    ℕ → List OpeningRef := fun r =>
  (Array.ofFn (n := arities.length + 1) fun r =>
    levelOpenings params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities r.val)).getD r []

theorem levelOpeningsMultiOf_eq {r : ℕ} (hr : r ≤ arities.length) :
    levelOpeningsMultiOf params shape arities r =
      levelOpenings params.logBlowup shape (logMaxHeight params.logBlowup shape)
        (cumLogArity arities r) := by
  have h : r < arities.length + 1 := Nat.lt_succ_of_le hr
  simp [levelOpeningsMultiOf, h]

/-- Query result computed by `verifyWithTensorMulti` for query `t`. -/
def queryResultTensorMulti (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (ch : TensorChallenges EF) (t : ℕ) :
    QueryResultMulti EF :=
  checkQueryTensorMulti (F := F) params shape arities (levelOpeningsMultiOf params shape arities)
    points values proof ch t (ch.indices.getD t 0)

/-- Agreement between executable multi-arity run and compiled multi-arity model values. -/
structure AgreesTensorMulti (commitments : Array D) (points values : Array EF)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof)
    (ch : TensorChallenges EF) (msg : ℕ → Compiled.Msg K D shape.length)
    (r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape))
    (β : ℕ → K) (index : Fin params.numQueries → ℕ) : Prop where
  msg : ∀ j ≤ arities.length + 1,
    msg j = viewMulti m params shape arities (messagesMulti params arities commitments points values proof j)
  colSize : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape)
  openSize : ch.schedule.openChallenges.size =
    tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)
  colWeights : ch.schedule.colWeights =
    tensorWeights ch.schedule.colChallenges (maxWidth shape)
  openWeights : ch.schedule.openWeights =
    tensorWeights ch.schedule.openChallenges (maxOpeningsPerHeight params.logBlowup shape)
  colChals : ∀ b : Fin (tensorNumChallenges (maxWidth shape)),
    r.1 b = m.ext.toModel (ch.schedule.colChallenges[b.val]'(by rw [colSize]; exact b.isLt))
  openChals : ∀ b : Fin (tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)),
    r.2 b = m.ext.toModel (ch.schedule.openChallenges[b.val]'(by rw [openSize]; exact b.isLt))
  beta : ∀ i < arities.length, β i = m.ext.toModel (ch.betas.getD i 0)
  index : ∀ t, index t = ch.indices.getD t.val 0

omit [TwoAdicOps F] [Inhabited D] in
private theorem extsIn_finalMessageMulti (finalPoly : Array EF) :
    extsIn m (finalMessageMulti (F := F) (D := D) arities finalPoly) =
      finalPoly.toList.map m.ext.toModel := by
  have hbase : extsIn m (arities.map fun a => (Observation.base (fieldOfNat (F := F) a) :
      Observation F EF D)) = [] := by
    induction arities with
    | nil => rfl
    | cons a as ih => simp [extsIn]
  rw [finalMessageMulti, Arith.extsIn_append, Arith.extsIn_map_ext, hbase, List.append_nil]

omit [TwoAdicOps F] in
private theorem extsIn_messagesMulti_last {commitments : Array D} {points values : Array EF}
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) :
    extsIn m (messagesMulti params arities commitments points values proof (arities.length + 1)) =
      proof.finalPoly.toList.map m.ext.toModel := by
  have hnot : ¬ (arities.length + 1 ≤ arities.length) := by omega
  simp only [messagesMulti, Nat.succ_ne_zero, ↓reduceIte, hnot, Arith.extsIn_append,
    extsIn_finalMessageMulti]
  split <;> simp [extsIn]

private theorem point_msg_zero_multi {commitments : Array D} {points values : Array EF}
    {InputProof CommitProof : Type} {proof : FriProof F EF D InputProof CommitProof}
    {ch : TensorChallenges EF} {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    {j : ℕ} (hj : j ≤ arities.length)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j)).length) :
    (msg 0).point j k.val =
      m.ext.toModel (points.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          (cumLogArity arities j))[k.val].pointIdx) 0) := by
  have hpts_sz : points.size = (pointRefs params.logBlowup shape).length := by
    simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.2
  have hmem := List.getElem_mem k.isLt
  have hpi : (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j))[k.val].pointIdx < points.size :=
    hpts_sz ▸ Arith.pointIdx_lt_of_mem_levelClaims hmem
  rw [hag.msg 0 (Nat.zero_le _), Compiled.Msg.point]
  simp only [messagesMulti, ↓reduceIte, viewMulti, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hj), Option.map_some,
    Option.getD_some, List.getElem?_eq_getElem k.isLt, Arith.extsIn_firstMessage]
  rw [List.getElem?_append_left (by simp [hpi]), List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hpi), Option.map_some, Option.getD_some,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hpi, Option.getD_some]
  rfl

private theorem value_msg_zero_multi {commitments : Array D} {points values : Array EF}
    {InputProof CommitProof : Type} {proof : FriProof F EF D InputProof CommitProof}
    {ch : TensorChallenges EF} {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    {j : ℕ} (hj : j ≤ arities.length)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j)).length) :
    (msg 0).value j k.val =
      m.ext.toModel (values.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
          (cumLogArity arities j))[k.val].valueIdx) 0) := by
  have hpts_sz : points.size = (pointRefs params.logBlowup shape).length := by
    simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.2
  have hvals_sz : values.size = (claimRefs params.logBlowup shape).length := by
    simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.2
  have hmem := List.getElem_mem k.isLt
  have hvi : (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
      (cumLogArity arities j))[k.val].valueIdx < values.size :=
    hvals_sz ▸ Arith.valueIdx_lt_of_mem_levelClaims hmem
  rw [hag.msg 0 (Nat.zero_le _), Compiled.Msg.value]
  simp only [messagesMulti, ↓reduceIte, viewMulti, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (Nat.lt_succ_of_le hj), Option.map_some,
    Option.getD_some, List.getElem?_eq_getElem k.isLt, Arith.extsIn_firstMessage]
  have hlen : (points.toList.map m.ext.toModel).length = (pointRefs params.logBlowup shape).length := by
    simp [hpts_sz]
  rw [List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using hvi), Option.map_some, Option.getD_some,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hvi, Option.getD_some]
  rfl

private theorem maxWidth_le_two_pow_m (shape : ClaimShape) :
    maxWidth shape ≤ 2 ^ tensorNumChallenges (maxWidth shape) := by
  cases h : maxWidth shape with
  | zero => exact Nat.zero_le _
  | succ w => exact lt_two_pow_tensorNumChallenges (Nat.lt_succ_self w)

private theorem maxOpenings_le_two_pow_m (lb : ℕ) (shape : ClaimShape) :
    maxOpeningsPerHeight lb shape ≤ 2 ^ tensorNumChallenges (maxOpeningsPerHeight lb shape) := by
  cases h : maxOpeningsPerHeight lb shape with
  | zero => exact Nat.zero_le _
  | succ w => exact lt_two_pow_tensorNumChallenges (Nat.lt_succ_self w)

/-- **Multi-arity tensor reduced openings refine to `Compiled.MultiParams.reducedTensor`.** -/
theorem toModel_reducedOpeningsTensorMulti {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    {j : ℕ} (hj : j ≤ arities.length) (t : Fin params.numQueries) (idx : ℕ)
    (hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width) :
    m.ext.toModel ((reducedOpeningsTensorMulti (F := F) (logMaxHeight params.logBlowup shape)
        arities (levelOpeningsMultiOf params shape arities) ch.schedule points values
        (queryRows proof t.val) idx).getD j 0) =
      (modelParamsMulti m params shape arities wf hpos hsum).reducedTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
        (msg 0)
        ((modelParamsMulti m params shape arities wf hpos hsum).opened
          (modelProofMulti m params shape proof) t)
        r idx j := by
  let n := logMaxHeight params.logBlowup shape
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let c := cumLogArity arities j
  let ops := levelOpenings params.logBlowup shape n c
  have hlt : j < arities.length + 1 := Nat.lt_succ_of_le hj
  have hcn : c ≤ n := (cumLogArity_le_sum arities j).trans hsum
  let x : EF := cosetPoint (F := F) n c (idx >>> c)
  let rawOps : List (EF × Array EF × Array F) :=
    ops.map fun o => (points.getD o.pointIdx 0, claimedRow values o,
      openedRow (queryRows proof t.val) o.batch o.matrix)
  have hget : (reducedOpeningsTensorMulti (F := F) n arities
      (levelOpeningsMultiOf params shape arities) ch.schedule points values
      (queryRows proof t.val) idx).getD j 0 =
      Fri.reducedOpeningTensor ch.schedule x
        (rawOps.zipIdx.map fun ((z, cl, op), oIdx) => (oIdx, z, cl, op)) := by
    simp only [reducedOpeningsTensorMulti, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt,
      ↓reduceDIte, Option.getD_some, levelOpeningsMultiOf_eq params shape arities hj, rawOps, x, c]
    congr 1
    have hzip : ∀ (l : List OpeningRef) (s : ℕ),
        (l.zipIdx s).map (fun (o, oIdx) =>
          (oIdx, points.getD o.pointIdx 0, claimedRow values o,
            openedRow (queryRows proof t.val) o.batch o.matrix)) =
        ((l.map fun o => (points.getD o.pointIdx 0, claimedRow values o,
            openedRow (queryRows proof t.val) o.batch o.matrix)).zipIdx s).map
          fun ((z, cl, op), oIdx) => (oIdx, z, cl, op) := by
      intro l; induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro s; simp only [List.zipIdx_cons, List.map_cons]
        exact congrArg (List.cons _) (ih (s + 1))
    simpa only [Array.getD_eq_getD_getElem?] using hzip ops 0
  rw [hget]
  have hsched : ch.schedule =
      { colChallenges := ch.schedule.colChallenges
        openChallenges := ch.schedule.openChallenges
        colWeights := tensorWeights ch.schedule.colChallenges W
        openWeights := tensorWeights ch.schedule.openChallenges M } := by
    cases hs : ch.schedule
    have hcW := hag.colWeights; have hoW := hag.openWeights
    rw [hs] at hcW hoW
    simp only [TensorSchedule.mk.injEq, true_and]
    exact ⟨hcW, hoW⟩
  rw [hsched]
  have hmaxW : W ≤ 2 ^ ch.schedule.colChallenges.size := by
    rw [hag.colSize]; exact maxWidth_le_two_pow_m shape
  have hmaxM : M ≤ 2 ^ ch.schedule.openChallenges.size := by
    rw [hag.openSize]; exact maxOpenings_le_two_pow_m params.logBlowup shape
  have hM : rawOps.length ≤ M := by
    rw [List.length_map]
    exact length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n c
  have hW : ∀ item ∈ rawOps, item.2.1.size ≤ W ∧ item.2.1.size = item.2.2.size := by
    intro item hm
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
    have ho_open : o ∈ openingRefs params.logBlowup shape := (List.mem_filter.mp ho).1
    refine ⟨?_, ?_⟩
    · simp only [claimedRow, Array.size_ofFn]
      exact width_le_maxWidth_of_mem_openingRefs ho_open
    · simp only [claimedRow, Array.size_ofFn]
      exact (hwidths o ho_open).symm
  rw [toModel_reducedOpeningTensor_tensorWeights m ch.schedule.colChallenges
    ch.schedule.openChallenges W M hmaxW hmaxM x rawOps hM hW]
  unfold Compiled.MultiParams.reducedTensor
  let g : ℕ → ℕ → ClaimRef → K := fun oIdx cIdx cl =>
    (if ho : oIdx < M then
      if hc : cIdx < W then
        PcsRbr.tensorCoordWeight r (⟨oIdx, ho⟩, ⟨cIdx, hc⟩)
      else 0
    else 0) *
    ((m.ext.toModel (values.getD cl.valueIdx 0) -
        m.base.toModel (openedEntry (queryRows proof t.val) cl)) *
      (m.ext.toModel (points.getD cl.pointIdx 0) - m.ext.toModel x)⁻¹)
  have hrhs_eq :
      (∑ k : Fin ((modelParamsMulti m params shape arities wf hpos hsum).numClaims j),
          PcsRbr.tensorCoordWeight r (tensorCoordMulti params shape arities j k) *
            (((msg 0).value j k.val -
              (modelParamsMulti m params shape arities wf hpos hsum).opened
                (modelProofMulti m params shape proof) t j k) /
              ((msg 0).point j k.val -
                (modelParamsMulti m params shape arities wf hpos hsum).shift *
                  pointOfIndex (modelParamsMulti m params shape arities wf hpos hsum).ω
                    (modelParamsMulti m params shape arities wf hpos hsum).n
                    ((modelParamsMulti m params shape arities wf hpos hsum).n -
                      (modelParamsMulti m params shape arities wf hpos hsum).cum j)
                    (idx >>> (modelParamsMulti m params shape arities wf hpos hsum).cum j)))) =
        ∑ k : Fin (ops.flatMap expandOpening).length,
          g ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).1
            ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).2
            (ops.flatMap expandOpening)[k.val] := by
    have hfl : ops.flatMap expandOpening = levelClaims params.logBlowup shape n c :=
      flatMap_expandOpening_levelOpenings params.logBlowup shape n c
    refine Finset.sum_bij
      (fun (k : Fin ((modelParamsMulti m params shape arities wf hpos hsum).numClaims j)) _ =>
        (⟨k.val, by rw [hfl]; exact k.isLt⟩ : Fin (ops.flatMap expandOpening).length))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun k _ => ⟨⟨k.val, by
          show k.val < (levelClaims params.logBlowup shape n c).length
          rw [← hfl]; exact k.isLt⟩,
        Finset.mem_univ _, Fin.ext rfl⟩)
      (fun k _ => ?_)
    have hbd := mem_openingCoords_bounds ops 0 _
      (List.getElem_mem (show k.val < (openingCoords ops 0).length by
        rw [length_openingCoords, hfl]; exact k.isLt))
    have ho_lt : ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).1 < M :=
      lt_of_lt_of_le (by simpa using hbd.2.1)
        (length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n c)
    have hc_lt : ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).2 < W := by
      obtain ⟨hidx, hcol⟩ := hbd.2.2
      exact lt_of_lt_of_le hcol
        (width_le_maxWidth_of_mem_openingRefs (List.mem_filter.mp (List.getElem_mem hidx)).1)
    have hpt := point_msg_zero_multi m params shape arities hshape hag hj k
    have hval := value_msg_zero_multi m params shape arities hshape hag hj k
    have hop : (modelParamsMulti m params shape arities wf hpos hsum).opened
        (modelProofMulti m params shape proof) t j k =
        m.base.toModel (openedEntry (queryRows proof t.val)
          ((levelClaims params.logBlowup shape n c)[k.val]'k.isLt)) := by
      let cl := (levelClaims params.logBlowup shape n c)[k.val]'k.isLt
      have hslot : (modelParamsMulti m params shape arities wf hpos hsum).slot j k =
          { batch := ⟨cl.batch, batch_lt_of_mem_claimRefs
                (mem_claimRefs_of_mem_levelClaims (List.getElem_mem k.isLt))⟩
            matrix := cl.matrix
            col := cl.col } := rfl
      unfold Compiled.MultiParams.opened
      rw [hslot]
      dsimp only [modelProofMulti, Compiled.entry, openedEntry]
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getD_eq_getD_getElem?]
      cases hrow : (queryRows proof t.val)[cl.batch]? with
      | none => simp [m.base.map_zero]
      | some mats =>
        simp only [Option.getD_some, Array.getElem?_map]
        cases hmat : mats[cl.matrix]? with
        | none => simp [m.base.map_zero]
        | some row =>
          simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
          cases hcol : row[cl.col]? with
          | none => simp [m.base.map_zero]
          | some v => simp
    have hx_eq : m.ext.toModel x =
        (modelParamsMulti m params shape arities wf hpos hsum).shift *
          pointOfIndex (modelParamsMulti m params shape arities wf hpos hsum).ω
            (modelParamsMulti m params shape arities wf hpos hsum).n
            ((modelParamsMulti m params shape arities wf hpos hsum).n -
              (modelParamsMulti m params shape arities wf hpos hsum).cum j)
            (idx >>> (modelParamsMulti m params shape arities wf hpos hsum).cum j) :=
      toModel_cosetPoint m params shape wf hcn (idx >>> c)
    have hklt : k.val < (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
        (cumLogArity arities j)).length := k.isLt
    have hcl_eq : (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape)
        (cumLogArity arities j))[k.val]'hklt =
        (ops.flatMap expandOpening)[k.val]'(by rw [hfl]; exact hklt) :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hklt,
          ← List.getElem?_eq_getElem (by rw [hfl]; exact hklt), ← hfl])
    have htc : tensorCoordMulti params shape arities j k =
        (⟨((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact hklt)).1, ho_lt⟩,
         ⟨((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact hklt)).2, hc_lt⟩) :=
      rfl
    dsimp only [g]
    rw [dite_eq_left ho_lt, dite_eq_left hc_lt, htc, hpt, hval, hop, ← hx_eq, div_eq_mul_inv]
    refine congrArg (PcsRbr.tensorCoordWeight r _ * ·) ?_
    exact congrArg₂ (· * ·)
      (congrArg₂ (· - ·)
        (congrArg (fun cl => m.ext.toModel (values.getD cl.valueIdx 0)) hcl_eq)
        (congrArg (fun cl => m.base.toModel (openedEntry (queryRows proof t.val) cl)) hcl_eq))
      (congrArg (fun cl => (m.ext.toModel (points.getD cl.pointIdx 0) - m.ext.toModel x)⁻¹) hcl_eq)
  refine (?_ : _ = ∑ k : Fin (ops.flatMap expandOpening).length,
      g ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).1
        ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).2
        (ops.flatMap expandOpening)[k.val]).trans hrhs_eq.symm
  rw [sum_flatMap_expandOpening_eq_sum_nested ops g 0]
  have hlen_raw : rawOps.length = ops.length := List.length_map _
  refine Finset.sum_bij
    (fun (oIdx : Fin rawOps.length) _ => (⟨oIdx.val, hlen_raw ▸ oIdx.isLt⟩ : Fin ops.length))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun oIdx _ => ⟨⟨oIdx.val, hlen_raw.symm ▸ oIdx.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun oIdx _ => ?_)
  have ho_lt : oIdx.val < M := lt_of_lt_of_le oIdx.isLt hM
  have ho_mem : ops[oIdx.val]'(hlen_raw ▸ oIdx.isLt) ∈ openingRefs params.logBlowup shape :=
    (List.mem_filter.mp (List.getElem_mem (hlen_raw ▸ oIdx.isLt))).1
  have hw_le : (ops[oIdx.val]'(hlen_raw ▸ oIdx.isLt)).width ≤ W :=
    width_le_maxWidth_of_mem_openingRefs ho_mem
  have hopen_eq :
      tensorWeight (fun b : Fin ch.schedule.openChallenges.size =>
        m.ext.toModel ch.schedule.openChallenges[b.val])
        ⟨oIdx.val, lt_of_lt_of_le ho_lt hmaxM⟩ =
      tensorWeight r.2 ⟨oIdx.val, lt_two_pow_tensorNumChallenges ho_lt⟩ := by
    unfold tensorWeight
    refine Finset.prod_bij
      (fun (b : Fin ch.schedule.openChallenges.size) _ =>
        (⟨b.val, hag.openSize ▸ b.isLt⟩ : Fin (tensorNumChallenges M)))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun b _ => ⟨⟨b.val, hag.openSize.symm ▸ b.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun b _ => ?_)
    simp only [← hag.openChals ⟨b.val, hag.openSize ▸ b.isLt⟩]
  rw [hopen_eq, Finset.mul_sum]
  have hsz_eq : (rawOps[oIdx.val].2.1).size = (ops[oIdx.val]'(hlen_raw ▸ oIdx.isLt)).width := by
    simp [rawOps, claimedRow]
  refine Finset.sum_bij
    (fun (cIdx : Fin rawOps[oIdx.val].2.1.size) _ =>
      (⟨cIdx.val, by rw [← hsz_eq]; exact cIdx.isLt⟩ : Fin (ops[oIdx.val]'(hlen_raw ▸ oIdx.isLt)).width))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun cIdx _ => ⟨⟨cIdx.val, by rw [hsz_eq]; exact cIdx.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun cIdx _ => ?_)
  have hc_w : cIdx.val < (ops[oIdx.val]'(hlen_raw ▸ oIdx.isLt)).width := by
    rw [← hsz_eq]; exact cIdx.isLt
  have hc_lt : cIdx.val < W := lt_of_lt_of_le hc_w hw_le
  have hcol_eq :
      tensorWeight (fun b : Fin ch.schedule.colChallenges.size =>
        m.ext.toModel ch.schedule.colChallenges[b.val])
        ⟨cIdx.val, lt_of_lt_of_le hc_lt hmaxW⟩ =
      tensorWeight r.1 ⟨cIdx.val, lt_two_pow_tensorNumChallenges hc_lt⟩ := by
    unfold tensorWeight
    refine Finset.prod_bij
      (fun (b : Fin ch.schedule.colChallenges.size) _ =>
        (⟨b.val, hag.colSize ▸ b.isLt⟩ : Fin (tensorNumChallenges W)))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun b _ => ⟨⟨b.val, hag.colSize.symm ▸ b.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun b _ => ?_)
    simp only [← hag.colChals ⟨b.val, hag.colSize ▸ b.isLt⟩]
  simp only [g, Nat.zero_add, dite_eq_left ho_lt, dite_eq_left hc_lt, hcol_eq,
    PcsRbr.tensorCoordWeight, rawOps, List.getElem_map, claimedRow, Array.getD_eq_getD_getElem?,
    Array.getElem?_ofFn, dite_eq_left hc_w, Option.getD_some, openedRow, openedEntry]
  ring

/-- **Multi-arity fold chain refines to `Compiled.MultiParams.foldedTensor` and `commitRowTensor`.** -/
theorem toModel_foldChainMulti {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    (t : Fin params.numQueries) (idx : ℕ)
    (hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    let ros := reducedOpeningsTensorMulti (F := F) (logMaxHeight params.logBlowup shape) arities
      (levelOpeningsMultiOf params shape arities) ch.schedule points values
      (queryRows proof t.val) idx
    ∀ i ≤ arities.length,
      m.ext.toModel (foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities ros
          (fun k => siblingsMulti proof k t.val) ch.betas idx i).1 =
        P.foldedTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
          (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
          (msg 0) r β idx t i ∧
      (foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities ros
          (fun k => siblingsMulti proof k t.val) ch.betas idx i).2.length = i ∧
      ∀ k < i,
        ((foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities ros
            (fun k => siblingsMulti proof k t.val) ch.betas idx i).2.getD k #[]).map m.ext.toModel =
          P.commitRowTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
            (msg 0) r β idx t k := by
  intro P ros i
  induction i with
  | zero =>
    intro _
    refine ⟨?_, rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    exact toModel_reducedOpeningsTensorMulti m params shape arities wf hpos hsum hshape hag
      (Nat.zero_le _) t idx hwidths
  | succ i ih =>
    intro hi
    have hi_lt : i < arities.length := hi
    obtain ⟨hfst, hlen, hrows⟩ := ih (Nat.le_of_succ_le hi)
    have ha_eq : arities.getD i 1 = P.logArity i := by
      simp only [P, modelParamsMulti, Compiled.MultiParams.logArity,
        List.getD_eq_getElem _ _ hi_lt]
    have hka : P.cum i + P.logArity i ≤ P.n := by
      rw [← P.cum_succ hi_lt]; exact P.cum_le_n (i + 1)
    have hrow_map :
        (placeRowMulti (2 ^ arities.getD i 1)
            (foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities ros
              (fun k => siblingsMulti proof k t.val) ch.betas idx i).1
            (siblingsMulti proof i t.val) ((idx >>> cumLogArity arities i) % 2 ^ arities.getD i 1)).map
            m.ext.toModel =
          P.commitRowTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
            (msg 0) r β idx t i := by
      rw [toModel_placeRowMulti, hfst, ha_eq]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · have hfold_eq :
          m.ext.toModel (foldRowMulti (F := F) (logMaxHeight params.logBlowup shape)
              (arities.getD i 1) (cumLogArity arities i)
              (idx >>> (cumLogArity arities i + arities.getD i 1)) (ch.betas.getD i 0)
              (placeRowMulti (2 ^ arities.getD i 1)
                (foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities ros
                  (fun k => siblingsMulti proof k t.val) ch.betas idx i).1
                (siblingsMulti proof i t.val)
                ((idx >>> cumLogArity arities i) % 2 ^ arities.getD i 1))) =
            foldRowMultiM P.ω P.n (P.logArity i) (P.cum i) (idx >>> (P.cum i + P.logArity i)) (β i)
              (P.commitRowTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
                (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
                (msg 0) r β idx t i) := by
        have hka' : cumLogArity arities i + arities.getD i 1 ≤ logMaxHeight params.logBlowup shape := by
          rw [ha_eq]; exact hka
        rw [toModel_foldRowMulti m _ _ _ _ _ _ hka', hrow_map, ha_eq, ← hag.beta i hi_lt]
        rfl
      have hro_eq :
          m.ext.toModel (fieldPowTwo (ch.betas.getD i 0) (arities.getD i 1) * ros.getD (i + 1) 0) =
            β i ^ 2 ^ P.logArity i * P.reducedTensor (maxWidth shape)
              (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
              (msg 0) (P.opened (modelProofMulti m params shape proof) t) r idx (i + 1) := by
        rw [m.ext.map_mul, toModel_fieldPowTwo, ha_eq, ← hag.beta i hi_lt]
        exact congrArg (β i ^ 2 ^ P.logArity i * ·)
          (toModel_reducedOpeningsTensorMulti m params shape arities wf hpos hsum hshape hag
            hi t idx hwidths)
      show m.ext.toModel (_ + _) = _
      rw [m.ext.map_add]
      exact congrArg₂ (· + ·) hfold_eq hro_eq
    · simp only [foldChainMulti, List.length_append, List.length_singleton, hlen]
    · intro k hk
      simp only [foldChainMulti]
      rw [List.getD_eq_getElem?_getD]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]
        have hprev := hrows k hlt
        rwa [List.getD_eq_getElem?_getD] at hprev
      · rw [List.getElem?_append_right (by rw [hlen]), hlen, Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
        exact hrow_map

/-- Model checks predicate for compiled multi-arity tensor FRI (matches
`Compiled.MultiParams.run_verifyWithTensor`). -/
def modelChecksTensorMulti [DecidableEq K] [DecidableEq D] (P : Compiled.MultiParams K)
    (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (H : MerkleHasher K D)
    (pf : Compiled.MultiProof K D P.batches P.queries) (msg : ℕ → Compiled.Msg K D P.batches)
    (r : PcsRbr.TensorChal K W M) (β : ℕ → K) (index : Fin P.queries → ℕ) : Bool :=
  ((List.finRange P.batches).all fun b =>
      Merkle.verifyOpenings H ((msg 0).inputRoots b) (P.dims b)
        (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
        (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
    decide (P.FinalCheckTensor W M coord pf msg r β index) &&
    (List.range P.rounds).all fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot (P.commitDims i)
        (Array.ofFn fun t => index t >>> P.cum (i + 1))
        (Array.ofFn fun t => #[P.commitRowTensor W M coord pf (msg 0) r β (index t) t i])
        (Array.ofFn (pf.commitPaths i))

/-- **Executable `verifyWithTensorMulti` refines to `modelChecksTensorMulti`.** -/
theorem modelChecksTensorMulti_of_verifyWithTensorMulti [DecidableEq K] [DecidableEq D]
    (H : MerkleHasher K D) {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true)
    (hag : AgreesTensorMulti m params shape arities commitments points values proof ch msg r β index)
    (h : verifyWithTensorMulti (merkleMmcs (inputHasher m H)) (merkleMmcs (friHasher m H))
      params shape arities commitments points values proof ch = true) :
    ch.powOk = true ∧
      modelChecksTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (tensorCoordMulti params shape arities) H
        (modelProofMulti m params shape proof) msg r β index = true := by
  let P := modelParamsMulti m params shape arities wf hpos hsum
  have h' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun t =>
        decide (ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs (inputHasher m H)) params shape commitments
        proof.inputOpenings ch.indices
      && (Array.ofFn fun t : Fin params.numQueries =>
        queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).all
          (·.ok)
      && commitChecksMulti (merkleMmcs (friHasher m H)) params.numQueries
        (logMaxHeight params.logBlowup shape) arities proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun t : Fin params.numQueries =>
          queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).map
            (·.rows))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hpow, -⟩, -⟩, hin⟩, hok⟩, hcommit⟩ := h'
  have hok_all : ∀ t : Fin params.numQueries,
      (queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).ok =
        true := fun t => by
    have := Array.all_eq_true.mp hok t.val (by rw [Array.size_ofFn]; exact t.isLt)
    simpa using this
  have hwidths_all : ∀ t : Fin params.numQueries, ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width := fun t o ho => by
    have hq := hok_all t
    simp only [queryResultTensorMulti, checkQueryTensorMulti, Bool.and_eq_true,
      List.all_eq_true, beq_iff_eq] at hq
    exact hq.1.1.1 o ho
  refine ⟨hpow, ?_⟩
  -- 1. Input Merkle checks
  have hin_model : ((List.finRange P.batches).all fun b =>
      Merkle.verifyOpenings H ((msg 0).inputRoots b) (P.dims b)
        (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
        (Array.ofFn ((modelProofMulti m params shape proof).inputRows b))
        (Array.ofFn ((modelProofMulti m params shape proof).inputPaths b))) = true := by
    rw [List.all_eq_true]
    intro b _
    have hblt : b.val < shape.length := b.isLt
    obtain ⟨root, opening, hroot, ho, hv⟩ := Checks.inputChecks_merkle _ hin hblt
    obtain ⟨hrows_sz, hpaths_sz⟩ := Checks.size_of_verifyOpenings hv
    rw [Array.size_ofFn] at hrows_sz hpaths_sz
    rw [Checks.verifyOpenings_inputHasher] at hv
    have hroot_eq : (msg 0).inputRoots b = root := by
      have hcomm_sz : commitments.size = shape.length := by
        simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
        exact hshape.1.1.1.1.1.1.1.1.1.2
      rw [hag.msg 0 (Nat.zero_le _)]
      simp only [viewMulti, messagesMulti, ↓reduceIte, Checks.digestsIn_firstMessage,
        List.getD_eq_getElem?_getD, Array.getElem?_toList, hroot, Option.getD_some]
    have hrows_eq : opening.openedValues.map (fun r => r.map (fun row => row.map m.base.toModel)) =
        Array.ofFn ((modelProofMulti m params shape proof).inputRows b) := by
      refine Array.ext (by simp [hrows_sz]) fun t h1 h2 => ?_
      simp only [Array.getElem_map, Array.getElem_ofFn, modelProofMulti, queryRows]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, ho, Option.map_some, Option.getD_some,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa [hrows_sz] using h1),
        Option.getD_some]
    have hpaths_eq : opening.openingProof =
        Array.ofFn ((modelProofMulti m params shape proof).inputPaths b) := by
      refine Array.ext (by simp [hpaths_sz]) fun t h1 h2 => ?_
      simp only [Array.getElem_ofFn, modelProofMulti, ho, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem h1, Option.getD_some]
    rw [hroot_eq, ← hrows_eq, ← hpaths_eq]
    simpa only [P, modelParamsMulti, hag.index] using hv
  -- 2. Final polynomial check
  have hfin : P.FinalCheckTensor (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
      (modelProofMulti m params shape proof) msg r β index := by
    intro t
    have hq := hok_all t
    simp only [queryResultTensorMulti, checkQueryTensorMulti, Bool.and_eq_true] at hq
    have hfeq := (m.ext.beq_iff _ _).mp hq.2
    have hchain := (toModel_foldChainMulti m params shape arities wf hpos hsum hshape hag
      t (index t) (hwidths_all t) arities.length le_rfl).1
    have hdp : m.base.toModel (domainPoint (F := F) (logMaxHeight params.logBlowup shape)
        arities.sum (ch.indices.getD t.val 0 >>> arities.sum)) =
        pointOfIndex P.ω P.n (P.n - arities.sum) (index t >>> arities.sum) := by
      rw [← hag.index t]
      exact toModel_domainPoint m params shape wf hsum (index t >>> arities.sum)
    have hfp_sz : proof.finalPoly.size = params.finalPolyLen := by
      simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
      exact hshape.1.1.2
    have hcoeffs : ((msg (arities.length + 1)).finalCoeffs.take P.finalDegree) =
        proof.finalPoly.toList.map m.ext.toModel := by
      rw [hag.msg (arities.length + 1) le_rfl]
      simp only [viewMulti, extsIn_messagesMulti_last]
      exact List.take_of_length_le (by simp [P, modelParamsMulti, hfp_sz])
    have hlhs : P.foldedTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
        (msg 0) r β (index t) t P.rounds =
        m.ext.toModel (foldChainMulti (F := F) (logMaxHeight params.logBlowup shape) arities
          (reducedOpeningsTensorMulti (F := F) (logMaxHeight params.logBlowup shape) arities
            (levelOpeningsMultiOf params shape arities) ch.schedule points values
            (queryRows proof t.val) (ch.indices.getD t.val 0))
          (fun k => siblingsMulti proof k t.val) ch.betas (ch.indices.getD t.val 0)
          arities.length).1 := by
      rw [← hag.index t]
      exact hchain.symm
    have hsum_ar : P.arities.sum = arities.sum := rfl
    show P.foldedTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
        (msg 0) r β (index t) t P.rounds =
      Compiled.hornerEval ((msg (P.rounds + 1)).finalCoeffs.take P.finalDegree)
        (pointOfIndex P.ω P.n (P.n - P.arities.sum) (index t >>> P.arities.sum))
    rw [hlhs, hfeq, m.ext.horner_eq_eval, m.embed, hsum_ar, hdp, ← Compiled.hornerEval_eq_eval,
      ← hcoeffs]
    rfl
  -- 3. Commit-phase Merkle checks
  have hcm : ((List.range P.rounds).all fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot (P.commitDims i)
        (Array.ofFn fun t => index t >>> P.cum (i + 1))
        (Array.ofFn fun t => #[P.commitRowTensor (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
          (modelProofMulti m params shape proof) (msg 0) r β (index t) t i])
        (Array.ofFn ((modelProofMulti m params shape proof).commitPaths i))) = true := by
    have hcommit_round : ∀ (h : MerkleHasher EF D) {numQueries n : ℕ} {arities : List ℕ}
        {commits : Array D} {openings : Array (CommitPhaseStep EF (Array (List D)))}
        {indices : Array ℕ} {rows : Array (List (Array EF))},
        commitChecksMulti (merkleMmcs h) numQueries n arities commits openings indices rows = true →
        ∀ i < arities.length,
          ∃ (root : D) (opening : CommitPhaseStep EF (Array (List D))),
            commits[i]? = some root ∧ openings[i]? = some opening ∧
            Merkle.verifyOpenings h root
              #[Dimensions.mk (2 ^ arities.getD i 1) (n - cumLogArity arities (i + 1))]
              (Array.ofFn (n := numQueries) fun t =>
                indices.getD t.val 0 >>> cumLogArity arities (i + 1))
              (Array.ofFn (n := numQueries) fun t => #[(rows.getD t.val []).getD i #[]])
              opening.openingProof = true := by
      intro h numQueries n arities commits openings indices rows hc i hi
      simp only [commitChecksMulti, List.all_eq_true, List.mem_range] at hc
      have hci := hc i hi
      split at hci
      · next root opening hroot ho => exact ⟨root, opening, hroot, ho, hci⟩
      · exact absurd hci (by simp)
    rw [List.all_eq_true]
    intro i hi
    have hi_lt : i < arities.length := List.mem_range.mp hi
    obtain ⟨root, opening, hroot, ho, hci⟩ := hcommit_round (friHasher m H) hcommit i hi_lt
    obtain ⟨-, hpaths_sz⟩ := Checks.size_of_verifyOpenings hci
    rw [Array.size_ofFn] at hpaths_sz
    rw [Checks.verifyOpenings_friHasher] at hci
    have hroot_eq : (msg (i + 1)).commitRoot = root := by
      rw [hag.msg (i + 1) (by omega)]
      simp [viewMulti, messagesMulti, hi_lt, digestsIn, hroot]
    have ha_eq : arities.getD i 1 = P.logArity i := by
      simp only [P, modelParamsMulti, Compiled.MultiParams.logArity,
        List.getD_eq_getElem _ _ hi_lt]
    have hdims_eq : #[Dimensions.mk (2 ^ arities.getD i 1)
        (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1))] = P.commitDims i := by
      rw [ha_eq]; rfl
    have hpaths_eq : opening.openingProof =
        Array.ofFn ((modelProofMulti m params shape proof).commitPaths i) := by
      refine Array.ext (by simp [hpaths_sz]) fun t h1 h2 => ?_
      simp only [Array.getElem_ofFn, modelProofMulti, ho, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem h1, Option.getD_some]
    have hrows_eq :
        (Array.ofFn fun t : Fin params.numQueries =>
          #[(((Array.ofFn fun t : Fin params.numQueries =>
              queryResultTensorMulti (F := F) params shape arities points values proof ch t.val).map
                (·.rows)).getD t.val []).getD i #[]]).map
          (fun r => r.map (fun row => row.map m.ext.toModel)) =
        Array.ofFn fun t : Fin params.numQueries =>
          #[P.commitRowTensor (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (tensorCoordMulti params shape arities) (modelProofMulti m params shape proof)
            (msg 0) r β (index t) t i] := by
      refine Array.ext (by simp) fun t h1 h2 => ?_
      have ht_lt : t < params.numQueries := by simpa using h1
      simp only [Array.getElem_map, Array.getElem_ofFn, Array.getD_eq_getD_getElem?,
        Array.getElem?_map, Array.getElem?_ofFn, dite_eq_left ht_lt, Option.map_some,
        Option.getD_some]
      have hrow := (toModel_foldChainMulti m params shape arities wf hpos hsum hshape hag
        ⟨t, ht_lt⟩ (index ⟨t, ht_lt⟩) (hwidths_all ⟨t, ht_lt⟩) arities.length le_rfl).2.2 i hi_lt
      rw [hag.index ⟨t, ht_lt⟩] at hrow
      have hmap1 : ∀ (x : Array EF), Array.map (fun row => Array.map m.ext.toModel row) #[x] =
          #[Array.map m.ext.toModel x] := fun x => by simp
      rw [hmap1, hag.index ⟨t, ht_lt⟩]
      exact congrArg (fun x => #[x]) hrow
    rw [hroot_eq, ← hdims_eq, ← hpaths_eq, ← hrows_eq]
    simpa only [P, modelParamsMulti, hag.index] using hci
  simp only [modelChecksTensorMulti, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hin_model, hfin⟩, hcm⟩

end MultiArith

/-! ## 3. Idealised multi-arity tensor challenger & transcript refinement -/

section MultiTranscript

open Oracle
open PcsRbr (TensorChal ChalTensorMulti GrindChal)

variable {F EF D K : Type} [Field K] [DecidableEq K]

def freeAnswerTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x)
    (s : FreeState F EF D) : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) s.round :=
  f (.chal (fsTranscript f s.hist s.round) s.cur)

def queryPointTensorMulti (P : Compiled.MultiParams K) {W M i : ℕ}
    (c : ChalTensorMulti P.ldt W M P.queries i) (k : ℕ) : K :=
  if h : k < P.queries then c.points ⟨k, h⟩ else 0

noncomputable def freeChallengerTensorMulti [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    (P : Compiled.MultiParams K) (W M firstLen : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x)
    (m : FieldModel F EF K) :
    Challenger (FreeState F EF D) F EF D where
  observe s o :=
    if s.nsamp = 0 then
      if s.round = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
          s.cur.length = firstLen then
        ⟨1, Function.update s.hist 0 s.cur, [o], 0⟩
      else { s with cur := s.cur ++ [o] }
    else ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩
  sampleExt s :=
    let ans := freeAnswerTensorMulti P W M bits f s
    let val : K :=
      if s.round = 0 then
        let kCol := Fri.tensorNumChallenges W
        let kOpen := Fri.tensorNumChallenges M
        if h1 : s.nsamp < kCol then ans.2.tensor.1 ⟨s.nsamp, h1⟩
        else if h2 : s.nsamp - kCol < kOpen then ans.2.tensor.2 ⟨s.nsamp - kCol, h2⟩
        else 0
      else ans.2.field
    (Function.surjInv m.surj val, { s with nsamp := s.nsamp + 1 })
  sampleBits s _ :=
    let ans := freeAnswerTensorMulti P W M bits f s
    (if s.nsamp = 0 ∧ bits s.round ≠ 0 then (ans.1 : ℕ)
      else P.indexOf (queryPointTensorMulti P ans.2
        (s.nsamp - if bits s.round = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

namespace MultiTranscriptProof

variable (P : Compiled.MultiParams K) (W M firstLen : ℕ) (bits : ℕ → ℕ)
  (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries))
      (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x)
  {ms : ℕ → RawMsg F EF D}

private theorem freeAnswerTensorMulti_mk {i : ℕ} {hist : ℕ → RawMsg F EF D}
    (hh : ∀ j < i, hist j = ms j) (k : ℕ) :
    freeAnswerTensorMulti P W M bits f ⟨i, hist, ms i, k⟩ = Transcript.answer f ms i := by
  unfold freeAnswerTensorMulti Transcript.answer
  rw [Transcript.fsTranscript_congr f hh]

variable [FieldOps F] [FieldOps EF] [ExtensionOps F EF] (m : FieldModel F EF K)

private def ReadyToAdvanceM (W M i k : ℕ) : Prop :=
  1 ≤ k ∨ (i = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0)

private theorem observe_extend {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0) (hno : i ≠ 0 ∨ cur.length < firstLen)
    (o : Observation F EF D) :
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).observe s o)
      i (cur ++ [o]) 0 := by
  have hcond : ¬ (s.round = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
      s.cur.length = firstLen) := by
    rw [h.round, h.cur]
    rintro ⟨rfl, -, hlen⟩
    rcases hno with hne | hlt
    · exact hne rfl
    · omega
  have hs : (freeChallengerTensorMulti P W M firstLen bits f m).observe s o =
      { s with cur := s.cur ++ [o] } := by
    unfold freeChallengerTensorMulti; dsimp only
    rw [ite_eq_left h.nsamp, ite_eq_right hcond]
  rw [hs]
  exact ⟨h.round, h.hist, by rw [← h.cur], h.nsamp⟩

private theorem observeAll_round0 {s : FreeState F EF D} {cur : RawMsg F EF D}
    (h : Transcript.At ms s 0 cur 0) (l : List (Observation F EF D))
    (hlen : cur.length + l.length ≤ firstLen) :
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).observeAll s l)
      0 (cur ++ l) 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have hlt : cur.length < firstLen := by simp at hlen; omega
    have h1 := observe_extend P W M firstLen bits f m h (Or.inr hlt) o
    have h2 := ih h1 (by simp at hlen ⊢; omega)
    rwa [List.append_assoc] at h2

private theorem observeAll_pos {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0) (hi : i ≠ 0) (l : List (Observation F EF D)) :
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).observeAll s l)
      i (cur ++ l) 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have h1 := observe_extend P W M firstLen bits f m h (Or.inl hi) o
    have h2 := ih h1
    rwa [List.append_assoc] at h2

private theorem observe_next {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hr : ReadyToAdvanceM W M i k)
    (hlen0 : i = 0 → (ms 0).length = firstLen) (o : Observation F EF D) :
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).observe s o)
      (i + 1) [o] 0 := by
  have hs : (freeChallengerTensorMulti P W M firstLen bits f m).observe s o =
      ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩ := by
    unfold freeChallengerTensorMulti; dsimp only
    rcases hr with hk | ⟨rfl, hzero⟩
    · rw [ite_eq_right (by rw [h.nsamp]; omega)]
    · by_cases hk0 : s.nsamp = 0
      · rw [ite_eq_left hk0, ite_eq_left ⟨h.round, hzero, by rw [h.cur]; exact hlen0 rfl⟩]
        simp [h.round]
      · rw [ite_eq_right hk0]
  rw [hs]
  refine ⟨by rw [← h.round], fun j hj => ?_, rfl, rfl⟩
  show Function.update s.hist s.round s.cur j = ms j
  rw [h.round, h.cur]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · rw [Function.update_of_ne hlt.ne]; exact h.hist j hlt
  · rw [Function.update_self]

private theorem observeAll_next {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hr : ReadyToAdvanceM W M i k)
    (hlen0 : i = 0 → (ms 0).length = firstLen) {l : List (Observation F EF D)} (hl : l ≠ []) :
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).observeAll s l)
      (i + 1) l 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l =>
    exact observeAll_pos P W M firstLen bits f m
      (observe_next P W M firstLen bits f m h hr hlen0 o) (Nat.succ_ne_zero i) l

private theorem sampleExt_col {s : FreeState F EF D} {k : ℕ}
    (h : Transcript.At ms s 0 (ms 0) k) (hk : k < Fri.tensorNumChallenges W) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.1 ⟨k, hk⟩) ∧
      Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).2
        0 (ms 0) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensorMulti, ↓reduceIte, hk, ↓reduceDIte,
    freeAnswerTensorMulti_mk P W M bits f hh]

private theorem sampleExtMany_col (cnt start : ℕ) (hcnt : start + cnt ≤ Fri.tensorNumChallenges W)
    {s : FreeState F EF D} (h : Transcript.At ms s 0 (ms 0) start) :
    (sampleExtMany (freeChallengerTensorMulti P W M firstLen bits f m) cnt s).1 =
      List.ofFn (fun j : Fin cnt =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.1 ⟨start + j.val, by omega⟩)) ∧
    Transcript.At ms
      (sampleExtMany (freeChallengerTensorMulti P W M firstLen bits f m) cnt s).2
      0 (ms 0) (start + cnt) := by
  induction cnt generalizing start s with
  | zero => exact ⟨rfl, by simpa [sampleExtMany] using h⟩
  | succ cnt ih =>
    obtain ⟨h1, hs1⟩ := sampleExt_col P W M firstLen bits f m h (by omega)
    obtain ⟨hrest, hs2⟩ := ih (start + 1) (by omega) hs1
    refine ⟨?_, by rwa [show start + 1 + cnt = start + (cnt + 1) by omega] at hs2⟩
    simp only [sampleExtMany, h1, hrest, List.ofFn_succ]
    refine congrArg₂ List.cons rfl ?_
    congr 1; funext j; congr 1; apply congrArg; ext; simp only [Fin.val_succ]; omega

private theorem sampleExt_open {s : FreeState F EF D} {k : ℕ}
    (h : Transcript.At ms s 0 (ms 0) (Fri.tensorNumChallenges W + k))
    (hk : k < Fri.tensorNumChallenges M) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.2 ⟨k, hk⟩) ∧
      Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).2
        0 (ms 0) (Fri.tensorNumChallenges W + k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  have hnot : ¬ (Fri.tensorNumChallenges W + k < Fri.tensorNumChallenges W) := by omega
  have hsub : Fri.tensorNumChallenges W + k - Fri.tensorNumChallenges W = k :=
    Nat.add_sub_cancel_left _ _
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensorMulti, ↓reduceIte, hnot, ↓reduceDIte, hsub, hk,
    freeAnswerTensorMulti_mk P W M bits f hh]

private theorem sampleExtMany_open (cnt start : ℕ) (hcnt : start + cnt ≤ Fri.tensorNumChallenges M)
    {s : FreeState F EF D} (h : Transcript.At ms s 0 (ms 0) (Fri.tensorNumChallenges W + start)) :
    (sampleExtMany (freeChallengerTensorMulti P W M firstLen bits f m) cnt s).1 =
      List.ofFn (fun j : Fin cnt =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.2 ⟨start + j.val, by omega⟩)) ∧
    Transcript.At ms
      (sampleExtMany (freeChallengerTensorMulti P W M firstLen bits f m) cnt s).2
      0 (ms 0) (Fri.tensorNumChallenges W + (start + cnt)) := by
  induction cnt generalizing start s with
  | zero => exact ⟨rfl, by simpa [sampleExtMany] using h⟩
  | succ cnt ih =>
    obtain ⟨h1, hs1⟩ := sampleExt_open P W M firstLen bits f m h (by omega)
    obtain ⟨hrest, hs2⟩ := ih (start + 1) (by omega) (by rwa [Nat.add_assoc] at hs1)
    refine ⟨?_, by rwa [show start + 1 + cnt = start + (cnt + 1) by omega] at hs2⟩
    simp only [sampleExtMany, h1, hrest, List.ofFn_succ]
    refine congrArg₂ List.cons rfl ?_
    congr 1; funext j; congr 1; apply congrArg; ext; simp only [Fin.val_succ]; omega

private theorem sampleExt_pos {s : FreeState F EF D} {i k : ℕ} (hi : i ≠ 0)
    (h : Transcript.At ms s i (ms i) k) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj (Transcript.answer f ms i).2.field ∧
      Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).sampleExt s).2
        i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensorMulti, hi, ↓reduceIte,
    freeAnswerTensorMulti_mk P W M bits f hh]

private theorem sampleBits_pow {s : FreeState F EF D} {i : ℕ}
    (h : Transcript.At ms s i (ms i) 0) (hb : bits i ≠ 0) (b : ℕ) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleBits s b).1 =
        ((Transcript.answer f ms i).1 : ℕ) ∧
      Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).sampleBits s b).2
        i (ms i) 1 := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensorMulti, true_and, freeAnswerTensorMulti_mk P W M bits f hh]
  rw [ite_eq_left hb]

private theorem sampleBits_query {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hk : k = 0 → bits i = 0) (b : ℕ) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleBits s b).1 =
        P.indexOf (queryPointTensorMulti P (Transcript.answer f ms i).2
          (k - if bits i = 0 then 0 else 1)) ∧
      Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).sampleBits s b).2
        i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  have hcond : ¬ (n = 0 ∧ bits r ≠ 0) := fun hn => hn.2 (hk hn.1)
  simp only [freeChallengerTensorMulti, hcond, ↓reduceIte,
    freeAnswerTensorMulti_mk P W M bits f hh]

private theorem checkWitness_pos {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0) (hi : i ≠ 0) (b : ℕ) (w : F)
    (hms : ms i = cur ++ if b = 0 then [] else [.base w]) (hb : bits i = b) :
    (((freeChallengerTensorMulti P W M firstLen bits f m).checkWitness s b w).1 = true →
      (Transcript.answer f ms i).1.val = 0) ∧
    Transcript.At ms ((freeChallengerTensorMulti P W M firstLen bits f m).checkWitness s b w).2
      i (ms i) (if b = 0 then 0 else 1) := by
  have hok : ∀ st, (freeChallengerTensorMulti P W M firstLen bits f m).ok st = true := fun _ => rfl
  by_cases h0 : b = 0
  · rw [ite_eq_left h0, List.append_nil] at hms
    rw [Challenger.checkWitness, hok, Bool.not_true, ite_eq_right (by simp), ite_eq_left h0,
      ite_eq_left h0, hms]
    exact ⟨fun _ => Transcript.fin_val_eq_zero (hb.trans h0) _, hms ▸ h⟩
  · rw [ite_eq_right h0] at hms
    have h1 := observe_extend P W M firstLen bits f m h (Or.inl hi) (.base w)
    rw [← hms] at h1
    obtain ⟨hv, hs⟩ := sampleBits_pow P W M firstLen bits f m h1 (hb ▸ h0) b
    rw [Challenger.checkWitness, hok, Bool.not_true, ite_eq_right (by simp), ite_eq_right h0,
      ite_eq_right h0]
    simp only [hok, Bool.true_and]
    refine ⟨fun hz => ?_, hs⟩
    rw [← hv]
    exact eq_of_beq hz

private theorem commitPhase_free [Inhabited D] (commitPowBits : ℕ) (commits : Array D)
    (witnesses : Array F) :
    ∀ (r : ℕ),
      (∀ i < r, ms (i + 1) = .digest (commits.getD i default) ::
        if commitPowBits = 0 then [] else [.base (witnesses.getD i 0)]) →
      (∀ i < r, bits (i + 1) = commitPowBits) →
      (ms 0).length = firstLen →
      ∀ {s : FreeState F EF D} {k₀ : ℕ},
        Transcript.At ms s 0 (ms 0) k₀ → ReadyToAdvanceM W M 0 k₀ →
        let res := commitPhase (freeChallengerTensorMulti P W M firstLen bits f m)
          commitPowBits commits witnesses r s
        res.1 = ((List.range r).map fun i =>
            Function.surjInv m.surj (Transcript.answer f ms (i + 1)).2.field).toArray ∧
          (res.2.1 = true → ∀ i < r, (Transcript.answer f ms (i + 1)).1.val = 0) ∧
          ∃ k, Transcript.At ms res.2.2 r (ms r) k ∧ ReadyToAdvanceM W M r k
  | 0, _, _, _, _, _, h0, hr0 => ⟨rfl, fun _ _ hi => absurd hi (Nat.not_lt_zero _), _, h0, hr0⟩
  | r + 1, hms, hbits, hlen0, s, k₀, h0, hr0 => by
    obtain ⟨hbetas, hpow, k, hr, hready⟩ := commitPhase_free commitPowBits commits witnesses r
      (fun i hi => hms i (Nat.lt_succ_of_lt hi)) (fun i hi => hbits i (Nat.lt_succ_of_lt hi))
      hlen0 h0 hr0
    have hobs := observe_next P W M firstLen bits f m hr hready (fun _ => hlen0)
      (.digest (commits.getD r default))
    obtain ⟨hpow_r, hchk⟩ := checkWitness_pos P W M firstLen bits f m hobs (Nat.succ_ne_zero r)
      commitPowBits (witnesses.getD r 0) (by simpa using hms r (Nat.lt_succ_self r))
      (hbits r (Nat.lt_succ_self r))
    obtain ⟨hsamp, hfin⟩ := sampleExt_pos P W M firstLen bits f m (Nat.succ_ne_zero r) hchk
    refine ⟨?_, ?_, _, hfin, Or.inl (Nat.le_add_left 1 _)⟩
    · rw [commitPhase, hbetas, hsamp, List.push_toArray, List.range_succ, List.map_append,
        List.map_singleton]
    · intro hok i hi
      simp only [commitPhase, Bool.and_eq_true] at hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hpow hok.1 i hlt
      · exact hpow_r hok.2

private theorem sampleIndices_free {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (j : ℕ)
    (hk : k = j + if bits i = 0 then 0 else 1) (nbits q : ℕ) :
    ((freeChallengerTensorMulti P W M firstLen bits f m).sampleIndices nbits q s) =
      (List.range q).map fun t =>
        P.indexOf (queryPointTensorMulti P (Transcript.answer f ms i).2 (j + t)) := by
  induction q generalizing s k j with
  | zero => rfl
  | succ q ih =>
    obtain ⟨hv, hs⟩ :=
      sampleBits_query P W M firstLen bits f m h (by intro h0; split at hk <;> omega) nbits
    have hj : k - (if bits i = 0 then 0 else 1) = j := by omega
    rw [hj] at hv
    rw [Challenger.sampleIndices, hv, ih hs (j + 1) (by omega), List.range_succ_eq_map,
      List.map_cons, List.map_map]
    refine congrArg₂ List.cons rfl (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_def]
    rw [show j + 1 + t = j + (t + 1) by omega]

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem tensorOfMulti_ungrind_fsTranscript (r : ℕ)
    (f : ∀ x, MerkleAnswer (RawMsg F EF D)
        (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x) (ms : ℕ → RawMsg F EF D) :
    PcsRbr.tensorOfMulti (PcsRbr.ungrind (fsTranscript f ms (r + 1))) =
      (Transcript.answer f ms 0).2.tensor := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem betasOfTensorMulti_ungrind_fsTranscript (f : ∀ x, MerkleAnswer (RawMsg F EF D)
    (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x) (ms : ℕ → RawMsg F EF D) :
    ∀ (n k : ℕ),
      PcsRbr.betasOfTensorMulti (PcsRbr.ungrind (fsTranscript f ms (n + 1))) k =
        if k < n then (Transcript.answer f ms (k + 1)).2.field else 0
  | 0, k => by simp [fsTranscript, PcsRbr.ungrind, PcsRbr.betasOfTensorMulti]
  | n + 1, k => by
    change PcsRbr.betasOfTensorMulti
        ((PcsRbr.ungrind (fsTranscript f ms (n + 1))).snoc (ms (n + 1))
          (Transcript.answer f ms (n + 1)).2) k = _
    rw [PcsRbr.betasOfTensorMulti_snoc_succ]
    by_cases hk : k = n
    · subst hk
      rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
    · rw [Function.update_of_ne hk, betasOfTensorMulti_ungrind_fsTranscript f ms n k]
      have hiff : k < n ↔ k < n + 1 := by omega
      simp [hiff]

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem queriesOfTensorMulti_ungrind_fsTranscript (f : ∀ x, MerkleAnswer (RawMsg F EF D)
    (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x) (ms : ℕ → RawMsg F EF D)
    (n : ℕ) :
    PcsRbr.queriesOfTensorMulti (PcsRbr.ungrind (fsTranscript f ms (n + 1))) =
      (Transcript.answer f ms n).2.points := rfl

/-- **Full transcript refinement for `Fri.transcriptTensorMulti`.** -/
theorem transcriptTensorMulti_free [TwoAdicOps F] [Inhabited D] (params : FriParams)
    (shape : ClaimShape) (arities : List ℕ) (wf : WellFormed m params shape)
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    (f : ∀ x : FSQuery (RawMsg F EF D)
        (GrindChal (powBitsMulti params arities)
          (ChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum).ldt
            (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (modelParamsMulti m params shape arities wf hpos hsum).queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D)
        (GrindChal (powBitsMulti params arities)
          (ChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum).ldt
            (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (modelParamsMulti m params shape arities wf hpos hsum).queries))
        K D x)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof)
    (hshape : shapeOkMultiArity (F := F) arities params shape commitments points values proof = true) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let ms := messagesMulti params arities commitments points values proof
    let t := fsTranscript f ms (P.rounds + 2)
    let ch := transcriptTensorMulti
      (freeChallengerTensorMulti P W M (firstMessageLen params shape)
        (powBitsMulti params arities) f m)
      FreeState.init params shape arities commitments points values proof
    ch.schedule.colChallenges.size = tensorNumChallenges W ∧
      ch.schedule.openChallenges.size = tensorNumChallenges M ∧
      ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges W ∧
      ch.schedule.openWeights = tensorWeights ch.schedule.openChallenges M ∧
      (∀ b : Fin (tensorNumChallenges W),
        (PcsRbr.tensorOfMulti (PcsRbr.ungrind t)).1 b =
          m.ext.toModel (ch.schedule.colChallenges[b.val]'(by
            simp only [ch, transcriptTensorMulti, transcriptTailTensorMulti,
              TensorSchedule.sample, List.size_toArray, length_sampleExtMany]; exact b.isLt))) ∧
      (∀ b : Fin (tensorNumChallenges M),
        (PcsRbr.tensorOfMulti (PcsRbr.ungrind t)).2 b =
          m.ext.toModel (ch.schedule.openChallenges[b.val]'(by
            simp only [ch, transcriptTensorMulti, transcriptTailTensorMulti,
              TensorSchedule.sample, List.size_toArray, length_sampleExtMany]; exact b.isLt))) ∧
      (∀ i < P.rounds,
        m.ext.toModel (ch.betas.getD i 0) = PcsRbr.betasOfTensorMulti (PcsRbr.ungrind t) i) ∧
      (ch.powOk = true → PcsRbr.PowPasses t) ∧
      (∀ k : Fin params.numQueries,
        ch.indices.getD k.val 0 = P.indexOf (PcsRbr.queriesOfTensorMulti (PcsRbr.ungrind t) k)) := by
  intro P W M ms t ch
  have hlen_first : (ms 0).length = firstMessageLen params shape := by
    simp only [ms, messagesMulti, ↓reduceIte, firstMessage, firstMessageLen, List.length_append,
      List.length_map, Array.length_toList]
    simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
    have hc := hshape.1.1.1.1.1.1.1.1.1.2
    have hp := hshape.1.1.1.1.1.1.1.1.2
    have hv := hshape.1.1.1.1.1.1.1.2
    omega
  have hfinal_ne : finalMessageMulti (F := F) (D := D) arities proof.finalPoly ≠ [] := by
    simp only [shapeOkMultiArity, Bool.and_eq_true, beq_iff_eq] at hshape
    have hfp : proof.finalPoly.size = 2 ^ params.logFinalPolyLen := hshape.1.1.2
    have hpos_fp : 0 < proof.finalPoly.size := by rw [hfp]; exact Nat.two_pow_pos _
    intro heq
    have hlen := congrArg List.length heq
    simp only [finalMessageMulti, List.length_append, List.length_map, Array.length_toList,
      List.length_nil] at hlen
    omega
  let chal := freeChallengerTensorMulti P W M (firstMessageLen params shape)
    (powBitsMulti params arities) f m
  have h0 : Transcript.At ms (chal.observeAll FreeState.init (firstMessage commitments points values))
      0 (ms 0) 0 := by
    have h := observeAll_round0 P W M (firstMessageLen params shape)
      (powBitsMulti params arities) f m (Transcript.At.init (ms := ms))
      (firstMessage commitments points values)
      (by simp only [List.length_nil, zero_add]; exact le_of_eq hlen_first)
    simpa [ms, messagesMulti] using h
  obtain ⟨hcol_list, h1⟩ := sampleExtMany_col P W M (firstMessageLen params shape)
    (powBitsMulti params arities) f m (tensorNumChallenges W) 0 (by omega) h0
  obtain ⟨hopen_list, h2⟩ := sampleExtMany_open P W M (firstMessageLen params shape)
    (powBitsMulti params arities) f m (tensorNumChallenges M) 0 (by omega) (by simpa using h1)
  have hready0 : ReadyToAdvanceM W M 0 (tensorNumChallenges W + tensorNumChallenges M) := by
    by_cases hz : tensorNumChallenges W + tensorNumChallenges M = 0
    · exact Or.inr ⟨rfl, hz⟩
    · exact Or.inl (by omega)
  have hms_commit : ∀ i < P.rounds,
      ms (i + 1) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then [] else [.base (proof.commitPowWitnesses.getD i 0)]) := by
    intro i hi; simp [ms, messagesMulti, show i + 1 ≤ arities.length from hi]
  have hbits_commit : ∀ i < P.rounds, powBitsMulti params arities (i + 1) = params.commitPowBits := by
    intro i hi; exact powBitsMulti_succ_of_lt params arities hi
  obtain ⟨hbetas, hpow_c, k', h3, hr3⟩ :=
    commitPhase_free P W M (firstMessageLen params shape) (powBitsMulti params arities) f m
      params.commitPowBits proof.commitPhaseCommits proof.commitPowWitnesses P.rounds
      hms_commit hbits_commit hlen_first (by simpa using h2) hready0
  have h4 := observeAll_next P W M (firstMessageLen params shape) (powBitsMulti params arities) f m
    h3 hr3 (fun _ => hlen_first) hfinal_ne
  have hms_last : ms (P.rounds + 1) =
      finalMessageMulti arities proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
    simp [ms, messagesMulti, show ¬ (P.rounds + 1 ≤ arities.length) by
      show ¬ (arities.length + 1 ≤ arities.length); omega]
  have hbits_last : powBitsMulti params arities (P.rounds + 1) = params.queryPowBits :=
    powBitsMulti_last params arities
  obtain ⟨hpow_q, h5⟩ := checkWitness_pos P W M (firstMessageLen params shape)
    (powBitsMulti params arities) f m h4 (Nat.succ_ne_zero _) params.queryPowBits
    proof.queryPowWitness hms_last hbits_last
  have hidx_list := sampleIndices_free P W M (firstMessageLen params shape)
    (powBitsMulti params arities) f m h5 0 (by simp [hbits_last])
    (logMaxHeight params.logBlowup shape) params.numQueries
  have hcol_arr : ch.schedule.colChallenges =
      (List.ofFn fun j : Fin (tensorNumChallenges W) =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.1
          ⟨0 + j.val, by dsimp only [W]; omega⟩)).toArray := by
    show (TensorSchedule.sample chal _ W M).1.colChallenges = _
    simp only [TensorSchedule.sample]
    exact congrArg List.toArray hcol_list
  have hopen_arr : ch.schedule.openChallenges =
      (List.ofFn fun j : Fin (tensorNumChallenges M) =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.2
          ⟨0 + j.val, by dsimp only [M]; omega⟩)).toArray := by
    show (TensorSchedule.sample chal _ W M).1.openChallenges = _
    simp only [TensorSchedule.sample]
    exact congrArg List.toArray hopen_list
  refine ⟨by rw [hcol_arr]; simp, by rw [hopen_arr]; simp, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [tensorOfMulti_ungrind_fsTranscript P W M (powBitsMulti params arities) (P.rounds + 1) f ms]
    simp only [hcol_arr, List.getElem_toArray, List.getElem_ofFn]
    rw [Function.surjInv_eq m.surj]
    have hb : (⟨0 + b.val, by omega⟩ : Fin (tensorNumChallenges W)) = b := by ext; simp
    rw [hb]
  · intro b
    rw [tensorOfMulti_ungrind_fsTranscript P W M (powBitsMulti params arities) (P.rounds + 1) f ms]
    simp only [hopen_arr, List.getElem_toArray, List.getElem_ofFn]
    rw [Function.surjInv_eq m.surj]
    have hb : (⟨0 + b.val, by omega⟩ : Fin (tensorNumChallenges M)) = b := by ext; simp
    rw [hb]
  · intro i hi
    have hbi : ch.betas = ((List.range P.rounds).map fun i =>
        Function.surjInv m.surj (Transcript.answer f ms (i + 1)).2.field).toArray := hbetas
    rw [hbi, Transcript.getD_map_range, ite_eq_left hi, Function.surjInv_eq m.surj,
      betasOfTensorMulti_ungrind_fsTranscript, ite_eq_left (by omega)]
  · intro hpowOk
    rw [Transcript.powPasses_fsTranscript]
    dsimp only [ch, transcriptTensorMulti, transcriptTailTensorMulti, TensorSchedule.sample] at hpowOk
    rw [Bool.and_eq_true] at hpowOk
    intro i hi
    rcases i with _ | k
    · exact Transcript.fin_val_eq_zero (by simp [powBitsMulti]) _
    · rcases Nat.lt_or_ge k P.rounds with hk | hk
      · exact hpow_c hpowOk.1 k hk
      · have hk_eq : k = P.rounds := by omega
        subst hk_eq
        exact hpow_q hpowOk.2
  · intro k
    have hind : ch.indices = ((List.range params.numQueries).map fun t =>
        P.indexOf (queryPointTensorMulti P (Transcript.answer f ms (P.rounds + 1)).2 (0 + t))).toArray := by
      show (chal.sampleIndices (logMaxHeight params.logBlowup shape) params.numQueries _).toArray = _
      exact congrArg List.toArray hidx_list
    rw [hind, Transcript.getD_map_range, ite_eq_left k.isLt,
      queriesOfTensorMulti_ungrind_fsTranscript]
    have hkq : k.val < P.queries := k.isLt
    simp only [Nat.zero_add, queryPointTensorMulti, dite_eq_left hkq]
    rfl

end MultiTranscriptProof

end MultiTranscript

/-! ## 4. Chained-ROM soundness of executable `Fri.verifyTensorWithSchedule` -/

section MultiChainedSoundness

open Oracle OracleComp
open PcsRbr (TensorChal ChalTensorMulti GrindChal ClaimsFailMulti PowPasses ungrind
  tensorOfMulti betasOfTensorMulti queriesOfTensorMulti)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
  (wf : WellFormed m params shape)
  (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)

/-- Oracle answer type for multi-arity tensor FRI in the chained random-oracle model. -/
abbrev TensorMultiOracleAnswer :=
  MerkleAnswer (RawMsg F EF D)
    (GrindChal (powBitsMulti params arities)
      (ChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum).ldt
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (modelParamsMulti m params shape arities wf hpos hsum).queries))
    K D

/-- Executable `Fri.verifyTensorWithSchedule` against an idealised multi-arity oracle `f`. -/
noncomputable def acceptsTensorMulti
    (f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) : Bool :=
  Fri.verifyTensorWithSchedule (merkleMmcs (inputHasher m (hasherOf f)))
    (merkleMmcs (friHasher m (hasherOf f)))
    (freeChallengerTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
      (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      (firstMessageLen params shape) (powBitsMulti params arities) f m)
    FreeState.init params shape arities a.commitments a.points a.values a.proof

omit [DecidableEq D] in
private theorem msgAt_fsTranscript_tensorMulti
    (f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) {j : ℕ} (hj : j ≤ arities.length + 1) :
    Compiled.msgAt (ungrind (fsTranscript f
        (messagesMulti params arities a.commitments a.points a.values a.proof)
        ((modelParamsMulti m params shape arities wf hpos hsum).rounds + 2))) j =
      messagesMulti params arities a.commitments a.points a.values a.proof j := by
  refine Compiled.msgAt_eq_of_getElem? ?_
  have hlt : j < (modelParamsMulti m params shape arities wf hpos hsum).rounds + 2 :=
    Nat.lt_succ_of_le hj
  rw [Compiled.msgs_ungrind, fsTranscript_msgs, List.getElem?_map, List.getElem?_range hlt]
  rfl

/-- **Refinement of `Fri.verifyTensorWithSchedule`:** acceptance implies compiled
multi-arity model verifier acceptance against `f`. -/
theorem run_model_of_acceptsTensorMulti
    (f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D)
    (h : acceptsTensorMulti m params shape arities wf hpos hsum f a = true) :
    ((modelParamsMulti m params shape arities wf hpos hsum).verifyGrindViewTensor
      (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      (tensorCoordMulti params shape arities) (powBitsMulti params arities)
      (viewMulti m params shape arities) (modelProofMulti m params shape a.proof)
      (fsTranscript f (messagesMulti params arities a.commitments a.points a.values a.proof)
        ((modelParamsMulti m params shape arities wf hpos hsum).rounds + 2))).run f = true := by
  unfold acceptsTensorMulti Fri.verifyTensorWithSchedule at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  obtain ⟨hcolSz, hopenSz, hcolW, hopenW, hcolC, hopenC, hβ, hpow, hidx⟩ :=
    MultiTranscriptProof.transcriptTensorMulti_free m params shape arities wf hpos hsum f
      a.commitments a.points a.values a.proof hshape
  let P := modelParamsMulti m params shape arities wf hpos hsum
  let ms := messagesMulti params arities a.commitments a.points a.values a.proof
  let t := fsTranscript f ms (P.rounds + 2)
  have hag : AgreesTensorMulti m params shape arities a.commitments a.points a.values a.proof
      (transcriptTensorMulti
        (freeChallengerTensorMulti P (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (firstMessageLen params shape)
          (powBitsMulti params arities) f m)
        FreeState.init params shape arities a.commitments a.points a.values a.proof)
      (fun j => viewMulti m params shape arities (Compiled.msgAt (ungrind t) j))
      (tensorOfMulti (ungrind t)) (betasOfTensorMulti (ungrind t))
      (fun k => P.indexOf (queriesOfTensorMulti (ungrind t) k)) :=
    { msg := fun j hj => by
        rw [msgAt_fsTranscript_tensorMulti m params shape arities wf hpos hsum f a hj]
      colSize := hcolSz
      openSize := hopenSz
      colWeights := hcolW
      openWeights := hopenW
      colChals := fun b => hcolC b
      openChals := fun b => hopenC b
      beta := fun i hi => (hβ i hi).symm
      index := fun k => (hidx k).symm }
  obtain ⟨hpowOk, hchecks⟩ := modelChecksTensorMulti_of_verifyWithTensorMulti m params shape arities
    wf hpos hsum (hasherOf f) hshape hag hwith
  refine (P.run_verifyGrindViewTensor _ _ _ _ _ f _ _).mpr ⟨hpow hpowOk, ?_⟩
  exact (P.run_verifyWithTensor _ _ _ f _ _ _ _ _).trans hchecks

variable [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- Chained-ROM soundness experiment for executable `Fri.verifyTensorWithSchedule`. -/
noncomputable def experimentTensorMulti {A : Type*}
    (adv : OracleComp (TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A)
    (attempt : A → Attempt F EF D) :
    OracleComp (TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) (A × Bool) :=
  (modelParamsMulti m params shape arities wf hpos hsum).experimentGrindViewTensor
    (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
    (tensorCoordMulti params shape arities) (powBitsMulti params arities)
    (viewMulti m params shape arities) adv
    (fun a => messagesMulti params arities (attempt a).commitments (attempt a).points
      (attempt a).values (attempt a).proof)
    (fun a => modelProofMulti m params shape (attempt a).proof)

/-- **Generic chained-ROM soundness of executable `Fri.verifyTensorWithSchedule`**
for any per-round variable arity schedule `arities : List ℕ`! -/
theorem soundnessTensorMulti {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      Tensor2DMCA (((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain j).image
          ((modelParamsMulti m params shape arities wf hpos hsum).shift * ·))
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.degree j)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) θ (εα j))
    (hε₀ : ∀ j ≤ (modelParamsMulti m params shape arities wf hpos hsum).rounds, εα j ≤ ε₀)
    (hstep : ∀ i < (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      StepMCAArity (2 ^ (modelParamsMulti m params shape arities wf hpos hsum).logArity i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.zeta i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain (i + 1))
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.degree (i + 1)) θ (εβ i))
    (hα : ε₀ ≤ εmax)
    (hβ : ∀ i < (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    prob (fun res l =>
        (∃ f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsTensorMulti m params shape arities wf hpos hsum f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift θ
          (P.claims (viewMulti m params shape arities
            (firstMessage (attempt res.1).commitments (attempt res.1).points
              (attempt res.1).values)) (committedRow l)))
      (experimentTensorMulti m params shape arities wf hpos hsum adv attempt) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  intro P
  have h := P.soundness_grind_view_tensorMulti_of_imp (maxWidth shape)
    (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
    (fun j _ => tensorCoordMulti_injective params shape arities j)
    (powBitsMulti params arities) (viewMulti m params shape arities) hθ hmca hε₀ hstep
    (by simpa [powBitsMulti_zero] using hα)
    (fun i hi => by rw [powBitsMulti_succ_of_lt params arities hi]; exact hβ i hi)
    (by rw [show P.rounds = arities.length from rfl, powBitsMulti_last]; exact hq)
    hadv
    (fun a => messagesMulti params arities (attempt a).commitments (attempt a).points
      (attempt a).values (attempt a).proof)
    (fun a => modelProofMulti m params shape (attempt a).proof)
    (fun a l => ∃ f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
      (∀ x y, l.dlookup x = some y → f x = y) ∧
        acceptsTensorMulti m params shape arities wf hpos hsum f (attempt a) = true)
    fun out l b l' hexp hver ⟨f, hf, hacc⟩ => by
      have hrun := run_model_of_acceptsTensorMulti m params shape arities wf hpos hsum f
        (attempt out.1) hacc
      have htf : l'.toFun f = f := funext fun x => by
        unfold Log.toFun
        cases hlook : l'.dlookup x with
        | none => rfl
        | some y => exact (hf x y hlook).symm
      have hrec : (P.verifyGrindViewTensor (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (tensorCoordMulti params shape arities)
          (powBitsMulti params arities) (viewMulti m params shape arities)
          (modelProofMulti m params shape (attempt out.1).proof)
          (fsTranscript (l'.toFun f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof)
            (P.rounds + 2))).run (l'.toFun f) = b := by
        rw [← Compiled.eq_fsTranscript_of_outcome_fsExperiment hexp hver.prefix f]
        exact hver.run_toFun f
      rw [htf] at hrec
      exact hrec.symm.trans hrun
  exact h

/-- **100% Unconditional Unique-Decoding Chained-ROM Soundness for `Fri.verifyTensorWithSchedule`**
for ANY variable-arity schedule `arities` (with error completely independent of arities!). -/
theorem soundnessTensorMulti_uniqueDecoding
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1)
    {εmax : ℝ}
    (hα : ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    prob (fun res l =>
        (∃ f : ∀ x, TensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsTensorMulti m params shape arities wf hpos hsum f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift (1 - δ)
          (P.claims (viewMulti m params shape arities
            (firstMessage (attempt res.1).commitments (attempt res.1).points
              (attempt res.1).values)) (committedRow l)))
      (experimentTensorMulti m params shape arities wf hpos hsum adv attempt) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  intro P
  have hθ : 0 ≤ 1 - δ := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hcard_mul : ∀ j ≤ P.rounds,
      (P.ldt.domain j).card = 2 ^ params.logBlowup * P.ldt.degree j := fun j hj => by
    rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_degree,
      card_twoAdicDomain P.prim (P.cum_le_n j)]
    show 2 ^ (P.n - P.cum j) = 2 ^ params.logBlowup * (2 ^ (arities.sum - P.cum j) * 2 ^ params.logFinalPolyLen)
    have hcle : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
    rw [← pow_add, ← pow_add]
    congr 1
    show logMaxHeight params.logBlowup shape - cumLogArity arities j =
      params.logBlowup + (arities.sum - cumLogArity arities j + params.logFinalPolyLen)
    unfold FriParams.logFinalHeight at hsum_eq
    omega
  have hdist_dom : ∀ j ≤ P.rounds,
      2 * (δ * (P.ldt.domain j).card) + P.ldt.degree j ≤ (P.ldt.domain j).card := fun j hj => by
    have hinv : (2 : ℝ) ^ params.logBlowup * (1 / 2 : ℝ) ^ params.logBlowup = 1 := by
      rw [← mul_pow]; norm_num
    have hdeg : (P.ldt.degree j : ℝ) = (1 / 2 : ℝ) ^ params.logBlowup * (P.ldt.domain j).card := by
      rw [hcard_mul j hj]; push_cast
      linear_combination -(P.ldt.degree j : ℝ) * hinv
    rw [hdeg]
    nlinarith [Nat.cast_nonneg (α := ℝ) (P.ldt.domain j).card]
  have hcard_le : ∀ j ≤ P.rounds, ((P.ldt.domain j).card : ℝ) ≤ (2 : ℝ) ^ P.n := fun j _ => by
    rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n (P.cum j))
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) (1 - δ)
        (((tensorNumChallenges (maxWidth shape) +
            tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
          (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K)) := by
    intro j hj
    refine tensor2DMCA_ud _ _ _ _ hδ ?_
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
    exact hdist_dom j hj
  have hε₀ : ∀ j ≤ P.rounds,
      ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K) ≤
      ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K := by
    intro j hj
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hcard_le j hj) (by linarith)) (Nat.cast_nonneg _)
  have hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) (1 - δ) (((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) := by
    intro i hi
    refine (stepMCAArity_ud (P.ldt.step i hi) (P.ldt.degree (i + 1)) hδ
      (hdist_dom (i + 1) hi)).mono_error ?_
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_left (hcard_le i hi.le) (by linarith)
  exact soundnessTensorMulti m params shape arities wf hpos hsum hθ hmca hε₀ hstep hα
    (fun _ _ => hβ) hq hadv attempt

end MultiChainedSoundness

end CertiFri.Exec
