import CertiFriProofs.Exec.Stark.State
import CertiFriProofs.Exec.TensorExec
import CertiFriProofs.Theory.ProximityGap.CurveListCA

/-!
# Round-by-round soundness of tensor-batched FRI for every supported STARK shard

Tensor-batched counterpart of `Exec/Stark/PcsSound.lean`, connecting every
supported shard's `starkShape` to `PcsRbr.rbrSound_grind_tensor` (`Theory/PcsRbrTensor.lean`).

## Contents

* `maxWidthBound sys d`: static upper bound on `maxWidth (starkShape ...)` over
  every activation bitmap of `sys`.
* `maxOpeningsBound sys`: static upper bound (`7 * sys.circuits.size`) on
  `maxOpeningsPerHeight` over every activation bitmap of `sys`.
* `fslotsBound sys d`: static upper bound `max 1 (kColMax + kOpenMax)` on the
  number of tensor challenges per round, completely independent of prover-chosen
  active masks or trace heights.
* `two_le_maxOpeningsPerHeight_starkShape`: every proof passing `Stark.shapeOk`
  has at least one active circuit (opened at 2 points in `stage1`), so
  `maxOpeningsPerHeight ≥ 2` and `tensorNumChallenges W + tensorNumChallenges M ≥ 1`.
* `pcsErrTensor sys d δ`: tight unconditional unique-decoding PCS error bound
  for tensor batching — **linear** in `kColMax + kOpenMax` (logarithmic in total
  claims) and **linear** in `2 ^ (maxLogDegree + logBlowup)`:
  * batching: `(kColMax + kOpenMax) * ((1 + δ) * 2 ^ nMax) / |K|`,
  * folding: `((1 + δ) * 2 ^ nMax) / |K| / 2 ^ commitPowBits`,
  * queries: `(1 - δ) ^ numQueries / 2 ^ queryPowBits`.
* `rbrSound_pcsTensor_ud`: unconditional unique-decoding `RbrSound` for
  `grindDoomed ... (PcsRbr.doomedTensor ...)` of every supported shard.
* `rbrSound_pcsTensor_johnson_of_curveListCA`: unconditional Johnson-regime
  `RbrSound` for `grindDoomed ... (PcsRbr.doomedTensor ...)` via `CurveListCA`
  (discharged unconditionally over `Fp3Model` by `curveListCA_fp3`).
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

/-! ## Static system bounds on tensor dimensions -/

/-- Static upper bound on the width of any matrix committed by `sys` for extension degree `d`. -/
def maxWidthBound (sys : System F D) (d : ℕ) : ℕ :=
  (sys.circuits.toList.map fun c =>
    max (max c.mainWidth c.stage2Width) (max (c.quotientDegree * d) c.preprocessedWidth)).foldr
    max 0

/-- Static upper bound on the number of opening groups at any single height in a shard of `sys`:
each circuit contributes at most `2` (main) + `2` (stage2) + `1` (quotient) + `2` (fixed) = `7`
opening points across all heights. -/
def maxOpeningsBound (sys : System F D) : ℕ :=
  7 * sys.circuits.size

/-- Static upper bound on the number of field challenge slots needed per round of a
tensor-batched STARK for `sys` and extension degree `d` (at least `1`). -/
def fslotsBound (sys : System F D) (d : ℕ) : ℕ :=
  max 1 (tensorNumChallenges (maxWidthBound sys d) + tensorNumChallenges (maxOpeningsBound sys))

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
theorem one_le_fslotsBound (sys : System F D) (d : ℕ) : 1 ≤ fslotsBound sys d :=
  le_max_left _ _

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
theorem pos_fslotsBound (sys : System F D) (d : ℕ) : 0 < fslotsBound sys d :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_fslotsBound sys d)

/-- `tensorNumChallenges` is monotone in the count. -/
theorem tensorNumChallenges_mono {a b : ℕ} (h : a ≤ b) :
    tensorNumChallenges a ≤ tensorNumChallenges b := by
  unfold tensorNumChallenges
  split_ifs with ha hb
  · exact Nat.le_refl 0
  · exact Nat.zero_le _
  · omega
  · refine Nat.add_le_add_right ((Nat.le_log2 (by omega)).mpr ?_) 1
    exact (Nat.log2_self_le (by omega)).trans (by omega)

private theorem foldr_max_le_of_forall {l : List ℕ} {bound : ℕ}
    (h : ∀ x ∈ l, x ≤ bound) : l.foldr max 0 ≤ bound := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

private theorem le_foldr_max_of_mem {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
private theorem circuit_width_le_maxWidthBound (sys : System F D) (d : ℕ) {ci : ℕ}
    (hci : ci < sys.circuits.size) :
    let c := sys.circuits.getD ci default
    c.mainWidth ≤ maxWidthBound sys d ∧ c.stage2Width ≤ maxWidthBound sys d ∧
      c.quotientDegree * d ≤ maxWidthBound sys d ∧ c.preprocessedWidth ≤ maxWidthBound sys d := by
  have hget : sys.circuits.getD ci default = sys.circuits[ci] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hci, Option.getD_some]
  have hmem : sys.circuits[ci] ∈ sys.circuits.toList := Array.getElem_mem_toList hci
  have hle : max (max sys.circuits[ci].mainWidth sys.circuits[ci].stage2Width)
      (max (sys.circuits[ci].quotientDegree * d) sys.circuits[ci].preprocessedWidth) ≤
      maxWidthBound sys d :=
    le_foldr_max_of_mem (List.mem_map.mpr ⟨sys.circuits[ci], hmem, rfl⟩)
  rw [hget]
  exact ⟨(le_max_left _ _).trans ((le_max_left _ _).trans hle),
    (le_max_right _ _).trans ((le_max_left _ _).trans hle),
    (le_max_left _ _).trans ((le_max_right _ _).trans hle),
    (le_max_right _ _).trans ((le_max_right _ _).trans hle)⟩

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- Every matrix in `starkShape` has width at most `maxWidthBound sys d`. -/
theorem maxWidth_starkShape_le (sys : System F D) (d : ℕ) {active : Array Bool}
    (hact : active.size ≤ sys.circuits.size) (logDegrees : Array ℕ) :
    maxWidth (starkShape sys d active logDegrees) ≤ maxWidthBound sys d := by
  unfold maxWidth
  refine foldr_max_le_of_forall fun w hw => ?_
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hw
  have hact_lt : ∀ ci ∈ activeIndices active, ci < sys.circuits.size := fun ci hci => by
    have := List.mem_range.mp (List.mem_filter.mp hci).1
    omega
  rw [starkShape, List.flatten_append, List.mem_append] at hm
  rcases hm with hm | hm
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hm
    rcases hm with hm | hm | hm
    · obtain ⟨⟨ci, pos⟩, hp, rfl⟩ := List.mem_map.mp hm
      have hci : ci < sys.circuits.size :=
        hact_lt ci (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp))
      exact (circuit_width_le_maxWidthBound sys d hci).1
    · obtain ⟨⟨ci, pos⟩, hp, rfl⟩ := List.mem_map.mp hm
      have hci : ci < sys.circuits.size :=
        hact_lt ci (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp))
      exact (circuit_width_le_maxWidthBound sys d hci).2.1
    · obtain ⟨⟨ci, pos⟩, hp, rfl⟩ := List.mem_map.mp hm
      have hci : ci < sys.circuits.size :=
        hact_lt ci (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp))
      exact (circuit_width_le_maxWidthBound sys d hci).2.2.1
  · split at hm
    · simp only [List.flatten_singleton, fixedShapes, List.mem_filterMap] at hm
      obtain ⟨ci, hci, hopt⟩ := hm
      have hci_lt : ci < sys.circuits.size := List.mem_range.mp hci
      split_ifs at hopt
      have hcw := (circuit_width_le_maxWidthBound sys d hci_lt).2.2.2
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hci_lt, Option.getD_some] at hcw
      split at hopt <;> cases hopt <;> exact hcw
    · cases hm

private theorem length_pointRefs_eq (lb : ℕ) (shape : ClaimShape) :
    (pointRefs lb shape).length = (shape.flatten.map (·.numPoints)).sum := by
  have h1 : ∀ (l : List (List MatrixShape)) (k : ℕ),
      ((l.zipIdx k).flatMap fun (mats, batch) =>
        mats.zipIdx.flatMap fun (m, matrix) =>
          List.replicate m.numPoints (PointRef.mk batch matrix (m.logDegree + lb) m.width)).length =
        (l.flatten.map (·.numPoints)).sum := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons mats rest ih =>
      intro k
      rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, ih (k + 1),
        List.flatten_cons, List.map_append, List.sum_append]
      congr 1
      have h2 : ∀ (ms : List MatrixShape) (j : ℕ),
          ((ms.zipIdx j).flatMap fun (m, matrix) =>
            List.replicate m.numPoints (PointRef.mk k matrix (m.logDegree + lb) m.width)).length =
            (ms.map (·.numPoints)).sum := by
        intro ms
        induction ms with
        | nil => intro _; rfl
        | cons m ms ihm =>
          intro j
          rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.length_replicate,
            ihm (j + 1), List.map_cons, List.sum_cons]
      exact h2 mats 0
  exact h1 shape 0

private theorem maxOpeningsPerHeight_le_length_pointRefs (lb : ℕ) (shape : ClaimShape) :
    maxOpeningsPerHeight lb shape ≤ (pointRefs lb shape).length := by
  unfold maxOpeningsPerHeight
  refine foldr_max_le_of_forall fun len hlen => ?_
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hlen
  exact List.length_filter_le _ _

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- The opening count at any height of `starkShape` is at most `maxOpeningsBound sys`. -/
theorem maxOpeningsPerHeight_starkShape_le (sys : System F D) (d : ℕ) {active : Array Bool}
    (hact : active.size ≤ sys.circuits.size) (logDegrees : Array ℕ) :
    maxOpeningsPerHeight sys.fri.logBlowup (starkShape sys d active logDegrees) ≤
      maxOpeningsBound sys := by
  refine (maxOpeningsPerHeight_le_length_pointRefs _ _).trans ?_
  rw [length_pointRefs_eq]
  have hact_le : (activeIndices active).length ≤ sys.circuits.size := by
    calc (activeIndices active).length ≤ (List.range active.size).length := List.length_filter_le _ _
      _ = active.size := List.length_range
      _ ≤ sys.circuits.size := hact
  have htrace : ∀ (w : ℕ → ℕ) (np : ℕ),
      ((traceShapes (activeIndices active) logDegrees w np).map (·.numPoints)).sum =
        (activeIndices active).length * np := fun w np => by
    unfold traceShapes
    rw [List.map_map]
    have hconst : ((activeIndices active).zipIdx.map
        ((fun x : MatrixShape => x.numPoints) ∘ fun p => ⟨logDegrees.getD p.2 0, w p.1, np⟩)) =
        List.replicate (activeIndices active).length np := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp
    rw [hconst, List.sum_replicate, smul_eq_mul]
  have hfixed : ((fixedShapes sys (activeIndices active) logDegrees).map (·.numPoints)).sum ≤
      2 * sys.circuits.size := by
    unfold fixedShapes
    have hle : ∀ (l : List ℕ),
        ((l.filterMap fun ci =>
          if (sys.preprocessedIndices.getD ci none).isNone then none
          else match (activeIndices active).idxOf? ci with
            | some pos => some (MatrixShape.mk (logDegrees.getD pos 0)
                (sys.circuits.getD ci default).preprocessedWidth 2)
            | none => some (MatrixShape.mk
                (Nat.log2 (sys.circuits.getD ci default).preprocessedHeight)
                (sys.circuits.getD ci default).preprocessedWidth 1)).map (·.numPoints)).sum ≤
        2 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons ci l ih =>
        rw [List.filterMap_cons]
        by_cases hn : (sys.preprocessedIndices.getD ci none).isNone
        · rw [ite_eq_left hn]
          dsimp only
          rw [List.length_cons]
          omega
        · rw [ite_eq_right hn]
          cases (activeIndices active).idxOf? ci <;>
            simp only [List.map_cons, List.sum_cons, List.length_cons] <;> omega
    have h := hle (List.range sys.circuits.size)
    rwa [List.length_range] at h
  rw [starkShape, List.flatten_append, List.map_append, List.sum_append]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append,
    List.sum_append, htrace]
  unfold maxOpeningsBound
  cases sys.preprocessedCommit
  · simp only [List.flatten_nil, List.map_nil, List.sum_nil]; omega
  · simp only [List.flatten_singleton]; omega

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- For any activation bitmap of size `≤ sys.circuits.size`, the tensor challenge count
of `starkShape` is at most `fslotsBound sys d`. -/
theorem tensorNumChallenges_starkShape_le_fslotsBound (sys : System F D) (d : ℕ)
    {active : Array Bool} (hact : active.size ≤ sys.circuits.size) (logDegrees : Array ℕ) :
    tensorNumChallenges (maxWidth (starkShape sys d active logDegrees)) +
      tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup
        (starkShape sys d active logDegrees)) ≤ fslotsBound sys d :=
  (Nat.add_le_add
    (tensorNumChallenges_mono (maxWidth_starkShape_le sys d hact logDegrees))
    (tensorNumChallenges_mono (maxOpeningsPerHeight_starkShape_le sys d hact logDegrees))).trans
    (le_max_right _ _)

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- Whenever at least one circuit is active, `starkShape` has at least `2` opening points at the
height of the first active circuit's main trace, so `maxOpeningsPerHeight ≥ 2` and
`kCol + kOpen ≥ 1`. -/
theorem two_le_maxOpeningsPerHeight_starkShape (sys : System F D) (d : ℕ) {active : Array Bool}
    (hne : ¬ (activeIndices active).isEmpty) (logDegrees : Array ℕ) :
    2 ≤ maxOpeningsPerHeight sys.fri.logBlowup (starkShape sys d active logDegrees) := by
  cases hact : activeIndices active with
  | nil => rw [hact] at hne; exact absurd rfl hne
  | cons ci rest =>
    set shape := starkShape sys d active logDegrees
    set k := logDegrees.getD 0 0
    set p : PointRef := ⟨0, 0, k + sys.fri.logBlowup, (sys.circuits.getD ci default).mainWidth⟩
    have hshape_hd : shape =
        (⟨k, (sys.circuits.getD ci default).mainWidth, 2⟩ ::
          ((rest.zipIdx 1).map fun q =>
            ⟨logDegrees.getD q.2 0, (sys.circuits.getD q.1 default).mainWidth, 2⟩)) ::
        [traceShapes (ci :: rest) logDegrees (fun c => (sys.circuits.getD c default).stage2Width) 2,
         traceShapes (ci :: rest) logDegrees
           (fun c => (sys.circuits.getD c default).quotientDegree * d) 1] ++
        match sys.preprocessedCommit with
        | some _ => [fixedShapes sys (ci :: rest) logDegrees]
        | none => [] := by
      dsimp only [shape, starkShape, k]
      rw [hact]
      congr 1
    have hpr_prefix : ∃ tail, pointRefs sys.fri.logBlowup shape = p :: p :: tail := by
      rw [pointRefs, hshape_hd]
      simp only [List.cons_append, List.zipIdx_cons, List.flatMap_cons, List.replicate,
        List.nil_append]
      exact ⟨_, rfl⟩
    obtain ⟨tail, hpr⟩ := hpr_prefix
    have hp_mem : p ∈ pointRefs sys.fri.logBlowup shape := by
      rw [hpr]; exact List.mem_cons_self
    have hflt_ge : 2 ≤ ((pointRefs sys.fri.logBlowup shape).filter
        fun q => q.logHeight == p.logHeight).length := by
      rw [hpr]
      simp only [List.filter_cons, beq_self_eq_true, ↓reduceIte, List.length_cons]
      omega
    have hmem_map : ((pointRefs sys.fri.logBlowup shape).filter
        fun q => q.logHeight == p.logHeight).length ∈
        (pointRefs sys.fri.logBlowup shape).map fun r =>
          ((pointRefs sys.fri.logBlowup shape).filter fun q => q.logHeight == r.logHeight).length :=
      List.mem_map.mpr ⟨p, hp_mem, rfl⟩
    exact hflt_ge.trans (le_foldr_max_of_mem hmem_map)

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- Whenever at least one circuit is active, `kCol + kOpen ≥ 1` (at least one tensor challenge
is always drawn in round `4`). -/
theorem pos_tensorChallenges_starkShape (sys : System F D) (d : ℕ) {active : Array Bool}
    (hne : ¬ (activeIndices active).isEmpty) (logDegrees : Array ℕ) :
    0 < tensorNumChallenges (maxWidth (starkShape sys d active logDegrees)) +
      tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup
        (starkShape sys d active logDegrees)) := by
  have h2 := two_le_maxOpeningsPerHeight_starkShape sys d hne logDegrees
  have h1 : 1 ≤ tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup
      (starkShape sys d active logDegrees)) := by
    have := tensorNumChallenges_mono h2
    exact le_trans (by decide : 1 ≤ tensorNumChallenges 2) this
  omega

/-! ## Tight unique-decoding tensor PCS error bound (`pcsErrTensor`) -/

/-- **Tight unconditional unique-decoding error bound for tensor-batched FRI** across
every supported shard of `sys` at agreement `1 - δ` (linear in `kColMax + kOpenMax`
and linear in `2 ^ (maxLogDegree + logBlowup)`). -/
noncomputable def pcsErrTensor [Fintype K] (sys : System F D) (d : ℕ) (δ : ℝ) : ℝ :=
  max
    (((tensorNumChallenges (maxWidthBound sys d) +
        tensorNumChallenges (maxOpeningsBound sys) : ℕ) : ℝ) *
      ((1 + δ) * (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup)) / Fintype.card K)
    (max
      (((1 + δ) * (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup)) / Fintype.card K /
        2 ^ sys.fri.commitPowBits)
      ((1 - δ) ^ sys.fri.numQueries / 2 ^ sys.fri.queryPowBits))

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq K] [Inhabited D]
  [DecidableEq D] in
theorem pcsErrTensor_nonneg [Fintype K] (sys : System F D) (d : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ pcsErrTensor (K := K) sys d δ := by
  refine le_max_of_le_left ?_
  positivity

private theorem not_claimsFail_of_forall_eq_zero_tensor {S : LdtInstance K} {s : K} {θ : ℝ}
    (hθ : θ ≤ 1) {m : ℕ → ℕ} (hm : ∀ j, m j = 0) (claims : ∀ j, Fin (m j) → Claim K) :
    ¬ ClaimsFail S s θ claims := by
  rintro ⟨j, -, hfail⟩
  refine hfail ⟨_, Finset.Subset.refl _, mul_le_of_le_one_left (Nat.cast_nonneg _) hθ,
    fun k => ?_⟩
  exact absurd (lt_of_lt_of_eq k.isLt (hm j)) (Nat.not_lt_zero _)

omit [Inhabited D] [DecidableEq D] in
/-- The tensor coordinate map of a supported STARK shard, typed directly over
`hs.params.numClaims` so unifying `PcsRbr.doomedTensor` with `pcsTTensor`
does not unfold `Supported.params`. -/
def starkTensorCoord (M : StarkModel F EF K) (sys : System F D) {θ : ℝ}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    ∀ j, Fin (hs.params.numClaims j) →
      Fin (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) ×
        Fin (maxWidth (v.shape M sys)) :=
  tensorCoord sys.fri (v.shape M sys)

omit [Inhabited D] [DecidableEq D] in
theorem starkTensorCoord_injective (M : StarkModel F EF K) (sys : System F D) {θ : ℝ}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (j : ℕ) :
    Function.Injective (starkTensorCoord M sys hs j) :=
  tensorCoord_injective sys.fri (v.shape M sys) j

omit [Inhabited D] [DecidableEq D] in
/-- **Unconditional unique-decoding round-by-round soundness of tensor-batched FRI
for every supported STARK shard.** Every round error is at most `pcsErrTensor sys d δ`. -/
theorem rbrSound_pcsTensor_ud [Fintype K] (M : StarkModel F EF K) (sys : System F D) {δ : ℝ}
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1) (v : ShardView F EF D K)
    (hactive : v.hdr.active.size = sys.circuits.size) (hs : Supported M sys (1 - δ) v) :
    RbrSound (hs.params.rounds + 2)
      (grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
          (1 - δ) hs.params.queries))
      fun _ => pcsErrTensor (K := K) sys M.extData.d δ := by
  let shape := v.shape M sys
  let W := maxWidth shape
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  rcases hfl : shape.flatten with _ | ⟨m, l⟩
  · -- Degenerate empty shape: no claims can fail.
    have hnil : claimRefs sys.fri.logBlowup shape = [] := by
      have hlen : (claimRefs sys.fri.logBlowup shape).length = 0 := by
        have hlen_p : (pointRefs sys.fri.logBlowup shape).length = 0 := by
          rw [length_pointRefs_eq, hfl]; rfl
        have hpnil : pointRefs sys.fri.logBlowup shape = [] := List.eq_nil_of_length_eq_zero hlen_p
        simp [claimRefs, hpnil]
      exact List.eq_nil_of_length_eq_zero hlen
    have hzero : ∀ j, hs.params.numClaims j = 0 := fun j => by
      show (levelClaims sys.fri.logBlowup shape _ j).length = 0
      rw [levelClaims, hnil]; rfl
    intro i hi t msg hd
    exact (FractionLE.false.mono_right (pcsErrTensor_nonneg sys M.extData.d hδ)).mono_left
      fun c hc => hc fun _ => doomedTensor_of_not_claimsFail
        (not_claimsFail_of_forall_eq_zero_tensor (sub_le_self 1 hδ) hzero _)
  · have hm : m ∈ shape.flatten := by rw [hfl]; exact List.mem_cons_self
    have hθ : (0 : ℝ) ≤ 1 - δ := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ sys.fri.logBlowup := by positivity
      linarith
    have hheight : sys.fri.logBlowup + sys.fri.logFinalPolyLen ≤
        logMaxHeight sys.fri.logBlowup shape :=
      (hs.final m hm).trans (le_logMaxHeight hm)
    have hn : hs.params.n = hs.params.rounds + sys.fri.logBlowup + sys.fri.logFinalPolyLen := by
      show logMaxHeight sys.fri.logBlowup shape =
        logMaxHeight sys.fri.logBlowup shape -
          (sys.fri.logBlowup + sys.fri.logFinalPolyLen) + sys.fri.logBlowup +
            sys.fri.logFinalPolyLen
      omega
    have hfinal : hs.params.finalDegree = 2 ^ sys.fri.logFinalPolyLen := rfl
    have hmca : ∀ j ≤ hs.params.rounds,
        Tensor2DMCA ((twoAdicDomain hs.params.ω hs.params.n j).image (hs.params.shift * ·))
          (2 ^ (hs.params.rounds - j) * hs.params.finalDegree) W Mopen (1 - δ)
          (((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
            (((1 + δ) * ((twoAdicDomain hs.params.ω hs.params.n j).image
              (hs.params.shift * ·)).card) / Fintype.card K)) := by
      intro j hj
      refine tensor2DMCA_ud _ _ W Mopen hδ ?_
      have hcard : ((twoAdicDomain hs.params.ω hs.params.n j).image
          (hs.params.shift * ·)).card =
          2 ^ sys.fri.logBlowup * (2 ^ (hs.params.rounds - j) * hs.params.finalDegree) := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ hs.params.shift_ne)]
        exact Compose.card_twoAdicDomain_eq_mul_degree hn hs.params.prim hj
      have hinv : (2 : ℝ) ^ sys.fri.logBlowup * (1 / 2 : ℝ) ^ sys.fri.logBlowup = 1 := by
        rw [← mul_pow]; norm_num
      have hdeg_le : ((2 ^ (hs.params.rounds - j) * hs.params.finalDegree : ℕ) : ℝ) =
          (1 / 2 : ℝ) ^ sys.fri.logBlowup *
            (((twoAdicDomain hs.params.ω hs.params.n j).image (hs.params.shift * ·)).card : ℝ) := by
        rw [hcard]; push_cast
        linear_combination -((2 : ℝ) ^ (hs.params.rounds - j) * (hs.params.finalDegree : ℝ)) * hinv
      rw [hdeg_le]
      nlinarith [Nat.cast_nonneg (α := ℝ)
        ((twoAdicDomain hs.params.ω hs.params.n j).image (hs.params.shift * ·)).card]
    have hε₀ : ∀ j ≤ hs.params.rounds,
        ((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
            (((1 + δ) * ((twoAdicDomain hs.params.ω hs.params.n j).image
              (hs.params.shift * ·)).card) / Fintype.card K) ≤
          ((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
            ((1 + δ) * (2 : ℝ) ^ hs.params.n) / Fintype.card K := by
      intro j hj
      have hcard_le : (((twoAdicDomain hs.params.ω hs.params.n j).image
          (hs.params.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ hs.params.n := by
        rw [Finset.card_image_of_injective _ (mul_right_injective₀ hs.params.shift_ne),
          card_twoAdicDomain hs.params.prim (hj.trans hs.params.rounds_le)]
        exact_mod_cast (Nat.pow_le_pow_right two_pos (Nat.sub_le hs.params.n j) :
          2 ^ (hs.params.n - j) ≤ 2 ^ hs.params.n)
      rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcard_le (add_nonneg zero_le_one hδ))
        (Nat.cast_nonneg _)
    have hstep : ∀ i < hs.params.rounds,
        StepMCA (twoAdicDomain hs.params.ω hs.params.n i)
          (twoAdicDomain hs.params.ω hs.params.n (i + 1))
          (2 ^ (hs.params.rounds - (i + 1)) * hs.params.finalDegree) (1 - δ)
          (((1 + δ) * (2 : ℝ) ^ hs.params.n) / Fintype.card K) :=
      fun i hi => hs.params.stepMCA_of_rate_of_curveCA (curveCA_udThreshold (F := K)) hn hfinal
        hδ hrate hi
    have hrbr := rbrSound_grind_tensor hs.params.ldt hs.params.shift_ne
      (starkTensorCoord M sys hs) (fun j _ => starkTensorCoord_injective M sys hs j) hθ
      hs.params.queries (powBits sys.fri shape) hmca hε₀ hstep
    have h2n_le : (2 : ℝ) ^ hs.params.n ≤ (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup) :=
      pow_le_pow_right₀ one_le_two hs.height
    have hk_le : ((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) ≤
        ((tensorNumChallenges (maxWidthBound sys M.extData.d) +
          tensorNumChallenges (maxOpeningsBound sys) : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add
        (tensorNumChallenges_mono (maxWidth_starkShape_le sys M.extData.d hactive.le v.hdr.logDegrees))
        (tensorNumChallenges_mono (maxOpeningsPerHeight_starkShape_le sys M.extData.d hactive.le
          v.hdr.logDegrees))
    have h1δ : 0 ≤ 1 + δ := add_nonneg zero_le_one hδ
    intro i hi t msg hd
    refine (hrbr i hi t msg hd).mono_right ?_
    beta_reduce
    rcases i with _ | k
    · rw [powBits_zero, pow_zero, div_one, roundErrorTensor_zero]
      refine le_trans ?_ (le_max_left _ _)
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact mul_le_mul hk_le (mul_le_mul_of_nonneg_left h2n_le h1δ)
        (mul_nonneg h1δ (pow_nonneg zero_le_two _)) (Nat.cast_nonneg _)
    · rcases Nat.lt_or_ge k hs.params.ldt.rounds with hk | hk
      · rw [powBits_succ_of_lt sys.fri shape hk, roundErrorTensor_succ_of_lt hk]
        refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
        refine div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
          (pow_nonneg zero_le_two _)
        exact mul_le_mul_of_nonneg_left h2n_le h1δ
      · obtain rfl : k = numRounds sys.fri shape := by
          have hR : hs.params.ldt.rounds = numRounds sys.fri shape := rfl
          have hR' : hs.params.rounds = numRounds sys.fri shape := rfl
          omega
        rw [powBits_last, roundErrorTensor_succ_of_not_lt (Nat.not_lt.mpr hk)]
        exact (le_max_right _ _).trans (le_max_right _ _)

/-! ## Unconditional Johnson-regime `RbrSound` via `CurveListCA` union bound -/

/-- **Unconditional Johnson-regime `RbrSound` for tensor-batched FRI** on any
parameters `(params, shape)` over any `CurveListCA` field `K` (in particular
`Fp3Model` via `curveListCA_fp3`, zero unproven proximity assumptions).
Exposed for direct instantiation in Johnson-regime callers such as `DynamicRom`. -/
theorem rbrSound_pcsTensor_johnson_of_curveListCA [Fintype K]
    (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
    (wf : WellFormed m params shape)
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA K T)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) :
    let P := modelParams m params shape wf
    RbrSound (P.rounds + 2)
      (grindDoomed (powBits params shape)
        (PcsRbr.doomedTensor P.ldt P.shift (tensorCoord params shape) θ P.queries))
      (fun _ => εmax) := by
  intro P
  let W := maxWidth shape
  let Mopen := maxOpeningsPerHeight params.logBlowup shape
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : P.finalDegree = 2 ^ params.logFinalPolyLen := rfl
  let ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  let LJ : ℝ := (θ - ρ) / (θ ^ 2 - ρ)
  let εline : ℝ := (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hcard_dom : ∀ j ≤ P.rounds, (twoAdicDomain P.ω P.n j).card = 2 ^ (P.n - j) := fun j hj =>
    card_twoAdicDomain P.prim (hj.trans P.rounds_le)
  have hdeg_le : ∀ j ≤ P.rounds,
      ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * ((twoAdicDomain P.ω P.n j).card : ℝ) := by
    intro j hj
    have hcard := Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj
    have hinv : (2 : ℝ) ^ params.logBlowup * ρ = 1 := by
      dsimp only [ρ]; rw [← mul_pow]; norm_num
    refine le_of_eq ?_
    rw [hcard, hfinal]; push_cast
    linear_combination -((2 : ℝ) ^ (P.rounds - j) * (2 : ℝ) ^ params.logFinalPolyLen) * hinv
  have hLJ_nn : 0 ≤ LJ := by
    have h1 : θ ^ 2 ≤ θ := by nlinarith
    exact div_nonneg (by linarith) (sub_pos.mpr hgap).le
  have hline_nn : 0 ≤ εline := by
    dsimp only [εline]
    exact div_nonneg (add_nonneg hcT0 (mul_nonneg hLJ_nn (mul_nonneg (sub_nonneg.mpr hθ1)
      (by positivity)))) (Nat.cast_nonneg _)
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) W Mopen θ
        (((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) * εline) := by
    intro j hj
    have hcard_img : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card = 2 ^ (P.n - j) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hcard_dom j hj
    have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
      rw [hcard_img]
      exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n j)
    have hd_img : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hdeg_le j hj
    have hTj : (T ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card
        (2 ^ (P.rounds - j) * P.finalDegree)
        ⌈θ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ)⌉₊ 2 : ℝ) ≤
        ((2 - 1 : ℕ) : ℝ) * cT := by
      rw [hcard_img, hfinal]
      push_cast
      have h := hT j 2 hj le_rfl
      norm_num at h
      simpa [P, modelParams] using h
    have hcurve := curveMCA_of_curveListCA_of_card_le hca
      ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) 2
      hθ0 hθ1 hd_img hgap (by positivity) hTj hcard_le
    have hcurve' : CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) 2 θ εline := by
      refine ProximityGap.curveMCA_mono hcurve le_rfl ?_
      dsimp only [εline, LJ, ρ]
      exact le_of_eq (by norm_num)
    exact tensor2DMCA_of_curveMCA_two hcurve'
  have hε₀ : ∀ j ≤ P.rounds,
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) * εline ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) *
          (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K := by
    intro _ _
    have hsub_le : ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ 1
    calc ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) * εline
        ≤ ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) * εline :=
          mul_le_mul_of_nonneg_right hsub_le hline_nn
      _ = ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) *
            (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K := by
          dsimp only [εline]; ring
  let εβ_val : ℝ := (2 * cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ εβ_val := by
    intro i hi
    have hi1 : i + 1 ≤ P.rounds := hi
    have hn1 : 1 ≤ P.n := by have := P.rounds_le; omega
    have hcard_i1 : (twoAdicDomain P.ω P.n (i + 1)).card = 2 ^ (P.n - (i + 1)) :=
      hcard_dom (i + 1) hi1
    have hcard_le : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ (2 : ℝ) ^ (P.n - 1) := by
      rw [hcard_i1]
      exact_mod_cast Nat.pow_le_pow_right two_pos (by omega)
    have hTi : (T (twoAdicDomain P.ω P.n (i + 1)).card
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
        ⌈θ * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ)⌉₊ 3 : ℝ) ≤ 2 * cT := by
      rw [hcard_i1, hfinal]
      push_cast
      have h := hT (i + 1) 3 hi1 (by omega)
      norm_num at h
      exact h
    have hst := stepMCA_of_curveListCA_of_card_le hca (P.ldt.step i hi)
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
      hθ0 hθ1 (hdeg_le (i + 1) hi1) hgap (by positivity) hTi hcard_le
    have h2pow : 2 * (2 : ℝ) ^ (P.n - 1) = (2 : ℝ) ^ P.n := by
      conv_rhs => rw [← Nat.sub_add_cancel hn1, pow_succ']
    have heq : (2 * cT + 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1)))) / Fintype.card K = εβ_val := by
      dsimp only [εβ_val]
      have : 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1))) =
          LJ * ((1 - θ) * (2 * (2 : ℝ) ^ (P.n - 1))) := by ring
      rw [this, h2pow]
    rwa [heq] at hst
  have hrbr := rbrSound_grind_tensor P.ldt P.shift_ne (tensorCoord params shape)
    (fun j _ => tensorCoord_injective params shape j) hθ0.le P.queries (powBits params shape)
    hmca hε₀ hstep
  intro i hi t msg hd
  refine (hrbr i hi t msg hd).mono_right ?_
  beta_reduce
  rcases i with _ | k
  · rw [powBits_zero, pow_zero, div_one, roundErrorTensor_zero]
    exact hα
  · rcases Nat.lt_or_ge k P.ldt.rounds with hk | hk
    · rw [powBits_succ_of_lt params shape hk, roundErrorTensor_succ_of_lt hk]
      exact hβ
    · obtain rfl : k = numRounds params shape := by
        have hR : P.ldt.rounds = numRounds params shape := rfl
        have hR' : P.rounds = numRounds params shape := rfl
        omega
      rw [powBits_last, roundErrorTensor_succ_of_not_lt (Nat.not_lt.mpr hk)]
      exact hq

end CertiFri.Exec.Stark
