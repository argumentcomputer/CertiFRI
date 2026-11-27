import CertiFriProofs.Exec.Stark.PcsSoundTensor
import CertiFriProofs.Exec.Stark.FreeTensor

/-!
# The state function of the tensor-batched STARK (`sdoomedTensor`)

Tensor-batched counterpart of `Exec/Stark/State.lean`. Reuses `ShardView`,
`Supported`, `comOf`, `valuesOf`, `pcsMsg`, and `roundErr` from `State.lean`,
replacing only the uniform challenge family `UAns` with `UTensorAns` and the
PCS state function `PcsRbr.doomed` with `PcsRbr.doomedTensor`.

## Main results

* `sdoomedTensor_nil`: the empty transcript is doomed.
* `rbrSound_sdoomedTensor`: round-by-round soundness for any `r` rounds under
  any tensor-PCS `RbrSound` bound `εpcs`.
* `rbrSound_sdoomedTensor_ud`: **unconditional unique-decoding `RbrSound`**
  (zero proximity hypotheses!) with explicit round error `roundErr M sys B (pcsErrTensor sys d δ)`
  — directly instantiable by external adaptive-ROM frameworks such as `DynamicRom`.
* `balance_of_sdoomedTensorL`, `good_of_sdoomedTensorL`: deterministic consequences
  of being doomed on an accepted transcript.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

section ReadTensor

variable {fslots slots width : ℕ} (chals : List (UTensorAns K fslots slots width))

/-- The multi-slot answer of round `j`. -/
def tAnsAt (j : ℕ) : UTensorAns K fslots slots width :=
  chals[j]?.getD (fun _ => 0, fun _ => ⟨0, Nat.two_pow_pos _⟩)

/-- The primary (`0`-th) field challenge of round `j`. -/
def tFieldAt (j : ℕ) : K := (tAnsAt chals j).field

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem rawAt_append_of_ltT {msgs : List (IMsg F EF D K)} (m : IMsg F EF D K)
    {j : ℕ} (hj : j < msgs.length) : rawAt (msgs ++ [m]) j = rawAt msgs j := by
  unfold rawAt; rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem comAt_append_of_ltT {msgs : List (IMsg F EF D K)} (m : IMsg F EF D K)
    {j : ℕ} (hj : j < msgs.length) : comAt (msgs ++ [m]) j = comAt msgs j := by
  unfold comAt; rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem rawAt_append_lengthT (msgs : List (IMsg F EF D K)) (m : IMsg F EF D K) :
    rawAt (msgs ++ [m]) msgs.length = m.1 := by
  unfold rawAt; rw [List.getElem?_concat_length]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_append_of_lt (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : j < chals.length) : tAnsAt (chals ++ [c]) j = tAnsAt chals j := by
  unfold tAnsAt; rw [List.getElem?_append_left hj]

omit [DecidableEq K] in
private theorem tAnsAt_append_length (c : UTensorAns K fslots slots width) :
    tAnsAt (chals ++ [c]) chals.length = c := by
  unfold tAnsAt; rw [List.getElem?_concat_length]; rfl

omit [DecidableEq K] in
private theorem tFieldAt_append_of_lt (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : j < chals.length) : tFieldAt (chals ++ [c]) j = tFieldAt chals j := by
  unfold tFieldAt; rw [tAnsAt_append_of_lt chals c hj]

omit [DecidableEq K] in
private theorem tFieldAt_append_length (c : UTensorAns K fslots slots width) :
    tFieldAt (chals ++ [c]) chals.length = c.field := by
  unfold tFieldAt; rw [tAnsAt_append_length]

omit [DecidableEq K] in
private theorem tFieldAt_append_of_gt (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : chals.length < j) : tFieldAt (chals ++ [c]) j = tFieldAt chals j := by
  unfold tFieldAt tAnsAt
  rw [List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega),
    List.getElem?_eq_none (by omega)]

end ReadTensor

section RowsTensor

variable {M : StarkModel F EF K} {sys : System F D} {θ : ℝ} {com com' : Compiled.Committed K D}

omit [DecidableEq K] [Inhabited D] [DecidableEq D] in
private theorem baseRows_congrT (M : StarkModel F EF K) {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i; unfold StarkModel.baseRows; rw [h]

omit [Inhabited D] [DecidableEq D] in
private theorem colPoly_congrT (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ) {root : D}
    (h : com root = com' root) (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord; rw [h]

omit [Inhabited D] [DecidableEq D] in
private theorem pointRow_shardCols_congrT {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) (h1 : com stage1 = com' stage1)
    (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) (c : Circuit F)
    (n : ℕ) (g : K) (pos ci : ℕ) (publics : Array K) (x : K) :
    pointRow c n g (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics x =
      pointRow c n g (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci)
        publics x := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
    funext fun j => colPoly_congrT M _ _ h1 _ _ _ _
  have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
    funext fun j => colPoly_congrT M _ _ h2 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
    funext j
    unfold shardCols; dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congrT M _ _ (h3 root hpc) _ _ _ _
  unfold pointRow; rw [hmain, hstage2, hpre]

omit [Inhabited D] [DecidableEq D] in
private theorem rowVals_congrT {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  funext pos ci x; unfold rowVals; rw [pointRow_shardCols_congrT quot' h1 h2 h3]

omit [Inhabited D] [DecidableEq D] in
private theorem constraintFail_congrT {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs ↔
      ConstraintFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  unfold ConstraintFail; rw [rowVals_congrT quot' h1 h2 h3]

omit [Inhabited D] [DecidableEq D] in
private theorem alphaFail_congrT {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K} {α : K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    AlphaFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs α ↔
      AlphaFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs α := by
  unfold AlphaFail; rw [rowVals_congrT quot' h1 h2 h3]

end RowsTensor

section StateTensor

variable {fslots slots width : ℕ} (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D)
  (θ : ℝ) (B : Bounds) (msgs : List (IMsg F EF D K))
  (chals : List (UTensorAns K fslots slots width))

/-- What a tensor STARK chain says about the shard with header `hdr`. -/
noncomputable def tViewOf (hdr : ShardHeader F D) : ShardView F EF D K where
  hdr := hdr
  stage2 := (digestsIn (rawAt msgs 2)).getD 0 default
  quot := (digestsIn (rawAt msgs 3)).getD 0 default
  acc0 := (claimsAccumulator (rep M (tFieldAt chals 0)) (rep M (tFieldAt chals 1)) hdr.claims).2
  accs := ((extsOf (rawAt msgs 2)).drop 1).toArray
  β := tFieldAt chals 0
  γ := tFieldAt chals 1
  α := tFieldAt chals 2
  ζ := tFieldAt chals 3

variable {M sys θ}

/-- The first `j` rounds of the tensor-batched opening protocol of a shard,
read off a tensor STARK chain. -/
noncomputable def pcsTTensor {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    (j : ℕ) → Transcript (PcsRbr.Msg K hs.params.numClaims)
      (GrindChal (powBits sys.fri (v.shape M sys))
        (ChalTensor hs.params.ldt (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) hs.params.queries)) j
  | 0 => .nil
  | j + 1 => (pcsTTensor hs j).snoc (pcsMsg msgs hs j)
      (pcsChalTensor hs.params (maxWidth (v.shape M sys))
        (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
        (powBits sys.fri (v.shape M sys)) j (tAnsAt chals (4 + j)))

/-- The tensor-batched opening protocol of a shard is in its doomed state. -/
def PcsDoomedTensor {v : ShardView F EF D K} (hs : Supported M sys θ v) : Prop :=
  grindDoomed (powBits sys.fri (v.shape M sys))
    (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
      θ hs.params.queries)
    (min (msgs.length - 4) (hs.params.rounds + 2))
    (pcsTTensor msgs chals hs (min (msgs.length - 4) (hs.params.rounds + 2)))

/-- The part of the tensor STARK state function about one shard. -/
def shardDoomedTensor {v : ShardView F EF D K} (hs : Supported M sys θ v) : Prop :=
  v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
    (msgs.length = 3 → v.AFail M sys θ (M.baseRows (comOf sys v msgs))) ∧
    (4 ≤ msgs.length → (v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) ∧
      (5 ≤ msgs.length → v.Check M sys (valuesOf msgs) → PcsDoomedTensor msgs chals hs))

variable (M sys θ)

/-- **The tensor STARK state function**, on the messages and challenges of a transcript. -/
def sdoomedTensorL : Prop :=
  ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
    (¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre) →
      (1 ≤ msgs.length →
        (balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (tFieldAt chals 0)) ≠ 0) ∧
      (2 ≤ msgs.length →
        ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (tFieldAt chals 0))).eval (tFieldAt chals 1) ≠ 0)) ∧
    (3 ≤ msgs.length → ∀ hdr, pre.headers[V.shard (rawAt msgs 2)]? = some hdr →
      ∀ hs : Supported M sys θ (tViewOf M msgs chals hdr), shardDoomedTensor msgs chals hs)

/-- **The state function of the tensor-batched STARK.** -/
def sdoomedTensor (i : ℕ)
    (t : Transcript (IMsg F EF D K) (UTensorChal K fslots slots width) i) : Prop :=
  sdoomedTensorL M sys V θ B t.msgs (chalsOf t)

variable {M sys V θ B msgs chals}

private theorem length_chalsOfT {Msg U : Type} :
    ∀ {i : ℕ} (t : Transcript Msg (fun _ => U) i), (chalsOf t).length = i
  | _, .nil => rfl
  | _, .snoc t _ c => by
    show (chalsOf t ++ [c]).length = _
    rw [List.length_append, length_chalsOfT t, List.length_singleton]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_append_two (hdr : ShardHeader F D) (hc : chals.length = 2)
    (c : UTensorAns K fslots slots width) :
    tViewOf M msgs (chals ++ [c]) hdr = { tViewOf M msgs chals hdr with α := c.field } := by
  have h0 := tFieldAt_append_of_lt chals c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_lt chals c (show 1 < chals.length by omega)
  have h2 : tFieldAt (chals ++ [c]) 2 = c.field := by
    have h := tFieldAt_append_length chals c; rwa [hc] at h
  have h3 := tFieldAt_append_of_gt chals c (show chals.length < 3 by omega)
  simp only [tViewOf, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_append_three (hdr : ShardHeader F D) (hm : msgs.length = 3)
    (hc : chals.length = 3) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr =
      { tViewOf M msgs chals hdr with quot := (digestsIn m.1).getD 0 default, ζ := c.field } := by
  have r2 := rawAt_append_of_ltT m (show 2 < msgs.length by omega)
  have r3 : rawAt (msgs ++ [m]) 3 = m.1 := by
    have h := rawAt_append_lengthT msgs m; rwa [hm] at h
  have h0 := tFieldAt_append_of_lt chals c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_lt chals c (show 1 < chals.length by omega)
  have h2 := tFieldAt_append_of_lt chals c (show 2 < chals.length by omega)
  have h3 : tFieldAt (chals ++ [c]) 3 = c.field := by
    have h := tFieldAt_append_length chals c; rwa [hc] at h
  simp only [tViewOf, r2, r3, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_append (hdr : ShardHeader F D) (hm : 4 ≤ msgs.length)
    (hc : 4 ≤ chals.length) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr = tViewOf M msgs chals hdr := by
  have r2 := rawAt_append_of_ltT m (show 2 < msgs.length by omega)
  have r3 := rawAt_append_of_ltT m (show 3 < msgs.length by omega)
  have h0 := tFieldAt_append_of_lt chals c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_lt chals c (show 1 < chals.length by omega)
  have h2 := tFieldAt_append_of_lt chals c (show 2 < chals.length by omega)
  have h3 := tFieldAt_append_of_lt chals c (show 3 < chals.length by omega)
  simp only [tViewOf, r2, r3, h0, h1, h2, h3]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem valuesOf_appendT (hm : 5 ≤ msgs.length) (m : IMsg F EF D K) :
    valuesOf (msgs ++ [m]) = valuesOf msgs := by
  unfold valuesOf; rw [rawAt_append_of_ltT m (by omega)]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] in
private theorem comOf_appendT (sys : System F D) (v : ShardView F EF D K) (hm : 4 ≤ msgs.length)
    (m : IMsg F EF D K) : comOf sys v (msgs ++ [m]) = comOf sys v msgs := by
  unfold comOf
  rw [comAt_append_of_ltT m (show 0 < msgs.length by omega),
    comAt_append_of_ltT m (show 2 < msgs.length by omega),
    comAt_append_of_ltT m (show 3 < msgs.length by omega)]

omit [DecidableEq K] [Inhabited D] in
private theorem baseRows_comOf_appendT (M : StarkModel F EF K) (sys : System F D)
    (v : ShardView F EF D K) (hm : 3 ≤ msgs.length) (m : IMsg F EF D K) {root : D}
    (hroot : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root ∨ root = v.stage2) :
    M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root := by
  refine baseRows_congrT M ?_
  unfold comOf
  rw [comAt_append_of_ltT m (show 0 < msgs.length by omega),
    comAt_append_of_ltT m (show 2 < msgs.length by omega)]
  by_cases h1 : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root
  · rw [ite_eq_left h1, ite_eq_left h1]
  · have h2 : root = v.stage2 := by tauto
    rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]

private theorem pcsMsg_appendT {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) {k : ℕ} (hk : 4 + k < msgs.length) :
    pcsMsg (msgs ++ [m]) hs k = pcsMsg msgs hs k := by
  rcases k with _ | k
  · simp only [pcsMsg, valuesOf_appendT (show 5 ≤ msgs.length by omega) m,
      comOf_appendT sys v (show 4 ≤ msgs.length by omega) m]
  · simp only [pcsMsg, rawAt_append_of_ltT m hk, comAt_append_of_ltT m hk]

private theorem pcsTTensor_append {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    ∀ j, 4 + j ≤ msgs.length → 4 + j ≤ chals.length →
      pcsTTensor (msgs ++ [m]) (chals ++ [c]) hs j = pcsTTensor msgs chals hs j
  | 0, _, _ => rfl
  | j + 1, hm, hc => by
    simp only [pcsTTensor, pcsTTensor_append hs m c j (by omega) (by omega),
      pcsMsg_appendT hs m (show 4 + j < msgs.length by omega),
      tAnsAt_append_of_lt chals c (show 4 + j < chals.length by omega)]

private theorem pcsTTensor_append_succ {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) {j : ℕ} (hm : msgs.length = 4 + j)
    (hc : chals.length = 4 + j) :
    pcsTTensor (msgs ++ [m]) (chals ++ [c]) hs (j + 1) =
      (pcsTTensor msgs chals hs j).snoc (pcsMsg (msgs ++ [m]) hs j)
        (pcsChalTensor hs.params (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
          (powBits sys.fri (v.shape M sys)) j c) := by
  have hans : tAnsAt (chals ++ [c]) (4 + j) = c := by
    have h := tAnsAt_append_length chals c; rwa [hc] at h
  simp only [pcsTTensor, pcsTTensor_append (msgs := msgs) (chals := chals) hs m c j
    (by omega) (by omega), hans]

private theorem pcsDoomedTensor_iff {v : ShardView F EF D K} {hs : Supported M sys θ v} {n : ℕ}
    (hn : min (msgs.length - 4) (hs.params.rounds + 2) = n) :
    PcsDoomedTensor msgs chals hs ↔
      grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
          θ hs.params.queries) n
        (pcsTTensor msgs chals hs n) := by
  subst hn; rfl

private theorem shardDoomedTensor_three {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : msgs.length = 3) :
    shardDoomedTensor msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.AFail M sys θ (M.baseRows (comOf sys v msgs))) := by
  unfold shardDoomedTensor
  exact ⟨fun h hcf => (h hcf).1 hm,
    fun h hcf => ⟨fun _ => h hcf, fun h4 => absurd h4 (by omega)⟩⟩

private theorem shardDoomedTensor_four {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : msgs.length = 4) :
    shardDoomedTensor msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) := by
  unfold shardDoomedTensor
  exact ⟨fun h hcf => ((h hcf).2 (by omega)).1,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega),
      fun _ => ⟨h hcf, fun h5 => absurd h5 (by omega)⟩⟩⟩

private theorem shardDoomedTensor_of_five_le {v : ShardView F EF D K} {hs : Supported M sys θ v}
    (hm : 5 ≤ msgs.length) :
    shardDoomedTensor msgs chals hs ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        (v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) ∧
          (v.Check M sys (valuesOf msgs) → PcsDoomedTensor msgs chals hs)) := by
  unfold shardDoomedTensor
  exact ⟨fun h hcf => ⟨((h hcf).2 (by omega)).1, ((h hcf).2 (by omega)).2 hm⟩,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega), fun _ => ⟨(h hcf).1, fun _ => (h hcf).2⟩⟩⟩

/-! ### Round-by-round soundness -/

private theorem fractionLE_beta_roundT [Fintype K] (hfpos : 0 < fslots) (m : IMsg F EF D K) :
    FractionLE (fun c : UTensorAns K fslots slots width => ¬ sdoomedTensorL M sys V θ B [m] [c])
      ((2 * itemBound sys B : ℕ) / Fintype.card K) := by
  have h0 : (0 : ℝ) ≤ (2 * itemBound sys B : ℕ) / Fintype.card K := by positivity
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) _ :=
    FractionLE.false.mono_right h0
  have hraw : rawAt [m] 0 = m.1 := rfl
  rcases hdec : V.dec0 m.1 with _ | pre
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
  by_cases hgood : PreOk sys B pre ∧ ¬ Balanced (allItems M sys θ (M.baseRows m.2) pre)
  · refine ((fractionLE_tensorField hfpos (fractionLE_balPoly_beta hgood.2)).mono_right ?_).mono_left
      fun c hc => ?_
    · exact div_le_div_of_nonneg_right
        (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 (length_allItems_le hgood.1))) (Nat.cast_nonneg _)
    · by_contra hne
      refine hc fun pre' hdec' _ => ?_
      rw [hraw, hdec] at hdec'; cases hdec'
      exact ⟨fun _ => ⟨fun _ => hne, fun h => absurd h (by simp)⟩, fun h => absurd h (by simp)⟩
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
    exact ⟨fun hb => absurd ⟨hpre', hb⟩ hgood, fun h => absurd h (by simp)⟩

private theorem fractionLE_gamma_roundT [Fintype K] (hfpos : 0 < fslots)
    (hd : sdoomedTensorL M sys V θ B msgs chals) (hm : msgs.length = 1) (hc : chals.length = 1)
    (m : IMsg F EF D K) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorL M sys V θ B (msgs ++ [m]) (chals ++ [c]))
      ((2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K) := by
  have h0 : (0 : ℝ) ≤ (2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K := by positivity
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) _ :=
    FractionLE.false.mono_right h0
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_ltT m (by omega)
  have hcom : comAt (msgs ++ [m]) 0 = comAt msgs 0 := comAt_append_of_ltT m (by omega)
  have hlen : (msgs ++ [m]).length = 2 := by rw [List.length_append, hm, List.length_singleton]
  rcases hdec : V.dec0 (rawAt msgs 0) with _ | pre
  · refine hnone.mono_left fun c hc' => hc' fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
  by_cases hgood : PreOk sys B pre ∧
      ¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)
  · have hβ := ((hd pre hdec hgood.1).1 hgood.2).1 (by omega)
    refine ((fractionLE_tensorField hfpos (fractionLE_balPoly_gamma (L := lenBound sys B)
      (length_args_allItems_le hgood.1) hβ)).mono_right ?_).mono_left fun c hc' => ?_
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left 2 (length_allItems_le hgood.1)))) (Nat.cast_nonneg _)
    · by_contra hne
      refine hc' fun pre' hdec' _ => ?_
      rw [hraw, hdec] at hdec'; cases hdec'
      have h1 : tFieldAt (chals ++ [c]) 1 = c.field := by
        have h := tFieldAt_append_length chals c; rwa [hc] at h
      refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [hcom, tFieldAt_append_of_lt chals c (show 0 < chals.length by omega), h1]
      exact fun _ => ⟨fun _ => hβ, fun _ => hne⟩
  · refine hnone.mono_left fun c hc' => hc' fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
    refine ⟨fun hb => ?_, fun h => absurd h (by omega)⟩
    rw [hcom] at hb
    exact absurd ⟨hpre', hb⟩ hgood

private theorem sdoomedTensorL_append {pre : BatchPreamble F D}
    (hd : sdoomedTensorL M sys V θ B msgs chals) (hdec : V.dec0 (rawAt msgs 0) = some pre)
    (hpre : PreOk sys B pre) (hm : 2 ≤ msgs.length) (hc : 2 ≤ chals.length)
    (m : IMsg F EF D K) (c : UTensorAns K fslots slots width)
    (h : ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
      ∀ hs : Supported M sys θ (tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
        shardDoomedTensor (msgs ++ [m]) (chals ++ [c]) hs) :
    sdoomedTensorL M sys V θ B (msgs ++ [m]) (chals ++ [c]) := by
  intro pre' hdec' _
  rw [rawAt_append_of_ltT m (show 0 < msgs.length by omega), hdec] at hdec'
  cases hdec'
  refine ⟨?_, fun _ => h⟩
  rw [comAt_append_of_ltT m (show 0 < msgs.length by omega),
    tFieldAt_append_of_lt chals c (show 0 < chals.length by omega),
    tFieldAt_append_of_lt chals c (show 1 < chals.length by omega)]
  exact fun hb => ⟨fun _ => ((hd _ hdec hpre).1 hb).1 (by omega),
    fun _ => ((hd _ hdec hpre).1 hb).2 hm⟩

private theorem fractionLE_of_shardT [Fintype K] {ε : ℝ} (h0 : 0 ≤ ε)
    (hd : sdoomedTensorL M sys V θ B msgs chals) (hlen : chals.length = msgs.length)
    (hm : 2 ≤ msgs.length) (m : IMsg F EF D K)
    (h : ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
      ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
        FractionLE
          (fun c : UTensorAns K fslots slots width =>
            ¬ ∀ hs : Supported M sys θ (tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
              shardDoomedTensor (msgs ++ [m]) (chals ++ [c]) hs) ε) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorL M sys V θ B (msgs ++ [m]) (chals ++ [c])) ε := by
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_ltT m (by omega)
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) ε :=
    FractionLE.false.mono_right h0
  rcases hdec : V.dec0 (rawAt msgs 0) with _ | pre
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
  by_cases hpre : PreOk sys B pre
  swap
  · refine hnone.mono_left fun c hc => hc fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
    exact absurd hpre' hpre
  rcases hh : pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? with _ | hdr
  · refine hnone.mono_left fun c hc => hc ?_
    refine sdoomedTensorL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'; cases hh'
  · refine (h pre hdec hpre hdr hh).mono_left fun c hc hgood => hc ?_
    refine sdoomedTensorL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'; cases hh'
    exact hgood

private theorem fractionLE_alpha_roundT [Fintype K] (hfpos : 0 < fslots) {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size) (hm : msgs.length = 3) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ ∀ hs : Supported M sys θ { v with α := c.field },
          shardDoomedTensor msgs (chals ++ [c]) hs)
      ((constraintBound sys M.extData.d - 1 : ℕ) / Fintype.card K) := by
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  · refine (fractionLE_tensorField hfpos (fractionLE_alphaFail hact hCF)).mono_left
      fun c hc hAF => hc fun hs => ?_
    exact (shardDoomedTensor_three hm).mpr fun _ => hAF
  · refine (FractionLE.false.mono_right (by positivity)).mono_left fun c hc => hc fun hs => ?_
    exact (shardDoomedTensor_three hm).mpr fun hcf => absurd hcf hCF

private theorem fractionLE_zeta_roundT [Fintype K] (hfpos : 0 < fslots)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F)) {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size)
    (hdeg : ∀ pos, v.hdr.logDegrees.getD pos 0 ≤ sys.maxLogDegree) (hm : msgs.length = 3)
    (m : IMsg F EF D K) (q : D) (hd : ∀ hs : Supported M sys θ v, shardDoomedTensor msgs chals hs) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ ∀ hs : Supported M sys θ { v with quot := q, ζ := c.field },
          shardDoomedTensor (msgs ++ [m]) (chals ++ [c]) hs)
      (((zetaBound sys + cosetBound sys : ℕ) : ℝ) / Fintype.card K) := by
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False)
      (((zetaBound sys + cosetBound sys : ℕ) : ℝ) / Fintype.card K) :=
    FractionLE.false.mono_right (by positivity)
  have hlen : (msgs ++ [m]).length = 4 := by rw [List.length_append, hm, List.length_singleton]
  have h1 := baseRows_comOf_appendT M sys v (le_of_eq hm.symm) m (.inl rfl)
  have h2 := baseRows_comOf_appendT M sys v (le_of_eq hm.symm) m (.inr (.inr rfl))
  have h3 : ∀ root, sys.preprocessedCommit = some root →
      M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root :=
    fun root hroot => baseRows_comOf_appendT M sys v (le_of_eq hm.symm) m (.inr (.inl hroot))
  by_cases hsup : Supported M sys θ v
  swap
  · exact hnone.mono_left fun c hc => hc fun hs =>
      absurd ⟨hs.two, hs.final, hs.margin, hs.active, hs.height⟩ hsup
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc => hc fun hs => ?_
    exact (shardDoomedTensor_four hlen).mpr fun hcf =>
      absurd ((constraintFail_congrT (quot' := v.quot) h1 h2 h3).mp hcf) hCF
  have hAF := (alphaFail_congrT (quot := q) (quot' := v.quot) h1 h2 h3).mpr
    ((shardDoomedTensor_three hm).mp (hd hsup) hCF)
  refine ((fractionLE_tensorField hfpos ((fractionLE_zetaFail hact hdeg htwo hAF).or
    (fractionLE_offCosets hsup.active hsup.height hsup.two))).mono_left
    fun c hc => ?_).mono_right (le_of_eq ?_)
  · by_contra hno
    rw [not_or, not_not, not_not] at hno
    exact hc fun hs => (shardDoomedTensor_four hlen).mpr fun _ => hno
  · rw [Nat.cast_add, add_div]

private theorem fractionLE_pcs_roundT [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {v : ShardView F EF D K}
    (hs : Supported M sys θ v)
    (hpcs : RbrSound (hs.params.rounds + 2)
      (grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
          θ hs.params.queries))
      fun _ => εpcs)
    (hm : 4 ≤ msgs.length) (hc : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : shardDoomedTensor msgs chals hs) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ shardDoomedTensor (msgs ++ [m]) (chals ++ [c]) hs) εpcs := by
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) εpcs :=
    FractionLE.false.mono_right hεpcs
  have hlen : (msgs ++ [m]).length = msgs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hcom : comOf sys v (msgs ++ [m]) = comOf sys v msgs := comOf_appendT sys v hm m
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc' => hc' fun hcf => ?_
    rw [hcom] at hcf; exact absurd hcf hCF
  obtain ⟨hZF, hP⟩ := (hd hCF).2 hm
  have hZF' : v.ZFail M sys θ (M.baseRows (comOf sys v (msgs ++ [m]))) ∧ v.Off M sys := by
    rw [hcom]; exact hZF
  by_cases hCk : v.Check M sys (valuesOf (msgs ++ [m]))
  swap
  · exact hnone.mono_left fun c hc' => hc' ((shardDoomedTensor_of_five_le (by omega)).mpr
      fun _ => ⟨hZF', fun hck => absurd hck hCk⟩)
  rcases Nat.lt_or_ge (msgs.length - 4) (hs.params.rounds + 2) with hj | hj
  · obtain ⟨j, hj'⟩ : ∃ j, msgs.length = 4 + j := ⟨msgs.length - 4, by omega⟩
    have hdoom : grindDoomed (powBits sys.fri (v.shape M sys))
        (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
          θ hs.params.queries) j (pcsTTensor msgs chals hs j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact grindDoomed_nil (doomedTensor_zero _ _ _ _ _ _)
      · have h5 : 5 ≤ msgs.length := by omega
        rw [valuesOf_appendT h5 m] at hCk
        exact (pcsDoomedTensor_iff (by omega)).mp (hP h5 hCk)
    have hbits : powBits sys.fri (v.shape M sys) j ≤ width := by
      unfold powBits; split_ifs <;> omega
    have hfslots_v : tensorNumChallenges (maxWidth (v.shape M sys)) +
        tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) ≤ fslots :=
      (tensorNumChallenges_starkShape_le_fslotsBound sys M.extData.d hs.active.le
        v.hdr.logDegrees).trans hfslots
    have hfpos : 0 < fslots := lt_of_lt_of_le (pos_fslotsBound sys M.extData.d) hfslots
    have hbound := fractionLE_pcsChalTensor (fslots := fslots) (slots := slots) (width := width)
      hs.params (maxWidth (v.shape M sys)) (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
      (powBits sys.fri (v.shape M sys)) j hfslots_v hfpos hslots hbits (hs.two.trans hwidth)
      (hpcs j (by omega) (pcsTTensor msgs chals hs j) (pcsMsg (msgs ++ [m]) hs j) hdoom)
    refine hbound.mono_left fun c hc' hgd => hc' ?_
    refine (shardDoomedTensor_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun _ => ?_⟩
    refine (pcsDoomedTensor_iff (n := j + 1) (by omega)).mpr ?_
    rw [pcsTTensor_append_succ hs m c hj' (hc.trans hj')]
    exact hgd
  · have h5 : 5 ≤ msgs.length := by omega
    refine hnone.mono_left fun c hc' => hc' ?_
    refine (shardDoomedTensor_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun hck => ?_⟩
    rw [valuesOf_appendT h5 m] at hck
    refine (pcsDoomedTensor_iff (n := hs.params.rounds + 2) (by omega)).mpr ?_
    rw [pcsTTensor_append hs m c (hs.params.rounds + 2) (by omega) (by omega)]
    exact (pcsDoomedTensor_iff (by omega)).mp (hP h5 hck)

private theorem fractionLE_sdoomedTensorL [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
            θ hs.params.queries))
        fun _ => εpcs)
    (hlen : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : sdoomedTensorL M sys V θ B msgs chals) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorL M sys V θ B (msgs ++ [m]) (chals ++ [c]))
      (roundErr M sys B εpcs msgs.length) := by
  have hfpos : 0 < fslots := lt_of_lt_of_le (pos_fslotsBound sys M.extData.d) hfslots
  unfold roundErr
  split_ifs with h0 h1 h2 h3
  · obtain rfl : msgs = [] := List.length_eq_zero_iff.mp h0
    obtain rfl : chals = [] := List.length_eq_zero_iff.mp hlen
    exact fractionLE_beta_roundT hfpos m
  · exact fractionLE_gamma_roundT hfpos hd h1 (hlen.trans h1) m
  · refine fractionLE_of_shardT (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_alpha_roundT (θ := θ) (msgs := msgs ++ [m]) (chals := chals) hfpos
      (v := tViewOf M (msgs ++ [m]) chals hdr) hok.active.le
      (by rw [List.length_append, h2, List.length_singleton])).mono_left
      fun c hc hgood => hc ?_
    rw [tViewOf_append_two hdr (hlen.trans h2) c]
    exact hgood
  · refine fractionLE_of_shardT (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_ltT m (by omega)] at hh
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_zeta_roundT hfpos htwo (v := tViewOf M msgs chals hdr) hok.active.le
      hok.logDegree_le h3 m ((digestsIn m.1).getD 0 default)
      ((hd pre hdec hpre).2 (by omega) hdr hh)).mono_left fun c hc hgood => hc ?_
    rw [tViewOf_append_three hdr h3 (hlen.trans h3) m c]
    exact hgood
  · have h4 : 4 ≤ msgs.length := by omega
    refine fractionLE_of_shardT hεpcs hd hlen (by omega) m fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_ltT m (by omega)] at hh
    have hv := fun c : UTensorAns K fslots slots width =>
      tViewOf_append (M := M) (chals := chals) hdr h4 (by omega) m c
    by_cases hsup : Supported M sys θ (tViewOf M msgs chals hdr)
    · refine (fractionLE_pcs_roundT hεpcs hfslots hslots hcommit hquery hwidth hsup (hpcs _ hsup)
        h4 hlen m ((hd pre hdec hpre).2 (by omega) hdr hh hsup)).mono_left
        fun c hc hgood => hc ?_
      rw [hv c]
      exact fun _ => hgood
    · refine (FractionLE.false.mono_right hεpcs).mono_left fun c hc => hc ?_
      rw [hv c]
      exact fun hs => absurd hs hsup

variable (M sys V θ B msgs chals)

/-- The empty tensor STARK transcript is doomed. -/
theorem sdoomedTensor_nil :
    sdoomedTensor (fslots := fslots) (slots := slots) (width := width) M sys V θ B 0 .nil :=
  fun _ _ _ => ⟨fun _ => ⟨fun h => (Nat.not_succ_le_zero _ h).elim,
    fun h => (Nat.not_succ_le_zero _ h).elim⟩, fun h => (Nat.not_succ_le_zero _ h).elim⟩

/-- **Round-by-round soundness of the tensor-batched STARK.** -/
theorem rbrSound_sdoomedTensor [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
            θ hs.params.queries))
        fun _ => εpcs)
    (r : ℕ) :
    RbrSound r (sdoomedTensor (fslots := fslots) (slots := slots) (width := width) M sys V θ B)
      (roundErr M sys B εpcs) := by
  intro i _ t m hd
  have h := fractionLE_sdoomedTensorL (V := V) (B := B) hεpcs htwo hfslots hslots hcommit hquery
    hwidth hpcs ((length_chalsOfT t).trans t.length_msgs.symm) m hd
  rw [t.length_msgs] at h
  exact h

/-- **Unconditional unique-decoding round-by-round soundness of the tensor-batched STARK.**
Requires zero proximity assumptions (only `0 ≤ δ` and `2 * δ + (1 / 2) ^ logBlowup ≤ 1`),
yielding `RbrSound r (sdoomedTensor ...)` over shape-independent `UTensorChal` with tight
tensor error `pcsErrTensor` — directly instantiable by adaptive-ROM theorems (`DynamicRom`). -/
theorem rbrSound_sdoomedTensor_ud [Fintype K] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) (r : ℕ) :
    RbrSound r (sdoomedTensor (fslots := fslots) (slots := slots) (width := width)
        M sys V (1 - δ) B)
      (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ)) :=
  rbrSound_sdoomedTensor M sys V (1 - δ) B (pcsErrTensor_nonneg sys M.extData.d hδ) htwo hfslots
    hslots hcommit hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate v hs.active hs) r

variable {M sys V θ B msgs chals}

/-- In a doomed transcript of at least two rounds whose first message decodes to a
preamble within bounds, unbalanced lookup messages do not vanish at `(β, γ)`. -/
theorem balance_of_sdoomedTensorL (hd : sdoomedTensorL M sys V θ B msgs chals)
    {pre : BatchPreamble F D} (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre)
    (hlen : 2 ≤ msgs.length)
    (hbal : ¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)) :
    ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
      (C (tFieldAt chals 0))).eval (tFieldAt chals 1) ≠ 0 :=
  ((hd pre hdec hpre).1 hbal).2 hlen

private theorem claimsOf_ungrind_pcsTTensor {v : ShardView F EF D K} (hs : Supported M sys θ v) :
    ∀ j, claimsOf (ungrind (pcsTTensor msgs chals hs (j + 1))) = (pcsMsg msgs hs 0).claims
  | 0 => rfl
  | j + 1 => claimsOf_ungrind_pcsTTensor hs j

omit [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] in
private theorem map_commitment_openingClaimsT (v : ShardView F EF D K)
    (proof : Proof F EF D Unit Unit) (ζ : EF) (h1 : proof.stage1Commit = v.hdr.stage1Commit)
    (h2 : proof.stage2Commit = v.stage2) (h3 : proof.quotientCommit = v.quot) :
    (openingClaims sys proof ζ).map (·.commitment) = v.commitments sys := by
  unfold openingClaims ShardView.commitments
  rw [h1, h2, h3]
  cases sys.preprocessedCommit <;> simp

private theorem claimsFail_pcsMsgTensor (hfixed : sys.FixedOk) {v : ShardView F EF D K}
    (hs : Supported M sys θ v) (hcheck : v.Check M sys (valuesOf msgs))
    (hZF : v.ZFail M sys θ (M.baseRows (comOf sys v msgs))) (hoff : v.Off M sys) :
    ClaimsFail hs.params.ldt hs.params.shift θ (pcsMsg msgs hs 0).claims := by
  obtain ⟨proof, hact, hst1, hst2, hq, haccs, hlog, hshape, hvals, hcons, hzeta⟩ := hcheck
  have hrep : ∀ x : K, M.ext.toModel (rep M x) = x := fun x => Function.surjInv_eq M.surj x
  have heq : starkShape sys M.extData.d proof.active proof.logDegrees = v.shape M sys := by
    unfold ShardView.shape; rw [hact, hlog]
  have key : ∀ (shape : ClaimShape)
      (htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F)),
      shape = v.shape M sys →
      ClaimsFail (modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).ldt
        (modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).shift θ
        ((modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri _ htwo)).claims
          (view M.toFieldModel sys.fri shape
            (firstMessage (v.commitments sys) (shapePoints (F := F) shape (rep M v.ζ))
              (valuesOf msgs)))
          (M.baseRows (comOf sys v msgs))) →
      ClaimsFail hs.params.ldt hs.params.shift θ (pcsMsg msgs hs 0).claims := by
    intro shape htwo h; subst h; exact id
  have hZF' : ZetaFail M sys θ (M.baseRows (comOf sys v msgs)) proof.active proof.logDegrees
      proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel (rep M v.β))
      (M.ext.toModel (rep M v.γ)) (M.ext.toModel v.acc0)
      (proof.intermediateAccumulators.map M.ext.toModel) (M.ext.toModel (rep M v.α))
      (M.ext.toModel (rep M v.ζ)) := by
    rw [hact, hlog, hst1, hst2, hq, haccs]; simp only [hrep]; exact hZF
  have hoff' : OffCosets M sys proof.active proof.logDegrees (M.ext.toModel (rep M v.ζ)) := by
    rw [hact, hlog, hrep]; exact hoff
  have hcf := claimsFail_of_zetaFail hfixed proof hshape (rep M v.β) (rep M v.γ) v.acc0
    (rep M v.α) (rep M v.ζ) hcons hzeta (by rw [heq]; exact hs.two)
    (by rw [heq]; exact hs.final) (by rw [heq]; exact hs.margin) hoff' hZF'
  rw [map_commitment_openingClaimsT v proof _ hst1 hst2 hq,
    claimPoints_openingClaims sys proof hshape, ← M.degree_eq, hvals] at hcf
  exact key _ (by rw [heq]; exact hs.two) heq hcf

/-- **An accepted tensor STARK transcript that is doomed has no failing constraint.** -/
theorem good_of_sdoomedTensorL (hfixed : sys.FixedOk) (hd : sdoomedTensorL M sys V θ B msgs chals)
    {pre : BatchPreamble F D} (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D} (hhdr : pre.headers[V.shard (rawAt msgs 2)]? = some hdr)
    (hs : Supported M sys θ (tViewOf M msgs chals hdr))
    (hlen : msgs.length = 4 + (hs.params.rounds + 2))
    (hcheck : (tViewOf M msgs chals hdr).Check M sys (valuesOf msgs))
    (hpow : PowPasses (pcsTTensor msgs chals hs (hs.params.rounds + 2)))
    (hacc : AcceptsTensor hs.params.ldt hs.params.shift
      (starkTensorCoord M sys hs)
      (ungrind (pcsTTensor msgs chals hs (hs.params.rounds + 2)))) :
    ¬ (tViewOf M msgs chals hdr).CFail M sys θ
      (M.baseRows (comOf sys (tViewOf M msgs chals hdr) msgs)) := by
  intro hCF
  obtain ⟨hZF, hP⟩ := ((hd pre hdec hpre).2 (by omega) hdr hhdr hs hCF).2 (by omega)
  have hgd := (pcsDoomedTensor_iff (n := hs.params.rounds + 2) (by omega)).mp (hP (by omega) hcheck)
  have hfail : ClaimsFail hs.params.ldt hs.params.shift θ
      (claimsOf (ungrind (pcsTTensor msgs chals hs (hs.params.rounds + 2)))) := by
    rw [claimsOf_ungrind_pcsTTensor hs (hs.params.rounds + 1)]
    exact claimsFail_pcsMsgTensor hfixed hs hcheck hZF.1 hZF.2
  exact not_grindDoomedTensor_of_accepts _ hpow hfail hacc hgd

end StateTensor

end CertiFri.Exec.Stark
