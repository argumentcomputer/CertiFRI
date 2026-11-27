import CertiFriProofs.Exec.Stark.GoodLogTensor
import CertiFriProofs.Exec.MultiArity.TensorExec

/-!
# State function and round-by-round soundness of multi-arity tensor-batched STARKs

Multi-arity (`2 ^ a`, `a ≥ 1`, variable per-round schedules `arities : List ℕ`)
counterpart of `Exec/Stark/{PcsSoundTensor,StateTensor,GoodLogTensor}.lean` and
`Theory/Stark/UniformTensor.lean`.

## Contents

1. **Schedule invariants (`scheduleOfShape_pos`, `scheduleOfShape_sum_le`,
   `scheduleOfShape_length_le_logMaxHeight`) & `claimsFailMulti_of_claimsFail`:**
   universal bounds on `Fri.scheduleOfShape` for any `0 < params.maxLogArity`,
   allowing direct reuse of the entire shape-independent STARK oracle (`STAns`),
   challenge family (`UTensorChal`), `interpTensor`, `fslotsBound`, `pcsErrTensor`,
   and `roundErr` infrastructure.
2. **Shape-independent uniform challenges (`pcsChalTensorMulti`,
   `fractionLE_pcsChalTensorMulti`):** pulls back every round fraction bound on
   `GrindChal bits (ChalTensorMulti P.ldt W M P.queries)` to `UTensorAns K fslots slots width`.
3. **Multi-arity PCS round-by-round soundness:**
   * `rbrSound_pcsTensorMulti_ud`: unconditional unique-decoding `RbrSound` for
     every supported shard, matching the exact binary tensor error `pcsErrTensor sys d δ`.
   * `rbrSound_pcsTensorMulti_johnson_of_curveListCA`: unconditional Johnson-regime
     `RbrSound` for ANY valid multi-arity schedule `arities` over any `CurveListCA`
     field (with exact `m = 2 ^ a` cancellation on every folding round).
4. **Multi-arity STARK state function & good logs:**
   * `sdoomedTensorMulti`, `sdoomedTensorMulti_nil`, `rbrSound_sdoomedTensorMulti`,
     `rbrSound_sdoomedTensorMulti_ud`, `balance_of_sdoomedTensorMultiL`,
     `good_of_sdoomedTensorMultiL`, `GoodLogTensorMulti`,
     `sdoomedTensorMulti_of_goodLogTensorMulti`, `prob_not_goodLogTensorMulti_le`.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr
  OracleComp Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D]

/-! ## 1. Universal `scheduleOfShape` invariants and `ClaimsFailMulti` bridge -/

section ScheduleHelpers

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- Every round log-arity produced by `scheduleOfShape` is positive whenever
`0 < params.maxLogArity`. -/
theorem scheduleOfShape_pos {params : FriParams} {shape : ClaimShape}
    (hcap : 0 < params.maxLogArity) :
    ∀ a ∈ scheduleOfShape params shape, 0 < a := by
  unfold scheduleOfShape
  cases hdh : distinctLogHeights params.logBlowup shape with
  | nil => simp [foldSchedule]
  | cons tallest rest =>
    have hp := distinctLogHeights_pairwise params.logBlowup shape
    rw [hdh] at hp
    intro a ha
    have hb := foldSchedule_bounds hp hcap a ha
    omega

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- The total log-arity reduction of `scheduleOfShape` never exceeds `logMaxHeight`. -/
theorem scheduleOfShape_sum_le {params : FriParams} {shape : ClaimShape}
    (hcap : 0 < params.maxLogArity) :
    (scheduleOfShape params shape).sum ≤ logMaxHeight params.logBlowup shape := by
  unfold scheduleOfShape
  cases hdh : distinctLogHeights params.logBlowup shape with
  | nil => simp [foldSchedule]
  | cons tallest rest =>
    have hp := distinctLogHeights_pairwise params.logBlowup shape
    rw [hdh] at hp
    have htall : tallest = logMaxHeight params.logBlowup shape := distinctLogHeights_head_eq hdh
    rw [foldSchedule_sum hp hcap, htall]
    exact Nat.sub_le _ _

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- Any list of positive natural numbers has `length ≤ sum`. -/
theorem list_length_le_sum_of_pos {l : List ℕ} (hpos : ∀ a ∈ l, 0 < a) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := hpos a List.mem_cons_self
    have has := ih fun x hx => hpos x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.sum_cons]
    omega

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
/-- The number of rounds of `scheduleOfShape` never exceeds `logMaxHeight`. -/
theorem scheduleOfShape_length_le_logMaxHeight {params : FriParams} {shape : ClaimShape}
    (hcap : 0 < params.maxLogArity) :
    (scheduleOfShape params shape).length ≤ logMaxHeight params.logBlowup shape :=
  (list_length_le_sum_of_pos (scheduleOfShape_pos hcap)).trans (scheduleOfShape_sum_le hcap)

omit [DecidableEq D] in
/-- Bridge from binary `ClaimsFail` to multi-arity `ClaimsFailMulti` for any valid schedule
(without requiring `θ ≤ 1`: when `1 < θ`, `ClaimsFailMulti` holds trivially at round `0`). -/
theorem claimsFailMulti_of_claimsFail (m : FieldModel F EF K) (params : FriParams)
    (shape : ClaimShape) (arities : List ℕ) (wf : WellFormed m params shape)
    (hvalid : scheduleValid params shape arities = true)
    (raw : RawMsg F EF D) (com : Compiled.Committed K D) {θ : ℝ}
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    (h : ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
      ((modelParams m params shape wf).claims (view m params shape raw) com)) :
    ClaimsFailMulti (modelParamsMulti m params shape arities wf hpos hsum).ldt
      (modelParamsMulti m params shape arities wf hpos hsum).shift θ
      ((modelParamsMulti m params shape arities wf hpos hsum).claims
        (viewMulti m params shape arities raw) com) := by
  by_cases hθ : θ ≤ 1
  · exact (claimsFailMulti_iff_claimsFail m params shape arities wf hvalid raw com hθ).mpr h
  · push Not at hθ
    let Pm := modelParamsMulti m params shape arities wf hpos hsum
    refine ⟨0, Nat.zero_le _, ?_⟩
    rintro ⟨A, hsub, hcard, -⟩
    have hA_le : (A.card : ℝ) ≤ (((Pm.ldt.domain 0).image (Pm.shift * ·)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hpos_card : (0 : ℝ) < (((Pm.ldt.domain 0).image (Pm.shift * ·)).card : ℝ) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ Pm.shift_ne),
        Compiled.MultiParams.ldt_domain, card_twoAdicDomain Pm.prim (Pm.cum_le_n 0)]
      positivity
    nlinarith

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] in
/-- Whenever at least one circuit is active, `starkShape.flatten` is nonempty. -/
theorem starkShape_flatten_ne_nil (sys : System F D) (d : ℕ) {active : Array Bool}
    (hne : ¬ (activeIndices active).isEmpty) (logDegrees : Array ℕ) :
    (starkShape sys d active logDegrees).flatten ≠ [] := by
  cases hact : activeIndices active with
  | nil => rw [hact] at hne; exact absurd rfl hne
  | cons ci rest =>
    intro hnil
    have hmem : MatrixShape.mk (logDegrees.getD 0 0) (sys.circuits.getD ci default).mainWidth 2 ∈
        (starkShape sys d active logDegrees).flatten := by
      unfold starkShape traceShapes
      rw [hact]
      simp [List.zipIdx_cons]
    rw [hnil] at hmem
    cases hmem

end ScheduleHelpers

/-! ## 2. Shape-independent uniform challenges for multi-arity tensor FRI -/

section UniformTensorMulti

variable {fslots slots width : ℕ}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
/-- `P.indexOf` is left-inverse to `pointOfIndex` on indices below `2 ^ P.n`. -/
theorem multiParams_indexOf_pointOfIndex (P : Compiled.MultiParams K) {i : ℕ} (hi : i < 2 ^ P.n) :
    P.indexOf (pointOfIndex P.ω P.n P.n i) = i := by
  have hex : ∃ j < 2 ^ P.n, pointOfIndex P.ω P.n P.n j = pointOfIndex P.ω P.n P.n i :=
    ⟨i, hi, rfl⟩
  rw [Compiled.MultiParams.indexOf, dite_eq_left hex]
  exact (pointOfIndex_inj P.prim le_rfl (Nat.find_spec hex).1 hi).mp (Nat.find_spec hex).2

/-- The challenge of round `j` of the multi-arity tensor-batched opening protocol
with parameters `P`, tensor dimensions `(W, M)`, and proof-of-work bits `bits`,
read off a uniform answer `u : UTensorAns K fslots slots width`. -/
noncomputable def pcsChalTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ)
    (j : ℕ) (u : UTensorAns K fslots slots width) :
    GrindChal bits (ChalTensorMulti P.ldt W M P.queries) j :=
  (⟨u.bits 0 (bits j), u.bits_lt 0 (bits j)⟩,
    if h0 : j = 0 then
      (chalTensorMulti0 h0).symm
        (fun b => u.fieldAt b.val, fun b => u.fieldAt (Fri.tensorNumChallenges W + b.val))
    else if hle : j ≤ P.ldt.rounds then
      (chalTensorMultiField h0 hle).symm u.field
    else
      (chalTensorMultiQuery hle).symm fun t =>
        ⟨pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n), by
          simpa [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.cum] using
            pointOfIndex_mem_twoAdicDomain P.prim P.n
              (u.bits (t.val + if bits j = 0 then 0 else 1) P.n)⟩)

variable (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ) (j : ℕ)
  (u : UTensorAns K fslots slots width)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem pcsChalTensorMulti_pow :
    ((pcsChalTensorMulti P W M bits j u).1 : ℕ) = u.bits 0 (bits j) := rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem tensor_pcsChalTensorMulti (h0 : j = 0) :
    (pcsChalTensorMulti P W M bits j u).2.tensor =
      (fun b => u.fieldAt b.val, fun b => u.fieldAt (Fri.tensorNumChallenges W + b.val)) := by
  rw [ChalTensorMulti.tensor_of_zero h0]
  simp only [pcsChalTensorMulti, dite_eq_left h0, Equiv.apply_symm_apply]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem field_pcsChalTensorMulti (h0 : j ≠ 0) (hle : j ≤ P.rounds) :
    (pcsChalTensorMulti P W M bits j u).2.field = u.field := by
  have hle' : j ≤ P.ldt.rounds := hle
  rw [ChalTensorMulti.field_of_pos_le h0 hle']
  simp only [pcsChalTensorMulti, dite_eq_right h0, dite_eq_left hle', Equiv.apply_symm_apply]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem field_pcsChalTensorMulti_of_not_le (hle : ¬ j ≤ P.rounds) :
    (pcsChalTensorMulti P W M bits j u).2.field = 0 :=
  ChalTensorMulti.field_of_not_le (S := P.ldt) hle _

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem points_pcsChalTensorMulti (hle : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    (pcsChalTensorMulti P W M bits j u).2.points t =
      pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n) := by
  have h0 : j ≠ 0 := by omega
  have hle' : ¬ j ≤ P.ldt.rounds := hle
  rw [ChalTensorMulti.points_of_not_le hle']
  simp only [pcsChalTensorMulti, dite_eq_right h0, dite_eq_right hle', Equiv.apply_symm_apply]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
theorem indexOf_points_pcsChalTensorMulti (hle : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    P.indexOf ((pcsChalTensorMulti P W M bits j u).2.points t) =
      u.bits (t.val + if bits j = 0 then 0 else 1) P.n := by
  rw [points_pcsChalTensorMulti P W M bits j u hle t]
  exact multiParams_indexOf_pointOfIndex P (u.bits_lt _ _)

private def pointOfTM (i : Fin (2 ^ P.n)) : ↥(P.ldt.domain 0) :=
  ⟨pointOfIndex P.ω P.n P.n i, by
    simpa [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.cum] using
      pointOfIndex_mem_twoAdicDomain P.prim P.n i⟩

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
private theorem pointOfTM_bijective : Function.Bijective (pointOfTM P) := by
  constructor
  · intro a b hab
    exact Fin.ext ((pointOfIndex_inj P.prim le_rfl a.2 b.2).mp (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    have hx' : x ∈ twoAdicDomain P.ω P.n (P.n - P.n) := by
      simpa [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.cum] using hx
    obtain ⟨i, hi, rfl⟩ := exists_pointOfIndex_eq P.prim le_rfl hx'
    exact ⟨⟨i, hi⟩, rfl⟩

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
private theorem balanced_pointsTM (hn : P.n ≤ width) (q : ℕ) :
    Oracle.Balanced (fun (v : Fin q → Fin (2 ^ width)) (t : Fin q) =>
      pointOfTM P ⟨(v t : ℕ) % 2 ^ P.n, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) :=
  Oracle.Balanced.postcomp ((Oracle.Balanced.of_bijective (pointOfTM_bijective P)).comp
    (Oracle.Balanced.finMod hn))

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem balanced_tensorSliceM [Finite K] {kCol kOpen : ℕ}
    (hfslots : kCol + kOpen ≤ fslots) :
    Oracle.Balanced (fun (v : Fin fslots → K) =>
      ((fun b : Fin kCol => v ⟨b.val, by omega⟩),
       (fun b : Fin kOpen => v ⟨kCol + b.val, by omega⟩))) := by
  let g : Fin kCol ⊕ Fin kOpen → Fin fslots := fun s =>
    match s with
    | .inl b => ⟨b.val, by omega⟩
    | .inr b => ⟨kCol + b.val, by omega⟩
  have hginj : Function.Injective g := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (by simpa [g] using congrArg Fin.val hab))
      | inr b =>
        have hv := congrArg Fin.val hab; dsimp only [g] at hv; omega
    | inr a =>
      cases b with
      | inl b =>
        have hv := congrArg Fin.val hab; dsimp only [g] at hv; omega
      | inr b =>
        have hv := congrArg Fin.val hab; dsimp only [g] at hv
        exact congrArg Sum.inr (Fin.ext (by omega))
  have h1 : Oracle.Balanced (fun (v : Fin fslots → K) (s : Fin kCol ⊕ Fin kOpen) => v (g s)) :=
    Oracle.Balanced.precomp_injective hginj
  have h2 := (Oracle.Balanced.of_equiv
    (Equiv.sumArrowEquivProdArrow (Fin kCol) (Fin kOpen) K)).comp h1
  exact h2.congr fun _ => rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
private theorem balanced_pcsChalTensorMulti_zero [Finite K]
    (hfslots : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ fslots)
    (hslots : 0 < slots) (hbits : bits j ≤ width) (h0 : j = 0) :
    Oracle.Balanced (pcsChalTensorMulti P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensorMulti P.ldt W M P.queries) j) := by
  have hb0 : Oracle.Balanced (fun v : Fin slots → Fin (2 ^ width) => v ⟨0, hslots⟩) :=
    Oracle.Balanced.eval _
  have hfst := (Oracle.Balanced.of_equiv (chalTensorMulti0 (S := P.ldt) (W := W) (M := M)
    (q := P.queries) h0).symm).comp (balanced_tensorSliceM hfslots)
  have hsnd := (Oracle.Balanced.finMod hbits).comp hb0
  refine ((Oracle.Balanced.of_equiv (Equiv.prodComm _ _)).comp
    (Oracle.Balanced.prodMap hfst hsnd)).congr fun u => ?_
  refine Prod.ext (Fin.ext ?_) ?_
  · exact (UTensorAns.bits_of_lt u hslots (bits j)).symm
  · simp only [pcsChalTensorMulti, dite_eq_left h0]
    refine congrArg (chalTensorMulti0 h0).symm (Prod.ext ?_ ?_)
    · funext b; exact (UTensorAns.fieldAt_of_lt u (by omega)).symm
    · funext b; exact (UTensorAns.fieldAt_of_lt u (by omega)).symm

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
private theorem balanced_pcsChalTensorMulti_fold [Finite K]
    (hfpos : 0 < fslots) (hslots : 0 < slots) (hbits : bits j ≤ width)
    (h0 : j ≠ 0) (hle : j ≤ P.ldt.rounds) :
    Oracle.Balanced (pcsChalTensorMulti P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensorMulti P.ldt W M P.queries) j) := by
  have hb0 : Oracle.Balanced (fun v : Fin slots → Fin (2 ^ width) => v ⟨0, hslots⟩) :=
    Oracle.Balanced.eval _
  have hf0 : Oracle.Balanced (fun v : Fin fslots → K => v ⟨0, hfpos⟩) := Oracle.Balanced.eval _
  have hfst := (Oracle.Balanced.of_equiv (chalTensorMultiField (S := P.ldt) (W := W) (M := M)
    (q := P.queries) h0 hle).symm).comp hf0
  have hsnd := (Oracle.Balanced.finMod hbits).comp hb0
  refine ((Oracle.Balanced.of_equiv (Equiv.prodComm _ _)).comp
    (Oracle.Balanced.prodMap hfst hsnd)).congr fun u => ?_
  refine Prod.ext (Fin.ext ?_) ?_
  · exact (UTensorAns.bits_of_lt u hslots (bits j)).symm
  · simp only [pcsChalTensorMulti, dite_eq_right h0, dite_eq_left hle]
    refine congrArg (chalTensorMultiField h0 hle).symm ?_
    exact (UTensorAns.fieldAt_of_lt u hfpos).symm

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
private theorem balanced_pcsChalTensorMulti_query [Finite K]
    (hslots : P.queries + 1 ≤ slots) (hbits : bits j ≤ width) (hn : P.n ≤ width)
    (hle : ¬ j ≤ P.ldt.rounds) :
    Oracle.Balanced (pcsChalTensorMulti P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensorMulti P.ldt W M P.queries) j) := by
  have h0 : j ≠ 0 := by omega
  have hpts := (Oracle.Balanced.of_equiv (chalTensorMultiQuery (S := P.ldt) (W := W) (M := M)
    (q := P.queries) hle).symm).comp (balanced_pointsTM P (width := width) hn P.queries)
  by_cases hb : bits j = 0
  · have hsub : Subsingleton (Fin (2 ^ bits j)) :=
      Fin.subsingleton_iff_le_one.mpr (by rw [hb, pow_zero])
    have hres : Oracle.Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin P.queries) =>
        v (Fin.castLE (Nat.le_of_succ_le hslots) t)) :=
      Oracle.Balanced.precomp_injective (Fin.castLE_injective _)
    have hq := hpts.comp (hres.comp (Oracle.Balanced.snd (β := Fin fslots → K)))
    refine (hq.prodMk_const ⟨0, Nat.two_pow_pos _⟩).congr fun u => ?_
    refine Prod.ext (Subsingleton.elim _ _) ?_
    simp only [pcsChalTensorMulti, dite_eq_right h0, dite_eq_right hle]
    refine congrArg (chalTensorMultiQuery hle).symm (funext fun t => Subtype.ext ?_)
    change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
    rw [ite_eq_left hb, Nat.add_zero,
      UTensorAns.bits_of_lt u (lt_of_lt_of_le t.2 (Nat.le_of_succ_le hslots))]
    rfl
  · have hres : Oracle.Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin (P.queries + 1)) =>
        v (Fin.castLE hslots t)) :=
      Oracle.Balanced.precomp_injective (Fin.castLE_injective _)
    have hsplit := (Oracle.Balanced.finConsSplit P.queries).comp
      (hres.comp (Oracle.Balanced.snd (β := Fin fslots → K)))
    refine ((Oracle.Balanced.prodMap (Oracle.Balanced.finMod hbits) hpts).comp hsplit).congr
      fun u => ?_
    refine Prod.ext (Fin.ext ?_) ?_
    · exact (UTensorAns.bits_of_lt u (by omega) (bits j)).symm
    · simp only [pcsChalTensorMulti, dite_eq_right h0, dite_eq_right hle]
      refine congrArg (chalTensorMultiQuery hle).symm (funext fun t => Subtype.ext ?_)
      change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
      rw [ite_eq_right hb, UTensorAns.bits_of_lt u (by omega)]
      rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] in
/-- **A fraction bound on round `j` of multi-arity tensor-batched FRI pulls back cleanly
to shape-independent `UTensorAns K fslots slots width`.** -/
theorem fractionLE_pcsChalTensorMulti [Fintype K]
    (hfslots : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ fslots)
    (hfpos : 0 < fslots) (hslots : P.queries + 1 ≤ slots) (hbits : bits j ≤ width)
    (hn : P.n ≤ width)
    {p : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) j → Prop} {ε : ℝ}
    (h : FractionLE p ε) :
    FractionLE (fun u : UTensorAns K fslots slots width =>
      p (pcsChalTensorMulti P W M bits j u)) ε := by
  refine FractionLE.comap ?_ h
  by_cases h0 : j = 0
  · exact balanced_pcsChalTensorMulti_zero P W M bits j hfslots (by omega) hbits h0
  · by_cases hle : j ≤ P.ldt.rounds
    · exact balanced_pcsChalTensorMulti_fold P W M bits j hfpos (by omega) hbits h0 hle
    · exact balanced_pcsChalTensorMulti_query P W M bits j hslots hbits hn hle

end UniformTensorMulti

/-! ## 3. Multi-arity PCS round-by-round soundness (UD & Johnson) -/

section PcsSoundMulti

omit [Inhabited D] [DecidableEq D] in
/-- Canonical per-round folding schedule of a supported shard. -/
def Supported.arities {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {v : ShardView F EF D K} (_ : Supported M sys θ v) : List ℕ :=
  scheduleOfShape sys.fri (v.shape M sys)

omit [Inhabited D] [DecidableEq D] in
/-- Multi-arity compiled opening parameters of a supported shard. -/
noncomputable def Supported.paramsMulti {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) :
    Compiled.MultiParams K :=
  modelParamsMulti M.toFieldModel sys.fri (v.shape M sys) (scheduleOfShape sys.fri (v.shape M sys))
    (M.wellFormed sys.fri _ hs.two) (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap)

omit [Inhabited D] [DecidableEq D] in
/-- The 2D tensor coordinate map of a supported multi-arity STARK shard, typed directly
over `(hs.paramsMulti hcap).numClaims`. -/
def starkTensorCoordMulti (M : StarkModel F EF K) (sys : System F D) {θ : ℝ}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) :
    ∀ j, Fin ((hs.paramsMulti hcap).numClaims j) →
      Fin (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) ×
        Fin (maxWidth (v.shape M sys)) :=
  tensorCoordMulti sys.fri (v.shape M sys) (scheduleOfShape sys.fri (v.shape M sys))

omit [Inhabited D] [DecidableEq D] in
theorem starkTensorCoordMulti_injective (M : StarkModel F EF K) (sys : System F D) {θ : ℝ}
    {v : ShardView F EF D K} (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) (j : ℕ) :
    Function.Injective (starkTensorCoordMulti M sys hs hcap j) :=
  tensorCoordMulti_injective sys.fri (v.shape M sys) (scheduleOfShape sys.fri (v.shape M sys)) j

private theorem not_claimsFailMulti_of_forall_eq_zero {S : MultiLdtInstance K} {s : K} {θ : ℝ}
    (hθ : θ ≤ 1) {m : ℕ → ℕ} (hm : ∀ j, m j = 0) (claims : ∀ j, Fin (m j) → Claim K) :
    ¬ ClaimsFailMulti S s θ claims := by
  rintro ⟨j, -, hfail⟩
  refine hfail ⟨_, Finset.Subset.refl _, mul_le_of_le_one_left (Nat.cast_nonneg _) hθ, fun k => ?_⟩
  exact absurd (lt_of_lt_of_eq k.isLt (hm j)) (Nat.not_lt_zero _)

omit [Inhabited D] [DecidableEq D] in
/-- **Unconditional unique-decoding round-by-round soundness of multi-arity tensor-batched
FRI for every supported STARK shard.** Because `m = 2 ^ a` cancels completely in
`stepMCAArity_ud`, every round error is bounded by the exact same `pcsErrTensor sys d δ`
as binary folding! -/
theorem rbrSound_pcsTensorMulti_ud [Fintype K] (M : StarkModel F EF K) (sys : System F D)
    (hcap : 0 < sys.fri.maxLogArity) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1) (v : ShardView F EF D K)
    (hactive : v.hdr.active.size = sys.circuits.size) (hs : Supported M sys (1 - δ) v) :
    let P := hs.paramsMulti hcap
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
        (PcsRbr.doomedTensorMulti P.ldt P.shift (starkTensorCoordMulti M sys hs hcap)
          (1 - δ) P.queries))
      fun _ => pcsErrTensor (K := K) sys M.extData.d δ := by
  intro P
  let shape := v.shape M sys
  let arities := scheduleOfShape sys.fri shape
  let W := maxWidth shape
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup shape
  rcases hfl : shape.flatten with _ | ⟨m, l⟩
  · have hnil : claimRefs sys.fri.logBlowup shape = [] := by
      have hlen : (claimRefs sys.fri.logBlowup shape).length = 0 := by
        have hlen_p : (pointRefs sys.fri.logBlowup shape).length = 0 := by
          have : (pointRefs sys.fri.logBlowup shape).length =
              (shape.flatten.map (·.numPoints)).sum := by
            have h1 : ∀ (ls : List (List MatrixShape)) (k : ℕ),
                ((ls.zipIdx k).flatMap fun (mats, batch) =>
                  mats.zipIdx.flatMap fun (m, matrix) =>
                    List.replicate m.numPoints (PointRef.mk batch matrix
                      (m.logDegree + sys.fri.logBlowup) m.width)).length =
                  (ls.flatten.map (·.numPoints)).sum := by
              intro ls
              induction ls with
              | nil => intro _; rfl
              | cons mats rest ih =>
                intro k
                rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, ih (k + 1),
                  List.flatten_cons, List.map_append, List.sum_append]
                congr 1
                have h2 : ∀ (ms : List MatrixShape) (j : ℕ),
                    ((ms.zipIdx j).flatMap fun (m, matrix) =>
                      List.replicate m.numPoints (PointRef.mk k matrix
                        (m.logDegree + sys.fri.logBlowup) m.width)).length =
                      (ms.map (·.numPoints)).sum := by
                  intro ms
                  induction ms with
                  | nil => intro _; rfl
                  | cons m ms ihm =>
                    intro j
                    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append,
                      List.length_replicate, ihm (j + 1), List.map_cons, List.sum_cons]
                exact h2 mats 0
            exact h1 shape 0
          rw [this, hfl]; rfl
        have hpnil : pointRefs sys.fri.logBlowup shape = [] :=
          List.eq_nil_of_length_eq_zero hlen_p
        simp [claimRefs, hpnil]
      exact List.eq_nil_of_length_eq_zero hlen
    have hzero : ∀ j, P.numClaims j = 0 := fun j => by
      show (levelClaims sys.fri.logBlowup shape _ _).length = 0
      rw [levelClaims, hnil]; rfl
    intro i hi t msg hd
    exact (FractionLE.false.mono_right (pcsErrTensor_nonneg sys M.extData.d hδ)).mono_left
      fun c hc => hc fun _ => doomedTensorMulti_of_not_claimsFail
        (not_claimsFailMulti_of_forall_eq_zero (sub_le_self 1 hδ) hzero _)
  · have hne : shape.flatten ≠ [] := by rw [hfl]; exact List.cons_ne_nil _ _
    have hvalid : scheduleValid sys.fri shape arities = true :=
      scheduleValid_scheduleOfShape hcap hne hs.final
    have hsum_eq : arities.sum + sys.fri.logFinalHeight =
        logMaxHeight sys.fri.logBlowup shape :=
      (scheduleValid_iff.mp hvalid).2.1
    have hθ : (0 : ℝ) ≤ 1 - δ := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ sys.fri.logBlowup := by positivity
      linarith
    have hcard_mul : ∀ j ≤ P.rounds,
        (P.ldt.domain j).card = 2 ^ sys.fri.logBlowup * P.ldt.degree j := fun j _ => by
      rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_degree,
        card_twoAdicDomain P.prim (P.cum_le_n j)]
      show 2 ^ (P.n - P.cum j) =
        2 ^ sys.fri.logBlowup * (2 ^ (arities.sum - P.cum j) * 2 ^ sys.fri.logFinalPolyLen)
      have hcle : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
      rw [← pow_add, ← pow_add]
      congr 1
      show logMaxHeight sys.fri.logBlowup shape - cumLogArity arities j =
        sys.fri.logBlowup + (arities.sum - cumLogArity arities j + sys.fri.logFinalPolyLen)
      unfold FriParams.logFinalHeight at hsum_eq
      omega
    have hdist_dom : ∀ j ≤ P.rounds,
        2 * (δ * (P.ldt.domain j).card) + P.ldt.degree j ≤ (P.ldt.domain j).card := fun j hj => by
      have hinv : (2 : ℝ) ^ sys.fri.logBlowup * (1 / 2 : ℝ) ^ sys.fri.logBlowup = 1 := by
        rw [← mul_pow]; norm_num
      have hdeg : (P.ldt.degree j : ℝ) = (1 / 2 : ℝ) ^ sys.fri.logBlowup * (P.ldt.domain j).card := by
        rw [hcard_mul j hj]; push_cast
        linear_combination -(P.ldt.degree j : ℝ) * hinv
      rw [hdeg]
      nlinarith [Nat.cast_nonneg (α := ℝ) (P.ldt.domain j).card]
    have hcard_le : ∀ j ≤ P.rounds, ((P.ldt.domain j).card : ℝ) ≤ (2 : ℝ) ^ P.n := fun j _ => by
      rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
      exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n (P.cum j))
    have hmca : ∀ j ≤ P.rounds,
        Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) W Mopen (1 - δ)
          (((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
            (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K)) := by
      intro j hj
      refine tensor2DMCA_ud _ _ W Mopen hδ ?_
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hdist_dom j hj
    have hε₀ : ∀ j ≤ P.rounds,
        ((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
          (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K) ≤
        ((tensorNumChallenges W + tensorNumChallenges Mopen : ℕ) : ℝ) *
          ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K := by
      intro j hj
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcard_le j hj) (add_nonneg zero_le_one hδ))
        (Nat.cast_nonneg _)
    have hstep : ∀ i < P.rounds,
        StepMCAArity (2 ^ P.ldt.logArity i) (P.ldt.zeta i) (P.ldt.domain i)
          (P.ldt.domain (i + 1)) (P.ldt.degree (i + 1)) (1 - δ)
          (((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) := by
      intro i hi
      have hps : PowStep (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i)
          (P.ldt.domain (i + 1)) := by
        rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_domain,
          Compiled.MultiParams.ldt_zeta, P.cum_succ hi]
        exact powStep_twoAdicDomain P.prim (P.logArity_pos hi) (P.cum_succ hi ▸ P.cum_le_n (i + 1))
      have hbase := stepMCAArity_ud hps (P.ldt.degree (i + 1)) hδ (hdist_dom (i + 1) hi)
      intro ro f
      obtain ⟨bad, hbad, hgood⟩ := hbase ro f
      refine ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcard_le i hi.le) (by linarith)) (Nat.cast_nonneg _))
        (Nat.cast_nonneg _)), hgood⟩
    have hrbr := rbrSound_grind_tensorMulti P.ldt P.shift_ne
      (starkTensorCoordMulti M sys hs hcap)
      (fun j _ => starkTensorCoordMulti_injective M sys hs hcap j) hθ P.queries
      (powBitsMulti sys.fri arities) hmca hε₀ hstep
    have h2n_le : (2 : ℝ) ^ P.n ≤ (2 : ℝ) ^ (sys.maxLogDegree + sys.fri.logBlowup) :=
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
    · rw [powBitsMulti_zero, pow_zero, div_one, roundErrorTensor_zero]
      refine le_trans ?_ (le_max_left _ _)
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact mul_le_mul hk_le (mul_le_mul_of_nonneg_left h2n_le h1δ)
        (mul_nonneg h1δ (pow_nonneg zero_le_two _)) (Nat.cast_nonneg _)
    · rcases Nat.lt_or_ge k P.ldt.rounds with hk | hk
      · have hka : k < arities.length := hk
        rw [powBitsMulti_succ_of_lt sys.fri arities hka, roundErrorTensor_succ_of_lt hk]
        refine le_trans ?_ ((le_max_left _ _).trans (le_max_right _ _))
        refine div_le_div_of_nonneg_right (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
          (pow_nonneg zero_le_two _)
        exact mul_le_mul_of_nonneg_left h2n_le h1δ
      · obtain rfl : k = arities.length := by
          have hR : P.ldt.rounds = arities.length := rfl
          have hR' : P.rounds = arities.length := rfl
          omega
        rw [powBitsMulti_last, roundErrorTensor_succ_of_not_lt (Nat.not_lt.mpr hk)]
        exact (le_max_right _ _).trans (le_max_right _ _)

omit [Inhabited D] [DecidableEq D] in
/-- **Unconditional Johnson-regime `RbrSound` for multi-arity tensor-batched FRI** on any
parameters `(params, shape)` and any variable per-round schedule `arities` over any
`CurveListCA` field `K` (in particular `Fp3Model` via `curveListCA_fp3`).
Because `m = 2 ^ a` cancels against BOTH `d' = d_src / m` and `|D'| = |D_src| / m`, the
folding error `(cT + L_J * (1 - θ) * 2 ^ H) / |K| / 2 ^ commitPowBits` is completely
independent of `m = 2 ^ a`! -/
theorem rbrSound_pcsTensorMulti_johnson_of_curveListCA [Fintype K]
    (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (wf : WellFormed m params shape) (hpos : ∀ a ∈ arities, 0 < a)
    (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)
    {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA K T)
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT_batch : ∀ j ≤ arities.length,
      (T (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j))
        (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j)⌉₊ 2 : ℝ) ≤ cT)
    (hT_fold : ∀ i < arities.length,
      (T (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) : ℝ) ≤ cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) / Fintype.card K ≤ εmax)
    (hβ : (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti params arities)
        (PcsRbr.doomedTensorMulti P.ldt P.shift (tensorCoordMulti params shape arities)
          θ P.queries))
      (fun _ => εmax) := by
  intro P
  set ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  set W := maxWidth shape
  set Mopen := maxOpeningsPerHeight params.logBlowup shape
  have hcard_mul : ∀ j ≤ P.rounds,
      (P.ldt.domain j).card = 2 ^ params.logBlowup * P.ldt.degree j := fun j _ => by
    rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_degree,
      card_twoAdicDomain P.prim (P.cum_le_n j)]
    show 2 ^ (P.n - P.cum j) =
      2 ^ params.logBlowup * (2 ^ (arities.sum - P.cum j) * 2 ^ params.logFinalPolyLen)
    have hcle : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
    rw [← pow_add, ← pow_add]
    congr 1
    show logMaxHeight params.logBlowup shape - cumLogArity arities j =
      params.logBlowup + (arities.sum - cumLogArity arities j + params.logFinalPolyLen)
    unfold FriParams.logFinalHeight at hsum_eq
    omega
  have hrate : ∀ j ≤ P.rounds, (P.ldt.degree j : ℝ) ≤ ρ * (P.ldt.domain j).card := fun j hj => by
    have hinv : (2 : ℝ) ^ params.logBlowup * ρ = 1 := by
      dsimp only [ρ]; rw [← mul_pow]; norm_num
    rw [hcard_mul j hj]; push_cast
    have : ρ * ((2 : ℝ) ^ params.logBlowup * (P.ldt.degree j : ℝ)) = (P.ldt.degree j : ℝ) := by
      linear_combination (P.ldt.degree j : ℝ) * hinv
    exact le_of_eq this.symm
  have hLJ_nn : 0 ≤ (θ - ρ) / (θ ^ 2 - ρ) := by
    have hnum : 0 ≤ θ - ρ := by nlinarith
    have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
    exact div_nonneg hnum hden.le
  have hcard_le : ∀ j ≤ P.rounds, ((P.ldt.domain j).card : ℝ) ≤ (2 : ℝ) ^ P.n := fun j _ => by
    rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n (P.cum j))
  let εLine : ℝ := (cT + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hεLine_nn : 0 ≤ εLine := by
    dsimp only [εLine]
    have : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    positivity
  have hpow_ge : ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) ≤
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le _ 1
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) W Mopen θ
        (((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) * εLine) := by
    intro j hj
    have hcard_img : ((P.ldt.domain j).image (P.shift * ·)).card = 2 ^ (P.n - P.cum j) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne),
        Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    have hdeg_img : (P.ldt.degree j : ℝ) ≤ ρ * ((P.ldt.domain j).image (P.shift * ·)).card := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hrate j hj
    have hTj : (T ((P.ldt.domain j).image (P.shift * ·)).card (P.ldt.degree j)
        ⌈θ * (((P.ldt.domain j).image (P.shift * ·)).card : ℝ)⌉₊ 2 : ℝ) ≤ cT := by
      rw [hcard_img]
      have hcast : ((2 ^ (P.n - P.cum j) : ℕ) : ℝ) = (2 : ℝ) ^ (P.n - P.cum j) := by push_cast; rfl
      rw [hcast]
      exact hT_batch j hj
    have hcm := curveMCA_of_curveListCA_rel hca ((P.ldt.domain j).image (P.shift * ·))
      (P.ldt.degree j) 2 hθ0 hθ1 hdeg_img hgap hcT0 hTj
    have hcm' : CurveMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) 2 θ εLine := by
      refine ProximityGap.curveMCA_mono hcm le_rfl ?_
      rw [show ((2 - 1 : ℕ) : ℝ) = 1 by norm_num, mul_one,
        Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcard_le j hj) (sub_nonneg.mpr hθ1)) hLJ_nn))
        (Nat.cast_nonneg _)
    exact tensor2DMCA_of_curveMCA_two hcm'
  have hε₀ : ∀ j ≤ P.rounds,
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) - 1 : ℕ) : ℝ) * εLine ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) * εLine :=
    fun _ _ => mul_le_mul_of_nonneg_right hpow_ge hεLine_nn
  have hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.ldt.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) θ εLine := by
    intro i hi
    have hps : PowStep (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i)
        (P.ldt.domain (i + 1)) := by
      rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_domain,
        Compiled.MultiParams.ldt_zeta, P.cum_succ hi]
      exact powStep_twoAdicDomain P.prim (P.logArity_pos hi) (P.cum_succ hi ▸ P.cum_le_n (i + 1))
    have hcard_dst : (P.ldt.domain (i + 1)).card = 2 ^ (P.n - P.cum (i + 1)) := by
      rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n (i + 1))]
    have hi_ar : i < arities.length := hi
    have ha_eq : arities.getD i 1 = P.logArity i := by
      simp only [P, modelParamsMulti, Compiled.MultiParams.logArity,
        List.getD_eq_getElem _ _ hi_ar]
    have hTi : (T (P.ldt.domain (i + 1)).card (P.ldt.degree (i + 1))
        ⌈θ * ((P.ldt.domain (i + 1)).card : ℝ)⌉₊ (2 ^ P.logArity i + 1) : ℝ) ≤ cT := by
      rw [hcard_dst, ← ha_eq]
      have hcast : ((2 ^ (P.n - P.cum (i + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (P.n - P.cum (i + 1)) := by
        push_cast; rfl
      rw [hcast]
      exact hT_fold i hi_ar
    have hbase := stepMCAArity_of_curveListCA_rel hca hps (P.ldt.degree (i + 1)) hθ0 hθ1
      (hrate (i + 1) hi) hgap hcT0 hTi
    intro ro f
    obtain ⟨bad, hbad, hgood⟩ := hbase ro f
    refine ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcard_le i hi.le) (sub_nonneg.mpr hθ1)) hLJ_nn))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)), hgood⟩
  have hrbr := rbrSound_grind_tensorMulti P.ldt P.shift_ne (tensorCoordMulti params shape arities)
    (fun j _ => tensorCoordMulti_injective params shape arities j) hθ0.le P.queries
    (powBitsMulti params arities) hmca hε₀ hstep
  intro i hi t msg hd
  refine (hrbr i hi t msg hd).mono_right ?_
  beta_reduce
  rcases i with _ | k
  · rw [powBitsMulti_zero, pow_zero, div_one, roundErrorTensor_zero]
    have hmul : ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) * εLine =
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges Mopen) : ℕ) : ℝ) *
          (cT + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K := by
      dsimp only [εLine]; ring
    rw [hmul]
    exact hα
  · rcases Nat.lt_or_ge k P.ldt.rounds with hk | hk
    · have hka : k < arities.length := hk
      rw [powBitsMulti_succ_of_lt params arities hka, roundErrorTensor_succ_of_lt hk]
      exact hβ
    · obtain rfl : k = arities.length := by
        have hR : P.ldt.rounds = arities.length := rfl
        have hR' : P.rounds = arities.length := rfl
        omega
      rw [powBitsMulti_last, roundErrorTensor_succ_of_not_lt (Nat.not_lt.mpr hk)]
      exact hq

end PcsSoundMulti

/-! ## 4. Multi-arity tensor STARK state function (`sdoomedTensorMulti`) -/

section StateTensorMulti

variable {fslots slots width : ℕ} (M : StarkModel F EF K) (sys : System F D)
  (hcap : 0 < sys.fri.maxLogArity) (V : Variant F EF D) (θ : ℝ) (B : Bounds)
  (msgs : List (IMsg F EF D K)) (chals : List (UTensorAns K fslots slots width))

variable {M sys θ}

/-- Round-`k` message of the multi-arity opening protocol of a shard, read off a tensor
STARK chain. -/
noncomputable def pcsMsgMulti {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) :
    ℕ → PcsRbr.Msg K (hs.paramsMulti hcap).numClaims
  | 0 => (hs.paramsMulti hcap).read 0
      (viewMulti M.toFieldModel sys.fri (v.shape M sys) (scheduleOfShape sys.fri (v.shape M sys))
        (firstMessage (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ))
          (valuesOf msgs)))
      (M.baseRows (comOf sys v msgs))
  | k + 1 => (hs.paramsMulti hcap).read (k + 1)
      (viewMulti M.toFieldModel sys.fri (v.shape M sys) (scheduleOfShape sys.fri (v.shape M sys))
        (rawAt msgs (4 + (k + 1))))
      (comAt msgs (4 + (k + 1)))

/-- The first `j` rounds of the multi-arity tensor-batched opening protocol of a shard,
read off a tensor STARK chain. -/
noncomputable def pcsTTensorMulti {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) :
    (j : ℕ) → Transcript (PcsRbr.Msg K (hs.paramsMulti hcap).numClaims)
      (GrindChal (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
        (ChalTensorMulti (hs.paramsMulti hcap).ldt (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
          (hs.paramsMulti hcap).queries)) j
  | 0 => .nil
  | j + 1 => (pcsTTensorMulti hs hcap j).snoc (pcsMsgMulti msgs hs hcap j)
      (pcsChalTensorMulti (hs.paramsMulti hcap) (maxWidth (v.shape M sys))
        (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
        (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys))) j (tAnsAt chals (4 + j)))

/-- The multi-arity tensor-batched opening protocol of a shard is in its doomed state. -/
def PcsDoomedTensorMulti {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) : Prop :=
  grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
    (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
      (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries)
    (min (msgs.length - 4) ((hs.paramsMulti hcap).rounds + 2))
    (pcsTTensorMulti msgs chals hs hcap (min (msgs.length - 4) ((hs.paramsMulti hcap).rounds + 2)))

/-- The part of the multi-arity tensor STARK state function about one shard. -/
def shardDoomedTensorMulti {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) : Prop :=
  v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
    (msgs.length = 3 → v.AFail M sys θ (M.baseRows (comOf sys v msgs))) ∧
    (4 ≤ msgs.length → (v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) ∧
      (5 ≤ msgs.length → v.Check M sys (valuesOf msgs) → PcsDoomedTensorMulti msgs chals hs hcap))

variable (M sys θ)

/-- **The multi-arity tensor STARK state function**, on messages and challenges. -/
def sdoomedTensorMultiL : Prop :=
  ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
    (¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre) →
      (1 ≤ msgs.length →
        (balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (tFieldAt chals 0)) ≠ 0) ∧
      (2 ≤ msgs.length →
        ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
          (C (tFieldAt chals 0))).eval (tFieldAt chals 1) ≠ 0)) ∧
    (3 ≤ msgs.length → ∀ hdr, pre.headers[V.shard (rawAt msgs 2)]? = some hdr →
      ∀ hs : Supported M sys θ (tViewOf M msgs chals hdr),
        shardDoomedTensorMulti msgs chals hs hcap)

/-- **The state function of the multi-arity tensor-batched STARK.** -/
def sdoomedTensorMulti (i : ℕ)
    (t : Transcript (IMsg F EF D K) (UTensorChal K fslots slots width) i) : Prop :=
  sdoomedTensorMultiL M sys hcap V θ B t.msgs (chalsOf t)

variable {M sys hcap V θ B msgs chals}

private theorem length_chalsOfTM {Msg U : Type} :
    ∀ {i : ℕ} (t : Transcript Msg (fun _ => U) i), (chalsOf t).length = i
  | _, .nil => rfl
  | _, .snoc t _ c => by
    show (chalsOf t ++ [c]).length = _
    rw [List.length_append, length_chalsOfTM t, List.length_singleton]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem rawAt_append_of_ltTM (m : IMsg F EF D K) {j : ℕ} (hj : j < msgs.length) :
    rawAt (msgs ++ [m]) j = rawAt msgs j := by
  unfold rawAt; rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem comAt_append_of_ltTM (m : IMsg F EF D K) {j : ℕ} (hj : j < msgs.length) :
    comAt (msgs ++ [m]) j = comAt msgs j := by
  unfold comAt; rw [List.getElem?_append_left hj]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem rawAt_append_lengthTM (m : IMsg F EF D K) :
    rawAt (msgs ++ [m]) msgs.length = m.1 := by
  unfold rawAt; rw [List.getElem?_concat_length]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_append_of_ltM (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : j < chals.length) : tAnsAt (chals ++ [c]) j = tAnsAt chals j := by
  unfold tAnsAt; rw [List.getElem?_append_left hj]

omit [DecidableEq K] in
private theorem tAnsAt_append_lengthM (c : UTensorAns K fslots slots width) :
    tAnsAt (chals ++ [c]) chals.length = c := by
  unfold tAnsAt; rw [List.getElem?_concat_length]; rfl

omit [DecidableEq K] in
private theorem tFieldAt_append_of_ltM (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : j < chals.length) : tFieldAt (chals ++ [c]) j = tFieldAt chals j := by
  unfold tFieldAt; rw [tAnsAt_append_of_ltM c hj]

omit [DecidableEq K] in
private theorem tFieldAt_append_lengthM (c : UTensorAns K fslots slots width) :
    tFieldAt (chals ++ [c]) chals.length = c.field := by
  unfold tFieldAt; rw [tAnsAt_append_lengthM]

omit [DecidableEq K] in
private theorem tFieldAt_append_of_gtM (c : UTensorAns K fslots slots width) {j : ℕ}
    (hj : chals.length < j) : tFieldAt (chals ++ [c]) j = tFieldAt chals j := by
  unfold tFieldAt tAnsAt
  rw [List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega),
    List.getElem?_eq_none (by omega)]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_append_twoM (hdr : ShardHeader F D) (hc : chals.length = 2)
    (c : UTensorAns K fslots slots width) :
    tViewOf M msgs (chals ++ [c]) hdr = { tViewOf M msgs chals hdr with α := c.field } := by
  have h0 := tFieldAt_append_of_ltM (chals := chals) c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_ltM (chals := chals) c (show 1 < chals.length by omega)
  have h2 : tFieldAt (chals ++ [c]) 2 = c.field := by
    have h := tFieldAt_append_lengthM (chals := chals) c; rwa [hc] at h
  have h3 := tFieldAt_append_of_gtM (chals := chals) c (show chals.length < 3 by omega)
  simp only [tViewOf, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_append_threeM (hdr : ShardHeader F D) (hm : msgs.length = 3)
    (hc : chals.length = 3) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr =
      { tViewOf M msgs chals hdr with quot := (digestsIn m.1).getD 0 default, ζ := c.field } := by
  have r2 := rawAt_append_of_ltTM (msgs := msgs) m (show 2 < msgs.length by omega)
  have r3 : rawAt (msgs ++ [m]) 3 = m.1 := by
    have h := rawAt_append_lengthTM (msgs := msgs) m; rwa [hm] at h
  have h0 := tFieldAt_append_of_ltM (chals := chals) c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_ltM (chals := chals) c (show 1 < chals.length by omega)
  have h2 := tFieldAt_append_of_ltM (chals := chals) c (show 2 < chals.length by omega)
  have h3 : tFieldAt (chals ++ [c]) 3 = c.field := by
    have h := tFieldAt_append_lengthM (chals := chals) c; rwa [hc] at h
  simp only [tViewOf, r2, r3, h0, h1, h2, h3]

omit [DecidableEq K] [DecidableEq D] in
private theorem tViewOf_appendM (hdr : ShardHeader F D) (hm : 4 ≤ msgs.length)
    (hc : 4 ≤ chals.length) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr = tViewOf M msgs chals hdr := by
  have r2 := rawAt_append_of_ltTM (msgs := msgs) m (show 2 < msgs.length by omega)
  have r3 := rawAt_append_of_ltTM (msgs := msgs) m (show 3 < msgs.length by omega)
  have h0 := tFieldAt_append_of_ltM (chals := chals) c (show 0 < chals.length by omega)
  have h1 := tFieldAt_append_of_ltM (chals := chals) c (show 1 < chals.length by omega)
  have h2 := tFieldAt_append_of_ltM (chals := chals) c (show 2 < chals.length by omega)
  have h3 := tFieldAt_append_of_ltM (chals := chals) c (show 3 < chals.length by omega)
  simp only [tViewOf, r2, r3, h0, h1, h2, h3]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] in
private theorem valuesOf_appendTM (hm : 5 ≤ msgs.length) (m : IMsg F EF D K) :
    valuesOf (msgs ++ [m]) = valuesOf msgs := by
  unfold valuesOf; rw [rawAt_append_of_ltTM (msgs := msgs) m (by omega)]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] in
private theorem comOf_appendTM (sys : System F D) (v : ShardView F EF D K) (hm : 4 ≤ msgs.length)
    (m : IMsg F EF D K) : comOf sys v (msgs ++ [m]) = comOf sys v msgs := by
  unfold comOf
  rw [comAt_append_of_ltTM (msgs := msgs) m (by omega),
    comAt_append_of_ltTM (msgs := msgs) m (by omega),
    comAt_append_of_ltTM (msgs := msgs) m (by omega)]

omit [DecidableEq K] [Inhabited D] [DecidableEq D] in
private theorem baseRows_congrTM (M : StarkModel F EF K) {com com' : Compiled.Committed K D}
    {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i; unfold StarkModel.baseRows; rw [h]

omit [Inhabited D] [DecidableEq D] in
private theorem colPoly_congrTM (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ)
    {com com' : Compiled.Committed K D} {root : D} (h : com root = com' root)
    (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord; rw [h]

omit [Inhabited D] [DecidableEq D] in
private theorem rowVals_congrTM {com com' : Compiled.Committed K D}
    {active : Array Bool} {logDegrees : Array ℕ} {stage1 stage2 quot : D} (quot' : D)
    {β γ acc0 : K} {accs : Array K} (h1 : com stage1 = com' stage1)
    (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  funext pos ci x
  unfold rowVals pointRow
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
    funext fun j => colPoly_congrTM M _ _ h1 _ _ _ _
  have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
    funext fun j => colPoly_congrTM M _ _ h2 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
    funext j; unfold shardCols; dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congrTM M _ _ (h3 root hpc) _ _ _ _
  rw [hmain, hstage2, hpre]

omit [DecidableEq K] [Inhabited D] in
private theorem baseRows_comOf_appendTM (M : StarkModel F EF K) (sys : System F D)
    (v : ShardView F EF D K) (hm : 3 ≤ msgs.length) (m : IMsg F EF D K) {root : D}
    (hroot : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root ∨ root = v.stage2) :
    M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root := by
  refine baseRows_congrTM M ?_
  unfold comOf
  rw [comAt_append_of_ltTM (msgs := msgs) m (by omega),
    comAt_append_of_ltTM (msgs := msgs) m (by omega)]
  by_cases h1 : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root
  · rw [ite_eq_left h1, ite_eq_left h1]
  · have h2 : root = v.stage2 := by tauto
    rw [ite_eq_right h1, ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]

private theorem pcsMsgMulti_append {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) (m : IMsg F EF D K) {k : ℕ} (hk : 4 + k < msgs.length) :
    pcsMsgMulti (msgs ++ [m]) hs hcap k = pcsMsgMulti msgs hs hcap k := by
  rcases k with _ | k
  · simp only [pcsMsgMulti, valuesOf_appendTM (show 5 ≤ msgs.length by omega) m,
      comOf_appendTM sys v (show 4 ≤ msgs.length by omega) m]
  · simp only [pcsMsgMulti, rawAt_append_of_ltTM (msgs := msgs) m hk,
      comAt_append_of_ltTM (msgs := msgs) m hk]

private theorem pcsTTensorMulti_append {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width) :
    ∀ j, 4 + j ≤ msgs.length → 4 + j ≤ chals.length →
      pcsTTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap j = pcsTTensorMulti msgs chals hs hcap j
  | 0, _, _ => rfl
  | j + 1, hm, hc => by
    simp only [pcsTTensorMulti, pcsTTensorMulti_append hs hcap m c j (by omega) (by omega),
      pcsMsgMulti_append hs hcap m (show 4 + j < msgs.length by omega),
      tAnsAt_append_of_ltM (chals := chals) c (show 4 + j < chals.length by omega)]

private theorem pcsTTensorMulti_append_succ {v : ShardView F EF D K} (hs : Supported M sys θ v)
    (hcap : 0 < sys.fri.maxLogArity) (m : IMsg F EF D K) (c : UTensorAns K fslots slots width)
    {j : ℕ} (hm : msgs.length = 4 + j) (hc : chals.length = 4 + j) :
    pcsTTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap (j + 1) =
      (pcsTTensorMulti msgs chals hs hcap j).snoc (pcsMsgMulti (msgs ++ [m]) hs hcap j)
        (pcsChalTensorMulti (hs.paramsMulti hcap) (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
          (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys))) j c) := by
  have hans : tAnsAt (chals ++ [c]) (4 + j) = c := by
    have h := tAnsAt_append_lengthM (chals := chals) c; rwa [hc] at h
  simp only [pcsTTensorMulti, pcsTTensorMulti_append (msgs := msgs) (chals := chals) hs hcap m c j
    (by omega) (by omega), hans]

private theorem pcsDoomedTensorMulti_iff {v : ShardView F EF D K} {hs : Supported M sys θ v}
    {hcap : 0 < sys.fri.maxLogArity} {n : ℕ}
    (hn : min (msgs.length - 4) ((hs.paramsMulti hcap).rounds + 2) = n) :
    PcsDoomedTensorMulti msgs chals hs hcap ↔
      grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
        (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
          (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries) n
        (pcsTTensorMulti msgs chals hs hcap n) := by
  subst hn; rfl

private theorem shardDoomedTensorMulti_three {v : ShardView F EF D K} {hs : Supported M sys θ v}
    {hcap : 0 < sys.fri.maxLogArity} (hm : msgs.length = 3) :
    shardDoomedTensorMulti msgs chals hs hcap ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.AFail M sys θ (M.baseRows (comOf sys v msgs))) := by
  unfold shardDoomedTensorMulti
  exact ⟨fun h hcf => (h hcf).1 hm,
    fun h hcf => ⟨fun _ => h hcf, fun h4 => absurd h4 (by omega)⟩⟩

private theorem shardDoomedTensorMulti_four {v : ShardView F EF D K} {hs : Supported M sys θ v}
    {hcap : 0 < sys.fri.maxLogArity} (hm : msgs.length = 4) :
    shardDoomedTensorMulti msgs chals hs hcap ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) := by
  unfold shardDoomedTensorMulti
  exact ⟨fun h hcf => ((h hcf).2 (by omega)).1,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega),
      fun _ => ⟨h hcf, fun h5 => absurd h5 (by omega)⟩⟩⟩

private theorem shardDoomedTensorMulti_of_five_le {v : ShardView F EF D K}
    {hs : Supported M sys θ v} {hcap : 0 < sys.fri.maxLogArity} (hm : 5 ≤ msgs.length) :
    shardDoomedTensorMulti msgs chals hs hcap ↔
      (v.CFail M sys θ (M.baseRows (comOf sys v msgs)) →
        (v.ZFail M sys θ (M.baseRows (comOf sys v msgs)) ∧ v.Off M sys) ∧
          (v.Check M sys (valuesOf msgs) → PcsDoomedTensorMulti msgs chals hs hcap)) := by
  unfold shardDoomedTensorMulti
  exact ⟨fun h hcf => ⟨((h hcf).2 (by omega)).1, ((h hcf).2 (by omega)).2 hm⟩,
    fun h hcf => ⟨fun h3 => absurd h3 (by omega), fun _ => ⟨(h hcf).1, fun _ => (h hcf).2⟩⟩⟩

/-! ### Round-by-round soundness of `sdoomedTensorMulti` -/

private theorem fractionLE_beta_roundTM [Fintype K] (hfpos : 0 < fslots) (m : IMsg F EF D K) :
    FractionLE (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorMultiL M sys hcap V θ B [m] [c])
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

private theorem fractionLE_gamma_roundTM [Fintype K] (hfpos : 0 < fslots)
    (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals) (hm : msgs.length = 1)
    (hc : chals.length = 1) (m : IMsg F EF D K) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorMultiL M sys hcap V θ B (msgs ++ [m]) (chals ++ [c]))
      ((2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K) := by
  have h0 : (0 : ℝ) ≤ (2 * itemBound sys B * lenBound sys B : ℕ) / Fintype.card K := by positivity
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) _ :=
    FractionLE.false.mono_right h0
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_ltTM m (by omega)
  have hcom : comAt (msgs ++ [m]) 0 = comAt msgs 0 := comAt_append_of_ltTM m (by omega)
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
        have h := tFieldAt_append_lengthM (chals := chals) c; rwa [hc] at h
      refine ⟨?_, fun h => absurd h (by omega)⟩
      rw [hcom, tFieldAt_append_of_ltM (chals := chals) c (by omega), h1]
      exact fun _ => ⟨fun _ => hβ, fun _ => hne⟩
  · refine hnone.mono_left fun c hc' => hc' fun pre' hdec' hpre' => ?_
    rw [hraw, hdec] at hdec'; cases hdec'
    refine ⟨fun hb => ?_, fun h => absurd h (by omega)⟩
    rw [hcom] at hb
    exact absurd ⟨hpre', hb⟩ hgood

private theorem sdoomedTensorMultiL_append {pre : BatchPreamble F D}
    (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals) (hdec : V.dec0 (rawAt msgs 0) = some pre)
    (hpre : PreOk sys B pre) (hm : 2 ≤ msgs.length) (hc : 2 ≤ chals.length)
    (m : IMsg F EF D K) (c : UTensorAns K fslots slots width)
    (h : ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
      ∀ hs : Supported M sys θ (tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
        shardDoomedTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap) :
    sdoomedTensorMultiL M sys hcap V θ B (msgs ++ [m]) (chals ++ [c]) := by
  intro pre' hdec' _
  rw [rawAt_append_of_ltTM m (by omega), hdec] at hdec'
  cases hdec'
  refine ⟨?_, fun _ => h⟩
  rw [comAt_append_of_ltTM m (by omega),
    tFieldAt_append_of_ltM (chals := chals) c (by omega),
    tFieldAt_append_of_ltM (chals := chals) c (by omega)]
  exact fun hb => ⟨fun _ => ((hd _ hdec hpre).1 hb).1 (by omega),
    fun _ => ((hd _ hdec hpre).1 hb).2 hm⟩

private theorem fractionLE_of_shardTM [Fintype K] {ε : ℝ} (h0 : 0 ≤ ε)
    (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals) (hlen : chals.length = msgs.length)
    (hm : 2 ≤ msgs.length) (m : IMsg F EF D K)
    (h : ∀ pre, V.dec0 (rawAt msgs 0) = some pre → PreOk sys B pre →
      ∀ hdr, pre.headers[V.shard (rawAt (msgs ++ [m]) 2)]? = some hdr →
        FractionLE
          (fun c : UTensorAns K fslots slots width =>
            ¬ ∀ hs : Supported M sys θ (tViewOf M (msgs ++ [m]) (chals ++ [c]) hdr),
              shardDoomedTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap) ε) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorMultiL M sys hcap V θ B (msgs ++ [m]) (chals ++ [c])) ε := by
  have hraw : rawAt (msgs ++ [m]) 0 = rawAt msgs 0 := rawAt_append_of_ltTM m (by omega)
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
    refine sdoomedTensorMultiL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'; cases hh'
  · refine (h pre hdec hpre hdr hh).mono_left fun c hc hgood => hc ?_
    refine sdoomedTensorMultiL_append hd hdec hpre hm (by omega) m c fun hdr' hh' => ?_
    rw [hh] at hh'; cases hh'
    exact hgood

private theorem fractionLE_alpha_roundTM [Fintype K] (hfpos : 0 < fslots) {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size) (hm : msgs.length = 3) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ ∀ hs : Supported M sys θ { v with α := c.field },
          shardDoomedTensorMulti msgs (chals ++ [c]) hs hcap)
      ((constraintBound sys M.extData.d - 1 : ℕ) / Fintype.card K) := by
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  · refine (fractionLE_tensorField hfpos (fractionLE_alphaFail hact hCF)).mono_left
      fun c hc hAF => hc fun hs => ?_
    exact (shardDoomedTensorMulti_three hm).mpr fun _ => hAF
  · refine (FractionLE.false.mono_right (by positivity)).mono_left fun c hc => hc fun hs => ?_
    exact (shardDoomedTensorMulti_three hm).mpr fun hcf => absurd hcf hCF

private theorem fractionLE_zeta_roundTM [Fintype K] (hfpos : 0 < fslots)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F)) {v : ShardView F EF D K}
    (hact : v.hdr.active.size ≤ sys.circuits.size)
    (hdeg : ∀ pos, v.hdr.logDegrees.getD pos 0 ≤ sys.maxLogDegree) (hm : msgs.length = 3)
    (m : IMsg F EF D K) (q : D)
    (hd : ∀ hs : Supported M sys θ v, shardDoomedTensorMulti msgs chals hs hcap) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ ∀ hs : Supported M sys θ { v with quot := q, ζ := c.field },
          shardDoomedTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap)
      (((zetaBound sys + cosetBound sys : ℕ) : ℝ) / Fintype.card K) := by
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False)
      (((zetaBound sys + cosetBound sys : ℕ) : ℝ) / Fintype.card K) :=
    FractionLE.false.mono_right (by positivity)
  have hlen : (msgs ++ [m]).length = 4 := by rw [List.length_append, hm, List.length_singleton]
  have h1 := baseRows_comOf_appendTM M sys v (le_of_eq hm.symm) m (.inl rfl)
  have h2 := baseRows_comOf_appendTM M sys v (le_of_eq hm.symm) m (.inr (.inr rfl))
  have h3 : ∀ root, sys.preprocessedCommit = some root →
      M.baseRows (comOf sys v (msgs ++ [m])) root = M.baseRows (comOf sys v msgs) root :=
    fun root hroot => baseRows_comOf_appendTM M sys v (le_of_eq hm.symm) m (.inr (.inl hroot))
  by_cases hsup : Supported M sys θ v
  swap
  · exact hnone.mono_left fun c hc => hc fun hs =>
      absurd ⟨hs.two, hs.final, hs.margin, hs.active, hs.height⟩ hsup
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc => hc fun hs => ?_
    refine (shardDoomedTensorMulti_four hlen).mpr fun hcf => ?_
    have hcf' : v.CFail M sys θ (M.baseRows (comOf sys v msgs)) := by
      have hcf0 : ConstraintFail M sys θ (M.baseRows (comOf sys v (msgs ++ [m])))
          v.hdr.active v.hdr.logDegrees v.hdr.stage1Commit v.stage2 q
          v.β v.γ (M.ext.toModel v.acc0) (v.accs.map M.ext.toModel) := hcf
      unfold ShardView.CFail ConstraintFail
      unfold ConstraintFail at hcf0
      rwa [rowVals_congrTM (M := M) (sys := sys) (θ := θ) v.quot h1 h2 h3] at hcf0
    exact absurd hcf' hCF
  have hAF : AlphaFail M sys θ (M.baseRows (comOf sys v (msgs ++ [m]))) v.hdr.active
      v.hdr.logDegrees v.hdr.stage1Commit v.stage2 q v.β v.γ (M.ext.toModel v.acc0)
      (v.accs.map M.ext.toModel) v.α := by
    have h0 := (shardDoomedTensorMulti_three hm).mp (hd hsup) hCF
    unfold ShardView.AFail AlphaFail at h0
    unfold AlphaFail
    rwa [rowVals_congrTM (M := M) (sys := sys) (θ := θ) v.quot h1 h2 h3]
  refine ((fractionLE_tensorField hfpos ((fractionLE_zetaFail hact hdeg htwo hAF).or
    (fractionLE_offCosets hsup.active hsup.height hsup.two))).mono_left
    fun c hc => ?_).mono_right (le_of_eq ?_)
  · by_contra hno
    rw [not_or, not_not, not_not] at hno
    exact hc fun hs => (shardDoomedTensorMulti_four hlen).mpr fun _ => hno
  · rw [Nat.cast_add, add_div]

private theorem fractionLE_pcs_roundTM [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {v : ShardView F EF D K}
    (hs : Supported M sys θ v)
    (hpcs : RbrSound ((hs.paramsMulti hcap).rounds + 2)
      (grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
        (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
          (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries))
      fun _ => εpcs)
    (hm : 4 ≤ msgs.length) (hc : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : shardDoomedTensorMulti msgs chals hs hcap) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ shardDoomedTensorMulti (msgs ++ [m]) (chals ++ [c]) hs hcap) εpcs := by
  have hnone : FractionLE (fun _ : UTensorAns K fslots slots width => False) εpcs :=
    FractionLE.false.mono_right hεpcs
  have hlen : (msgs ++ [m]).length = msgs.length + 1 := by
    rw [List.length_append, List.length_singleton]
  have hcom : comOf sys v (msgs ++ [m]) = comOf sys v msgs := comOf_appendTM sys v hm m
  by_cases hCF : v.CFail M sys θ (M.baseRows (comOf sys v msgs))
  swap
  · refine hnone.mono_left fun c hc' => hc' fun hcf => ?_
    rw [hcom] at hcf; exact absurd hcf hCF
  obtain ⟨hZF, hP⟩ := (hd hCF).2 hm
  have hZF' : v.ZFail M sys θ (M.baseRows (comOf sys v (msgs ++ [m]))) ∧ v.Off M sys := by
    rw [hcom]; exact hZF
  by_cases hCk : v.Check M sys (valuesOf (msgs ++ [m]))
  swap
  · exact hnone.mono_left fun c hc' => hc' ((shardDoomedTensorMulti_of_five_le (by omega)).mpr
      fun _ => ⟨hZF', fun hck => absurd hck hCk⟩)
  rcases Nat.lt_or_ge (msgs.length - 4) ((hs.paramsMulti hcap).rounds + 2) with hj | hj
  · obtain ⟨j, hj'⟩ : ∃ j, msgs.length = 4 + j := ⟨msgs.length - 4, by omega⟩
    have hdoom : grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
        (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
          (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries) j
        (pcsTTensorMulti msgs chals hs hcap j) := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exact grindDoomed_nil (doomedTensorMulti_zero _ _ _ _ _ _)
      · have h5 : 5 ≤ msgs.length := by omega
        rw [valuesOf_appendTM h5 m] at hCk
        exact (pcsDoomedTensorMulti_iff (by omega)).mp (hP h5 hCk)
    have hbits : powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)) j ≤ width := by
      unfold powBitsMulti; split_ifs <;> omega
    have hfslots_v : tensorNumChallenges (maxWidth (v.shape M sys)) +
        tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) ≤ fslots :=
      (tensorNumChallenges_starkShape_le_fslotsBound sys M.extData.d hs.active.le
        v.hdr.logDegrees).trans hfslots
    have hfpos : 0 < fslots := lt_of_lt_of_le (pos_fslotsBound sys M.extData.d) hfslots
    have hbound := fractionLE_pcsChalTensorMulti (fslots := fslots) (slots := slots)
      (width := width) (hs.paramsMulti hcap) (maxWidth (v.shape M sys))
      (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
      (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys))) j hfslots_v hfpos hslots
      hbits (hs.two.trans hwidth)
      (hpcs j (by omega) (pcsTTensorMulti msgs chals hs hcap j)
        (pcsMsgMulti (msgs ++ [m]) hs hcap j) hdoom)
    refine hbound.mono_left fun c hc' hgd => hc' ?_
    refine (shardDoomedTensorMulti_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun _ => ?_⟩
    refine (pcsDoomedTensorMulti_iff (n := j + 1) (by omega)).mpr ?_
    rw [pcsTTensorMulti_append_succ hs hcap m c hj' (hc.trans hj')]
    exact hgd
  · have h5 : 5 ≤ msgs.length := by omega
    refine hnone.mono_left fun c hc' => hc' ?_
    refine (shardDoomedTensorMulti_of_five_le (by omega)).mpr fun _ => ⟨hZF', fun hck => ?_⟩
    rw [valuesOf_appendTM h5 m] at hck
    refine (pcsDoomedTensorMulti_iff (n := (hs.paramsMulti hcap).rounds + 2) (by omega)).mpr ?_
    rw [pcsTTensorMulti_append hs hcap m c ((hs.paramsMulti hcap).rounds + 2) (by omega) (by omega)]
    exact (pcsDoomedTensorMulti_iff (by omega)).mp (hP h5 hck)

private theorem fractionLE_sdoomedTensorMultiL [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound ((hs.paramsMulti hcap).rounds + 2)
        (grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
          (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
            (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries))
        fun _ => εpcs)
    (hlen : chals.length = msgs.length) (m : IMsg F EF D K)
    (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals) :
    FractionLE
      (fun c : UTensorAns K fslots slots width =>
        ¬ sdoomedTensorMultiL M sys hcap V θ B (msgs ++ [m]) (chals ++ [c]))
      (roundErr M sys B εpcs msgs.length) := by
  have hfpos : 0 < fslots := lt_of_lt_of_le (pos_fslotsBound sys M.extData.d) hfslots
  unfold roundErr
  split_ifs with h0 h1 h2 h3
  · obtain rfl : msgs = [] := List.length_eq_zero_iff.mp h0
    obtain rfl : chals = [] := List.length_eq_zero_iff.mp hlen
    exact fractionLE_beta_roundTM hfpos m
  · exact fractionLE_gamma_roundTM hfpos hd h1 (hlen.trans h1) m
  · refine fractionLE_of_shardTM (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_alpha_roundTM (hcap := hcap) (θ := θ) (msgs := msgs ++ [m]) (chals := chals)
      hfpos (v := tViewOf M (msgs ++ [m]) chals hdr) hok.active.le
      (by rw [List.length_append, h2, List.length_singleton])).mono_left
      fun c hc hgood => hc ?_
    rw [tViewOf_append_twoM hdr (hlen.trans h2) c]
    exact hgood
  · refine fractionLE_of_shardTM (by positivity) hd hlen (by omega) m
      fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_ltTM m (by omega)] at hh
    have hok := hpre.header hdr (Array.mem_of_getElem? hh)
    refine (fractionLE_zeta_roundTM (hcap := hcap) hfpos htwo (v := tViewOf M msgs chals hdr)
      hok.active.le hok.logDegree_le h3 m ((digestsIn m.1).getD 0 default)
      ((hd pre hdec hpre).2 (by omega) hdr hh)).mono_left fun c hc hgood => hc ?_
    rw [tViewOf_append_threeM hdr h3 (hlen.trans h3) m c]
    exact hgood
  · have h4 : 4 ≤ msgs.length := by omega
    refine fractionLE_of_shardTM hεpcs hd hlen (by omega) m fun pre hdec hpre hdr hh => ?_
    rw [rawAt_append_of_ltTM m (by omega)] at hh
    have hv := fun c : UTensorAns K fslots slots width =>
      tViewOf_appendM (M := M) (chals := chals) hdr h4 (by omega) m c
    by_cases hsup : Supported M sys θ (tViewOf M msgs chals hdr)
    · refine (fractionLE_pcs_roundTM (hcap := hcap) hεpcs hfslots hslots hcommit hquery hwidth
        hsup (hpcs _ hsup) h4 hlen m ((hd pre hdec hpre).2 (by omega) hdr hh hsup)).mono_left
        fun c hc hgood => hc ?_
      rw [hv c]
      exact fun _ => hgood
    · refine (FractionLE.false.mono_right hεpcs).mono_left fun c hc => hc ?_
      rw [hv c]
      exact fun hs => absurd hs hsup

variable (M sys hcap V θ B msgs chals)

/-- The empty multi-arity tensor STARK transcript is doomed. -/
theorem sdoomedTensorMulti_nil :
    sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
      M sys hcap V θ B 0 .nil :=
  fun _ _ _ => ⟨fun _ => ⟨fun h => (Nat.not_succ_le_zero _ h).elim,
    fun h => (Nat.not_succ_le_zero _ h).elim⟩, fun h => (Nat.not_succ_le_zero _ h).elim⟩

/-- **Round-by-round soundness of the multi-arity tensor-batched STARK.** -/
theorem rbrSound_sdoomedTensorMulti [Fintype K] {εpcs : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound ((hs.paramsMulti hcap).rounds + 2)
        (grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
          (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
            (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries))
        fun _ => εpcs)
    (r : ℕ) :
    RbrSound r (sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
        M sys hcap V θ B)
      (roundErr M sys B εpcs) := by
  intro i _ t m hd
  have h := fractionLE_sdoomedTensorMultiL (hcap := hcap) (V := V) (B := B) hεpcs htwo hfslots
    hslots hcommit hquery hwidth hpcs ((length_chalsOfTM t).trans t.length_msgs.symm) m hd
  rw [t.length_msgs] at h
  exact h

/-- **Unconditional unique-decoding round-by-round soundness of the multi-arity tensor-batched
STARK.** Requires zero proximity assumptions, matching the exact binary tensor error
`roundErr M sys B (pcsErrTensor sys d δ)` — directly instantiable by adaptive-ROM frameworks
such as `DynamicRom`. -/
theorem rbrSound_sdoomedTensorMulti_ud [Fintype K] {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) (r : ℕ) :
    RbrSound r (sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
        M sys hcap V (1 - δ) B)
      (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ)) :=
  rbrSound_sdoomedTensorMulti M sys hcap V (1 - δ) B (pcsErrTensor_nonneg sys M.extData.d hδ)
    htwo hfslots hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcsTensorMulti_ud M sys hcap hδ hrate v hs.active hs) r

variable {M sys hcap V θ B msgs chals}

/-- In a doomed multi-arity transcript of at least two rounds whose first message decodes
to a preamble within bounds, unbalanced lookup messages do not vanish at `(β, γ)`. -/
theorem balance_of_sdoomedTensorMultiL (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals)
    {pre : BatchPreamble F D} (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre)
    (hlen : 2 ≤ msgs.length)
    (hbal : ¬ Balanced (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)) :
    ((balPoly (allItems M sys θ (M.baseRows (comAt msgs 0)) pre)).eval
      (C (tFieldAt chals 0))).eval (tFieldAt chals 1) ≠ 0 :=
  ((hd pre hdec hpre).1 hbal).2 hlen

private theorem claimsOf_ungrind_pcsTTensorMulti {v : ShardView F EF D K}
    (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity) :
    ∀ j, claimsOf (ungrind (pcsTTensorMulti msgs chals hs hcap (j + 1))) =
      (pcsMsgMulti msgs hs hcap 0).claims
  | 0 => rfl
  | j + 1 => claimsOf_ungrind_pcsTTensorMulti hs hcap j

omit [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] in
private theorem map_commitment_openingClaimsTM (v : ShardView F EF D K)
    (proof : Proof F EF D Unit Unit) (ζ : EF) (h1 : proof.stage1Commit = v.hdr.stage1Commit)
    (h2 : proof.stage2Commit = v.stage2) (h3 : proof.quotientCommit = v.quot) :
    (openingClaims sys proof ζ).map (·.commitment) = v.commitments sys := by
  unfold openingClaims ShardView.commitments
  rw [h1, h2, h3]
  cases sys.preprocessedCommit <;> simp

private theorem claimsFailMulti_pcsMsgMulti (hfixed : sys.FixedOk) {v : ShardView F EF D K}
    (hs : Supported M sys θ v) (hcap : 0 < sys.fri.maxLogArity)
    (hcheck : v.Check M sys (valuesOf msgs))
    (hZF : v.ZFail M sys θ (M.baseRows (comOf sys v msgs))) (hoff : v.Off M sys) :
    ClaimsFailMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift θ
      (pcsMsgMulti msgs hs hcap 0).claims := by
  obtain ⟨proof, hact, hst1, hst2, hq, haccs, hlog, hshape, hvals, hcons, hzeta⟩ := hcheck
  have hrep : ∀ x : K, M.ext.toModel (rep M x) = x := fun x => Function.surjInv_eq M.surj x
  have heq : starkShape sys M.extData.d proof.active proof.logDegrees = v.shape M sys := by
    unfold ShardView.shape; rw [hact, hlog]
  have hact_ne : ¬ (activeIndices proof.active).isEmpty := by
    have h := hshape
    simp only [Stark.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact Bool.eq_false_iff.mp h.1.1.1.1.1.1.1.1.1.2
  have hfl_ne : (v.shape M sys).flatten ≠ [] := by
    rw [← heq]
    exact starkShape_flatten_ne_nil sys M.extData.d hact_ne proof.logDegrees
  have hvalid : scheduleValid sys.fri (v.shape M sys)
      (scheduleOfShape sys.fri (v.shape M sys)) = true :=
    scheduleValid_scheduleOfShape hcap hfl_ne hs.final
  have hbin : ClaimsFail hs.params.ldt hs.params.shift θ
      (hs.params.claims (view M.toFieldModel sys.fri (v.shape M sys)
        (firstMessage (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ))
          (valuesOf msgs)))
        (M.baseRows (comOf sys v msgs))) := by
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
        ClaimsFail hs.params.ldt hs.params.shift θ
          (hs.params.claims (view M.toFieldModel sys.fri (v.shape M sys)
            (firstMessage (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ))
              (valuesOf msgs)))
            (M.baseRows (comOf sys v msgs))) := by
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
    rw [map_commitment_openingClaimsTM v proof _ hst1 hst2 hq,
      claimPoints_openingClaims sys proof hshape, ← M.degree_eq, hvals] at hcf
    exact key _ (by rw [heq]; exact hs.two) heq hcf
  exact claimsFailMulti_of_claimsFail M.toFieldModel sys.fri (v.shape M sys)
    (scheduleOfShape sys.fri (v.shape M sys)) (M.wellFormed sys.fri _ hs.two) hvalid _ _
    (scheduleOfShape_pos hcap) (scheduleOfShape_sum_le hcap) hbin

/-- **An accepted multi-arity tensor STARK transcript that is doomed has no failing constraint.** -/
theorem good_of_sdoomedTensorMultiL (hfixed : sys.FixedOk)
    (hd : sdoomedTensorMultiL M sys hcap V θ B msgs chals)
    {pre : BatchPreamble F D} (hdec : V.dec0 (rawAt msgs 0) = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D} (hhdr : pre.headers[V.shard (rawAt msgs 2)]? = some hdr)
    (hs : Supported M sys θ (tViewOf M msgs chals hdr))
    (hlen : msgs.length = 4 + ((hs.paramsMulti hcap).rounds + 2))
    (hcheck : (tViewOf M msgs chals hdr).Check M sys (valuesOf msgs))
    (hpow : PowPasses (pcsTTensorMulti msgs chals hs hcap ((hs.paramsMulti hcap).rounds + 2)))
    (hacc : AcceptsTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
      (starkTensorCoordMulti M sys hs hcap)
      (ungrind (pcsTTensorMulti msgs chals hs hcap ((hs.paramsMulti hcap).rounds + 2)))) :
    ¬ (tViewOf M msgs chals hdr).CFail M sys θ
      (M.baseRows (comOf sys (tViewOf M msgs chals hdr) msgs)) := by
  intro hCF
  obtain ⟨hZF, hP⟩ := ((hd pre hdec hpre).2 (by omega) hdr hhdr hs hCF).2 (by omega)
  have hgd := (pcsDoomedTensorMulti_iff (n := (hs.paramsMulti hcap).rounds + 2) (by omega)).mp
    (hP (by omega) hcheck)
  have hfail : ClaimsFailMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift θ
      (claimsOf (ungrind (pcsTTensorMulti msgs chals hs hcap
        ((hs.paramsMulti hcap).rounds + 2)))) := by
    rw [claimsOf_ungrind_pcsTTensorMulti hs hcap ((hs.paramsMulti hcap).rounds + 1)]
    exact claimsFailMulti_pcsMsgMulti hfixed hs hcap hcheck hZF.1 hZF.2
  exact not_grindDoomedTensorMulti_of_accepts _ hpow hfail hacc hgd

end StateTensorMulti

/-! ## 5. Good logs for the multi-arity tensor STARK experiment -/

section GoodLogMulti

variable [DecidableEq F] [DecidableEq EF] {fslots slots width : ℕ}
  (M : StarkModel F EF K) (sys : System F D) (hcap : 0 < sys.fri.maxLogArity)
  (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ)

/-- A log without luck for the multi-arity tensor-batched STARK: no challenge entry flips
`sdoomedTensorMulti`, and no hash entry hits a digest in play. -/
def GoodLogTensorMulti (l : Log (STAns F EF D K fslots slots width)) : Prop :=
  ¬ HasBad (InterpFlips r (sdoomedTensorMulti M sys hcap V θ B) (interpTensor B r)) l ∧
    ¬ HasBad (Hit (fun _ => digestsOf B) r) l

variable {M sys hcap V θ B r}

/-- In a good log, every answered chain of at most `r` rounds is doomed. -/
theorem sdoomedTensorMulti_of_goodLogTensorMulti {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensorMulti M sys hcap V θ B r l) {i : ℕ}
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) i) (hi : i ≤ r)
    (hs : Supports l t) :
    sdoomedTensorMulti M sys hcap V θ B i (t.mapIdx (interpTensor B r l)) :=
  doomed_mapIdx_of_supports (settles_interpTensor B r) hgood.1 hgood.2
    (sdoomedTensorMulti_nil M sys hcap V θ B) t hi hs

/-- **Probability of a bad log in the multi-arity tensor-batched STARK experiment.** -/
theorem prob_not_goodLogTensorMulti_le [Fintype K] [Fintype D] {εpcs εmax : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound ((hs.paramsMulti hcap).rounds + 2)
        (grindDoomed (powBitsMulti sys.fri (scheduleOfShape sys.fri (v.shape M sys)))
          (PcsRbr.doomedTensorMulti (hs.paramsMulti hcap).ldt (hs.paramsMulti hcap).shift
            (starkTensorCoordMulti M sys hs hcap) θ (hs.paramsMulti hcap).queries))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {α : Type}
    {c : OracleComp (STAns F EF D K fslots slots width) α} {N : ℕ} (hc : c.QueryBound N) :
    prob (fun _ l => ¬ GoodLogTensorMulti M sys hcap V θ B r l) c []
      ≤ N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * Fintype.card D) := by
  have hflip := prob_hasBad_interpFlips_le (interp := interpTensor B r)
    (rbrSound_sdoomedTensorMulti M sys hcap V θ B hεpcs htwo hfslots hslots hcommit hquery hwidth
      hpcs r)
    (fun i _ => hε i) h0 hc
  have hhit_pot := prob_hasBad_hit_le_potential
    (digestsOf := fun _ => digestsOf (F := F) (EF := EF) B) (r := r)
    (M := (B.shards + 1) * r) (fun x => by
      unfold chalDigests
      refine (MerkleRO.length_flatMap_zipIdx_le (fun _ => digestsOf B) (fun _ => B.shards + 1)
        (fun _ m => by unfold digestsOf; exact List.length_take_le _ _) _ 0).trans ?_
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (List.length_take_le _ _)) hc
  have hhit : prob (fun _ l => HasBad (Hit (fun _ => digestsOf B) r) l) c []
      ≤ (((B.shards + 1) * r + 3 : ℝ) * N * (N - 1)) / (2 * Fintype.card D) := by
    refine hhit_pot.trans ?_
    have hle := MerkleRO.hitPotential_zero_le_choose ((B.shards + 1) * r) N
    have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hdiv := div_le_div_of_nonneg_right hle hD
    push_cast at hdiv
    simpa only [div_div, mul_comm (2 : ℝ)] using hdiv
  refine le_trans (prob_le_add_of_outcome fun _ l _ hbad => ?_) (add_le_add hflip hhit)
  by_contra hno
  exact hbad ⟨fun h => hno (.inl h), fun h => hno (.inr h)⟩

end GoodLogMulti

end CertiFri.Exec.Stark
