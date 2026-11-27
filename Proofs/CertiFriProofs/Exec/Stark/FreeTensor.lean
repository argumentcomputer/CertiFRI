import CertiFriProofs.Exec.Transcript
import CertiFriProofs.Theory.Stark.UniformTensor

/-!
# Idealised challenger with multi-slot uniform answers for tensor-batched STARKs

Tensor-batched counterpart of `Exec/Stark/Free.lean`. Uses `UTensorAns K fslots slots width`
so that round `4` (tensor FRI batching) can draw `kCol + kOpen` independent field challenges
(`TensorSchedule.sample`) within one Fiat–Shamir round, while all other rounds draw at most
one field challenge (`fieldAt 0 = field`), and folding/query rounds draw independent PoW bits
and query indices (`bits`).

## Contents

* `UTensorChal K fslots slots width`: constant challenge family `fun _ => UTensorAns ...`.
* `UStateTensor`, `uChallengerTensor`: idealised challenger over `UTensorChal`.
* `UAtTensor`: invariant tracking closed rounds, current round absorptions, squeeze state,
  field-sample counter `nfields`, and bit-sample counter `nbits`.
* `sampleExtMany_ufreeTensor`, `tensorSchedule_ufreeTensor`, `commitPhase_ufreeTensor`,
  `transcriptTailTensor_ufreeTensor`: exact characterization of `Fri.transcriptTailTensor`
  when run on `uChallengerTensor`.
-/

namespace CertiFri.Exec.Stark

open Oracle Fri CertiFri.Stark
open CertiFri.Exec.Transcript (answer)

/-- The challenge types of the tensor-batched STARK experiment: the same
multi-slot uniform answer in every round. -/
abbrev UTensorChal (K : Type) (fslots slots width : ℕ) : ℕ → Type :=
  fun _ => UTensorAns K fslots slots width

/-- The state of the idealised tensor STARK challenger: closed rounds, their raw
messages, current round absorptions, whether the current round has been squeezed,
and the counts of field and bit samples drawn in the current round. -/
structure UStateTensor (F EF D : Type) where
  round : ℕ
  hist : ℕ → RawMsg F EF D
  cur : RawMsg F EF D
  squeezed : Bool
  nfields : ℕ
  nbits : ℕ

/-- Initial state before anything is absorbed. -/
def UStateTensor.init {F EF D : Type} : UStateTensor F EF D :=
  ⟨0, fun _ => [], [], false, 0, 0⟩

section FreeTensor

variable {F EF D K : Type} {fslots slots width : ℕ}
  (f : ∀ x : FSQuery (RawMsg F EF D) (UTensorChal K fslots slots width) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (UTensorChal K fslots slots width) K D x)

/-- Oracle answer for the current round of a state. -/
def uAnswerTensor (s : UStateTensor F EF D) : UTensorAns K fslots slots width :=
  f (.chal (fsTranscript f s.hist s.round) s.cur)

variable [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]

/-- **Idealised challenger with multi-slot uniform answers for tensor-batched STARKs.** -/
noncomputable def uChallengerTensor (m : FieldModel F EF K) :
    Challenger (UStateTensor F EF D) F EF D where
  observe s o :=
    if s.squeezed then ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], false, 0, 0⟩
    else { s with cur := s.cur ++ [o] }
  sampleExt s :=
    (Function.surjInv m.surj ((uAnswerTensor f s).fieldAt s.nfields),
      { s with squeezed := true, nfields := s.nfields + 1 })
  sampleBits s b :=
    ((uAnswerTensor f s).bits s.nbits b,
      { s with squeezed := true, nbits := s.nbits + 1 })

variable {ms : ℕ → RawMsg F EF D}

/-- Invariant describing the state of `uChallengerTensor` at round `i` of chain `ms`. -/
structure UAtTensor (ms : ℕ → RawMsg F EF D) (s : UStateTensor F EF D) (i : ℕ)
    (cur : RawMsg F EF D) (squeezed : Bool) (nfields nbits : ℕ) : Prop where
  round : s.round = i
  hist : ∀ j < i, s.hist j = ms j
  cur : s.cur = cur
  squeezed : s.squeezed = squeezed
  nfields : s.nfields = nfields
  nbits : s.nbits = nbits

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K] in
theorem UAtTensor.init : UAtTensor ms (UStateTensor.init : UStateTensor F EF D) 0 [] false 0 0 :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl, rfl⟩

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K] in
private theorem uAnswerTensor_mk {i : ℕ} {hist : ℕ → RawMsg F EF D} (hh : ∀ j < i, hist j = ms j)
    (sq : Bool) (nf nb : ℕ) :
    uAnswerTensor f ⟨i, hist, ms i, sq, nf, nb⟩ = answer f ms i := by
  unfold uAnswerTensor answer
  rw [Transcript.fsTranscript_congr f hh]

variable (m : FieldModel F EF K)

theorem UAtTensor.observe {s : UStateTensor F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAtTensor ms s i cur false 0 0) (o : Observation F EF D) :
    UAtTensor ms ((uChallengerTensor f m).observe s o) i (cur ++ [o]) false 0 0 := by
  have hs : (uChallengerTensor f m).observe s o = { s with cur := s.cur ++ [o] } :=
    ite_eq_right (by rw [h.squeezed]; exact Bool.false_ne_true)
  rw [hs]
  exact ⟨h.round, h.hist, by rw [← h.cur], h.squeezed, h.nfields, h.nbits⟩

theorem UAtTensor.observeAll {s : UStateTensor F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAtTensor ms s i cur false 0 0) (l : List (Observation F EF D)) :
    UAtTensor ms ((uChallengerTensor f m).observeAll s l) i (cur ++ l) false 0 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have h' := ih (h.observe f m o)
    rwa [List.append_assoc] at h'

theorem UAtTensor.observe_next {s : UStateTensor F EF D} {i nf nb : ℕ}
    (h : UAtTensor ms s i (ms i) true nf nb) (o : Observation F EF D) :
    UAtTensor ms ((uChallengerTensor f m).observe s o) (i + 1) [o] false 0 0 := by
  have hs : (uChallengerTensor f m).observe s o =
      ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], false, 0, 0⟩ :=
    ite_eq_left h.squeezed
  rw [hs]
  refine ⟨by rw [← h.round], fun j hj => ?_, rfl, rfl, rfl, rfl⟩
  show Function.update s.hist s.round s.cur j = ms j
  rw [h.round, h.cur]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [Function.update_of_ne hj.ne]
    exact h.hist j hj
  · rw [Function.update_self]

theorem UAtTensor.observeAll_next {s : UStateTensor F EF D} {i nf nb : ℕ}
    (h : UAtTensor ms s i (ms i) true nf nb) {l : List (Observation F EF D)} (hl : l ≠ []) :
    UAtTensor ms ((uChallengerTensor f m).observeAll s l) (i + 1) l false 0 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l => exact (h.observe_next f m o).observeAll f m l

theorem UAtTensor.sampleExt {s : UStateTensor F EF D} {i nf nb : ℕ} {sq : Bool}
    (h : UAtTensor ms s i (ms i) sq nf nb) :
    ((uChallengerTensor f m).sampleExt s).1 =
        Function.surjInv m.surj ((answer f ms i).fieldAt nf) ∧
      UAtTensor ms ((uChallengerTensor f m).sampleExt s).2 i (ms i) true (nf + 1) nb := by
  obtain ⟨r, hist, cur, sq', nf', nb'⟩ := s
  obtain ⟨hr, hh, hc, hsq, hnf, hnb⟩ := h
  dsimp only at hr hh hc hsq hnf hnb
  subst hr hc hsq hnf hnb
  refine ⟨?_, rfl, hh, rfl, rfl, rfl, rfl⟩
  show Function.surjInv m.surj ((uAnswerTensor f ⟨r, hist, ms r, sq', nf', nb'⟩).fieldAt nf') = _
  rw [uAnswerTensor_mk f hh]

theorem UAtTensor.sampleExt_zero {s : UStateTensor F EF D} {i nb : ℕ} {sq : Bool}
    (h : UAtTensor ms s i (ms i) sq 0 nb) :
    ((uChallengerTensor f m).sampleExt s).1 =
        Function.surjInv m.surj (answer f ms i).field ∧
      UAtTensor ms ((uChallengerTensor f m).sampleExt s).2 i (ms i) true 1 nb :=
  h.sampleExt f m

theorem UAtTensor.sampleBits {s : UStateTensor F EF D} {i nf nb : ℕ} {sq : Bool}
    (h : UAtTensor ms s i (ms i) sq nf nb) (b : ℕ) :
    ((uChallengerTensor f m).sampleBits s b).1 = (answer f ms i).bits nb b ∧
      UAtTensor ms ((uChallengerTensor f m).sampleBits s b).2 i (ms i) true nf (nb + 1) := by
  obtain ⟨r, hist, cur, sq', nf', nb'⟩ := s
  obtain ⟨hr, hh, hc, hsq, hnf, hnb⟩ := h
  dsimp only at hr hh hc hsq hnf hnb
  subst hr hc hsq hnf hnb
  refine ⟨?_, rfl, hh, rfl, rfl, rfl, rfl⟩
  show (uAnswerTensor f ⟨r, hist, ms r, sq', nf', nb'⟩).bits nb' b = _
  rw [uAnswerTensor_mk f hh]

theorem UAtTensor.checkWitness {s : UStateTensor F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAtTensor ms s i cur false 0 0) (b : ℕ) (w : F)
    (hms : ms i = cur ++ if b = 0 then [] else [.base w]) :
    (((uChallengerTensor f m).checkWitness s b w).1 = true → b ≠ 0 →
        (answer f ms i).bits 0 b = 0) ∧
      UAtTensor ms ((uChallengerTensor f m).checkWitness s b w).2 i (ms i)
        (decide (b ≠ 0)) 0 (if b = 0 then 0 else 1) := by
  by_cases hb : b = 0
  · rw [ite_eq_left hb, List.append_nil] at hms
    rw [Challenger.checkWitness, ite_eq_left hb, ite_eq_left hb, hms,
      decide_eq_false (not_not.mpr hb)]
    exact ⟨fun _ hb' => absurd hb hb', h⟩
  · rw [ite_eq_right hb] at hms
    have h' := h.observe f m (.base w)
    rw [← hms] at h'
    obtain ⟨hv, hs⟩ := h'.sampleBits f m b
    rw [Challenger.checkWitness, ite_eq_right hb, ite_eq_right hb, decide_eq_true hb]
    refine ⟨fun hz _ => ?_, hs⟩
    rw [← hv]
    exact eq_of_beq hz

theorem UAtTensor.sampleIndices {s : UStateTensor F EF D} {i nf nb : ℕ} {sq : Bool}
    (h : UAtTensor ms s i (ms i) sq nf nb) (b count : ℕ) :
    (uChallengerTensor f m).sampleIndices b count s =
      (List.range count).map fun t => (answer f ms i).bits (nb + t) b := by
  induction count generalizing s nb sq with
  | zero => rfl
  | succ count ih =>
    obtain ⟨hv, hs⟩ := h.sampleBits f m b
    rw [Challenger.sampleIndices, hv, ih hs, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun t _ => ?_)
    rw [Function.comp_apply, Nat.add_right_comm, Nat.add_assoc]

/-- Sampling `cnt` field challenges in round `i` starting at slot `nf` returns
`fieldAt (nf + 0), …, fieldAt (nf + cnt - 1)` and advances `nfields` to `nf + cnt`. -/
theorem UAtTensor.sampleExtMany {s : UStateTensor F EF D} {i nf nb : ℕ} {sq : Bool}
    (h : UAtTensor ms s i (ms i) sq nf nb) (cnt : ℕ) :
    (sampleExtMany (uChallengerTensor f m) cnt s).1 =
        (List.range cnt).map (fun k => Function.surjInv m.surj ((answer f ms i).fieldAt (nf + k))) ∧
      UAtTensor ms (sampleExtMany (uChallengerTensor f m) cnt s).2 i (ms i)
        (sq || decide (0 < cnt)) (nf + cnt) nb := by
  induction cnt generalizing s nf sq with
  | zero =>
    exact ⟨rfl, by simpa [Fri.sampleExtMany] using h⟩
  | succ cnt ih =>
    obtain ⟨h1, hs1⟩ := h.sampleExt f m
    obtain ⟨hrest, hs2⟩ := ih hs1
    refine ⟨?_, ?_⟩
    · change ((uChallengerTensor f m).sampleExt s).1 ::
          (Fri.sampleExtMany (uChallengerTensor f m) cnt ((uChallengerTensor f m).sampleExt s).2).1 = _
      rw [h1, hrest, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ _ rfl (List.map_congr_left fun k _ => ?_)
      simp [Function.comp_apply, Nat.add_assoc, Nat.add_comm 1 k]
    · change UAtTensor ms
          (Fri.sampleExtMany (uChallengerTensor f m) cnt ((uChallengerTensor f m).sampleExt s).2).2
          i (ms i) (sq || decide (0 < cnt + 1)) (nf + (cnt + 1)) nb
      rw [show (sq || decide (0 < cnt + 1)) = (true || decide (0 < cnt)) by simp,
        show nf + (cnt + 1) = nf + 1 + cnt by omega]
      exact hs2

/-- Sampling a `TensorSchedule` in round `i₀` (with `0 < tensorNumChallenges W + tensorNumChallenges M`)
draws the `kCol` column challenges from slots `0 .. kCol - 1` and the `kOpen` opening-group
challenges from slots `kCol .. kCol + kOpen - 1`, leaving the challenger squeezed. -/
theorem tensorSchedule_ufreeTensor (W M i₀ : ℕ)
    (hpos : 0 < tensorNumChallenges W + tensorNumChallenges M)
    {s : UStateTensor F EF D} (h : UAtTensor ms s i₀ (ms i₀) false 0 0) :
    let res := TensorSchedule.sample (uChallengerTensor f m) s W M
    res.1.colChallenges =
        ((List.range (tensorNumChallenges W)).map fun k =>
          Function.surjInv m.surj ((answer f ms i₀).fieldAt k)).toArray ∧
      res.1.openChallenges =
        ((List.range (tensorNumChallenges M)).map fun k =>
          Function.surjInv m.surj ((answer f ms i₀).fieldAt (tensorNumChallenges W + k))).toArray ∧
      res.1.colWeights = tensorWeights res.1.colChallenges W ∧
      res.1.openWeights = tensorWeights res.1.openChallenges M ∧
      UAtTensor ms res.2 i₀ (ms i₀) true (tensorNumChallenges W + tensorNumChallenges M) 0 := by
  dsimp only [TensorSchedule.sample]
  obtain ⟨hcol, hs1⟩ := h.sampleExtMany f m (tensorNumChallenges W)
  simp only [Nat.zero_add, Bool.false_or] at hcol hs1
  obtain ⟨hopen, hs2⟩ := hs1.sampleExtMany f m (tensorNumChallenges M)
  have hsq : (decide (0 < tensorNumChallenges W) || decide (0 < tensorNumChallenges M)) = true := by
    by_cases hw : 0 < tensorNumChallenges W
    · simp [hw]
    · have hm : 0 < tensorNumChallenges M := by omega
      simp [hm]
  rw [hsq] at hs2
  exact ⟨congrArg List.toArray hcol, congrArg List.toArray hopen, rfl, rfl, hs2⟩

/-- The commit phase with `uChallengerTensor`. -/
theorem commitPhase_ufreeTensor [Inhabited D] (cpb : ℕ) (commits : Array D) (witnesses : Array F)
    (r i₀ : ℕ)
    (hms : ∀ i < r, ms (i₀ + 1 + i) = .digest (commits.getD i default) ::
      (if cpb = 0 then [] else [.base (witnesses.getD i 0)]))
    {s : UStateTensor F EF D} {nf nb : ℕ} (h : UAtTensor ms s i₀ (ms i₀) true nf nb) :
    (commitPhase (uChallengerTensor f m) cpb commits witnesses r s).1 =
        ((List.range r).map fun i =>
          Function.surjInv m.surj (answer f ms (i₀ + 1 + i)).field).toArray ∧
      ((commitPhase (uChallengerTensor f m) cpb commits witnesses r s).2.1 = true → cpb ≠ 0 →
        ∀ i < r, (answer f ms (i₀ + 1 + i)).bits 0 cpb = 0) ∧
      ∃ nf' nb', UAtTensor ms (commitPhase (uChallengerTensor f m) cpb commits witnesses r s).2.2
        (i₀ + r) (ms (i₀ + r)) true nf' nb' := by
  induction r with
  | zero => exact ⟨rfl, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _), nf, nb, h⟩
  | succ r ih =>
    obtain ⟨hβ, hpow, nf', nb', hs⟩ := ih fun i hi => hms i (Nat.lt_succ_of_lt hi)
    have e : i₀ + r + 1 = i₀ + 1 + r := Nat.add_right_comm i₀ r 1
    have h1 := hs.observe_next f m (.digest (commits.getD r default))
    rw [e] at h1
    obtain ⟨hw, h2⟩ := h1.checkWitness f m cpb (witnesses.getD r 0)
      (hms r (Nat.lt_succ_self r))
    obtain ⟨hv, h3⟩ := h2.sampleExt_zero f m
    rw [← e] at h3
    refine ⟨?_, fun hok hc i hi => ?_, _, _, h3⟩
    · rw [commitPhase, hβ, hv, List.push_toArray, List.range_succ, List.map_append,
        List.map_singleton]
    · rw [commitPhase] at hok
      obtain ⟨hok₁, hok₂⟩ := Bool.and_eq_true_iff.mp hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hpow hok₁ hc i hi
      · exact hw hok₂ hc

/-- **The challenges of `Fri.transcriptTailTensor` with `uChallengerTensor`.** -/
theorem transcriptTailTensor_ufreeTensor [Inhabited D] (params : FriParams) (shape : ClaimShape)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) (i₀ : ℕ)
    {s : UStateTensor F EF D} (h : UAtTensor ms s i₀ (ms i₀) false 0 0)
    (hpos : 0 < tensorNumChallenges (maxWidth shape) +
      tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape))
    (hmC : ∀ i < numRounds params shape,
      ms (i₀ + 1 + i) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]))
    (hmF : ms (i₀ + 1 + numRounds params shape) =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]))
    (hfinal : proof.finalPoly.size ≠ 0) :
    let ch := transcriptTailTensor (uChallengerTensor f m) s params shape proof
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
        ((List.range (numRounds params shape)).map fun i =>
          Function.surjInv m.surj (answer f ms (i₀ + 1 + i)).field).toArray ∧
      (ch.powOk = true →
        (params.commitPowBits ≠ 0 → ∀ i < numRounds params shape,
          (answer f ms (i₀ + 1 + i)).bits 0 params.commitPowBits = 0) ∧
        (params.queryPowBits ≠ 0 →
          (answer f ms (i₀ + 1 + numRounds params shape)).bits 0 params.queryPowBits = 0)) ∧
      ch.indices =
        ((List.range params.numQueries).map fun t =>
          (answer f ms (i₀ + 1 + numRounds params shape)).bits
            (t + if params.queryPowBits = 0 then 0 else 1)
            (logMaxHeight params.logBlowup shape)).toArray := by
  have e : i₀ + numRounds params shape + 1 = i₀ + 1 + numRounds params shape :=
    Nat.add_right_comm i₀ (numRounds params shape) 1
  have hne : finalMessage (F := F) (D := D) (numRounds params shape) proof.finalPoly ≠ [] := by
    intro h0
    have hlen := congrArg List.length h0
    simp only [finalMessage, List.length_append, List.length_map, Array.length_toList,
      List.length_replicate, List.length_nil] at hlen
    omega
  obtain ⟨hcol, hopen, hcolW, hopenW, h1⟩ :=
    tensorSchedule_ufreeTensor f m (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      i₀ hpos h
  obtain ⟨hβ, hpowC, nf, nb, h2⟩ := commitPhase_ufreeTensor f m params.commitPowBits
    proof.commitPhaseCommits proof.commitPowWitnesses (numRounds params shape) i₀ hmC h1
  have h3 := h2.observeAll_next f m hne
  rw [e] at h3
  obtain ⟨hpowQ, h4⟩ := h3.checkWitness f m params.queryPowBits proof.queryPowWitness hmF
  have hidx := h4.sampleIndices f m (logMaxHeight params.logBlowup shape) params.numQueries
  refine ⟨hcol, hopen, hcolW, hopenW, hβ, fun hpow => ?_, ?_⟩
  · obtain ⟨hpow₁, hpow₂⟩ := Bool.and_eq_true_iff.mp hpow
    exact ⟨hpowC hpow₁, hpowQ hpow₂⟩
  · exact congrArg List.toArray
      (hidx.trans (List.map_congr_left fun t _ => by rw [Nat.add_comm _ t]))

end FreeTensor

end CertiFri.Exec.Stark
