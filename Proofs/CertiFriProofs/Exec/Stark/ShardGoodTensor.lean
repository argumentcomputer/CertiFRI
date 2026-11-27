import CertiFriProofs.Exec.Stark.ChainTensor

/-!
# An accepted tensor-batched STARK proof in a good log has no failing constraint

Tensor-batched counterpart of `Exec/Stark/ShardGood.lean`. Proves:
* `shard_goodTensor_of_derive_verify`: deterministic soundness for one tensor-batched
  shard given any `Outcome` of `deriveA` and a subsequent `Outcome` of
  `Compiled.Params.verifyWithTensor` in a prefix-extending log (used directly by both
  unpruned `shard_goodTensor` and pruned MMCS `PrunedTensor.lean`).
* `shard_goodTensor`: specialized to unpruned `shardCompTensor`.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle OracleComp Polynomial
open CertiFri.Exec.Transcript (answer)
open CertiFri.PcsRbr (TensorChal ChalTensor GrindChal tensorOf betasOfTensor queriesOfTensor
  claimsOf wordsOf AcceptsTensor PowPasses ungrind)

/-! ## Transcripts given by their messages and challenges -/

section BuildTensor

variable {Msg Msg' : Type} {C : ℕ → Type}

private def mkTT (m : ℕ → Msg) (c : ∀ j, C j) : (i : ℕ) → Transcript Msg C i
  | 0 => .nil
  | i + 1 => (mkTT m c i).snoc (m i) (c i)

private theorem msgs_mkTT (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkTT m c i).msgs = (List.range i).map m := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkTT, Transcript.msgs_snoc, ih, List.range_succ, List.map_append, List.map_singleton]

private theorem mapIdx_mkTT (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkTT m c i).mapIdx g = mkTT (fun j => g j (m j)) c i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [mkTT, Transcript.mapIdx_snoc, ih, mkTT]

private theorem msgAt_mkTT (m : ℕ → Msg) (c : ∀ j, C j) (i j : ℕ) :
    Compiled.msgAt (mkTT m c (i + 1)) j = m (min j i) := by
  rw [mkTT, Compiled.msgAt, msgs_mkTT, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge j i with h | h
  · rw [List.getElem?_range h, min_eq_left h.le]; rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h), min_eq_right h]; rfl

private theorem getElem?_msgs_mapIdx_mkTT (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j)
    {i j : ℕ} (hj : j < i) : ((mkTT m c i).mapIdx g).msgs[j]? = some (g j (m j)) := by
  rw [mapIdx_mkTT, msgs_mkTT, List.getElem?_map, List.getElem?_range hj]; rfl

private theorem mentions_of_supports_mkTT {X' : Type} {Y' : X' → Type}
    [DecidableEq (FSQuery Msg C X')] {l : Log (FSAnswer (Msg := Msg) C Y')} {m : ℕ → Msg}
    {c : ∀ j, C j} : ∀ {i : ℕ}, Supports l (mkTT m c i) → ∀ j < i, Mentions l j (m j)
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i + 1, h, j, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact mentions_of_supports_mkTT h.1 j hlt
    · refine ⟨_, List.of_mem_dlookup h.2, ?_⟩
      have hlast := List.getElem?_concat_length (l := (mkTT m c j).msgs) (a := m j)
      rwa [Transcript.length_msgs] at hlast

private theorem fsTranscript_eq_mkTT {X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg C X', FSAnswer C Y' x) (ms : ℕ → Msg) (i : ℕ) :
    fsTranscript f ms i = mkTT ms (answer f ms) i := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun t => t.snoc (ms i) (answer f ms i)) ih

private theorem chalsOf_mkTT {U : Type} (m : ℕ → Msg) (c : ℕ → U) (i : ℕ) :
    chalsOf (mkTT (C := fun _ => U) m c i) = (List.range i).map c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkTT, chalsOf, ih, List.range_succ, List.map_append, List.map_singleton]

variable {K : Type} [Field K] {nc : ℕ → ℕ} {S : LdtInstance K} {W M q : ℕ}

private theorem claimsOf_mkTT (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i : ℕ) :
    claimsOf (mkTT m c (i + 1)) = (m 0).claims := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

private theorem wordsOf_mkTT (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i k : ℕ) :
    wordsOf (mkTT m c i) k = if k + 1 < i then (m (k + 1)).word else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkTT, PcsRbr.wordsOf_snoc_succ]
      by_cases hk : k = i
      · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

private theorem tensorOf_mkTT (m : ℕ → Msg) (c : ∀ j, ChalTensor S W M q j) (i : ℕ) :
    tensorOf (mkTT m c (i + 1)) = (c 0).tensor := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

private theorem betasOfTensor_mkTT (m : ℕ → Msg) (c : ∀ j, ChalTensor S W M q j) (i k : ℕ) :
    betasOfTensor (mkTT m c i) k = if k + 1 < i then (c (k + 1)).field else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkTT, PcsRbr.betasOfTensor_snoc_succ]
      by_cases hk : k = i
      · subst hk; rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

private theorem queriesOfTensor_mkTT (m : ℕ → Msg) (c : ∀ j, ChalTensor S W M q j) (i : ℕ) :
    queriesOfTensor (mkTT m c (i + 1)) = (c i).points := rfl

private theorem acceptsTensor_mkTT_congr [DecidableEq K]
    {coord : ∀ j, Fin (nc j) → Fin M × Fin W} {m m' : ℕ → PcsRbr.Msg K nc}
    {c : ∀ j, ChalTensor S W M q j} {i : ℕ} {s : K} (h0 : (m' 0).claims = (m 0).claims)
    (hw : ∀ k < i, (m' (k + 1)).word = (m (k + 1)).word)
    (h : AcceptsTensor S s coord (mkTT m c (i + 1))) :
    AcceptsTensor S s coord (mkTT m' c (i + 1)) := by
  have hc : claimsOf (mkTT m' c (i + 1)) = claimsOf (mkTT m c (i + 1)) := by
    rw [claimsOf_mkTT, claimsOf_mkTT, h0]
  have hwo : wordsOf (mkTT m' c (i + 1)) = wordsOf (mkTT m c (i + 1)) := by
    funext k
    rw [wordsOf_mkTT, wordsOf_mkTT]
    by_cases hk : k + 1 < i + 1
    · rw [ite_eq_left hk, ite_eq_left hk, hw k (by omega)]
    · rw [ite_eq_right hk, ite_eq_right hk]
  have hr : tensorOf (mkTT m' c (i + 1)) = tensorOf (mkTT m c (i + 1)) := by
    rw [tensorOf_mkTT, tensorOf_mkTT]
  have hβ : betasOfTensor (mkTT m' c (i + 1)) = betasOfTensor (mkTT m c (i + 1)) := by
    funext k; rw [betasOfTensor_mkTT, betasOfTensor_mkTT]
  unfold AcceptsTensor
  rw [hc, hwo, hr, hβ, queriesOfTensor_mkTT]
  exact h

end BuildTensor

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-! ## Reading a tensor chain against a log -/

section ReadingTensor

omit [DecidableEq K] in
private theorem tLastField_fsTranscriptA {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UTensorChal K fslots slots width) X',
      FSAnswer (UTensorChal K fslots slots width) Y' x)
    (next : ∀ i, Transcript Msg (UTensorChal K fslots slots width) i → Msg) (j : ℕ) :
    tLastField (fsTranscriptA f next (j + 1)) =
      (answer f (fun i => next i (fsTranscriptA f next i)) j).field := by
  show UTensorAns.field (f (.chal (fsTranscriptA f next j) (next j (fsTranscriptA f next j)))) =
    UTensorAns.field (f (.chal (fsTranscript f (fun i => next i (fsTranscriptA f next i)) j)
      (next j (fsTranscriptA f next j))))
  rw [← fsTranscriptA_eq_fsTranscript]

variable (B : Bounds) (r : ℕ) (l : Log (STAns F EF D K fslots slots width)) (m : ℕ → RawMsg F EF D)
  (c : ℕ → UTensorAns K fslots slots width)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem rawAt_interpTensor {i j : ℕ} (hj : j < i) :
    rawAt ((mkTT (C := UTensorChal K fslots slots width) m c i).mapIdx
      (interpTensor B r l)).msgs j = m j := by
  rw [rawAt, getElem?_msgs_mapIdx_mkTT _ _ _ hj]; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem comAt_interpTensor {i j : ℕ} (hj : j < i) (hr : j < r) :
    comAt ((mkTT (C := UTensorChal K fslots slots width) m c i).mapIdx
      (interpTensor B r l)).msgs j = (readMsg B (m j) (committedRow l)).2 := by
  rw [comAt, getElem?_msgs_mapIdx_mkTT _ _ _ hj, interpTensor, ite_eq_left hr]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_chalsOf_mkTT {Msg : Type} (m : ℕ → Msg) {i j : ℕ} (hj : j < i) :
    tAnsAt (chalsOf (mkTT (C := UTensorChal K fslots slots width) m c i)) j = c j := by
  rw [chalsOf_mkTT, tAnsAt, List.getElem?_map, List.getElem?_range hj]; rfl

omit [DecidableEq K] in
private theorem tAnsAt_chalsOf_fsTranscriptA {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UTensorChal K fslots slots width) X',
      FSAnswer (UTensorChal K fslots slots width) Y' x)
    (next : ∀ i, Transcript Msg (UTensorChal K fslots slots width) i → Msg) {i j : ℕ} (hj : j < i) :
    tAnsAt (chalsOf (fsTranscriptA f next i)) j =
      answer f (fun i => next i (fsTranscriptA f next i)) j := by
  rw [fsTranscriptA_eq_fsTranscript, fsTranscript_eq_mkTT]
  exact tAnsAt_chalsOf_mkTT _ _ hj

omit [Field K] [DecidableEq K] in
private theorem tBits_eq_zero (u : UTensorAns K fslots slots width) (k : ℕ) {b : ℕ} (hb : b = 0) :
    u.bits k b = 0 := by
  subst hb; exact Nat.lt_one_iff.mp (u.bits_lt k 0)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private theorem readMsg_snd_of_memT {m : RawMsg F EF D} (com : Compiled.Committed K D) {root : D}
    (h : root ∈ digestsOf B m) : (readMsg B m com).2 root = com root :=
  ite_eq_left h

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem getD_zero_mem_digestsOfT {m : RawMsg F EF D} (h : digestsIn m ≠ []) :
    (digestsIn m).getD 0 default ∈ digestsOf B m := by
  unfold digestsOf
  cases hd : digestsIn m with
  | nil => exact absurd hd h
  | cons d ds => exact List.mem_cons_self (a := d) (l := List.take B.shards ds)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
private theorem committedRow_of_mentionsT {l₁ : Log (STAns F EF D K fslots slots width)}
    (hl₁ : l₁ <+: l)
    (hno : ¬ HasBad (Hit (fun _ => digestsOf (F := F) (EF := EF) B) r) l) {j : ℕ}
    {m : RawMsg F EF D} (hm : Mentions l₁ j m) (hj : j < r) {root : D}
    (hroot : root ∈ digestsOf B m) :
    committedRow l root = committedRow l₁ root := by
  obtain ⟨s, rfl⟩ := hl₁
  funext dims
  exact committedRow_append_of_not_hit (present_of_mentions hm hj hroot)
    (fun h => hno h.hasBad) dims

end ReadingTensor

/-! ## Raw messages helpers -/

section MessagesTensor

variable {InputProof CommitProof : Type}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem digestsIn_of_baseT {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) : digestsIn mid = [] := by
  rw [digestsIn, List.filterMap_eq_nil_iff]
  intro o ho; obtain ⟨a, rfl⟩ := hmid o ho; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_of_baseT {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) : extsOf mid = [] := by
  rw [extsOf, List.filterMap_eq_nil_iff]
  intro o ho; obtain ⟨a, rfl⟩ := hmid o ho; rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_map_extT (l : List EF) :
    extsOf (l.map (Observation.ext (F := F) (D := D))) = l := by
  simp [extsOf, List.filterMap_map]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem digestsIn_secondT (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    digestsIn (.ext γ :: (mid ++ secondMessage proof)) = [proof.stage2Commit] := by
  have h := digestsIn_of_baseT hmid
  simp only [digestsIn] at h
  simp [digestsIn, secondMessage, List.filterMap_append, List.filterMap_map, h]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
private theorem extsOf_secondT (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    extsOf (.ext γ :: (mid ++ secondMessage proof)) =
      γ :: proof.intermediateAccumulators.toList := by
  have h := extsOf_of_baseT hmid
  simp only [extsOf] at h
  simp [extsOf, secondMessage, List.filterMap_append, List.filterMap_map, h]

variable (params : FriParams) (shape : ClaimShape) (commitments : Array D)
  (points values : Array EF) (proof : FriProof F EF D InputProof CommitProof)

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messages_succ_of_ltT {i : ℕ} (hi : i < numRounds params shape) :
    messages params shape commitments points values proof (i + 1) =
      .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]) := by
  rw [messages, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
    Nat.add_sub_cancel]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messages_of_gtT {j : ℕ} (hj : numRounds params shape < j) :
    messages params shape commitments points values proof j =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
  rw [messages, ite_eq_right (by omega), ite_eq_right (by omega)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messages_succ_congrT (commitments' : Array D) (points' values' : Array EF)
    (j : ℕ) :
    messages params shape commitments points values proof (j + 1) =
      messages params shape commitments' points' values' proof (j + 1) := by
  rw [messages, messages, ite_eq_right (Nat.succ_ne_zero j), ite_eq_right (Nat.succ_ne_zero j)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem messages_minT (j : ℕ) :
    messages params shape commitments points values proof (min j (numRounds params shape + 1)) =
      messages params shape commitments points values proof j := by
  rcases Nat.lt_or_ge (numRounds params shape + 1) j with h | h
  · rw [min_eq_right h.le, messages_of_gtT _ _ _ _ _ _ (Nat.lt_succ_self _),
      messages_of_gtT _ _ _ _ _ _ (by omega)]
  · rw [min_eq_left h]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
private theorem digestsIn_messages_ne_nilT {i : ℕ} (hi : i < numRounds params shape) :
    digestsIn (messages params shape commitments points values proof (i + 1)) ≠ [] := by
  rw [messages_succ_of_ltT _ _ _ _ _ _ hi]
  exact List.cons_ne_nil (proof.commitPhaseCommits.getD i default) _

end MessagesTensor

/-! ## Executable checks to compiled tensor verifier -/

section RunTensor

omit [DecidableEq F] [DecidableEq EF] in
private theorem run_of_checkTensor (M : StarkModel F EF K) (sys : System F D)
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
    (h5 : ∀ j, ms (5 + j) = messages sys.fri shape #[] #[] #[] proof.openingProof (j + 1))
    (hcheck : checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    ∃ htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F),
      (∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup) ∧
      zetaOk proof ζ = true ∧ constraintsOk sys proof β γ acc α ζ = true ∧
      ((modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri shape htwo)).verifyWithTensor
        (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape) (tensorCoord sys.fri shape)
        (modelProof M.toFieldModel sys.fri shape proof.openingProof)
        (fun j => view M.toFieldModel sys.fri shape (messages sys.fri shape
          ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
          (claimValues (openingClaims sys proof ζ)) proof.openingProof j))
        (tensorChalOfAns (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape)
          (answer f ms 4))
        (fun i => if i < numRounds sys.fri shape then (answer f ms (5 + i)).field else 0)
        (fun k => (answer f ms (5 + numRounds sys.fri shape)).bits
          (k.val + if sys.fri.queryPowBits = 0 then 0 else 1)
          (logMaxHeight sys.fri.logBlowup shape))).run f = true ∧
      (sys.fri.commitPowBits ≠ 0 → ∀ i < numRounds sys.fri shape,
        (answer f ms (5 + i)).bits 0 sys.fri.commitPowBits = 0) ∧
      (sys.fri.queryPowBits ≠ 0 →
        (answer f ms (5 + numRounds sys.fri shape)).bits 0 sys.fri.queryPowBits = 0) := by
  subst hα hζ
  have hsh' : claimShape (openingClaims
      (InputProof := (merkleMmcs (inputHasher M.toFieldModel (hasherOf f))).MultiProof)
      (CommitProof := (merkleMmcs (friHasher M.toFieldModel (hasherOf f))).MultiProof) sys proof
      (Function.surjInv M.surj (answer f ms 3).field)) = shape := hsh _
  obtain ⟨hz, hc, -, hfs, ch, -, hw, hcol, hopen, hcolW, hopenW, hβ, hpow, hidx⟩ :=
    checkAfterChallengesTensor_ufreeTensor M f (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys proof hshape β γ acc hs h2 h3 h4
      (fun i hi => by
        rw [hsh'] at hi
        rw [h5 i, messages_succ_of_ltT _ _ _ _ _ _ hi])
      (by rw [hsh', h5, messages_of_gtT _ _ _ _ _ _ (Nat.lt_succ_self _)]) hcheck
  rw [hsh'] at hfs hw hcol hopen hcolW hopenW hβ hpow hidx
  obtain ⟨htwo, hfinal⟩ : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F) ∧
      ∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup := by
    have h := hfs
    simp only [Fri.shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.2, fun m hm => (h.1.1.1.1.1.1.1.1.1.1.1.2 m hm).2⟩
  have hcolSz : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape) := by
    rw [hcol, List.size_toArray, List.length_map, List.length_range]
  have hopenSz : ch.schedule.openChallenges.size =
      tensorNumChallenges (maxOpeningsPerHeight sys.fri.logBlowup shape) := by
    rw [hopen, List.size_toArray, List.length_map, List.length_range]
  obtain ⟨hpowOk, hmc⟩ := modelChecksTensor_of_verifyWithTensor_exec M.toFieldModel sys.fri shape
    (M.wellFormed sys.fri shape htwo) f hfs hcolSz hopenSz hcolW hopenW hw
  refine ⟨htwo, hfinal, hz, hc, ?_, (hpow hpowOk).1, (hpow hpowOk).2⟩
  refine Eq.trans (congrArg (OracleComp.run f) ?_)
    (((modelParams M.toFieldModel sys.fri shape _).run_verifyWithTensor _ _ _ f _ _ _ _ _).trans hmc)
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

end RunTensor

/-! ## Proof-view check & committed row helpers -/

section HelpersTensor

variable {InputProof CommitProof : Type}

private def forgetProofsT (proof : Proof F EF D InputProof CommitProof) :
    Proof F EF D Unit Unit where
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
private theorem check_of_proofT (M : StarkModel F EF K) (sys : System F D)
    (v : ShardView F EF D K) (proof : Proof F EF D InputProof CommitProof)
    (h1 : proof.active = v.hdr.active) (h2 : proof.stage1Commit = v.hdr.stage1Commit)
    (h3 : proof.stage2Commit = v.stage2) (h4 : proof.quotientCommit = v.quot)
    (h5 : proof.intermediateAccumulators = v.accs) (h6 : proof.logDegrees = v.hdr.logDegrees)
    (hshape : Stark.shapeOk sys proof = true)
    (hc : constraintsOk sys proof (rep M v.β) (rep M v.γ) v.acc0 (rep M v.α) (rep M v.ζ) = true)
    (hz : zetaOk proof (rep M v.ζ) = true) :
    v.Check M sys (claimValues (openingClaims sys proof (rep M v.ζ))) :=
  ⟨forgetProofsT proof, h1, h2, h3, h4, h5, h6, hshape, rfl, hc, hz⟩

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem baseRows_congrSG (M : StarkModel F EF K) {com com' : Compiled.Committed K D}
    {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i; unfold StarkModel.baseRows; rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem colPoly_congrSG (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ)
    {com com' : Compiled.Committed K D} {root : D} (h : com root = com' root)
    (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord; rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem pointRow_shardCols_congrSG {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {com com' : Compiled.Committed K D} {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) (h1 : com stage1 = com' stage1)
    (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) (c : Circuit F)
    (n : ℕ) (g : K) (pos ci : ℕ) (publics : Array K) (x : K) :
    pointRow c n g (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics x =
      pointRow c n g (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci)
        publics x := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
    funext fun j => colPoly_congrSG M _ _ h1 _ _ _ _
  have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
    funext fun j => colPoly_congrSG M _ _ h2 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
    funext j; unfold shardCols; dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congrSG M _ _ (h3 root hpc) _ _ _ _
  unfold pointRow; rw [hmain, hstage2, hpre]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem constraintFail_congrSG {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
    {com com' : Compiled.Committed K D} {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs ↔
      ConstraintFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  have hvals : rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
    funext pos ci x; unfold rowVals; rw [pointRow_shardCols_congrSG quot' h1 h2 h3]
  unfold ConstraintFail; rw [hvals]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem mem_commitmentsT {sys : System F D} {v : ShardView F EF D K} {root : D}
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
private theorem comOf_eqT {sys : System F D} {msgs : List (IMsg F EF D K)}
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
private theorem inputRoots_mem_commitmentsT (M : StarkModel F EF K) {sys : System F D}
    (v : ShardView F EF D K) (points values : Array EF) (b : Fin (v.shape M sys).length) :
    (view M.toFieldModel sys.fri (v.shape M sys)
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
private theorem commitments_openingClaimsT {sys : System F D}
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) :
    (openingClaims sys proof ζ).map (·.commitment) =
      #[proof.stage1Commit, proof.stage2Commit, proof.quotientCommit] ++
        match sys.preprocessedCommit with
        | some c => #[c]
        | none => #[] := by
  unfold openingClaims
  cases sys.preprocessedCommit <;> simp

omit [Inhabited D] in
private theorem baseRows_of_opensT (M : StarkModel F EF K)
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

end HelpersTensor

/-! ## Tensor opening protocol of a chain -/

section OpeningTensor

variable {M : StarkModel F EF K} {sys : System F D} {θ : ℝ} {msgs : List (IMsg F EF D K)}
  {chals : List (UTensorAns K fslots slots width)} {v : ShardView F EF D K}

omit [DecidableEq F] [DecidableEq EF] in
private theorem ungrind_pcsTTensor (hs : Supported M sys θ v) (j : ℕ) :
    ungrind (pcsTTensor msgs chals hs j) =
      mkTT (pcsMsg msgs hs) (fun i =>
        (pcsChalTensor hs.params (maxWidth (v.shape M sys))
          (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
          (powBits sys.fri (v.shape M sys)) i (tAnsAt chals (4 + i))).2) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pcsTTensor, PcsRbr.ungrind_snoc, ih, mkTT]

omit [DecidableEq F] [DecidableEq EF] in
private theorem powPasses_pcsTTensor (hs : Supported M sys θ v) (j : ℕ) :
    PowPasses (pcsTTensor msgs chals hs j) ↔
      ∀ i < j, (tAnsAt chals (4 + i)).bits 0 (powBits sys.fri (v.shape M sys) i) = 0 := by
  induction j with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩
  | succ j ih =>
    rw [pcsTTensor, PcsRbr.powPasses_snoc, ih]
    constructor
    · rintro ⟨h, hj⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hj
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)⟩

omit [DecidableEq F] [DecidableEq EF] in
private theorem accepts_pcsTTensor (hs : Supported M sys θ v) {Mq : Type} {Cq : ℕ → Type}
    [DecidableEq (FSQuery Mq Cq (HashQuery K D))]
    {pf : Compiled.Proof K D hs.params.batches hs.params.queries}
    {l' l₁ : Log (MerkleAnswer Mq Cq K D)} (pm : ℕ → RawMsg F EF D)
    (ans : ℕ → UTensorAns K fslots slots width)
    (hans : ∀ j < 4 + (hs.params.rounds + 2), tAnsAt chals j = ans j)
    (hmin : ∀ j, pm (min j (hs.params.rounds + 1)) = pm j)
    (h0 : pm 0 = firstMessage (v.commitments sys)
      (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs))
    (hraw : ∀ k ≤ hs.params.rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1))
    (hrun : Outcome (hs.params.verifyWithTensor (M' := Mq) (C := Cq)
      (maxWidth (v.shape M sys)) (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys))
      (starkTensorCoord M sys hs) pf
      (fun j => view M.toFieldModel sys.fri (v.shape M sys) (pm j))
      (tensorChalOfAns (maxWidth (v.shape M sys))
        (maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)) (ans 4))
      (fun i => if i < hs.params.rounds then (ans (5 + i)).field else 0)
      (fun k => (ans (5 + hs.params.rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) hs.params.n)) l' true l₁)
    (hl : ¬ LogCollision hashObs l₁)
    (hc : ∀ (b : Fin hs.params.batches) (k : Fin hs.params.queries) (mi : ℕ) (d : Dimensions),
      (hs.params.dims b)[mi]? = some d →
      M.baseRows (comOf sys v msgs)
          ((view M.toFieldModel sys.fri (v.shape M sys) (pm 0)).inputRoots b) (hs.params.dims b) mi
          ((ans (5 + hs.params.rounds)).bits
            (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) hs.params.n >>>
              (hs.params.n - d.logHeight)) =
        committedRow l₁ ((view M.toFieldModel sys.fri (v.shape M sys) (pm 0)).inputRoots b)
          (hs.params.dims b) mi
          ((ans (5 + hs.params.rounds)).bits
            (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) hs.params.n >>>
              (hs.params.n - d.logHeight)))
    (hw : ∀ k < hs.params.rounds,
      comAt msgs (4 + (k + 1))
          (view M.toFieldModel sys.fri (v.shape M sys) (pm (k + 1))).commitRoot =
        committedRow l₁ (view M.toFieldModel sys.fri (v.shape M sys) (pm (k + 1))).commitRoot) :
    AcceptsTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
      (ungrind (pcsTTensor msgs chals hs (hs.params.rounds + 2))) := by
  let W := maxWidth (v.shape M sys)
  let Mopen := maxOpeningsPerHeight sys.fri.logBlowup (v.shape M sys)
  have hr : tensorOf (mkTT pm (fun i =>
      (pcsChalTensor hs.params W Mopen (powBits sys.fri (v.shape M sys)) i
        (tAnsAt chals (4 + i))).2)
      (hs.params.rounds + 2)) = tensorChalOfAns W Mopen (ans 4) := by
    rw [tensorOf_mkTT, tensor_pcsChalTensor _ _ _ _ _ _ rfl, hans (4 + 0) (by omega)]
    rfl
  have hβ : betasOfTensor (mkTT pm (fun i =>
      (pcsChalTensor hs.params W Mopen (powBits sys.fri (v.shape M sys)) i
        (tAnsAt chals (4 + i))).2)
      (hs.params.rounds + 2)) =
      fun i => if i < hs.params.rounds then (ans (5 + i)).field else 0 := by
    funext i
    rw [betasOfTensor_mkTT]
    rcases Nat.lt_trichotomy i hs.params.rounds with hi | rfl | hi
    · rw [ite_eq_left (by omega), ite_eq_left hi,
        field_pcsChalTensor _ _ _ _ _ _ (Nat.succ_ne_zero _) (Nat.succ_le_of_lt hi),
        hans (4 + (i + 1)) (by omega), show 4 + (i + 1) = 5 + i by omega]
    · rw [ite_eq_left (Nat.lt_succ_self _), ite_eq_right (Nat.lt_irrefl _),
        field_pcsChalTensor_of_not_le _ _ _ _ _ _ (Nat.not_succ_le_self _)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hq : (fun k => hs.params.indexOf (queriesOfTensor (mkTT pm (fun i =>
      (pcsChalTensor hs.params W Mopen (powBits sys.fri (v.shape M sys)) i
        (tAnsAt chals (4 + i))).2)
      (hs.params.rounds + 2)) k)) =
      fun k => (ans (5 + hs.params.rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) hs.params.n := by
    funext k
    rw [queriesOfTensor_mkTT, indexOf_points_pcsChalTensor _ _ _ _ _ _ (Nat.not_succ_le_self _),
      show powBits sys.fri (v.shape M sys) (hs.params.rounds + 1) = sys.fri.queryPowBits from
        powBits_last sys.fri (v.shape M sys),
      hans (4 + (hs.params.rounds + 1)) (by omega),
      show 4 + (hs.params.rounds + 1) = 5 + hs.params.rounds by omega]
  have hmsg : (fun j => view M.toFieldModel sys.fri (v.shape M sys) (Compiled.msgAt (mkTT pm
      (fun i => (pcsChalTensor hs.params W Mopen (powBits sys.fri (v.shape M sys)) i
        (tAnsAt chals (4 + i))).2)
      (hs.params.rounds + 2)) j)) =
      fun j => view M.toFieldModel sys.fri (v.shape M sys) (pm j) := by
    funext j
    rw [msgAt_mkTT, hmin]
  have hacc := hs.params.acceptsTensor_of_outcome_verifyWithTensor_view_com
    (W := W) (M := Mopen) (coord := starkTensorCoord M sys hs) (pf := pf) (l := l') (l' := l₁)
    (view M.toFieldModel sys.fri (v.shape M sys))
    (mkTT pm (fun i =>
      (pcsChalTensor hs.params W Mopen (powBits sys.fri (v.shape M sys)) i
        (tAnsAt chals (4 + i))).2)
      (hs.params.rounds + 2))
    (by rw [hmsg, hr, hβ, hq]; exact hrun) hl (M.baseRows (comOf sys v msgs))
    (fun b k mi d hd => by
      rw [congrFun hq k, msgAt_mkTT, Nat.zero_min]
      exact hc b k mi d hd)
  rw [mapIdx_mkTT] at hacc
  rw [ungrind_pcsTTensor]
  refine acceptsTensor_mkTT_congr ?_ (fun k hk => ?_) hacc
  · show (hs.params.read 0 (view M.toFieldModel sys.fri (v.shape M sys) (firstMessage
      (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs)))
      (M.baseRows (comOf sys v msgs))).claims = _
    rw [← h0]; rfl
  · show (hs.params.read (k + 1) (view M.toFieldModel sys.fri (v.shape M sys)
      (rawAt msgs (4 + (k + 1)))) (comAt msgs (4 + (k + 1)))).word =
      (hs.params.read (k + 1) (view M.toFieldModel sys.fri (v.shape M sys) (pm (k + 1)))
        (committedRow l₁)).word
    rw [hraw k (Nat.le_of_lt_succ hk)]
    rcases Nat.lt_or_ge k hs.params.rounds with hlt | hge
    · exact ((hs.params.read_word_of_lt hlt _ _).trans
        (congrArg (fun c => hs.params.commitWord k (c (hs.params.commitDims k) 0))
          (hw k hlt))).trans (hs.params.read_word_of_lt hlt _ _).symm
    · obtain rfl : k = hs.params.rounds := by omega
      exact (hs.params.read_word_last _ _).trans (hs.params.read_word_last _ _).symm

end OpeningTensor

/-! ## The deterministic shard soundness theorem -/

private theorem shard_goodTensor_aux (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D)
    (θ : ℝ) (B : Bounds) (r : ℕ) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys V θ B r l) {f : ∀ x, STAns F EF D K fslots slots width x}
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
    {R : ℕ} (hR : R = numRounds sys.fri shape)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hsup : Supports l₁ (fsTranscript f ms (4 + (R + 2))))
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D) {ζ : EF}
    (hβ : β = Function.surjInv M.surj (answer f ms 0).field)
    (hγ : γ = Function.surjInv M.surj (answer f ms 1).field)
    (hζ : ζ = Function.surjInv M.surj (answer f ms 3).field) (h0 : ms 0 = m0)
    (h2 : ms 2 = .ext γ :: (mid ++ secondMessage proof))
    (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof ζ)).toList.map .ext)
    (h5 : ∀ j, ms (5 + j) = messages sys.fri shape #[] #[] #[] proof.openingProof (j + 1))
    (hs : UAtTensor ms s 2 (.ext γ :: mid) false 0 0) (hacc : acc = (claimsAccumulator β γ claims).2)
    (hcheck : checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
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
    (hrun : Outcome ((modelParams M.toFieldModel sys.fri shape
        (M.wellFormed sys.fri shape htwo)).verifyWithTensor
      (maxWidth shape) (maxOpeningsPerHeight sys.fri.logBlowup shape) (tensorCoord sys.fri shape)
      (modelProof M.toFieldModel sys.fri shape proof.openingProof)
      (fun j => view M.toFieldModel sys.fri shape (messages sys.fri shape
        ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
        (claimValues (openingClaims sys proof ζ)) proof.openingProof j)) rT bF idx) l' b l₁) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  have hr : 4 + (R + 2) ≤ r := by
    have hle : R ≤ logMaxHeight sys.fri.logBlowup shape := hR ▸ Nat.sub_le _ _
    omega
  have hd := sdoomedTensor_of_goodLogTensor hgood _ hr (hsup.of_prefix hl₁)
  rw [fsTranscript_eq_mkTT] at hd hsup
  obtain ⟨msgs, chals, hlen, hraw, hcom, hans, hment, hdl⟩ :
      ∃ (msgs : List (IMsg F EF D K)) (chals : List (UTensorAns K fslots slots width)),
        msgs.length = 4 + (R + 2) ∧ (∀ j < msgs.length, rawAt msgs j = ms j) ∧
        (∀ j < msgs.length, comAt msgs j = (readMsg B (ms j) (committedRow l)).2) ∧
        (∀ j < msgs.length, tAnsAt chals j = answer f ms j) ∧
        (∀ j < msgs.length, Mentions l₁ j (ms j)) ∧ sdoomedTensorL M sys V θ B msgs chals := by
    have hlen := Transcript.length_msgs
      ((mkTT (C := UTensorChal K fslots slots width) ms (answer f ms) (4 + (R + 2))).mapIdx
        (interpTensor B r l))
    exact ⟨_, _, hlen, fun j hj => rawAt_interpTensor B r l ms _ (hlen ▸ hj),
      fun j hj => comAt_interpTensor B r l ms _ (hlen ▸ hj) (by omega),
      fun j hj => by
        rw [mapIdx_mkTT]
        exact tAnsAt_chalsOf_mkTT _ _ (hlen ▸ hj),
      fun j hj => mentions_of_supports_mkTT hsup j (hlen ▸ hj), hd⟩
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
  obtain ⟨_, hfinal, hz, hc, hrunf, hpowC, hpowQ⟩ := run_of_checkTensor M sys f proof hshape
    (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) _ _ _ hα hζ
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
  have hlen' : msgs.length = 4 + (hsv.params.rounds + 2) := hlen
  have hv2 : proof.stage2Commit = (digestsIn (rawAt msgs 2)).getD 0 default := by
    rw [hraw 2 (by omega), h2, digestsIn_secondT _ hmid proof]; rfl
  have hv3 : proof.quotientCommit = (digestsIn (rawAt msgs 3)).getD 0 default := by
    rw [hraw 3 (by omega), h3]; rfl
  have hva : proof.intermediateAccumulators = ((extsOf (rawAt msgs 2)).drop 1).toArray := by
    rw [hraw 2 (by omega), h2, extsOf_secondT _ hmid proof]; rfl
  have hvals : valuesOf msgs =
      claimValues (openingClaims sys proof (rep M (tFieldAt chals 3))) := by
    rw [valuesOf, hraw 4 (by omega), h4, extsOf_map_extT]
  have hcol : ¬ LogCollision hashObs l := not_logCollision_of_not_hasBad_hit hgood.2
  have hc0 : ∀ root, root = proof.stage1Commit ∨ sys.preprocessedCommit = some root →
      comAt msgs 0 root = committedRow l root := by
    intro root hroot
    rw [hcom 0 (by omega), h0]
    exact readMsg_snd_of_memT B _ (hroot.elim (fun h => h ▸ hdig) (hdigFixed root))
  have hc2 : comAt msgs 2 ((digestsIn (rawAt msgs 2)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 2)).getD 0 default) := by
    rw [hcom 2 (by omega), hraw 2 (by omega)]
    exact readMsg_snd_of_memT B _ (getD_zero_mem_digestsOfT B
      (by rw [h2, digestsIn_secondT _ hmid proof]; exact List.cons_ne_nil _ _))
  have hc3 : comAt msgs 3 ((digestsIn (rawAt msgs 3)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 3)).getD 0 default) := by
    rw [hcom 3 (by omega), hraw 3 (by omega)]
    exact readMsg_snd_of_memT B _ (getD_zero_mem_digestsOfT B
      (by rw [h3]; exact List.cons_ne_nil proof.quotientCommit []))
  have hcomOf : ∀ root, (root = proof.stage1Commit ∨ root = _ ∨ root = _ ∨
      sys.preprocessedCommit = some root) → comOf sys (tViewOf M msgs chals
        ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) msgs root =
        committedRow l root := fun root h => comOf_eqT hc0 hc2 hc3 h
  obtain ⟨pm, hpm⟩ : ∃ pm : ℕ → RawMsg F EF D, pm = messages sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
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
    rw [commitments_openingClaimsT, claimPoints_openingClaims sys proof hshape, ← M.degree_eq,
      ← hvals, hv2, hv3]
    rfl
  have hpmraw : ∀ k ≤ hsv.params.rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1) := fun k hk => by
    rw [hraw _ (by omega), show 4 + (k + 1) = 5 + k by omega, h5 k, hpm]
    exact messages_succ_congrT _ _ _ _ _ _ _ _ _ _
  have hpmmin : ∀ j, pm (min j (hsv.params.rounds + 1)) = pm j := fun j => by
    rw [hpm]; exact messages_minT _ _ _ _ _ _ j
  have hacc := accepts_pcsTTensor hsv pm (answer f ms) (fun j hj => hans j (by omega)) hpmmin hpm0
    hpmraw hrun (fun h => hcol (h.of_prefix hl₁))
    (fun b k mi d hd => by
      have hopen := (hsv.params.outcome_verifyWithTensor hrun).1 b k
      rw [hpm0] at hopen ⊢
      have h := baseRows_of_opensT M hl₁ hcol
        (hcomOf _ (mem_commitmentsT (inputRoots_mem_commitmentsT M _ _ _ b))) hopen hd
      have hle := Merkle.le_maxLogHeight
        (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hd))
      have hH := hsv.params.height_le b
      rw [← Nat.shiftRight_add, show hsv.params.n - Merkle.maxLogHeight (hsv.params.dims b).toList +
        (Merkle.maxLogHeight (hsv.params.dims b).toList - d.logHeight) =
          hsv.params.n - d.logHeight by omega] at h
      exact h)
    (fun k hk => by
      have hj : 4 + (k + 1) < msgs.length := by omega
      have hms : ms (4 + (k + 1)) = pm (k + 1) := (hraw _ hj).symm.trans (hpmraw k hk.le)
      have hmem := getD_zero_mem_digestsOfT B (m := pm (k + 1))
        (by rw [hpm]; exact digestsIn_messages_ne_nilT _ _ _ _ _ _ hk)
      rw [hcom _ hj, hms]
      refine (readMsg_snd_of_memT B _ hmem).trans ?_
      exact committedRow_of_mentionsT B r l hl₁ hgood.2 (hms ▸ hment _ hj) (by omega) hmem)
  have hpow : PowPasses (pcsTTensor msgs chals hsv (hsv.params.rounds + 2)) := by
    refine (powPasses_pcsTTensor hsv _).mpr fun i hi => ?_
    rw [hans (4 + i) (by omega)]
    rcases i with _ | i
    · exact tBits_eq_zero _ _ (powBits_zero sys.fri _)
    · rcases Nat.lt_or_ge i hsv.params.rounds with hlt | hge
      · refine (congrArg (UTensorAns.bits _ 0) (powBits_succ_of_lt sys.fri _ hlt)).trans ?_
        by_cases hb : sys.fri.commitPowBits = 0
        · exact tBits_eq_zero _ _ hb
        · have h := hpowC hb i hlt
          rwa [show 5 + i = 4 + (i + 1) by omega] at h
      · obtain rfl : i = hsv.params.rounds := by omega
        refine (congrArg (UTensorAns.bits _ 0) (powBits_last sys.fri _)).trans ?_
        by_cases hb : sys.fri.queryPowBits = 0
        · exact tBits_eq_zero _ _ hb
        · have h : (answer f ms (5 + hsv.params.rounds)).bits 0 sys.fri.queryPowBits = 0 :=
            hpowQ hb
          rwa [show 5 + hsv.params.rounds = 4 + (hsv.params.rounds + 1) by omega] at h
  have hdec' : V.dec0 (rawAt msgs 0) = some pre := by rw [hraw 0 (by omega), h0]; exact hdec
  have e0 : M.ext.toModel (rep M (tFieldAt chals 0)) = tFieldAt chals 0 :=
    Function.surjInv_eq M.surj _
  have e1 : M.ext.toModel (rep M (tFieldAt chals 1)) = tFieldAt chals 1 :=
    Function.surjInv_eq M.surj _
  have hgl := good_of_sdoomedTensorL hfixed hdl hdec' hpre
    (by rw [hraw 2 (by omega)]; exact hhdr) hsv hlen'
    (by
      rw [hvals]
      exact check_of_proofT M sys _ proof rfl rfl hv2 hv3 hva rfl hshape hc hz)
    hpow hacc
  refine ⟨fun hfail => hgl ?_, fun hbal => ?_⟩
  · rw [e0, e1, hv2, hv3, hva] at hfail
    exact (constraintFail_congrSG
      (baseRows_congrSG M (hcomOf _ (.inl rfl)).symm)
      (baseRows_congrSG M (hcomOf _ (.inr (.inl rfl))).symm)
      fun root hroot => baseRows_congrSG M (hcomOf _ (.inr (.inr (.inr hroot)))).symm).mp hfail
  · rw [e0, e1]
    have h := balance_of_sdoomedTensorL hdl hdec' hpre (by omega)
      (by rw [hcom 0 (by omega), h0]; exact hbal)
    rwa [hcom 0 (by omega), h0] at h

/-- **Deterministic tensor-shard soundness from separated `deriveA` and `verifyWithTensor`
outcomes.** Accepts any intermediate prefix `l' <+: l''` between deriving the Fiat–Shamir
transcript and verifying the unpruned `Compiled.Proof` (for instance `restorePathsM` in the
pruned-MMCS verifier `PrunedTensor.lean`, or `l'' = l'` in unpruned `shard_goodTensor`). -/
theorem shard_goodTensor_of_derive_verify (M : StarkModel F EF K) (sys : System F D)
    (V : Variant F EF D) (θ : ℝ) (B : Bounds) (r : ℕ) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys V θ B r l) {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F))
    {l₀ l' l'' l₁ : Log (STAns F EF D K fslots slots width)}
    {t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width)
      (4 + ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2))}
    {b : Bool}
    (hder : Outcome (deriveA (fun _ : HashQuery K D => D)
      (nextMsgTensor M sys proof m0 mid)
      (4 + ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2))) l₀ t l')
    (hl' : l' <+: l'')
    (hver : Outcome ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).verifyWithTensor
      (maxWidth (starkShape sys M.extData.d proof.active proof.logDegrees))
      (maxOpeningsPerHeight sys.fri.logBlowup
        (starkShape sys M.extData.d proof.active proof.logDegrees))
      (tensorCoord sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees))
      (modelProof M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees) proof.openingProof)
      (fun j => view M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (messages sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
          ((openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))).map (·.commitment))
          (claimPoints (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
          (claimValues (openingClaims sys proof (rep M (tFieldAt (chalsOf t) 3))))
          proof.openingProof j))
      (tensorChalOfAns (maxWidth (starkShape sys M.extData.d proof.active proof.logDegrees))
        (maxOpeningsPerHeight sys.fri.logBlowup
          (starkShape sys M.extData.d proof.active proof.logDegrees)) (tAnsAt (chalsOf t) 4))
      (fun i => if i < (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds then tFieldAt (chalsOf t) (5 + i) else 0)
      (fun k => (tAnsAt (chalsOf t) (5 + (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1)
        (modelParams M.toFieldModel sys.fri
          (starkShape sys M.extData.d proof.active proof.logDegrees)
          (M.wellFormed sys.fri _ htwo)).n)) l'' b l₁)
    (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensor M sys proof m0 mid 2
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = proof.active) (hstage1 : hdr.stage1Commit = proof.stage1Commit)
    (hlogs : hdr.logDegrees = proof.logDegrees)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensor M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) s 2 (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
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
  have hlast := tLastField_fsTranscriptA f (nextMsgTensor M sys proof m0 mid)
  have hfl₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y h =>
    hf x y (dlookup_of_prefix h hl₁)
  have hl'₁ : l' <+: l₁ := hl'.trans hver.prefix
  obtain rfl := hder.eq_fsTranscriptA fun x y h => hfl₁ x y (dlookup_of_prefix h hl'₁)
  have hsup := (supports_of_outcome_deriveA hder).of_prefix hl'₁
  rw [fsTranscriptA_eq_fsTranscript] at hsup
  have hans : ∀ j < 4 + ((modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds + 2),
      tAnsAt (chalsOf (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) (4 + ((modelParams
        M.toFieldModel sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2)))) j =
        answer f (fun j => nextMsgTensor M sys proof m0 mid j
          (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) j := fun j hj =>
    tAnsAt_chalsOf_fsTranscriptA f _ hj
  have hfield : ∀ j < 4 + ((modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds + 2),
      tFieldAt (chalsOf (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) (4 + ((modelParams
        M.toFieldModel sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2)))) j =
        (answer f (fun j => nextMsgTensor M sys proof m0 mid j
          (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) j).field := fun j hj =>
    congrArg UTensorAns.field (hans j hj)
  have hR : (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds =
      numRounds sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees) := rfl
  refine shard_goodTensor_aux M sys V θ B r hfixed hheightOk hθ hgood proof m0 mid hmid hl₁ hfl₁
    hdec hpre
    (ms := fun j => nextMsgTensor M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j))
    hhdr hdig hdigFixed rfl htwo rfl hr hsup hshape β γ acc s hβ hγ
    (congrArg (rep M) (hfield 3 (by omega))) rfl ?_ rfl ?_ (fun j => ?_) hs hacc hcheck
    (congrArg (tensorChalOfAns _ _) (hans 4 (by omega)))
    (fun i => ite_congr rfl (fun hi => hfield (5 + i) (by omega)) fun _ => rfl)
    (fun k => congrArg (fun u : UTensorAns K fslots slots width => u.bits _ _)
      (hans (5 + (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds) (by omega)))
    hver
  · show Observation.ext (rep M (tLastField (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 2)))
      :: (mid ++ secondMessage proof) = _
    rw [hlast 1, hγ]; rfl
  · show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (tLastField
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 4))))).toList = _
    rw [hlast 3, hfield 3 (by omega)]
  · rw [Nat.add_comm 5 j]; rfl

/-- **An accepted tensor-batched STARK proof in a good log has no failing constraint.** -/
theorem shard_goodTensor (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D) (θ : ℝ)
    (B : Bounds) (r : ℕ) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys V θ B r l) {f : ∀ x, STAns F EF D K fslots slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    {l₀ l₁ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensor M sys proof m0 mid) l₀ b l₁) (hl₁ : l₁ <+: l)
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsgTensor M sys proof m0 mid 2
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = proof.active) (hstage1 : hdr.stage1Commit = proof.stage1Commit)
    (hlogs : hdr.logDegrees = proof.logDegrees)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UStateTensor F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsgTensor M sys proof m0 mid j
        (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) 1).field)
    (hs : UAtTensor (fun j => nextMsgTensor M sys proof m0 mid j
      (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) j)) s 2 (.ext γ :: mid) false 0 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel) sys
      proof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  have hlast := tLastField_fsTranscriptA f (nextMsgTensor M sys proof m0 mid)
  obtain ⟨htwo, -⟩ := run_of_checkTensor M sys f proof hshape
    (shape := starkShape sys M.extData.d proof.active proof.logDegrees)
    (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) β γ acc rfl rfl hs
    (show Observation.ext (rep M (tLastField (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 2)))
        :: (mid ++ secondMessage proof) = _ by
      rw [hlast 1, hγ]; rfl)
    rfl
    (show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (tLastField
        (fsTranscriptA f (nextMsgTensor M sys proof m0 mid) 4))))).toList = _ by
      rw [hlast 3]; rfl)
    (fun j => by rw [Nat.add_comm 5 j]; rfl) hcheck
  unfold shardCompTensor at hout
  rw [dite_eq_left htwo, outcome_bind] at hout
  obtain ⟨t, l', hder, hver⟩ := hout
  exact shard_goodTensor_of_derive_verify M sys V θ B r hfixed hheightOk hθ hgood hf proof m0 mid
    hmid htwo hder (List.prefix_refl l') hver hl₁ hdec hpre hhdr hactive hstage1 hlogs hdig
    hdigFixed hr hshape β γ acc s hβ hγ hs hacc hcheck

end CertiFri.Exec.Stark
