import CertiFriProofs.Exec.Stark.ShardGoodTensor
import CertiFriProofs.Exec.Stark.Lookups

/-!
# Soundness of `Stark.verifyTensor` and `Stark.verifyBatchTensor` in the ROM

Tensor-batched counterpart of `Exec/Stark/{Soundness,SoundnessBatch,Lookups,Unconditional}.lean`.
Connects the executable tensor-batched STARK verifiers `Stark.verifyTensor` and
`Stark.verifyBatchTensor` (`CertiFri/Stark/Verifier.lean`, matching `multi-stark` `v6`'s
`FriBatching::Tensor`) to unconditional unique-decoding soundness with exponentially tighter
PCS batching error `pcsErrTensor` (linear in `kColMax + kOpenMax` and `2 ^ (maxLogDegree + logBlowup)`).

## Main results

* `verifyTensor_good`, `verifyBatchTensor_good`: deterministic soundness in a good log
  (`GoodLogTensor`) for single-shard and multi-shard batches.
* `soundness_verifyTensor`, `soundness_verifyBatchTensor`,
  `soundness_verifyTensor_lookups`, `soundness_verifyBatchTensor_lookups`:
  generic ROM soundness under any tensor-PCS `RbrSound` bound `εpcs`.
* `starkErrTensor`: tight round error bound using `pcsErrTensor`.
* `soundness_verifyTensor_ud`, `soundness_verifyBatchTensor_ud`,
  `soundness_verifyTensor_lookups_ud`, `soundness_verifyBatchTensor_lookups_ud`:
  unconditional unique-decoding ROM soundness (zero proximity hypotheses) for constraints
  and LogUp lookup balance.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr OracleComp
  Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-! ## Single-shard tensor STARK (`Stark.verifyTensor`) -/

section SingleTensor

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyTensor` against an oracle**: with Merkle commitment schemes over
`hasherOf f` and the multi-slot idealised challenger `uChallengerTensor f`. -/
noncomputable def verifyTensorAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : SAttempt F EF D) : Bool :=
  Stark.verifyTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a.claims a.proof

/-- The two lookup challenges of a run of `Stark.verifyTensor` against `f`. -/
noncomputable def lookupOfTensor (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : SAttempt F EF D) : EF × EF :=
  ((lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims))).1,
    (lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims))).2.1)

/-- Some constraint of an active circuit fails for the decoded polynomials of `a`. -/
def ViolatesTensor (l : Log (STAns F EF D K fslots slots width))
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : SAttempt F EF D) : Prop :=
  ConstraintFail M sys θ (M.baseRows (committedRow l)) a.proof.active a.proof.logDegrees
    a.proof.stage1Commit a.proof.stage2Commit a.proof.quotientCommit
    (M.ext.toModel (lookupOfTensor M sys f a).1) (M.ext.toModel (lookupOfTensor M sys f a).2)
    (M.ext.toModel (claimsAccumulator (lookupOfTensor M sys f a).1
      (lookupOfTensor M sys f a).2 a.claims).2)
    (a.proof.intermediateAccumulators.map M.ext.toModel)

/-- The lookup messages of a single-shard attempt are balanced against `l`. -/
def LookupsBalancedTensor (l : Log (STAns F EF D K fslots slots width))
    (a : SAttempt F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2) a.preamble)

/-- The soundness experiment for `Stark.verifyTensor`. -/
noncomputable def experimentTensorStark {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → SAttempt F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardCompTensor M sys (attempt a).proof
      (firstMessage sys (attempt a).proof (attempt a).claims) []).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_shardCompTensor_twoAdicity
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D) :
    (shardCompTensor (fslots := fslots) (slots := slots) (width := width)
      M sys proof m0 mid).QueryBound (shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  by_cases h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F)
  · exact queryBound_shardCompTensor M sys proof m0 mid h
  · rw [shardCompTensor, dite_eq_right h]
    exact queryBound_pure _ _

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_experimentTensorStark {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    (experimentTensorStark M sys adv attempt).QueryBound
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    (queryBound_shardCompTensor_twoAdicity M sys _ _ _).bind fun _ => queryBound_pure _ 0

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerOk_of_shapeOkT {InputProof CommitProof : Type}
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

/-- **In a good log, an accepted and covered `Stark.verifyTensor` attempt violates no
constraint and its lookup challenges are not roots of `balPoly`.** -/
theorem verifyTensor_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards)
    {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttempt F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardCompTensor M sys a.proof (firstMessage sys a.proof a.claims) []) l₀ b l)
    (hacc : verifyTensorAccepts M sys f a = true) (hcov : Covered B a) :
    ¬ ViolatesTensor M sys θ l f a ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (firstMessage sys a.proof a.claims) (committedRow l)).2)
          ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩)).eval
            (Polynomial.C (M.ext.toModel (lookupOfTensor M sys f a).1))).eval
          (M.ext.toModel (lookupOfTensor M sys f a).2) ≠ 0) := by
  simp only [verifyTensorAccepts, Stark.verifyTensor, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, -⟩, -, hcheck⟩ := hacc
  have hhdr := headerOk_of_shapeOkT sys B hshape hcov.claims hcov.claim_len
  have hdec : (singleVariant (EF := EF) sys B).dec0 (firstMessage sys a.proof a.claims) =
      some ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ := by
    rw [firstMessage_eq]
    exact singleVariant_dec0 M.base hN hcast hhdr
  have hpre : PreOk sys B
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ :=
    ⟨hshards, fun h hh => by rwa [List.mem_singleton.mp (Array.mem_toList_iff.mpr hh)],
      Nat.zero_le _, fun m hm => absurd hm (Array.not_mem_empty m)⟩
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  have a0 : UAtTensor (fun j => nextMsgTensor M sys a.proof
        (firstMessage sys a.proof a.claims) [] j
        (fsTranscriptA f (nextMsgTensor M sys a.proof (firstMessage sys a.proof a.claims) []) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (firstMessage sys a.proof a.claims)) 0 (firstMessage sys a.proof a.claims) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (firstMessage sys a.proof a.claims)
    (ms := fun j => nextMsgTensor M sys a.proof (firstMessage sys a.proof a.claims) [] j
      (fsTranscriptA f (nextMsgTensor M sys a.proof (firstMessage sys a.proof a.claims) []) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  exact shard_goodTensor M sys (singleVariant sys B) θ B (maxRounds F) hfixed hheightOk hθ hgood hf
    a.proof (firstMessage sys a.proof a.claims) [] (fun o ho => absurd ho List.not_mem_nil) hout
    (List.prefix_refl l) hdec hpre
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩) rfl rfl rfl rfl
    (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self)
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs rfl hcheck

/-- **Soundness of `Stark.verifyTensor`** under any tensor-PCS `RbrSound` bound `εpcs`. -/
theorem soundness_verifyTensor [Fintype K] [Fintype D] (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
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
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorAccepts M sys f (attempt out.1) = true ∧ Covered B (attempt out.1) ∧
          ViolatesTensor M sys θ l f (attempt out.1))
      (experimentTensorStark M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hfslots hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_experimentTensorStark M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyTensor_good M sys θ B hfixed hheightOk hshards hN hcast hθ hgood hf (attempt a)
    hcomp hacc hcov).1 hviol

end SingleTensor

/-! ## Multi-shard batch tensor STARK (`Stark.verifyBatchTensor`) -/

section BatchTensor

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyBatchTensor` against an oracle.** -/
noncomputable def batchTensorAccepts (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : BAttempt F EF D) : Bool :=
  Stark.verifyBatchTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallengerTensor f M.toFieldModel)
    UStateTensor.init sys a

/-- The two shared lookup challenges of a run of `Stark.verifyBatchTensor` against `f`. -/
noncomputable def batchLookupOfTensor (f : ∀ x, STAns F EF D K fslots slots width x)
    (a : BAttempt F EF D) : EF × EF :=
  ((lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble))).1,
    (lookupChallenges (uChallengerTensor f M.toFieldModel)
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble))).2.1)

/-- Some constraint of some shard in the batch fails. -/
def BatchViolatesTensor (l : Log (STAns F EF D K fslots slots width))
    (f : ∀ x, STAns F EF D K fslots slots width x) (a : BAttempt F EF D) : Prop :=
  ∃ (i : ℕ) (hdr : ShardHeader F D) (proof : Proof F EF D (Array (List D)) (Array (List D))),
    a.preamble.headers[i]? = some hdr ∧ a.proofs[i]? = some proof ∧
    ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
      proof.stage1Commit proof.stage2Commit proof.quotientCommit
      (M.ext.toModel (batchLookupOfTensor M sys f a).1)
      (M.ext.toModel (batchLookupOfTensor M sys f a).2)
      (M.ext.toModel (claimsAccumulator (batchLookupOfTensor M sys f a).1
        (batchLookupOfTensor M sys f a).2 hdr.claims).2)
      (proof.intermediateAccumulators.map M.ext.toModel)

/-- The lookup messages of a batch are balanced against `l`. -/
def BatchLookupsBalancedTensor (l : Log (STAns F EF D K fslots slots width))
    (a : BAttempt F EF D) : Prop :=
  Balanced (allItems M sys θ
    (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
      (committedRow l)).2) a.preamble)

/-- The oracle queries of verifying a list of tensor-batched shards sequentially. -/
noncomputable def shardsCompTensor (m0 : RawMsg F EF D) :
    List (Proof F EF D (Array (List D)) (Array (List D))) → ℕ →
      OracleComp (STAns F EF D K fslots slots width) Bool
  | [], _ => .pure true
  | proof :: rest, i =>
    (shardCompTensor M sys proof m0 [observeNat i]).bind fun b =>
      (shardsCompTensor m0 rest (i + 1)).bind fun b' => .pure (b && b')

/-- The soundness experiment for `Stark.verifyBatchTensor`. -/
noncomputable def batchExperimentTensorStark {A : Type}
    (adv : OracleComp (STAns F EF D K fslots slots width) A)
    (attempt : A → BAttempt F EF D) :
    OracleComp (STAns F EF D K fslots slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardsCompTensor M sys (batchFirstMessage sys (attempt a).preamble)
      ((attempt a).proofs.toList.take B.shards) 0).bind fun b => .pure (a, b)

omit [DecidableEq F] [DecidableEq EF] in
private theorem queryBound_shardsCompTensor (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i : ℕ) :
    (shardsCompTensor (fslots := fslots) (slots := slots) (width := width)
      M sys m0 proofs i).QueryBound
      (proofs.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  induction proofs generalizing i with
  | nil => exact queryBound_pure _ _
  | cons proof rest ih =>
    have h : (shardsCompTensor (fslots := fslots) (slots := slots) (width := width)
        M sys m0 (proof :: rest) i).QueryBound
        (shardQueries sys (TwoAdicOps.twoAdicity (F := F)) +
          (rest.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
      (queryBound_shardCompTensor_twoAdicity M sys proof m0 _).bind fun _ =>
        (ih (i + 1)).bind fun _ => queryBound_pure _ _
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

omit [DecidableEq F] [DecidableEq EF] in
theorem queryBound_batchExperimentTensorStark {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    (batchExperimentTensorStark M sys B adv attempt).QueryBound
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    ((queryBound_shardsCompTensor M sys _ _ 0).mono
      (Nat.mul_le_mul_right _ (List.length_take_le _ _))).bind fun _ => queryBound_pure _ 0

private theorem outcome_shardsCompTensor (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i₀ : ℕ)
    {l l' : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (h : Outcome (shardsCompTensor M sys m0 proofs i₀) l b l') (k : ℕ)
    {proof : Proof F EF D (Array (List D)) (Array (List D))} (hk : proofs[k]? = some proof) :
    ∃ (l₀ : Log (STAns F EF D K fslots slots width)) (b' : Bool)
      (l₁ : Log (STAns F EF D K fslots slots width)),
      Outcome (shardCompTensor M sys proof m0 [observeNat (i₀ + k)]) l₀ b' l₁ ∧ l₁ <+: l' := by
  induction proofs generalizing i₀ l b k with
  | nil => exact absurd hk (by simp)
  | cons p rest ih =>
    rw [shardsCompTensor] at h
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
private theorem headerOk_of_shardOkT {InputProof CommitProof : Type}
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
theorem shardOkTensor_of_batchTensorAccepts {f : ∀ x, STAns F EF D K fslots slots width x}
    {a : BAttempt F EF D} (hacc : batchTensorAccepts M sys f a = true) :
    a.preamble.headers.size = a.proofs.size ∧
      ∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (Array (List D)) (Array (List D))),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        Stark.shapeOk sys proof = true ∧ hdr.active = proof.active ∧
          hdr.stage1Commit = proof.stage1Commit ∧ hdr.logDegrees = proof.logDegrees ∧
          checkAfterChallengesTensor (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
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
  simp only [batchTensorAccepts, Stark.verifyBatchTensor, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hacc
  obtain ⟨⟨-, hsz⟩, ⟨-, hall⟩, -⟩ := hacc
  refine ⟨hsz, fun i hdr proof hhdr hproof => ?_⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensor, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, -, hcheck⟩ := h
  exact ⟨hshape, hactive, hstage1, hlogs, hcheck⟩

/-- **In a good log, a shard of an accepted and covered `Stark.verifyBatchTensor` batch
violates no constraint and the batch lookup challenges are not roots of `balPoly`.** -/
theorem verifyBatchTensor_good (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ)
    {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, STAns F EF D K fslots slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttempt F EF D) {l₀ : Log (STAns F EF D K fslots slots width)} {b : Bool}
    (hout : Outcome (shardsCompTensor M sys (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchTensorAccepts M sys f a = true) (hcov : BatchCovered B a) {i : ℕ}
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
  obtain ⟨hsz, hall⟩ := shardOkTensor_of_batchTensorAccepts M sys hacc
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
    exact headerOk_of_shardOkT sys B hshape' hactive' hlogs' (hcov.claims h hh).1
      (hcov.claims h hh).2
  have hdec := batchVariant_dec0 (EF := EF) M.base hN hcast hpre
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hk : (a.proofs.toList.take B.shards)[i]? = some proof := by
    rw [List.getElem?_take_of_lt hi, Array.getElem?_toList]; exact hproof
  obtain ⟨l₀', b', l₁, hcomp, hl₁⟩ := outcome_shardsCompTensor M sys _ _ 0 hout i hk
  rw [Nat.zero_add] at hcomp
  have a0 : UAtTensor (fun j => nextMsgTensor M sys proof
        (batchFirstMessage sys a.preamble) [observeNat i] j
        (fsTranscriptA f
          (nextMsgTensor M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j))
      ((uChallengerTensor f M.toFieldModel).observeAll UStateTensor.init
        (batchFirstMessage sys a.preamble)) 0 (batchFirstMessage sys a.preamble) false 0 0 :=
    UAtTensor.init.observeAll f M.toFieldModel _
  have hβ0 := (UAtTensor.sampleExt_zero f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufreeTensor M f (batchFirstMessage sys a.preamble)
    (ms := fun j => nextMsgTensor M sys proof (batchFirstMessage sys a.preamble) [observeNat i] j
      (fsTranscriptA f
        (nextMsgTensor M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  have hs' := hs.observe f M.toFieldModel (observeNat i)
  have hshard : (batchVariant (EF := EF) sys B N).shard
      (nextMsgTensor M sys proof (batchFirstMessage sys a.preamble) [observeNat i] 2
        (fsTranscriptA f
          (nextMsgTensor M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) 2)) = i :=
    batchVariant_shard M.base sys B hcast _ (hi.le.trans hN.shards) _
  exact shard_goodTensor M sys (batchVariant sys B N) θ B (maxRounds F) hfixed hheightOk hθ hgood hf
    proof (batchFirstMessage sys a.preamble) [observeNat i]
    (fun o ho => ⟨_, List.mem_singleton.mp ho⟩) hcomp hl₁ hdec hpre (hdr := hdr)
    (by rw [hshard]; exact hhdr) hactive hstage1 hlogs
    (by
      rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩))
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    (Nat.le_refl _) hshape _ _ _ _ hβ hγ hs' rfl hcheck

/-- **Soundness of `Stark.verifyBatchTensor`** under any tensor-PCS `RbrSound` bound `εpcs`. -/
theorem soundness_verifyBatchTensor [Fintype K] [Fintype D] (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
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
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorAccepts M sys f (attempt out.1) = true ∧ BatchCovered B (attempt out.1) ∧
          BatchViolatesTensor M sys θ l f (attempt out.1))
      (batchExperimentTensorStark M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hfslots hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_batchExperimentTensorStark M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, i, hdr, proof, hhdr, hproof, hfail⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact (verifyBatchTensor_good M sys θ B hfixed hheightOk hN hcast hθ hgood hf (attempt a)
    hcomp hacc hcov hhdr hproof).1 hfail

end BatchTensor

/-! ## LogUp lookup balance for tensor-batched STARKs -/

section LookupsTensor

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
private theorem readMsg_snd_eqT {m : RawMsg F EF D} (c : Compiled.Committed K D) {root : D}
    (h : root ∈ digestsOf B m) : (readMsg B m c).2 root = c root :=
  ite_eq_left h

omit [DecidableEq K] [Inhabited D] [DecidableEq F] [DecidableEq EF] in
theorem baseRows_readMsgT {m : RawMsg F EF D}
    (c : Compiled.Committed K D) {root : D} (h : root ∈ digestsOf B m) :
    M.baseRows (readMsg B m c).2 root = M.baseRows c root := by
  funext dims mi i; unfold StarkModel.baseRows; rw [readMsg_snd_eqT B c h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem colPoly_congr_rootT (lb : ℕ) {com com' : Compiled.Committed K D} {root : D}
    (h : com root = com' root) (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord; rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem rowAgree_plainRow_of_congrT {com com' : Compiled.Committed K D}
    (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (h1 : com stage1 = com' stage1)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root)
    (publics : Array K) (pos ci r : ℕ) :
    RowAgree
      (pointRow (sys.circuits.getD ci default) (2 ^ logDegrees.getD pos 0)
        (M.gen (logDegrees.getD pos 0))
        (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics
        (M.gen (logDegrees.getD pos 0) ^ r))
      (plainRow M sys θ com' active logDegrees stage1 pos ci r) := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage1 stage1 pos ci).main :=
    funext fun j => colPoly_congr_rootT M θ _ h1 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage1 stage1 pos ci).pre := by
    funext j; unfold shardCols; dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congr_rootT M θ _ (h3 root hpc) _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).preprocessedWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r)) hpre
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).preprocessedWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r * M.gen (logDegrees.getD pos 0)))
      hpre
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).mainWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r)) hmain
  · exact congrArg (fun cols : ℕ → K[X] =>
      Array.ofFn (n := (sys.circuits.getD ci default).mainWidth) fun j =>
        (cols j.val).eval (M.gen (logDegrees.getD pos 0) ^ r * M.gen (logDegrees.getD pos 0)))
      hmain

omit [FieldOps F] [TwoAdicOps F] [DecidableEq K] [DecidableEq F] in
private theorem circuitItems_congr_of_rowAgreeT (ι : F → K) {c : Circuit F}
    (hplain : c.LookupsPlain) {rows rows' : ℕ → RowValues K}
    (h : ∀ r, RowAgree (rows r) (rows' r)) (n : ℕ) :
    circuitItems ι c rows n = circuitItems ι c rows' n := by
  obtain ⟨k, hnodes, hlookups⟩ := hplain
  rw [circuitItems, circuitItems]
  refine List.flatMap_congr fun r _ => List.map_congr_left fun l hl => ?_
  obtain ⟨hm, hargs⟩ := hlookups l (Array.mem_toList_iff.mp hl)
  rw [getD_sweep_congr_of_plain ι _ k hnodes (h r) hm]
  refine congrArg _ (List.map_congr_left fun a ha => ?_)
  exact getD_sweep_congr_of_plain ι _ k hnodes (h r) (hargs a (Array.mem_toList_iff.mp ha))

omit [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem headerItems_eqT {com com' : Compiled.Committed K D} {h : ShardHeader F D}
    (hplain : ∀ p ∈ (activeIndices h.active).zipIdx,
      (sys.circuits.getD p.1 default).LookupsPlain)
    (h1 : com h.stage1Commit = com' h.stage1Commit)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    headerItems M sys θ com h =
      (h.claims.toList.map fun c => ((1 : K), c.toList.map M.base.toModel)) ++
        shardLookupItems M sys θ com' h.active h.logDegrees h.stage1Commit := by
  rw [headerItems, shardLookupItems]
  refine congrArg _ (List.flatMap_congr fun p hp => ?_)
  exact circuitItems_congr_of_rowAgreeT M.base.toModel (hplain p hp)
    (fun r => rowAgree_plainRow_of_congrT M sys θ h.active h.logDegrees h.stage1Commit
      default default h1 h3 #[] p.2 p.1 r) _

omit [FieldOps F] [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] in
private theorem getD_mem_circuits_of_activeT {active : Array Bool}
    (hsize : active.size = sys.circuits.size) {p : ℕ × ℕ}
    (hp : p ∈ (activeIndices active).zipIdx) : sys.circuits.getD p.1 default ∈ sys.circuits := by
  have hmem : p.1 ∈ activeIndices active :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  have hlt : p.1 < sys.circuits.size := by
    rw [← hsize]; exact List.mem_range.mp (List.mem_filter.mp hmem).1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact Array.getElem_mem hlt

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
private theorem sizes_of_shapeOkT {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (hshape : Stark.shapeOk sys proof = true) :
    proof.active.size = sys.circuits.size ∧ 0 < (activeIndices proof.active).length ∧
      proof.intermediateAccumulators.size = (activeIndices proof.active).length := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, hact⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, haccs⟩, -⟩, -⟩ := hshape
  refine ⟨hsize, List.length_pos_iff.mpr fun hnil => ?_, haccs⟩
  rw [hnil] at hact; cases hact

omit [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem toModel_residualT (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0)
    {com com' : Compiled.Committed K D} {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} {hdr : ShardHeader F D}
    (hshape : Stark.shapeOk sys proof = true) (hactive : hdr.active = proof.active)
    (hstage1 : hdr.stage1Commit = proof.stage1Commit) (hlogs : hdr.logDegrees = proof.logDegrees)
    (h1 : com' proof.stage1Commit = com proof.stage1Commit)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com' root = com root)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    {β γ : EF} (hclaims : (claimsAccumulator β γ hdr.claims).1 = true)
    (hfail : ¬ ConstraintFail M sys θ com proof.active proof.logDegrees proof.stage1Commit
      proof.stage2Commit proof.quotientCommit (M.ext.toModel β) (M.ext.toModel γ)
      (M.ext.toModel (claimsAccumulator β γ hdr.claims).2)
      (proof.intermediateAccumulators.map M.ext.toModel))
    (hne : ∀ it ∈ headerItems M sys θ com' hdr,
      M.ext.toModel β + (fpPoly it.2).eval (M.ext.toModel γ) ≠ 0) :
    M.ext.toModel (Stark.residual proof) =
      lookupSum (M.ext.toModel β) (M.ext.toModel γ) (headerItems M sys θ com' hdr) := by
  obtain ⟨hsize, hact, haccs⟩ := sizes_of_shapeOkT sys hshape
  obtain ⟨act, stage1, logs, claims⟩ := hdr
  dsimp only at hactive hstage1 hlogs hclaims hfail
  subst hactive hstage1 hlogs
  have hpl : ∀ p ∈ (activeIndices proof.active).zipIdx,
      (sys.circuits.getD p.1 default).LookupsPlain := fun p hp =>
    hplain _ (getD_mem_circuits_of_activeT sys hsize hp)
  rw [headerItems_eqT M sys θ (h := ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩)
    hpl h1 h3] at hne ⊢
  obtain ⟨-, hcl⟩ := messagesAccumulator_model M β γ _ hclaims
  have hmap : ((claims.toList.map fun claim => (claim, (1 : F))).map fun msg =>
      (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) =
      claims.toList.map fun c => ((1 : K), c.toList.map M.base.toModel) := by
    rw [List.map_map]
    refine List.map_congr_left fun c _ => ?_
    show (M.base.toModel 1, _) = _; rw [M.base.map_one]
  rw [hmap] at hcl
  have hsum := lookupSum_of_not_constraintFail h2 hfail hpl
    (fun p hp => (logDegree_le_of_shapeOk hshape hp).trans htwo)
    (by rw [Array.size_map]; exact haccs) fun it hit => hne it (List.mem_append_right _ hit)
  have hlast : (proof.intermediateAccumulators.map M.ext.toModel).back?.getD
      (M.ext.toModel (claimsAccumulator β γ claims).2) =
      M.ext.toModel (Stark.residual proof) := by
    rw [Stark.residual, Array.back?_eq_getElem?, Array.back?_eq_getElem?, Array.size_map,
      Array.getElem?_map, Array.getElem?_eq_getElem (by omega)]
    rfl
  rw [lookupSum_append, ← hcl, ← hlast, hsum]; rfl

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem toModel_foldl_residualT {InputProof CommitProof : Type} (β γ : K)
    (g : ShardHeader F D → List (K × List K)) (hs : List (ShardHeader F D))
    (ps : List (Proof F EF D InputProof CommitProof)) (hlen : hs.length = ps.length)
    (h : ∀ (i : ℕ) (hdr : ShardHeader F D) (proof : Proof F EF D InputProof CommitProof),
      hs[i]? = some hdr → ps[i]? = some proof →
      M.ext.toModel (Stark.residual proof) = lookupSum β γ (g hdr)) (init : EF) :
    M.ext.toModel (ps.foldl (fun total proof => total + Stark.residual proof) init) =
      M.ext.toModel init + lookupSum β γ (hs.flatMap g) := by
  induction hs generalizing ps init with
  | nil =>
    obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hlen.symm
    exact (add_zero _).symm
  | cons hd hs ih =>
    cases ps with
    | nil => cases hlen
    | cons p ps =>
      rw [List.foldl_cons, ih ps (Nat.succ.inj hlen)
        (fun i hdr proof hh hp => h (i + 1) hdr proof hh hp), M.ext.map_add, h 0 hd p rfl rfl,
        List.flatMap_cons, lookupSum_append, add_assoc]

/-- **`Stark.verifyTensor` only accepts balanced lookups** under any tensor-PCS `RbrSound`. -/
theorem soundness_verifyTensor_lookups [Fintype K] [Fintype D]
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
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
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyTensorAccepts M sys f (attempt out.1) = true ∧ Covered B (attempt out.1) ∧
          ¬ LookupsBalancedTensor M sys θ B l (attempt out.1))
      (experimentTensorStark M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hfslots hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_experimentTensorStark M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hviol, hbal⟩ :=
    verifyTensor_good M sys θ B hfixed hheightOk hshards hN hcast hθ hgood hf (attempt a)
      hcomp hacc hcov
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero (hbal hnb)
  simp only [verifyTensorAccepts, Stark.verifyTensor, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, hres⟩, hclaims, -⟩ := hacc
  have hitems : allItems M sys θ
      (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
        (committedRow l)).2)
      ⟨#[⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
        (attempt a).claims⟩], #[]⟩ =
      headerItems M sys θ
        (M.baseRows (readMsg B (firstMessage sys (attempt a).proof (attempt a).claims)
          (committedRow l)).2)
        ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit, (attempt a).proof.logDegrees,
          (attempt a).claims⟩ := by
    rw [allItems]; exact (List.append_nil _).trans (List.flatMap_singleton _ _)
  rw [hitems] at hne hsum
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards (attempt a).proof (attempt a).claims
  have hlast := toModel_residualT M sys θ (com := M.baseRows (committedRow l))
    (hdr := ⟨(attempt a).proof.active, (attempt a).proof.stage1Commit,
      (attempt a).proof.logDegrees, (attempt a).claims⟩)
    (β := (lookupOfTensor M sys f (attempt a)).1) (γ := (lookupOfTensor M sys f (attempt a)).2)
    hplain h2 hshape rfl rfl rfl
    (baseRows_readMsgT M B _ (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self))
    (fun root hroot => baseRows_readMsgT M B _
      (by rw [hdigs, hroot]; exact List.mem_append_left _ List.mem_cons_self))
    htwo hclaims hviol hne
  exact hsum (hlast.symm.trans (((M.ext.beq_iff _ _).mp hres).trans M.ext.map_zero))

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
private theorem sums_of_batchTensorAccepts {f : ∀ x, STAns F EF D K fslots slots width x}
    {a : BAttempt F EF D} (hacc : batchTensorAccepts M sys f a = true) :
    a.preamble.headers.size ≠ 0 ∧
      (messagesAccumulator (batchLookupOfTensor M sys f a).1 (batchLookupOfTensor M sys f a).2
        (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).1 = true ∧
      (∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (Array (List D)) (Array (List D))),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        (claimsAccumulator (batchLookupOfTensor M sys f a).1 (batchLookupOfTensor M sys f a).2
          hdr.claims).1 = true) ∧
      (a.proofs.foldl (fun total proof => total + Stark.residual proof)
        (messagesAccumulator (batchLookupOfTensor M sys f a).1 (batchLookupOfTensor M sys f a).2
          (a.preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 == 0) = true := by
  simp only [batchTensorAccepts, Stark.verifyBatchTensor, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq] at hacc
  obtain ⟨⟨hne, -⟩, ⟨hmsgs, hall⟩, hzero⟩ := hacc
  refine ⟨hne, hmsgs, fun i hdr proof hhdr hproof => ?_, hzero⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOkTensor, Bool.and_eq_true] at h
  exact h.2.1

/-- **`Stark.verifyBatchTensor` only accepts balanced lookups** under any tensor-PCS `RbrSound`. -/
theorem soundness_verifyBatchTensor_lookups [Fintype K] [Fintype D]
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
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
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (STAns F EF D K fslots slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, STAns F EF D K fslots slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchTensorAccepts M sys f (attempt out.1) = true ∧ BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalancedTensor M sys θ B l (attempt out.1))
      (batchExperimentTensorStark M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLogTensor_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hfslots hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_batchExperimentTensorStark M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hnb⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  obtain ⟨hsz, hall⟩ := shardOkTensor_of_batchTensorAccepts M sys hacc
  obtain ⟨hne0, hmsgs, hclaims, hzero⟩ := sums_of_batchTensorAccepts M sys hacc
  have hshardGood := fun {i : ℕ} {hdr : ShardHeader F D}
      {proof : Proof F EF D (Array (List D)) (Array (List D))}
      (hhdr : (attempt a).preamble.headers[i]? = some hdr)
      (hproof : (attempt a).proofs[i]? = some proof) =>
    verifyBatchTensor_good M sys θ B hfixed hheightOk hN hcast hθ hgood hf (attempt a)
      hcomp hacc hcov hhdr hproof
  have h0' : 0 < (attempt a).preamble.headers.size := Nat.pos_of_ne_zero hne0
  obtain ⟨hne, hsum⟩ := of_eval_balPoly_ne_zero
    ((hshardGood (Array.getElem?_eq_getElem h0') (Array.getElem?_eq_getElem (hsz ▸ h0'))).2 hnb)
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  have hshard : ∀ (i : ℕ) (hdr : ShardHeader F D)
      (proof : Proof F EF D (Array (List D)) (Array (List D))),
      (attempt a).preamble.headers.toList[i]? = some hdr →
      (attempt a).proofs.toList[i]? = some proof →
      M.ext.toModel (Stark.residual proof) =
        lookupSum (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).1)
          (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).2)
          (headerItems M sys θ
            (M.baseRows (readMsg B (batchFirstMessage sys (attempt a).preamble : RawMsg F EF D)
              (committedRow l)).2) hdr) := by
    intro i hdr proof hhdr hproof
    rw [Array.getElem?_toList] at hhdr hproof
    obtain ⟨hshape, hactive, hstage1, hlogs, -⟩ := hall i hdr proof hhdr hproof
    have hmem : hdr ∈ (attempt a).preamble.headers := Array.mem_of_getElem? hhdr
    refine toModel_residualT M sys θ (com := M.baseRows (committedRow l)) hplain h2 hshape hactive
      hstage1 hlogs (baseRows_readMsgT M B _ ?_) (fun root hroot => baseRows_readMsgT M B _ ?_)
      htwo (hclaims i hdr proof hhdr hproof) (hshardGood hhdr hproof).1 fun it hit => hne it ?_
    · rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩)
    · rw [hdigs, hroot]
      exact List.mem_append_left _ List.mem_cons_self
    · rw [allItems]
      exact List.mem_append_left _
        (List.mem_flatMap.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, hit⟩)
  have hm : M.ext.toModel (messagesAccumulator (batchLookupOfTensor M sys f (attempt a)).1
      (batchLookupOfTensor M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2 =
      lookupSum (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).1)
        (M.ext.toModel (batchLookupOfTensor M sys f (attempt a)).2)
        ((attempt a).preamble.messages.toList.map fun m =>
          (M.base.toModel m.multiplicity, m.args.toList.map M.base.toModel)) :=
    (messagesAccumulator_model M _ _ _ hmsgs).2.trans (congrArg _ List.map_map)
  have hfold := toModel_foldl_residualT M _ _ (headerItems M sys θ _)
    (attempt a).preamble.headers.toList (attempt a).proofs.toList
    (by rw [Array.length_toList, Array.length_toList, hsz]) hshard
    (messagesAccumulator (batchLookupOfTensor M sys f (attempt a)).1
      (batchLookupOfTensor M sys f (attempt a)).2
      ((attempt a).preamble.messages.toList.map fun m => (m.args, m.multiplicity))).2
  refine hsum ?_
  rw [allItems, lookupSum_append, add_comm, ← hm, ← hfold, Array.foldl_toList]
  exact ((M.ext.beq_iff _ _).mp hzero).trans M.ext.map_zero

end LookupsTensor

/-! ## Unconditional unique-decoding tensor STARK soundness (`starkErrTensor`) -/

section UnconditionalTensor

variable [Fintype K] (M : StarkModel F EF K) (sys : System F D) (B : Bounds) (δ : ℝ)

/-- **The tightest per-round error of the tensor-batched STARK** at agreement `1 - δ`,
combining the LogUp, AIR constraint, OOD, and `pcsErrTensor` bounds. -/
noncomputable def starkErrTensor : ℝ :=
  max (max (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) 0)
      (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) 1))
    (max (max (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) 2)
        (roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) 3))
      (pcsErrTensor (K := K) sys M.extData.d δ))

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem roundErr_le_starkErrTensor (i : ℕ) :
    roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) i ≤ starkErrTensor M sys B δ := by
  by_cases h0 : i = 0
  · subst h0; exact le_max_of_le_left (le_max_left _ _)
  by_cases h1 : i = 1
  · subst h1; exact le_max_of_le_left (le_max_right _ _)
  by_cases h2 : i = 2
  · subst h2; exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  by_cases h3 : i = 3
  · subst h3; exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hi : roundErr M sys B (pcsErrTensor (K := K) sys M.extData.d δ) i =
      pcsErrTensor (K := K) sys M.extData.d δ := by
    simp only [roundErr, h0, h1, h2, h3, ↓reduceIte]
  rw [hi]
  exact le_max_of_le_right (le_max_right _ _)

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
theorem starkErrTensor_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ starkErrTensor M sys B δ :=
  (pcsErrTensor_nonneg (K := K) sys M.extData.d hδ).trans (le_max_of_le_right (le_max_right _ _))

variable {δ}

/-- **Unconditional unique-decoding soundness of `Stark.verifyTensor`** (zero proximity
hypotheses). -/
theorem soundness_verifyTensor_ud [Fintype D] (hδ : 0 ≤ δ)
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
          verifyTensorAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ViolatesTensor M sys (1 - δ) l f (attempt out.1))
      (experimentTensorStark M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensor M sys (1 - δ) B hfixed hheightOk hshards hN hcast (by linarith)
    (pcsErrTensor_nonneg (K := K) sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ) hadv attempt

/-- **Unconditional unique-decoding soundness of `Stark.verifyBatchTensor`** (zero proximity
hypotheses). -/
theorem soundness_verifyBatchTensor_ud [Fintype D] (hδ : 0 ≤ δ)
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
          batchTensorAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          BatchViolatesTensor M sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStark M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensor M sys (1 - δ) B hfixed hheightOk hN hcast (by linarith)
    (pcsErrTensor_nonneg (K := K) sys M.extData.d hδ) htwo hfslots hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ) hadv attempt

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyTensor`.** -/
theorem soundness_verifyTensor_lookups_ud [Fintype D] (hδ : 0 ≤ δ)
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
          verifyTensorAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ¬ LookupsBalancedTensor M sys (1 - δ) B l (attempt out.1))
      (experimentTensorStark M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensor_lookups M sys (1 - δ) B hplain h2 hfixed hheightOk hshards hN hcast
    (by linarith) (pcsErrTensor_nonneg (K := K) sys M.extData.d hδ) htwo hfslots hslots hcommit
    hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ) hadv attempt

/-- **Unconditional unique-decoding lookup balance for `Stark.verifyBatchTensor`.** -/
theorem soundness_verifyBatchTensor_lookups_ud [Fintype D] (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
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
          batchTensorAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalancedTensor M sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStark M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErrTensor M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensor_lookups M sys (1 - δ) B hplain h2 hfixed hheightOk hN hcast
    (by linarith) (pcsErrTensor_nonneg (K := K) sys M.extData.d hδ) htwo hfslots hslots hcommit
    hquery hwidth (fun v hs => rbrSound_pcsTensor_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErrTensor M sys B δ) (starkErrTensor_nonneg M sys B hδ) hadv attempt

end UnconditionalTensor

end CertiFri.Exec.Stark
