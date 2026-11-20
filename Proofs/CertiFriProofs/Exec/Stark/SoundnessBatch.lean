import CertiFriProofs.Exec.Stark.Soundness

/-!
# Soundness of `Stark.verifyBatch` in the random-oracle model

The batch verifier `Stark.verifyBatch` (`CertiFri/Stark/Verifier.lean`) checks
several proofs (shards) for one system under shared lookup challenges. This
file proves for it what `Exec/Stark/Soundness.lean` proves for `Stark.verify`:
it accepts only batches each of whose shards has committed columns that decode
to traces satisfying every constraint, except with small probability over the
random oracle.

## The experiment

`batchExperiment M sys B adv attempt`: the adversary returns `a`, of which
`attempt a` is a batch proof. Then, for each of the first `B.shards` shards in
turn, the queries of its verification are made (`shardComp`, with the first
message of the batch and the position of the shard).

## The event

There is a total answer function `f` that agrees with the final log `l` such
that

* `batchAccepts`: `Stark.verifyBatch` accepts the batch, with the Merkle
  commitment schemes over the hash functions of `f` and the idealised
  challenger over `f`;
* `BatchCovered`: the preamble is within the size bounds and the shape of every
  shard is supported;
* `BatchViolates`: for some shard, some constraint value of some active circuit
  is not zero on some row, for the polynomials the committed columns of the
  shard decode to against `l`, the shared lookup challenges of the run, and the
  lookup sums of the shard's proof.

## Results

* `soundness_verifyBatch`: the probability of the event is at most
  `N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, with
  `N = Q + B.shards * shardQueries sys twoAdicity` and `r = maxRounds F`.
* `verifyBatch_good`: the deterministic part, for one shard. In a good log, no
  constraint of a shard of an accepted and covered batch fails, and if the
  lookup messages of the batch are not balanced, `balPoly` of them does not
  vanish at the shared lookup challenges (used in `Exec/Stark/Lookups.lean`).

## Proof

The experiment makes at most `N` queries, so its final log is good (`GoodLog`)
except with the probability of the bound (`prob_not_goodLog_le`). In a good log
the event does not happen, by `shard_good` for the layout `batchVariant`, at
the shard with the failing constraint: its position is below `B.shards`, so the
queries of its verification are in the log (`outcome_shardsComp`); the run of
`Stark.verifyBatch` against `f` follows the chain of the shard
(`lookupChallenges_ufree`, then the position of the shard is absorbed); the
first message decodes to the preamble (`batchVariant_dec0`: every header is
that of a proof that passes the shape check, and the bounds are those of
`BatchCovered`) and the message of round `2` to the position of the shard
(`batchVariant_shard`); and the commitments to the fixed traces and to the
main traces of every shard are the digests of the first message, which are all
read (`digestsOf_batchFirstMessage`).

## Assumptions

Those of `soundness_verify`. The sum check on the residuals of the shards and
the messages of the batch is not used here: this theorem is about the
constraints of each shard; what the sum check adds is that the lookup messages
of the whole batch are balanced (`Exec/Stark/Lookups.lean`,
`soundness_verifyBatch_lookups`).
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ}

/-- What an adversary against `Stark.verifyBatch` outputs: a batch proof, with
one Merkle path per query as commitment proofs. -/
abbrev BAttempt (F EF D : Type) : Type :=
  BatchProof F EF D (Array (List D)) (Array (List D))

section Batch

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

/-- **`Stark.verifyBatch` against an oracle**: with the Merkle commitment
schemes over the hash functions of the answer function `f`, and the idealised
challenger over `f`. -/
noncomputable def batchAccepts (f : ∀ x, SAns F EF D K slots width x) (a : BAttempt F EF D) :
    Bool :=
  Stark.verifyBatch (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel)
    UState.init sys a

/-- The two shared lookup challenges of a run of `Stark.verifyBatch` against
`f`. -/
noncomputable def batchLookupOf (f : ∀ x, SAns F EF D K slots width x) (a : BAttempt F EF D) :
    EF × EF :=
  ((lookupChallenges (uChallenger f M.toFieldModel)
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (batchFirstMessage sys a.preamble))).1,
    (lookupChallenges (uChallenger f M.toFieldModel)
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (batchFirstMessage sys a.preamble))).2.1)

/-- **A constraint of some shard fails**, for the polynomials the committed
columns of the shard decode to against the log `l`, the shared lookup
challenges of the run against `f`, the lookup sum of the shard's public claims
and the lookup sums of its proof. -/
def BatchViolates (l : Log (SAns F EF D K slots width)) (f : ∀ x, SAns F EF D K slots width x)
    (a : BAttempt F EF D) : Prop :=
  ∃ (i : ℕ) (hdr : ShardHeader F D) (proof : Proof F EF D (Array (List D)) (Array (List D))),
    a.preamble.headers[i]? = some hdr ∧ a.proofs[i]? = some proof ∧
    ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
      proof.stage1Commit proof.stage2Commit proof.quotientCommit
      (M.ext.toModel (batchLookupOf M sys f a).1) (M.ext.toModel (batchLookupOf M sys f a).2)
      (M.ext.toModel (claimsAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
        hdr.claims).2)
      (proof.intermediateAccumulators.map M.ext.toModel)

/-- The batch is covered: its preamble is within the size bounds, and the shape
of every shard is supported. -/
structure BatchCovered (a : BAttempt F EF D) : Prop where
  /-- The number of shards. -/
  shards : a.preamble.headers.size ≤ B.shards
  /-- The number of public claims of each shard, and their lengths. -/
  claims : ∀ h ∈ a.preamble.headers, h.claims.size ≤ B.claims ∧ ∀ c ∈ h.claims, c.size ≤ B.len
  /-- The number of messages. -/
  messages : a.preamble.messages.size ≤ B.messages
  /-- The length of a message. -/
  message_len : ∀ m ∈ a.preamble.messages, m.args.size ≤ B.len
  /-- The first domain of every opening exists in the field. -/
  two : ∀ h ∈ a.preamble.headers,
    logMaxHeight sys.fri.logBlowup (starkShape sys M.extData.d h.active h.logDegrees) ≤
      TwoAdicOps.twoAdicity (F := F)
  /-- No committed column is shorter than the final height. -/
  final : ∀ h ∈ a.preamble.headers,
    ∀ m ∈ (starkShape sys M.extData.d h.active h.logDegrees).flatten,
      sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup
  /-- The margin of unique decoding at the height of every committed matrix. -/
  margin : ∀ h ∈ a.preamble.headers,
    ∀ m ∈ (starkShape sys M.extData.d h.active h.logDegrees).flatten,
      DecodeMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ
  /-- The first domain of every opening is no larger than the largest trace the
  system supports, times the blowup. -/
  height : ∀ h ∈ a.preamble.headers,
    logMaxHeight sys.fri.logBlowup (starkShape sys M.extData.d h.active h.logDegrees) ≤
      sys.maxLogDegree + sys.fri.logBlowup

/-- The queries of the verification of the shards `proofs`, the first of them
at position `i`: those of each shard in turn. -/
noncomputable def shardsComp (m0 : RawMsg F EF D) :
    List (Proof F EF D (Array (List D)) (Array (List D))) → ℕ →
      OracleComp (SAns F EF D K slots width) Bool
  | [], _ => .pure true
  | proof :: rest, i =>
    (shardComp M sys proof m0 [observeNat i]).bind fun b =>
      (shardsComp m0 rest (i + 1)).bind fun b' => .pure (b && b')

/-- **The soundness experiment for `Stark.verifyBatch`.** The adversary runs
and returns `a`; then the queries of the verification of each of the first
`B.shards` shards of `attempt a` are made. -/
noncomputable def batchExperiment {A : Type} (adv : OracleComp (SAns F EF D K slots width) A)
    (attempt : A → BAttempt F EF D) : OracleComp (SAns F EF D K slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardsComp M sys (batchFirstMessage sys (attempt a).preamble)
      ((attempt a).proofs.toList.take B.shards) 0).bind fun b => .pure (a, b)

/-! ## The queries of the experiment -/

omit [DecidableEq F] [DecidableEq EF] in
/-- The verification of a shard makes at most `shardQueries sys twoAdicity`
queries: a proof whose first domain does not exist in the field makes none. -/
private theorem queryBound_shardComp_le
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D) :
    (shardComp (slots := slots) (width := width) M sys proof m0 mid).QueryBound
      (shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  by_cases h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F)
  · exact queryBound_shardComp M sys proof m0 mid h
  · rw [shardComp, dite_eq_right h]
    exact queryBound_pure _ _

omit [DecidableEq F] [DecidableEq EF] in
/-- The verification of a list of shards makes at most
`shardQueries sys twoAdicity` queries for each of them. -/
private theorem queryBound_shardsComp (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i : ℕ) :
    (shardsComp (slots := slots) (width := width) M sys m0 proofs i).QueryBound
      (proofs.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  induction proofs generalizing i with
  | nil => exact queryBound_pure _ _
  | cons proof rest ih =>
    have h : (shardsComp (slots := slots) (width := width) M sys m0 (proof :: rest) i).QueryBound
        (shardQueries sys (TwoAdicOps.twoAdicity (F := F)) +
          (rest.length * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
      (queryBound_shardComp_le M sys proof m0 _).bind fun _ =>
        (ih (i + 1)).bind fun _ => queryBound_pure _ _
    exact h.mono (by rw [List.length_cons, Nat.succ_mul]; omega)

omit [DecidableEq F] [DecidableEq EF] in
/-- The experiment makes at most `Q + B.shards * shardQueries sys twoAdicity`
queries. -/
theorem queryBound_batchExperiment {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    (batchExperiment M sys B adv attempt).QueryBound
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  have h : (batchExperiment M sys B adv attempt).QueryBound
      (Q + (B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) + 0)) :=
    hadv.bind fun a =>
      ((queryBound_shardsComp M sys _ _ 0).mono
        (Nat.mul_le_mul_right _ (List.length_take_le _ _))).bind fun _ => queryBound_pure _ _
  exact h

/-- **The run of the shards holds the run of each shard.** An outcome of the
verification of a list of shards, the first at position `i₀`, holds for the
shard at position `i₀ + k` an outcome of its verification, whose final log is a
prefix of the final log. -/
private theorem outcome_shardsComp (m0 : RawMsg F EF D)
    (proofs : List (Proof F EF D (Array (List D)) (Array (List D)))) (i₀ : ℕ)
    {l l' : Log (SAns F EF D K slots width)} {b : Bool}
    (h : Outcome (shardsComp M sys m0 proofs i₀) l b l') (k : ℕ)
    {proof : Proof F EF D (Array (List D)) (Array (List D))} (hk : proofs[k]? = some proof) :
    ∃ (l₀ : Log (SAns F EF D K slots width)) (b' : Bool)
      (l₁ : Log (SAns F EF D K slots width)),
      Outcome (shardComp M sys proof m0 [observeNat (i₀ + k)]) l₀ b' l₁ ∧ l₁ <+: l' := by
  induction proofs generalizing i₀ l b k with
  | nil => exact absurd hk (by simp)
  | cons p rest ih =>
    rw [shardsComp] at h
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

/-! ## The first message -/

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- A message of base-field elements holds no digest. -/
private theorem digestsIn_eq_nil_of_base {m : RawMsg F EF D}
    (h : ∀ o ∈ m, ∃ a : F, o = .base a) : digestsIn m = [] := by
  rw [digestsIn, List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨a, rfl⟩ := h o ho
  rfl

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The digests of the first message of `Stark.verifyBatch`: the commitment to
the fixed traces, if the system has one, then the commitments to the main
traces of the shards, in order. -/
private theorem digestsIn_batchFirstMessage (pre : BatchPreamble F D) :
    digestsIn (batchFirstMessage (EF := EF) sys pre) =
      sys.preprocessedCommit.toList ++ pre.headers.toList.map (·.stage1Commit) := by
  have happ : ∀ m m' : RawMsg F EF D, digestsIn (m ++ m') = digestsIn m ++ digestsIn m' :=
    fun _ _ => List.filterMap_append
  have hcons : ∀ (n : ℕ) (m : RawMsg F EF D), digestsIn (observeNat n :: m) = digestsIn m :=
    fun _ _ => rfl
  have hshape : digestsIn (shapeMessage (EF := EF) sys) = [] :=
    digestsIn_eq_nil_of_base fun o ho => by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨_, rfl⟩
      · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp ho
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hfixed : digestsIn (fixedMessage (EF := EF) sys) = sys.preprocessedCommit.toList := by
    unfold fixedMessage
    cases sys.preprocessedCommit <;> rfl
  have hactive : ∀ active : Array Bool,
      digestsIn (activeMessage (F := F) (EF := EF) (D := D) active) = [] := fun active =>
    digestsIn_eq_nil_of_base fun o ho => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨_, rfl⟩
  have hlogs : ∀ logs : Array ℕ,
      digestsIn (logs.toList.map (observeNat (F := F) (EF := EF) (D := D))) = [] := fun logs =>
    digestsIn_eq_nil_of_base fun o ho => by
      obtain ⟨n, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨_, rfl⟩
  have hclaims : ∀ claims : Array (Array F),
      digestsIn (claimsMessage (EF := EF) (D := D) claims) = [] := fun claims =>
    digestsIn_eq_nil_of_base fun o ho => by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨_, rfl⟩
      · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp ho
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, rfl⟩
        · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
          exact ⟨_, rfl⟩
  have hheaders : ∀ hs : List (ShardHeader F D),
      digestsIn (hs.flatMap fun h =>
        (activeMessage h.active ++ [.digest h.stage1Commit]
          ++ observeNat h.logDegrees.size :: h.logDegrees.toList.map observeNat
          ++ claimsMessage h.claims : RawMsg F EF D)) = hs.map (·.stage1Commit) := by
    intro hs
    induction hs with
    | nil => rfl
    | cons h hs ih =>
      rw [List.flatMap_cons, happ, ih, happ, happ, happ, hactive, hcons, hlogs, hclaims]
      rfl
  have hmessages : ∀ ms : List (BatchMessage F),
      digestsIn (ms.flatMap fun m =>
        (observeNat m.args.size :: m.args.toList.map .base ++ [.base m.multiplicity] :
          RawMsg F EF D)) = [] := fun ms =>
    digestsIn_eq_nil_of_base fun o ho => by
      obtain ⟨m, -, hm⟩ := List.mem_flatMap.mp ho
      rcases List.mem_append.mp hm with hm | hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨_, rfl⟩
        · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hm
          exact ⟨_, rfl⟩
      · exact ⟨_, List.mem_singleton.mp hm⟩
  rw [batchFirstMessage, happ, happ, happ, hshape, hfixed, hcons, hcons, hheaders, hmessages,
    List.nil_append, List.append_nil]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- With room for the shards of the preamble, the digests of the first message
of `Stark.verifyBatch` are all read. -/
theorem digestsOf_batchFirstMessage {pre : BatchPreamble F D}
    (hshards : pre.headers.size ≤ B.shards) :
    digestsOf B (batchFirstMessage (EF := EF) sys pre) =
      sys.preprocessedCommit.toList ++ pre.headers.toList.map (·.stage1Commit) := by
  rw [digestsOf, digestsIn_batchFirstMessage, List.take_of_length_le]
  rw [List.length_append, List.length_map, Array.length_toList, Nat.add_comm]
  refine Nat.add_le_add hshards ?_
  cases sys.preprocessedCommit with
  | none => exact Nat.zero_le 1
  | some c => exact Nat.le_refl 1

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The header of a shard whose proof passes the shape check is within the size
bounds, when its public claims are. -/
private theorem headerOk_of_shardOk {InputProof CommitProof : Type}
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

/-! ## The deterministic part -/

omit [DecidableEq K] [DecidableEq F] [DecidableEq EF] in
/-- **What acceptance of a batch says about each shard.** There is one proof
per header, and for the header and the proof at each position: the proof passes
the shape check, the activation bitmap, the commitment to the main traces and
the trace heights of the header are those of the proof, and the checks that
follow the lookup challenges pass, from the shared state after the position of
the shard is absorbed. -/
theorem shardOk_of_batchAccepts {f : ∀ x, SAns F EF D K slots width x}
    {a : BAttempt F EF D} (hacc : batchAccepts M sys f a = true) :
    a.preamble.headers.size = a.proofs.size ∧
      ∀ (i : ℕ) (hdr : ShardHeader F D)
        (proof : Proof F EF D (Array (List D)) (Array (List D))),
        a.preamble.headers[i]? = some hdr → a.proofs[i]? = some proof →
        Stark.shapeOk sys proof = true ∧ hdr.active = proof.active ∧
          hdr.stage1Commit = proof.stage1Commit ∧ hdr.logDegrees = proof.logDegrees ∧
          checkAfterChallenges (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
            (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel)
            sys proof
            ((uChallenger f M.toFieldModel).observe
              (lookupChallenges (uChallenger f M.toFieldModel)
                ((uChallenger f M.toFieldModel).observeAll UState.init
                  (batchFirstMessage sys a.preamble))).2.2 (observeNat i))
            (lookupChallenges (uChallenger f M.toFieldModel)
              ((uChallenger f M.toFieldModel).observeAll UState.init
                (batchFirstMessage sys a.preamble))).1
            (lookupChallenges (uChallenger f M.toFieldModel)
              ((uChallenger f M.toFieldModel).observeAll UState.init
                (batchFirstMessage sys a.preamble))).2.1
            (claimsAccumulator
              (lookupChallenges (uChallenger f M.toFieldModel)
                ((uChallenger f M.toFieldModel).observeAll UState.init
                  (batchFirstMessage sys a.preamble))).1
              (lookupChallenges (uChallenger f M.toFieldModel)
                ((uChallenger f M.toFieldModel).observeAll UState.init
                  (batchFirstMessage sys a.preamble))).2.1 hdr.claims).2 = true := by
  simp only [batchAccepts, Stark.verifyBatch, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hacc
  obtain ⟨⟨-, hsz⟩, ⟨-, hall⟩, -⟩ := hacc
  refine ⟨hsz, fun i hdr proof hhdr hproof => ?_⟩
  have hmem : ((hdr, proof), i) ∈ (a.preamble.headers.toList.zip a.proofs.toList).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, Array.getElem?_toList,
      Array.getElem?_toList]
    exact ⟨hhdr, hproof⟩
  have h := hall _ hmem
  simp only [Stark.shardOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hshape, hactive⟩, hstage1⟩, hlogs⟩, -, hcheck⟩ := h
  exact ⟨hshape, hactive, hstage1, hlogs, hcheck⟩

/-- **In a good log, a shard of an accepted and covered batch violates no
constraint, and the lookup challenges of the batch are not roots of
`balPoly`.** Take a good log that holds the queries of the verification of the
first `B.shards` shards of the batch, and an answer function that agrees with
it. If `Stark.verifyBatch` accepts the batch against the function and the batch
is covered, then for the header and the proof at any position no constraint
fails, and if the lookup messages of the batch are not balanced, `balPoly` of
them does not vanish at the two shared lookup challenges of the run. -/
theorem verifyBatch_good (hfixed : sys.FixedOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, SAns F EF D K slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttempt F EF D) {l₀ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardsComp M sys (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchAccepts M sys f a = true) (hcov : BatchCovered M sys θ B a) {i : ℕ}
    {hdr : ShardHeader F D} {proof : Proof F EF D (Array (List D)) (Array (List D))}
    (hhdr : a.preamble.headers[i]? = some hdr) (hproof : a.proofs[i]? = some proof) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit
        (M.ext.toModel (batchLookupOf M sys f a).1) (M.ext.toModel (batchLookupOf M sys f a).2)
        (M.ext.toModel (claimsAccumulator (batchLookupOf M sys f a).1 (batchLookupOf M sys f a).2
          hdr.claims).2)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble) →
        ((balPoly (allItems M sys θ
          (M.baseRows (readMsg B (batchFirstMessage sys a.preamble : RawMsg F EF D)
            (committedRow l)).2) a.preamble)).eval
            (Polynomial.C (M.ext.toModel (batchLookupOf M sys f a).1))).eval
          (M.ext.toModel (batchLookupOf M sys f a).2) ≠ 0) := by
  obtain ⟨hsz, hall⟩ := shardOk_of_batchAccepts M sys hacc
  obtain ⟨hshape, hactive, hstage1, hlogs, hcheck⟩ := hall i hdr proof hhdr hproof
  have hmem : hdr ∈ a.preamble.headers := Array.mem_of_getElem? hhdr
  have hi : i < B.shards :=
    lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hhdr).1 hcov.shards
  -- The preamble: every header is the header of an accepted shard.
  have hpre : PreOk sys B a.preamble := by
    refine ⟨hcov.shards, fun h hh => ?_, hcov.messages, hcov.message_len⟩
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp hh
    have hklt : k < a.proofs.size := hsz ▸ (Array.getElem?_eq_some_iff.mp hk).1
    obtain ⟨hshape', hactive', -, hlogs', -⟩ :=
      hall k h a.proofs[k] hk (Array.getElem?_eq_getElem hklt)
    exact headerOk_of_shardOk sys B hshape' hactive' hlogs' (hcov.claims h hh).1
      (hcov.claims h hh).2
  have hdec := batchVariant_dec0 (EF := EF) M.base hN hcast hpre
  -- The digests of the first message.
  have hdigs := digestsOf_batchFirstMessage (EF := EF) sys B hcov.shards
  -- The queries of the verification of the shard are in the log.
  have hk : (a.proofs.toList.take B.shards)[i]? = some proof := by
    rw [List.getElem?_take_of_lt hi, Array.getElem?_toList]
    exact hproof
  obtain ⟨l₀', b', l₁, hcomp, hl₁⟩ := outcome_shardsComp M sys _ _ 0 hout i hk
  rw [Nat.zero_add] at hcomp
  -- The shape of the shard is supported.
  have htwo := hcov.two hdr hmem
  have hfinal := hcov.final hdr hmem
  have hmargin := hcov.margin hdr hmem
  have hheight := hcov.height hdr hmem
  rw [hactive, hlogs] at htwo hfinal hmargin hheight
  -- The chain: the first lookup challenge is absorbed back in round `1`, and the
  -- position of the shard follows the second one in round `2`.
  have a0 : UAt (fun j => nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i] j
        (fsTranscriptA f
          (nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j))
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (batchFirstMessage sys a.preamble)) 0 (batchFirstMessage sys a.preamble) false 0 :=
    UAt.init.observeAll f M.toFieldModel _
  have hβ0 := (UAt.sampleExt f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufree M f (batchFirstMessage sys a.preamble)
    (ms := fun j => nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i] j
      (fsTranscriptA f
        (nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  have hs' := hs.observe f M.toFieldModel (observeNat i)
  have hshard : (batchVariant (EF := EF) sys B N).shard
      (nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i] 2
        (fsTranscriptA f
          (nextMsg M sys proof (batchFirstMessage sys a.preamble) [observeNat i]) 2)) = i :=
    batchVariant_shard M.base sys B hcast _ (hi.le.trans hN.shards) _
  exact shard_good M sys (batchVariant sys B N) θ B (maxRounds F) hfixed hgood hf proof
    (batchFirstMessage sys a.preamble) [observeNat i]
    (fun o ho => ⟨_, List.mem_singleton.mp ho⟩) hcomp hl₁ hdec hpre (hdr := hdr)
    (by rw [hshard]; exact hhdr) hactive hstage1 hlogs
    (by
      rw [hdigs, ← hstage1]
      exact List.mem_append_right _
        (List.mem_map.mpr ⟨hdr, Array.mem_toList_iff.mpr hmem, rfl⟩))
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    htwo hfinal hmargin hheight
    (Nat.add_le_add_left (Nat.add_le_add_right
      (le_trans (Compiled.Params.rounds_le _) htwo) 2) 4)
    hshape _ _ _ _ hβ hγ hs' rfl hcheck

/-- **In a good log, an accepted and covered batch violates no constraint.**
Take a good log that holds the queries of the verification of the first
`B.shards` shards of the batch, and an answer function that agrees with it. If
`Stark.verifyBatch` accepts the batch against the function and the batch is
covered, no constraint of any shard fails. -/
private theorem not_batchViolates_of_goodLog (hfixed : sys.FixedOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys (batchVariant sys B N) θ B (maxRounds F) l)
    {f : ∀ x, SAns F EF D K slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : BAttempt F EF D) {l₀ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardsComp M sys (batchFirstMessage sys a.preamble)
      (a.proofs.toList.take B.shards) 0) l₀ b l)
    (hacc : batchAccepts M sys f a = true) (hcov : BatchCovered M sys θ B a) :
    ¬ BatchViolates M sys θ l f a := by
  rintro ⟨i, hdr, proof, hhdr, hproof, hfail⟩
  exact (verifyBatch_good M sys θ B hfixed hN hcast hgood hf a hout hacc hcov hhdr hproof).1 hfail

/-- **Soundness of `Stark.verifyBatch`.** The probability that some answer
function that agrees with the final log makes `Stark.verifyBatch` accept a
covered batch one of whose shards has a failing constraint, for the polynomials
its committed columns decode to, is at most
`N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, with
`N = Q + B.shards * shardQueries sys twoAdicity` and `r = maxRounds F`. -/
theorem soundness_verifyBatch [Fintype K] [Fintype D] (hfixed : sys.FixedOk) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {εpcs εmax : ℝ}
    (hεpcs : 0 ≤ εpcs) (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts M sys f (attempt out.1) = true ∧ BatchCovered M sys θ B (attempt out.1) ∧
          BatchViolates M sys θ l f (attempt out.1))
      (batchExperiment M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLog_le (M := M) (sys := sys) (V := batchVariant sys B N) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_batchExperiment M sys B hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact not_batchViolates_of_goodLog M sys θ B hfixed hN hcast hgood hf (attempt a) hcomp hacc
    hcov hviol

end Batch

end CertiFri.Exec.Stark
