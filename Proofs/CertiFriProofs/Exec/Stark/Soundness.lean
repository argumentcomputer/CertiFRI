import CertiFriProofs.Exec.Stark.ShardGood
import CertiFriProofs.Exec.Stark.Encode

/-!
# Soundness of `Stark.verify` in the random-oracle model

The executable verifier of one proof, `Stark.verify`
(`CertiFri/Stark/Verifier.lean`), accepts only proofs whose committed columns
decode to traces that satisfy every constraint of the system, except with small
probability over the random oracle.

## The experiment

`experiment M sys adv attempt`: the adversary `adv` runs with access to the
oracle and returns `a`, of which `attempt a` holds the public claims and a
proof. Then the queries of the verification are made (`shardComp`): the
challenge queries of the Fiat–Shamir chain of the proof and the hash queries of
the Merkle checks of its opening proof.

## The event

The theorem bounds the probability of the following event of the final log `l`.
There is a total answer function `f` that agrees with `l` such that

* `verifyAccepts`: `Stark.verify` accepts the attempt, with the Merkle
  commitment schemes over the hash functions of `f` and the idealised
  challenger over `f` (`uChallenger`);
* `Covered`: the attempt is within the size bounds and its shape is supported
  (see below);
* `Violates`: some constraint value of some active circuit — a zero of its
  graph or a lookup constraint — is not zero on some row of its trace domain,
  for the polynomials that the committed columns decode to against `l`
  (`StarkModel.colPoly` of the base-field rows `l` commits to), the lookup
  challenges of the run, and the lookup sums of the proof.

So outside the event, an accepted and covered proof comes with base-field
polynomials, read off its commitments and the oracle queries, whose values on
the trace domains satisfy all constraints of all active circuits.

## Results

* `soundness_verify`: the probability of the event is at most
  `N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, where `N` is
  the number of oracle queries of the experiment, `r` the largest number of
  rounds of a chain, and `εmax` bounds the error of every round (`roundErr`).

## Proof

The experiment makes at most `N` queries, so its final log is good (`GoodLog`)
except with the probability of the bound (`prob_not_goodLog_le`). In a good log
the event does not happen, by `shard_good` for the layout `singleVariant`: the
run of `Stark.verify` against `f` follows the chain of the proof
(`lookupChallenges_ufree`), its first message decodes to the header of the
proof (`singleVariant_dec0`, with the shape check and the bounds of `Covered`),
and the commitments to the fixed and the main traces are the digests of the
first message, which are read when there is room for one shard.

## Assumptions

* The random-oracle model, with the idealised challenger and Merkle trees over
  the oracle; a `StarkModel` of the fields.
* `hpcs`: the opening protocol is round-by-round sound, with every error at most
  `εpcs`, for every supported shape. `Exec/Stark/PcsSound.lean` proves it at
  the unique-decoding radius.
* `Covered`: the public claims are within the bounds `B`; the first domain of
  the opening exists in the field and no committed column is shorter than the
  final height (both also follow from acceptance); and the margin of unique
  decoding holds at the height of every committed matrix. A proof with a trace
  too short for the margin is not covered.
* `sys.FixedOk`, and sizes that are distinct as field elements (`hcast`).
* The system is fixed before the adversary runs: its constraint graphs are not
  absorbed into the transcript.

## Not covered

What the constraints mean for a particular system. The batch verifier
(`Exec/Stark/SoundnessBatch.lean`). Completeness, zero knowledge.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle CertiFri.PcsRbr OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ}

/-- What an adversary against `Stark.verify` outputs: the public claims and a
proof, with one Merkle path per query as commitment proofs. -/
structure SAttempt (F EF D : Type) where
  /-- The public claims. -/
  claims : Array (Array F)
  /-- The proof. -/
  proof : Proof F EF D (Array (List D)) (Array (List D))

section Single

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (B : Bounds)

/-- **`Stark.verify` against an oracle**: with the Merkle commitment schemes
over the hash functions of the answer function `f`, and the idealised
challenger over `f`. -/
noncomputable def verifyAccepts (f : ∀ x, SAns F EF D K slots width x) (a : SAttempt F EF D) :
    Bool :=
  Stark.verify (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
    (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel)
    UState.init sys a.claims a.proof

/-- The two lookup challenges of a run of `Stark.verify` against `f`. -/
noncomputable def lookupOf (f : ∀ x, SAns F EF D K slots width x) (a : SAttempt F EF D) :
    EF × EF :=
  ((lookupChallenges (uChallenger f M.toFieldModel)
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (firstMessage sys a.proof a.claims))).1,
    (lookupChallenges (uChallenger f M.toFieldModel)
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (firstMessage sys a.proof a.claims))).2.1)

/-- **A constraint fails.** Some constraint value of some active circuit of the
attempt is not zero on some row of its trace domain, for the polynomials the
committed columns decode to against the log `l`, the lookup challenges of the
run against `f`, and the lookup sums of the proof. -/
def Violates (l : Log (SAns F EF D K slots width)) (f : ∀ x, SAns F EF D K slots width x)
    (a : SAttempt F EF D) : Prop :=
  ConstraintFail M sys θ (M.baseRows (committedRow l)) a.proof.active a.proof.logDegrees
    a.proof.stage1Commit a.proof.stage2Commit a.proof.quotientCommit
    (M.ext.toModel (lookupOf M sys f a).1) (M.ext.toModel (lookupOf M sys f a).2)
    (M.ext.toModel (claimsAccumulator (lookupOf M sys f a).1 (lookupOf M sys f a).2 a.claims).2)
    (a.proof.intermediateAccumulators.map M.ext.toModel)

/-- The attempt is covered: its claims are within the size bounds and its shape
is supported. -/
structure Covered (a : SAttempt F EF D) : Prop where
  /-- The number of public claims. -/
  claims : a.claims.size ≤ B.claims
  /-- The length of a public claim. -/
  claim_len : ∀ c ∈ a.claims, c.size ≤ B.len
  /-- The first domain of the opening exists in the field. -/
  two : logMaxHeight sys.fri.logBlowup
    (starkShape sys M.extData.d a.proof.active a.proof.logDegrees) ≤
      TwoAdicOps.twoAdicity (F := F)
  /-- No committed column is shorter than the final height. -/
  final : ∀ m ∈ (starkShape sys M.extData.d a.proof.active a.proof.logDegrees).flatten,
    sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup
  /-- The margin of unique decoding at the height of every committed matrix. -/
  margin : ∀ m ∈ (starkShape sys M.extData.d a.proof.active a.proof.logDegrees).flatten,
    DecodeMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ

/-- **The soundness experiment for `Stark.verify`.** The adversary runs and
returns `a`; then the queries of the verification of `attempt a` are made. The
result is `a` and the verdict of the model verifier of the opening protocol. -/
noncomputable def experiment {A : Type} (adv : OracleComp (SAns F EF D K slots width) A)
    (attempt : A → SAttempt F EF D) : OracleComp (SAns F EF D K slots width) (A × Bool) :=
  adv.bind fun a =>
    (shardComp M sys (attempt a).proof
      (firstMessage sys (attempt a).proof (attempt a).claims) []).bind fun b => .pure (a, b)

/-- The largest number of rounds of a chain. -/
def maxRounds (F : Type) [FieldOps F] [TwoAdicOps F] : ℕ :=
  4 + (TwoAdicOps.twoAdicity (F := F) + 2)

/-! ## The queries of the experiment -/

omit [DecidableEq F] [DecidableEq EF] in
/-- The verification of a proof makes at most `shardQueries sys twoAdicity`
queries: a proof whose first domain does not exist in the field makes none. -/
private theorem queryBound_shardComp_twoAdicity
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D) :
    (shardComp (slots := slots) (width := width) M sys proof m0 mid).QueryBound
      (shardQueries sys (TwoAdicOps.twoAdicity (F := F))) := by
  by_cases h : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤ TwoAdicOps.twoAdicity (F := F)
  · exact queryBound_shardComp M sys proof m0 mid h
  · rw [shardComp, dite_eq_right h]
    exact queryBound_pure _ _

omit [DecidableEq F] [DecidableEq EF] in
/-- The experiment makes at most `Q + shardQueries sys twoAdicity` queries. -/
private theorem queryBound_experiment {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    (experiment M sys adv attempt).QueryBound
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F))) :=
  hadv.bind fun _ =>
    (queryBound_shardComp_twoAdicity M sys _ _ _).bind fun _ => queryBound_pure _ 0

/-! ## The first message -/

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- A message of base-field elements holds no digest. -/
private theorem digestsIn_eq_nil {m : RawMsg F EF D} (h : ∀ o ∈ m, ∃ a : F, o = .base a) :
    digestsIn m = [] := by
  rw [digestsIn, List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨a, rfl⟩ := h o ho
  rfl

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The digests of the first message of `Stark.verify`: the commitment to the
fixed traces, if the system has one, then the commitment to the main traces. -/
private theorem digestsIn_firstMessage {InputProof CommitProof : Type}
    (proof : Proof F EF D InputProof CommitProof) (claims : Array (Array F)) :
    digestsIn (firstMessage sys proof claims) =
      sys.preprocessedCommit.toList ++ [proof.stage1Commit] := by
  have happ : ∀ m m' : RawMsg F EF D, digestsIn (m ++ m') = digestsIn m ++ digestsIn m' :=
    fun _ _ => List.filterMap_append
  have hshape : digestsIn (shapeMessage (EF := EF) sys) = [] := digestsIn_eq_nil fun o ho => by
    rcases List.mem_cons.mp ho with rfl | ho
    · exact ⟨_, rfl⟩
    · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hactive : digestsIn (activeMessage (F := F) (EF := EF) (D := D) proof.active) = [] :=
    digestsIn_eq_nil fun o ho => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨_, rfl⟩
  have hfixed : digestsIn (fixedMessage (EF := EF) sys) = sys.preprocessedCommit.toList := by
    unfold fixedMessage
    cases sys.preprocessedCommit <;> rfl
  have hlogs : digestsIn (proof.logDegrees.toList.map (observeNat (F := F) (EF := EF) (D := D)))
      = [] := digestsIn_eq_nil fun o ho => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp ho
    exact ⟨_, rfl⟩
  have hclaims : digestsIn (claimsMessage (EF := EF) (D := D) claims) = [] :=
    digestsIn_eq_nil fun o ho => by
      rcases List.mem_cons.mp ho with rfl | ho
      · exact ⟨_, rfl⟩
      · obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp ho
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨_, rfl⟩
        · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hc
          exact ⟨_, rfl⟩
  rw [Stark.firstMessage, happ, happ, happ, happ, happ, hshape, hactive, hfixed, hlogs, hclaims,
    List.nil_append, List.append_nil, List.append_nil]
  rfl

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- With room for one shard, the digests of the first message of `Stark.verify`
are all read. -/
private theorem digestsOf_firstMessage (hshards : 1 ≤ B.shards) {InputProof CommitProof : Type}
    (proof : Proof F EF D InputProof CommitProof) (claims : Array (Array F)) :
    digestsOf B (firstMessage sys proof claims) =
      sys.preprocessedCommit.toList ++ [proof.stage1Commit] := by
  rw [digestsOf, digestsIn_firstMessage, List.take_of_length_le]
  cases sys.preprocessedCommit with
  | none => exact Nat.le_add_left 1 B.shards
  | some c => exact Nat.succ_le_succ hshards

omit [TwoAdicOps F] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The header of a proof that passes the shape check is within the size
bounds, when its public claims are. -/
private theorem headerOk_of_shapeOk {InputProof CommitProof : Type}
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

/-! ## The deterministic part -/

/-- **In a good log, an accepted and covered attempt violates no constraint.**
Take a good log that holds the queries of the verification of the attempt, and
an answer function that agrees with it. If `Stark.verify` accepts the attempt
against the function and the attempt is covered, no constraint fails. -/
private theorem not_violates_of_goodLog (hfixed : sys.FixedOk) (hshards : 1 ≤ B.shards) {N : ℕ}
    (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys (singleVariant sys B) θ B (maxRounds F) l)
    {f : ∀ x, SAns F EF D K slots width x} (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (a : SAttempt F EF D) {l₀ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardComp M sys a.proof (firstMessage sys a.proof a.claims) []) l₀ b l)
    (hacc : verifyAccepts M sys f a = true) (hcov : Covered M sys θ B a) :
    ¬ Violates M sys θ l f a := by
  simp only [verifyAccepts, Stark.verify, Bool.and_eq_true] at hacc
  obtain ⟨⟨hshape, -⟩, -, hcheck⟩ := hacc
  -- The preamble.
  have hhdr := headerOk_of_shapeOk sys B hshape hcov.claims hcov.claim_len
  have hdec : (singleVariant (EF := EF) sys B).dec0 (firstMessage sys a.proof a.claims) =
      some ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ := by
    rw [firstMessage_eq]
    exact singleVariant_dec0 M.base hN hcast hhdr
  have hpre : PreOk sys B
      ⟨#[⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩], #[]⟩ :=
    ⟨hshards, fun h hh => by rwa [List.mem_singleton.mp (Array.mem_toList_iff.mpr hh)],
      Nat.zero_le _, fun m hm => absurd hm (Array.not_mem_empty m)⟩
  -- The digests of the first message.
  have hdigs := digestsOf_firstMessage (EF := EF) sys B hshards a.proof a.claims
  -- The chain: the first lookup challenge is absorbed back in round `1`.
  have a0 : UAt (fun j => nextMsg M sys a.proof (firstMessage sys a.proof a.claims) [] j
        (fsTranscriptA f (nextMsg M sys a.proof (firstMessage sys a.proof a.claims) []) j))
      ((uChallenger f M.toFieldModel).observeAll UState.init
        (firstMessage sys a.proof a.claims)) 0 (firstMessage sys a.proof a.claims) false 0 :=
    UAt.init.observeAll f M.toFieldModel _
  have hβ0 := (UAt.sampleExt f M.toFieldModel a0).1
  obtain ⟨hβ, hγ, hs⟩ := lookupChallenges_ufree M f (firstMessage sys a.proof a.claims)
    (ms := fun j => nextMsg M sys a.proof (firstMessage sys a.proof a.claims) [] j
      (fsTranscriptA f (nextMsg M sys a.proof (firstMessage sys a.proof a.claims) []) j)) rfl
    (congrArg (fun x => [Observation.ext x]) hβ0.symm)
  exact (shard_good M sys (singleVariant sys B) θ B (maxRounds F) hfixed hgood hf a.proof
    (firstMessage sys a.proof a.claims) [] (fun o ho => absurd ho List.not_mem_nil) hout
    (List.prefix_refl l) hdec hpre
    (hdr := ⟨a.proof.active, a.proof.stage1Commit, a.proof.logDegrees, a.claims⟩) rfl rfl rfl rfl
    (by rw [hdigs]; exact List.mem_append_right _ List.mem_cons_self)
    (fun c hc => by rw [hdigs, hc]; exact List.mem_append_left _ List.mem_cons_self)
    hcov.two hcov.final hcov.margin
    (Nat.add_le_add_left (Nat.add_le_add_right
      (le_trans (Compiled.Params.rounds_le _) hcov.two) 2) 4)
    hshape _ _ _ _ hβ hγ hs rfl hcheck).1

/-- **Soundness of `Stark.verify`.** The probability that some answer function
that agrees with the final log makes `Stark.verify` accept a covered attempt
one of whose constraints fails, for the polynomials its committed columns
decode to, is at most
`N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, with
`N = Q + shardQueries sys twoAdicity` the number of queries of the experiment
and `r = maxRounds F`. -/
theorem soundness_verify [Fintype K] [Fintype D] (hfixed : sys.FixedOk) (hshards : 1 ≤ B.shards)
    {N : ℕ} (hN : BoundsLE sys B N)
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
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts M sys f (attempt out.1) = true ∧ Covered M sys θ B (attempt out.1) ∧
          Violates M sys θ l f (attempt out.1))
      (experiment M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * εmax +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) := by
  refine (prob_mono_of_outcome ?_).trans
    (prob_not_goodLog_le (M := M) (sys := sys) (V := singleVariant sys B) (θ := θ) (B := B)
      (r := maxRounds F) hεpcs htwo hslots hcommit hquery hwidth hpcs hε h0
      (queryBound_experiment M sys hadv attempt))
  rintro out l hout ⟨f, hf, hacc, hcov, hviol⟩ hgood
  obtain ⟨a, l₀, -, hout⟩ := outcome_bind.mp hout
  obtain ⟨b, l₁, hcomp, hpure⟩ := outcome_bind.mp hout
  obtain ⟨rfl, rfl⟩ := hpure
  exact not_violates_of_goodLog M sys θ B hfixed hshards hN hcast hgood hf (attempt a) hcomp hacc
    hcov hviol

end Single

end CertiFri.Exec.Stark
