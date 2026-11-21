import CertiFriProofs.Exec.Stark.Chain

/-!
# An accepted proof in a good log has no failing constraint

The deterministic heart of the soundness proof of the STARK, for one proof (one
shard of a batch). Take a log of oracle queries that is good (`GoodLog`: no
entry flips the state function, no hash entry hits a digest in play) and that
holds the queries of the verification of the proof (`shardComp`). Take any
total answer function `f` that agrees with the log. If the executable checks
that follow the lookup challenges accept the proof, with the Merkle schemes
over the hash functions of `f` and the idealised challenger over `f`, then no
constraint of the proof fails on any row, for the polynomials that its
committed columns decode to against the log.

* `shard_good`: the statement, together with what the state function gives for
  the lookup challenges: if the lookup messages of the preamble are not
  balanced, `balPoly` does not vanish at the two lookup challenges.

The entry points `Stark.verify` and `Stark.verifyBatch` differ in the first
message, in what they absorb before the commitment to the lookup traces
(`mid`), and in how the preamble is decoded (`Variant`); these are parameters
here.

## Assumptions

* The proof passes the shape check, and its header is the one the preamble
  holds at the position of the chain.
* `sys.FixedOk`, and `sys.HeightOk`: no fixed trace of the system is taller
  than the largest trace the system supports.
* `1 + 2 ^ (-logBlowup) < 2 * θ`: the agreement `θ` is inside the
  unique-decoding radius.
* The commitments to the main traces and to the fixed traces are among the
  digests of the first message that are read (`digestsOf`).
* `mid` holds base-field elements only.
* The good log is good for the rounds of the longest chain:
  `4 + (twoAdicity + 2) ≤ r`.

Nothing is assumed about the shape of the opening of the proof. That it is
supported (`Supported`) follows from the accepting checks:

* its first domain exists in the field and no committed column is shorter than
  the final height, because the shape check of the opening proof passed
  (`Fri.shapeOk`, through `run_of_check`);
* its first domain is no larger than the largest trace the system supports,
  times the blowup, because the shape check of the proof bounds the traces of
  the active circuits and `sys.HeightOk` the fixed traces of the inactive ones
  (`logMaxHeight_starkShape_le`);
* the strict margin of unique decoding (`StrictMargin`,
  `|D| + d < 2 * θ * |D|`) holds at the height of every committed matrix, by
  `strictMargin_coset`, whatever the trace heights;
* the chain has at most `r` rounds: it has no more folding rounds than the
  log-size of its first domain, which is at most `twoAdicity`.

## The proof

Against `f`, the chain of the proof (`nextMsg`) is the chain of `fsTranscript`
on its own messages. `shardComp` makes queries only for a proof whose first
domain exists in the field, so `shard_good` first runs the executable checks
along the chain to learn that it does (`run_of_check`). Then it unfolds
`shardComp` and reduces to `shard_good_aux`, which is stated for any messages
that satisfy the equations of the chain. There:

* In a good log the chain, read against the log, is doomed
  (`sdoomed_of_goodLog`).
* The executable checks give the constraint checks on the opened values, and
  make the model verifier of the opening protocol accept against `f`
  (`run_of_check`). So the run of the model verifier in the log accepted. They
  also give that the shape of the opening is supported, as above.
* An accepting run that leaves a log without a collision makes the opening
  protocol read off the chain accept (`accepts_pcsT`). Its claims are read from
  the base-field rows under the commitments of the shard, which are the rows of
  the log where the queries open (`comOf_eq`, `baseRows_of_opens`). Its words
  are read from the rows under the commitments of the folding rounds, which are
  frozen once the challenge query of their round is in the log
  (`committedRow_of_mentions`).
* The proof-of-work numbers of the chain are zero (`powPasses_pcsT`), and the
  proof, without its commitment proofs, witnesses `Check` (`check_of_proof`).
* `good_of_sdoomedL` and `balance_of_sdoomedL` give the two conclusions for the
  rows the chain reads. A failing constraint reads the committed rows only
  under the commitments to the main, the lookup and the fixed traces
  (`constraintFail_congr`), where these are the rows of the log.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle OracleComp Polynomial
open CertiFri.Exec.Transcript (answer)
open CertiFri.PcsRbr (Chal GrindChal alphaOf betasOf queriesOf claimsOf wordsOf Accepts PowPasses
  ungrind)

/-! ## Transcripts given by their messages and their challenges -/

section Build

variable {Msg Msg' : Type} {C : ℕ → Type}

/-- The transcript of `i` rounds with the messages `m 0, …, m (i - 1)` and the
challenges `c 0, …, c (i - 1)`. -/
private def mkT (m : ℕ → Msg) (c : ∀ j, C j) : (i : ℕ) → Transcript Msg C i
  | 0 => .nil
  | i + 1 => (mkT m c i).snoc (m i) (c i)

/-- The messages of `mkT m c i` are `m 0, …, m (i - 1)`. -/
private theorem msgs_mkT (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkT m c i).msgs = (List.range i).map m := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkT, Transcript.msgs_snoc, ih, List.range_succ, List.map_append, List.map_singleton]

/-- Reading the messages of `mkT m c i` through `g` reads each `m j`. -/
private theorem mapIdx_mkT (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j) (i : ℕ) :
    (mkT m c i).mapIdx g = mkT (fun j => g j (m j)) c i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [mkT, Transcript.mapIdx_snoc, ih, mkT]

/-- The message of a round of `mkT m c (i + 1)`. -/
private theorem msgAt_mkT (m : ℕ → Msg) (c : ∀ j, C j) (i j : ℕ) :
    Compiled.msgAt (mkT m c (i + 1)) j = m (min j i) := by
  rw [mkT, Compiled.msgAt, msgs_mkT, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases Nat.lt_or_ge j i with h | h
  · rw [List.getElem?_range h, min_eq_left h.le]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; exact h), min_eq_right h]
    rfl

/-- The message of round `j` of `mkT m c i`, read through `g`. -/
private theorem getElem?_msgs_mapIdx_mkT (g : ℕ → Msg → Msg') (m : ℕ → Msg) (c : ∀ j, C j)
    {i j : ℕ} (hj : j < i) : ((mkT m c i).mapIdx g).msgs[j]? = some (g j (m j)) := by
  rw [mapIdx_mkT, msgs_mkT, List.getElem?_map, List.getElem?_range hj]
  rfl

/-- A log that answers the chain of `mkT m c i` holds a challenge query with
the message `m j` in round `j`, for every `j < i`. -/
private theorem mentions_of_supports_mkT {X' : Type} {Y' : X' → Type}
    [DecidableEq (FSQuery Msg C X')] {l : Log (FSAnswer (Msg := Msg) C Y')} {m : ℕ → Msg}
    {c : ∀ j, C j} : ∀ {i : ℕ}, Supports l (mkT m c i) → ∀ j < i, Mentions l j (m j)
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | i + 1, h, j, hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · exact mentions_of_supports_mkT h.1 j hlt
    · refine ⟨_, List.of_mem_dlookup h.2, ?_⟩
      have hlast := List.getElem?_concat_length (l := (mkT m c j).msgs) (a := m j)
      rwa [Transcript.length_msgs] at hlast

/-- The chain of `fsTranscript` is the transcript of its messages and of the
answers along the chain. -/
private theorem fsTranscript_eq_mkT {X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg C X', FSAnswer C Y' x) (ms : ℕ → Msg) (i : ℕ) :
    fsTranscript f ms i = mkT ms (answer f ms) i := by
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (fun t => t.snoc (ms i) (answer f ms i)) ih

/-- The challenges of `mkT m c i` are `c 0, …, c (i - 1)`. -/
private theorem chalsOf_mkT {U : Type} (m : ℕ → Msg) (c : ℕ → U) (i : ℕ) :
    chalsOf (mkT (C := fun _ => U) m c i) = (List.range i).map c := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [mkT, chalsOf, ih, List.range_succ, List.map_append, List.map_singleton]

variable {K : Type} [Field K] {nc : ℕ → ℕ} {S : LdtInstance K} {q : ℕ}

/-- The claims of `mkT m c (i + 1)` are those of `m 0`. -/
private theorem claimsOf_mkT (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i : ℕ) :
    claimsOf (mkT m c (i + 1)) = (m 0).claims := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

/-- Word `k` of `mkT m c i` is the word of `m (k + 1)`. -/
private theorem wordsOf_mkT (m : ℕ → PcsRbr.Msg K nc) (c : ∀ j, C j) (i k : ℕ) :
    wordsOf (mkT m c i) k = if k + 1 < i then (m (k + 1)).word else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkT, PcsRbr.wordsOf_snoc_succ]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The batching challenge of `mkT m c (i + 1)` is the field element of
`c 0`. -/
private theorem alphaOf_mkT (m : ℕ → Msg) (c : ∀ j, Chal S q j) (i : ℕ) :
    alphaOf (mkT m c (i + 1)) = (c 0).field := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih

/-- Folding challenge `k` of `mkT m c i` is the field element of `c (k + 1)`. -/
private theorem betasOf_mkT (m : ℕ → Msg) (c : ∀ j, Chal S q j) (i k : ℕ) :
    betasOf (mkT m c i) k = if k + 1 < i then (c (k + 1)).field else 0 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [mkT, PcsRbr.betasOf_snoc_succ]
      by_cases hk : k = i
      · subst hk
        rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hk, ih]
        by_cases hlt : k + 1 < i + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- The query points of `mkT m c (i + 1)` are those of `c i`. -/
private theorem queriesOf_mkT (m : ℕ → Msg) (c : ∀ j, Chal S q j) (i : ℕ) :
    queriesOf (mkT m c (i + 1)) = (c i).points := rfl

/-- **Acceptance reads the claims of the first message and the words of the
later ones.** Two transcripts with the same challenges, the same claims in the
first message and the same word in every later message are accepted
together. -/
private theorem accepts_mkT_congr [DecidableEq K] {m m' : ℕ → PcsRbr.Msg K nc}
    {c : ∀ j, Chal S q j} {i : ℕ} {s : K} (h0 : (m' 0).claims = (m 0).claims)
    (hw : ∀ k < i, (m' (k + 1)).word = (m (k + 1)).word) (h : Accepts S s (mkT m c (i + 1))) :
    Accepts S s (mkT m' c (i + 1)) := by
  have hc : claimsOf (mkT m' c (i + 1)) = claimsOf (mkT m c (i + 1)) := by
    rw [claimsOf_mkT, claimsOf_mkT, h0]
  have hwo : wordsOf (mkT m' c (i + 1)) = wordsOf (mkT m c (i + 1)) := by
    funext k
    rw [wordsOf_mkT, wordsOf_mkT]
    by_cases hk : k + 1 < i + 1
    · rw [ite_eq_left hk, ite_eq_left hk, hw k (by omega)]
    · rw [ite_eq_right hk, ite_eq_right hk]
  have hα : alphaOf (mkT m' c (i + 1)) = alphaOf (mkT m c (i + 1)) := by
    rw [alphaOf_mkT, alphaOf_mkT]
  have hβ : betasOf (mkT m' c (i + 1)) = betasOf (mkT m c (i + 1)) := by
    funext k
    rw [betasOf_mkT, betasOf_mkT]
  unfold Accepts
  rw [hc, hwo, hα, hβ, queriesOf_mkT]
  exact h

end Build

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ}

/-! ## Reading a chain against a log -/

section Reading

omit [DecidableEq K] in
/-- The field challenge of the last round of a chain with computed messages is
that of the answer of the round. -/
private theorem lastField_fsTranscriptA {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UChal K slots width) X', FSAnswer (UChal K slots width) Y' x)
    (next : ∀ i, Transcript Msg (UChal K slots width) i → Msg) (j : ℕ) :
    lastField (fsTranscriptA f next (j + 1)) =
      (answer f (fun i => next i (fsTranscriptA f next i)) j).field := by
  show UAns.field (f (.chal (fsTranscriptA f next j) (next j (fsTranscriptA f next j)))) =
    UAns.field (f (.chal (fsTranscript f (fun i => next i (fsTranscriptA f next i)) j)
      (next j (fsTranscriptA f next j))))
  rw [← fsTranscriptA_eq_fsTranscript]

variable (B : Bounds) (r : ℕ) (l : Log (SAns F EF D K slots width)) (m : ℕ → RawMsg F EF D)
  (c : ℕ → UAns K slots width)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
/-- What the verifier absorbed in round `j` of a chain read against a log. -/
private theorem rawAt_interp {i j : ℕ} (hj : j < i) :
    rawAt ((mkT (C := UChal K slots width) m c i).mapIdx (interp B r l)).msgs j = m j := by
  rw [rawAt, getElem?_msgs_mapIdx_mkT _ _ _ hj]
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
/-- The committed rows of round `j < r` of a chain read against a log. -/
private theorem comAt_interp {i j : ℕ} (hj : j < i) (hr : j < r) :
    comAt ((mkT (C := UChal K slots width) m c i).mapIdx (interp B r l)).msgs j =
      (readMsg B (m j) (committedRow l)).2 := by
  rw [comAt, getElem?_msgs_mapIdx_mkT _ _ _ hj, interp, ite_eq_left hr]
  rfl

omit [DecidableEq K] in
/-- The answer of round `j` of a transcript given by its messages and its
challenges. -/
private theorem ansAt_chalsOf_mkT {Msg : Type} (m : ℕ → Msg) {i j : ℕ} (hj : j < i) :
    ansAt (chalsOf (mkT (C := UChal K slots width) m c i)) j = c j := by
  rw [chalsOf_mkT, ansAt, List.getElem?_map, List.getElem?_range hj]
  rfl

omit [DecidableEq K] in
/-- The answer of round `j` of a chain with computed messages. -/
private theorem ansAt_chalsOf_fsTranscriptA {Msg X' : Type} {Y' : X' → Type}
    (f : ∀ x : FSQuery Msg (UChal K slots width) X', FSAnswer (UChal K slots width) Y' x)
    (next : ∀ i, Transcript Msg (UChal K slots width) i → Msg) {i j : ℕ} (hj : j < i) :
    ansAt (chalsOf (fsTranscriptA f next i)) j =
      answer f (fun i => next i (fsTranscriptA f next i)) j := by
  rw [fsTranscriptA_eq_fsTranscript, fsTranscript_eq_mkT]
  exact ansAt_chalsOf_mkT _ _ hj

omit [Field K] [DecidableEq K] in
/-- A number of an answer reduced to no bits is zero. -/
private theorem bits_eq_zero (u : UAns K slots width) (k : ℕ) {b : ℕ} (hb : b = 0) :
    u.bits k b = 0 := by
  subst hb
  exact Nat.lt_one_iff.mp (u.bits_lt k 0)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq F] [DecidableEq EF] in
/-- A digest that is read in a message is read with the rows it commits to. -/
private theorem readMsg_snd_of_mem {m : RawMsg F EF D} (com : Compiled.Committed K D) {root : D}
    (h : root ∈ digestsOf B m) : (readMsg B m com).2 root = com root :=
  ite_eq_left h

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- The first digest of a message is among the digests that are read. -/
private theorem getD_zero_mem_digestsOf {m : RawMsg F EF D} (h : digestsIn m ≠ []) :
    (digestsIn m).getD 0 default ∈ digestsOf B m := by
  unfold digestsOf
  cases hd : digestsIn m with
  | nil => exact absurd hd h
  | cons d ds => exact List.mem_cons_self (a := d) (l := List.take B.shards ds)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
/-- **The rows of a digest in play are frozen.** In a log without a hit, a digest
that is read in a message of a challenge query of a prefix of the log commits to
the same rows in the prefix and in the log. -/
private theorem committedRow_of_mentions {l₁ : Log (SAns F EF D K slots width)} (hl₁ : l₁ <+: l)
    (hno : ¬ HasBad (Hit (digestsOf (F := F) (EF := EF) B) r) l) {j : ℕ} {m : RawMsg F EF D}
    (hm : Mentions l₁ j m) (hj : j < r) {root : D} (hroot : root ∈ digestsOf B m) :
    committedRow l root = committedRow l₁ root := by
  obtain ⟨s, rfl⟩ := hl₁
  funext dims
  exact committedRow_append_of_not_hit (present_of_mentions hm hj hroot)
    (fun h => hno h.hasBad) dims

end Reading

/-! ## The raw messages -/

section Messages

variable {InputProof CommitProof : Type}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- A message of base-field elements holds no digest. -/
private theorem digestsIn_of_base {mid : RawMsg F EF D} (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) :
    digestsIn mid = [] := by
  rw [digestsIn, List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨a, rfl⟩ := hmid o ho
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- A message of base-field elements holds no extension-field element. -/
private theorem extsOf_of_base {mid : RawMsg F EF D} (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) :
    extsOf mid = [] := by
  rw [extsOf, List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨a, rfl⟩ := hmid o ho
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- The extension-field elements of a message of such elements. -/
private theorem extsOf_map_ext (l : List EF) :
    extsOf (l.map (Observation.ext (F := F) (D := D))) = l := by
  simp [extsOf, List.filterMap_map]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- The one digest of the message of round `2` is the commitment to the lookup
traces. -/
private theorem digestsIn_second (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    digestsIn (.ext γ :: (mid ++ secondMessage proof)) = [proof.stage2Commit] := by
  have h := digestsIn_of_base hmid
  simp only [digestsIn] at h
  simp [digestsIn, secondMessage, List.filterMap_append, List.filterMap_map, h]

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Inhabited D] [DecidableEq D]
  [DecidableEq F] [DecidableEq EF] in
/-- The extension-field elements of the message of round `2`: the second lookup
challenge and the lookup sums. -/
private theorem extsOf_second (γ : EF) {mid : RawMsg F EF D}
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) (proof : Proof F EF D InputProof CommitProof) :
    extsOf (.ext γ :: (mid ++ secondMessage proof)) =
      γ :: proof.intermediateAccumulators.toList := by
  have h := extsOf_of_base hmid
  simp only [extsOf] at h
  simp [extsOf, secondMessage, List.filterMap_append, List.filterMap_map, h]

variable (params : FriParams) (shape : ClaimShape) (commitments : Array D)
  (points values : Array EF) (proof : FriProof F EF D InputProof CommitProof)

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The message of a folding round of the opening proof. -/
private theorem messages_succ_of_lt {i : ℕ} (hi : i < numRounds params shape) :
    messages params shape commitments points values proof (i + 1) =
      .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]) := by
  rw [messages, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
    Nat.add_sub_cancel]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The message of the opening proof after the folding rounds. -/
private theorem messages_of_gt {j : ℕ} (hj : numRounds params shape < j) :
    messages params shape commitments points values proof j =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
  rw [messages, ite_eq_right (by omega), ite_eq_right (by omega)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- From its second round on, the messages of the opening proof do not depend
on the statement. -/
private theorem messages_succ_congr (commitments' : Array D) (points' values' : Array EF)
    (j : ℕ) :
    messages params shape commitments points values proof (j + 1) =
      messages params shape commitments' points' values' proof (j + 1) := by
  rw [messages, messages, ite_eq_right (Nat.succ_ne_zero j), ite_eq_right (Nat.succ_ne_zero j)]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The messages of the opening proof beyond its last round are the last one. -/
private theorem messages_min (j : ℕ) :
    messages params shape commitments points values proof (min j (numRounds params shape + 1)) =
      messages params shape commitments points values proof j := by
  rcases Nat.lt_or_ge (numRounds params shape + 1) j with h | h
  · rw [min_eq_right h.le, messages_of_gt _ _ _ _ _ _ (Nat.lt_succ_self _),
      messages_of_gt _ _ _ _ _ _ (by omega)]
  · rw [min_eq_left h]

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [DecidableEq D] [DecidableEq F]
  [DecidableEq EF] in
/-- The message of a folding round of the opening proof holds a digest. -/
private theorem digestsIn_messages_ne_nil {i : ℕ} (hi : i < numRounds params shape) :
    digestsIn (messages params shape commitments points values proof (i + 1)) ≠ [] := by
  rw [messages_succ_of_lt _ _ _ _ _ _ hi]
  exact List.cons_ne_nil (proof.commitPhaseCommits.getD i default) _

end Messages

/-! ## The run of the executable checks -/

section Run

omit [DecidableEq F] [DecidableEq EF] in
/-- **The executable checks make the model verifier accept.** Let the state of
the idealised challenger be in round `2` of a chain whose rounds from `2` on
hold what the verifier absorbs, and let the checks that follow the lookup
challenges pass. Then the first domain of the opening exists in the field, no
committed column is shorter than the final height, the out-of-domain point is
usable, the constraint checks pass, the model verifier of the opening protocol
accepts against `f` on the challenges of the chain, and the proof-of-work
numbers of the chain are zero. -/
private theorem run_of_check (M : StarkModel F EF K) (sys : System F D)
    (f : ∀ x, SAns F EF D K slots width x)
    (proof : Proof F EF D (Array (List D)) (Array (List D)))
    (hshape : Stark.shapeOk sys proof = true) {shape : ClaimShape}
    (hsh : ∀ ζ, claimShape (openingClaims sys proof ζ) = shape)
    {ms : ℕ → RawMsg F EF D} {s : UState F EF D} {cur : RawMsg F EF D} (β γ acc : EF) {α ζ : EF}
    (hα : α = Function.surjInv M.surj (answer f ms 2).field)
    (hζ : ζ = Function.surjInv M.surj (answer f ms 3).field)
    (hs : UAt ms s 2 cur false 0) (h2 : ms 2 = cur ++ secondMessage proof)
    (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof ζ)).toList.map .ext)
    (h5 : ∀ j, ms (5 + j) = messages sys.fri shape #[] #[] #[] proof.openingProof (j + 1))
    (hcheck : checkAfterChallenges (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel) sys
      proof s β γ acc = true) :
    ∃ htwo : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F),
      (∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup) ∧
      zetaOk proof ζ = true ∧ constraintsOk sys proof β γ acc α ζ = true ∧
      ((modelParams M.toFieldModel sys.fri shape (M.wellFormed sys.fri shape htwo)).verifyWith
        (modelProof M.toFieldModel sys.fri shape proof.openingProof)
        (fun j => view M.toFieldModel sys.fri shape (messages sys.fri shape
          ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
          (claimValues (openingClaims sys proof ζ)) proof.openingProof j))
        (answer f ms 4).field
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
  obtain ⟨hz, hc, -, hfs, ch, hw, hα, hβ, hpow, hidx⟩ :=
    checkAfterChallenges_ufree M f (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) sys proof hshape β γ acc hs h2 h3 h4
      (fun i hi => by
        rw [hsh'] at hi
        rw [h5 i, messages_succ_of_lt _ _ _ _ _ _ hi])
      (by rw [hsh', h5, messages_of_gt _ _ _ _ _ _ (Nat.lt_succ_self _)]) hcheck
  rw [hsh'] at hfs hw hβ hpow hidx
  -- The shape check of the opening proof: the first domain and the final height.
  obtain ⟨htwo, hfinal⟩ : logMaxHeight sys.fri.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F) ∧
      ∀ m ∈ shape.flatten, sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup := by
    have h := hfs
    simp only [Fri.shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1.1.1.1.1.1.1.1.2, fun m hm => (h.1.1.1.1.1.1.1.1.1.1.1.2 m hm).2⟩
  obtain ⟨hpowOk, hmc⟩ := modelChecks_of_verifyWith M.toFieldModel sys.fri shape
    (M.wellFormed sys.fri shape htwo) f hfs hw
  refine ⟨htwo, hfinal, hz, hc, ?_, (hpow hpowOk).1, (hpow hpowOk).2⟩
  refine Eq.trans (congrArg (OracleComp.run f) ?_)
    (((modelParams M.toFieldModel sys.fri shape _).run_verifyWith f _ _ _ _ _).trans hmc)
  congr 1
  · rw [hα]
    exact (Function.surjInv_eq M.surj _).symm
  · funext i
    rw [hβ, Transcript.getD_map_range, apply_ite M.ext.toModel, M.ext.map_zero,
      Function.surjInv_eq M.surj]
  · funext k
    rw [hidx, Transcript.getD_map_range,
      ite_eq_left (show k.val < sys.fri.numQueries from k.isLt)]

end Run

/-! ## The executable checks on the view of a proof -/

section Check

variable {InputProof CommitProof : Type}

/-- A proof without its commitment proofs: the same fields, with an empty
opening proof. -/
private def forgetProofs (proof : Proof F EF D InputProof CommitProof) :
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
/-- **The executable checks pass on the view of a proof.** A proof with the
header, the commitments and the lookup sums of a view, that has the right shape
and passes the constraint checks for the representations of the challenges of
the view, witnesses `Check` for its opened values. -/
private theorem check_of_proof (M : StarkModel F EF K) (sys : System F D)
    (v : ShardView F EF D K) (proof : Proof F EF D InputProof CommitProof)
    (h1 : proof.active = v.hdr.active) (h2 : proof.stage1Commit = v.hdr.stage1Commit)
    (h3 : proof.stage2Commit = v.stage2) (h4 : proof.quotientCommit = v.quot)
    (h5 : proof.intermediateAccumulators = v.accs) (h6 : proof.logDegrees = v.hdr.logDegrees)
    (hshape : Stark.shapeOk sys proof = true)
    (hc : constraintsOk sys proof (rep M v.β) (rep M v.γ) v.acc0 (rep M v.α) (rep M v.ζ) = true)
    (hz : zetaOk proof (rep M v.ζ) = true) :
    v.Check M sys (claimValues (openingClaims sys proof (rep M v.ζ))) :=
  ⟨forgetProofs proof, h1, h2, h3, h4, h5, h6, hshape, rfl, hc, hz⟩

end Check

/-! ## What a failing constraint reads of the committed rows -/

section Rows

variable {M : StarkModel F EF K} {sys : System F D} {θ : ℝ} {com com' : Compiled.Committed K D}

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The base-field rows under a root only depend on the committed rows under
that root. -/
private theorem baseRows_congr (M : StarkModel F EF K) {root : D} (h : com root = com' root) :
    M.baseRows com root = M.baseRows com' root := by
  funext dims mi i
  unfold StarkModel.baseRows
  rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The polynomial a column under a root decodes to only depends on the
committed rows under that root. -/
private theorem colPoly_congr (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ) {root : D}
    (h : com root = com' root) (dims : Array Dimensions) (mi col ht : ℕ) :
    M.colPoly lb θ com root dims mi col ht = M.colPoly lb θ com' root dims mi col ht := by
  unfold StarkModel.colPoly StarkModel.colWord
  rw [h]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The row of a circuit at a point does not read the quotient columns, and
reads the committed rows only under the commitments to the main, the lookup and
the fixed traces. -/
private theorem pointRow_shardCols_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} (quot' : D) (h1 : com stage1 = com' stage1)
    (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) (c : Circuit F)
    (n : ℕ) (g : K) (pos ci : ℕ) (publics : Array K) (x : K) :
    pointRow c n g (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics x =
      pointRow c n g (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci)
        publics x := by
  have hmain : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).main =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).main :=
    funext fun j => colPoly_congr M _ _ h1 _ _ _ _
  have hstage2 : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).stage2 =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).stage2 :=
    funext fun j => colPoly_congr M _ _ h2 _ _ _ _
  have hpre : (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).pre =
      (shardCols M sys θ com' active logDegrees stage1 stage2 quot' pos ci).pre := by
    funext j
    unfold shardCols
    dsimp only
    cases hpc : sys.preprocessedCommit with
    | none => rfl
    | some root => exact colPoly_congr M _ _ (h3 root hpc) _ _ _ _
  unfold pointRow
  rw [hmain, hstage2, hpre]

omit [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- Whether a constraint fails does not depend on the commitment to the
quotients, and depends on the committed rows only under the commitments to the
main, the lookup and the fixed traces. -/
private theorem constraintFail_congr {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot quot' : D} {β γ acc0 : K} {accs : Array K}
    (h1 : com stage1 = com' stage1) (h2 : com stage2 = com' stage2)
    (h3 : ∀ root, sys.preprocessedCommit = some root → com root = com' root) :
    ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs ↔
      ConstraintFail M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
  have hvals : rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs =
      rowVals M sys θ com' active logDegrees stage1 stage2 quot' β γ acc0 accs := by
    funext pos ci x
    unfold rowVals
    rw [pointRow_shardCols_congr quot' h1 h2 h3]
  unfold ConstraintFail
  rw [hvals]

end Rows

/-! ## The committed rows a chain reads -/

section Committed

variable {M : StarkModel F EF K} {sys : System F D} {msgs : List (IMsg F EF D K)}

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- A commitment of a shard is the commitment to its main traces, to its lookup
traces, to its quotients or to the fixed traces. -/
private theorem mem_commitments {v : ShardView F EF D K} {root : D}
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
/-- **The rows a chain reads under the commitments of its shard are those of
the log**, when the messages of rounds `0`, `2` and `3` are read with the rows
of the log at the commitments they hold. -/
private theorem comOf_eq {v : ShardView F EF D K} {c : Compiled.Committed K D}
    (h0 : ∀ root, root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root →
      comAt msgs 0 root = c root)
    (h2 : comAt msgs 2 v.stage2 = c v.stage2) (h3 : comAt msgs 3 v.quot = c v.quot) {root : D}
    (hroot : root = v.hdr.stage1Commit ∨ root = v.stage2 ∨ root = v.quot ∨
      sys.preprocessedCommit = some root) : comOf sys v msgs root = c root := by
  unfold comOf
  by_cases h : root = v.hdr.stage1Commit ∨ sys.preprocessedCommit = some root
  · rw [ite_eq_left h]
    exact h0 root h
  · rw [ite_eq_right h]
    by_cases h' : root = v.stage2
    · rw [ite_eq_left h', h']
      exact h2
    · rw [ite_eq_right h']
      obtain rfl : root = v.quot := by tauto
      exact h3

omit [DecidableEq K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The root of an input batch of the statement of the opening of a shard is a
commitment of the shard. -/
private theorem inputRoots_mem_commitments (M : StarkModel F EF K) (v : ShardView F EF D K)
    (points values : Array EF) (b : Fin (v.shape M sys).length) :
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
/-- The commitments of the opening claims of a proof. -/
private theorem commitments_openingClaims {InputProof CommitProof : Type}
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) :
    (openingClaims sys proof ζ).map (·.commitment) =
      #[proof.stage1Commit, proof.stage2Commit, proof.quotientCommit] ++
        match sys.preprocessedCommit with
        | some c => #[c]
        | none => #[] := by
  unfold openingClaims
  cases sys.preprocessedCommit <;> simp

omit [Inhabited D] in
/-- **The base-field rows at an opened row.** Let a prefix of a log without a
collision hold an opening of rows of base-field elements, under a root at which
`com` reads the rows of the log. Then the base-field rows of `com` at the
opened row of each matrix are the rows the prefix commits to. -/
private theorem baseRows_of_opens (M : StarkModel F EF K)
    {l l₁ : Log (SAns F EF D K slots width)} (hl₁ : l₁ <+: l)
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

end Committed

/-! ## The opening protocol of a chain -/

section Opening

variable {M : StarkModel F EF K} {sys : System F D} {θ : ℝ} {msgs : List (IMsg F EF D K)}
  {chals : List (UAns K slots width)} {v : ShardView F EF D K}

omit [DecidableEq F] [DecidableEq EF] in
/-- The opening protocol read off a chain, without its proof-of-work samples,
is the transcript of its messages and its challenges. -/
private theorem ungrind_pcsT (hs : Supported M sys θ v) (j : ℕ) :
    ungrind (pcsT msgs chals hs j) =
      mkT (pcsMsg msgs hs) (fun i =>
        (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pcsT, PcsRbr.ungrind_snoc, ih, mkT]

omit [DecidableEq F] [DecidableEq EF] in
/-- The proof-of-work checks of the opening protocol read off a chain pass when
the first number of the answer of every round, reduced to the bits of the
round, is zero. -/
private theorem powPasses_pcsT (hs : Supported M sys θ v) (j : ℕ) :
    PowPasses (pcsT msgs chals hs j) ↔
      ∀ i < j, (ansAt chals (4 + i)).bits 0 (powBits sys.fri (v.shape M sys) i) = 0 := by
  induction j with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩
  | succ j ih =>
    rw [pcsT, PcsRbr.powPasses_snoc, ih]
    constructor
    · rintro ⟨h, hj⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hj
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h j (Nat.lt_succ_self j)⟩

omit [DecidableEq F] [DecidableEq EF] in
/-- **The opening protocol read off a chain accepts.** Let the model verifier
accept the raw messages `pm` of the opening protocol on the challenges read off
the answers `ans` of the chain, and leave a log without a collision. Let the
chain hold these messages from round `4` on, the first one for the commitments,
the opening points and the opened values of the shard. Let the base-field rows
the chain reads agree with the rows of the final log at the rows the queries
open, and the rows read for the commitment of every folding round be those of
the final log. Then the transcript of the opening protocol read off the chain is
accepted. -/
private theorem accepts_pcsT (hs : Supported M sys θ v) {Mq : Type} {Cq : ℕ → Type}
    [DecidableEq (FSQuery Mq Cq (HashQuery K D))]
    {pf : Compiled.Proof K D hs.params.batches hs.params.queries}
    {l' l₁ : Log (MerkleAnswer Mq Cq K D)} (pm : ℕ → RawMsg F EF D)
    (ans : ℕ → UAns K slots width)
    (hans : ∀ j < 4 + (hs.params.rounds + 2), ansAt chals j = ans j)
    (hmin : ∀ j, pm (min j (hs.params.rounds + 1)) = pm j)
    (h0 : pm 0 = firstMessage (v.commitments sys)
      (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs))
    (hraw : ∀ k ≤ hs.params.rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1))
    (hrun : Outcome (hs.params.verifyWith (M := Mq) (C := Cq) pf
      (fun j => view M.toFieldModel sys.fri (v.shape M sys) (pm j))
      (ans 4).field (fun i => if i < hs.params.rounds then (ans (5 + i)).field else 0)
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
    Accepts hs.params.ldt hs.params.shift
      (ungrind (pcsT msgs chals hs (hs.params.rounds + 2))) := by
  -- The challenges of the opening protocol, and what the verifier reads of them.
  have hα : alphaOf (mkT pm (fun i =>
      (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2)
      (hs.params.rounds + 2)) = (ans 4).field := by
    rw [alphaOf_mkT, field_pcsChal _ _ _ _ (Nat.zero_le _), hans (4 + 0) (by omega)]
  have hβ : betasOf (mkT pm (fun i =>
      (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2)
      (hs.params.rounds + 2)) =
      fun i => if i < hs.params.rounds then (ans (5 + i)).field else 0 := by
    funext i
    rw [betasOf_mkT]
    rcases Nat.lt_trichotomy i hs.params.rounds with hi | rfl | hi
    · rw [ite_eq_left (by omega), ite_eq_left hi, field_pcsChal _ _ _ _ (Nat.succ_le_of_lt hi),
        hans (4 + (i + 1)) (by omega), show 4 + (i + 1) = 5 + i by omega]
    · rw [ite_eq_left (Nat.lt_succ_self _), ite_eq_right (Nat.lt_irrefl _),
        field_pcsChal_of_not_le _ _ _ _ (Nat.not_succ_le_self _)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hq : (fun k => hs.params.indexOf (queriesOf (mkT pm (fun i =>
      (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2)
      (hs.params.rounds + 2)) k)) =
      fun k => (ans (5 + hs.params.rounds)).bits
        (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) hs.params.n := by
    funext k
    rw [queriesOf_mkT, indexOf_points_pcsChal _ _ _ _ (Nat.not_succ_le_self _),
      show powBits sys.fri (v.shape M sys) (hs.params.rounds + 1) = sys.fri.queryPowBits from
        powBits_last sys.fri (v.shape M sys),
      hans (4 + (hs.params.rounds + 1)) (by omega),
      show 4 + (hs.params.rounds + 1) = 5 + hs.params.rounds by omega]
  have hmsg : (fun j => view M.toFieldModel sys.fri (v.shape M sys) (Compiled.msgAt (mkT pm
      (fun i => (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2)
      (hs.params.rounds + 2)) j)) =
      fun j => view M.toFieldModel sys.fri (v.shape M sys) (pm j) := by
    funext j
    rw [msgAt_mkT, hmin]
  have hacc := hs.params.accepts_of_outcome_verifyWith_view_com (pf := pf) (l := l') (l' := l₁)
    (view M.toFieldModel sys.fri (v.shape M sys))
    (mkT pm (fun i =>
      (pcsChal hs.params (powBits sys.fri (v.shape M sys)) i (ansAt chals (4 + i))).2)
      (hs.params.rounds + 2))
    (by rw [hmsg, hα, hβ, hq]; exact hrun) hl (M.baseRows (comOf sys v msgs))
    (fun b k mi d hd => by
      rw [congrFun hq k, msgAt_mkT, Nat.zero_min]
      exact hc b k mi d hd)
  rw [mapIdx_mkT] at hacc
  rw [ungrind_pcsT]
  refine accepts_mkT_congr ?_ (fun k hk => ?_) hacc
  · show (hs.params.read 0 (view M.toFieldModel sys.fri (v.shape M sys) (firstMessage
      (v.commitments sys) (shapePoints (F := F) (v.shape M sys) (rep M v.ζ)) (valuesOf msgs)))
      (M.baseRows (comOf sys v msgs))).claims = _
    rw [← h0]
    rfl
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

end Opening

/-! ## The statement -/

/-- **The statement, for a chain given by its messages.** `shard_good` for
messages `ms` that satisfy the equations of the chain of the proof, a header
with the activation, the commitment and the heights of the proof, and a run of
the model verifier on the challenges of the chain. The model verifier is that
of a first domain that exists in the field (`htwo`); the rest of what makes the
shape of the opening supported is derived here from the accepting checks. -/
private theorem shard_good_aux (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D)
    (θ : ℝ) (B : Bounds) (r : ℕ) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys V θ B r l) {f : ∀ x, SAns F EF D K slots width x}
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a) {l' l₁ : Log (SAns F EF D K slots width)}
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
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UState F EF D) {ζ : EF}
    (hβ : β = Function.surjInv M.surj (answer f ms 0).field)
    (hγ : γ = Function.surjInv M.surj (answer f ms 1).field)
    (hζ : ζ = Function.surjInv M.surj (answer f ms 3).field) (h0 : ms 0 = m0)
    (h2 : ms 2 = .ext γ :: (mid ++ secondMessage proof))
    (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof ζ)).toList.map .ext)
    (h5 : ∀ j, ms (5 + j) = messages sys.fri shape #[] #[] #[] proof.openingProof (j + 1))
    (hs : UAt ms s 2 (.ext γ :: mid) false 0) (hacc : acc = (claimsAccumulator β γ claims).2)
    (hcheck : checkAfterChallenges (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel) sys
      proof s β γ acc = true)
    {b : Bool} {a : K} {bF : ℕ → K} {idx : Fin sys.fri.numQueries → ℕ}
    (ha : a = (answer f ms 4).field)
    (hbF : ∀ i, bF i = if i < R then (answer f ms (5 + i)).field else 0)
    (hidx : ∀ k, idx k = (answer f ms (5 + R)).bits
      (k.val + if sys.fri.queryPowBits = 0 then 0 else 1) (logMaxHeight sys.fri.logBlowup shape))
    (hrun : Outcome ((modelParams M.toFieldModel sys.fri shape
        (M.wellFormed sys.fri shape htwo)).verifyWith
      (modelProof M.toFieldModel sys.fri shape proof.openingProof)
      (fun j => view M.toFieldModel sys.fri shape (messages sys.fri shape
        ((openingClaims sys proof ζ).map (·.commitment)) (claimPoints (openingClaims sys proof ζ))
        (claimValues (openingClaims sys proof ζ)) proof.openingProof j)) a bF idx) l' b l₁) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  -- The chain has at most `r` rounds.
  have hr : 4 + (R + 2) ≤ r := by
    have hle : R ≤ logMaxHeight sys.fri.logBlowup shape := hR ▸ Nat.sub_le _ _
    omega
  -- The chain, read against the log, is doomed.
  have hd := sdoomed_of_goodLog hgood _ hr (hsup.of_prefix hl₁)
  rw [fsTranscript_eq_mkT] at hd hsup
  obtain ⟨msgs, chals, hlen, hraw, hcom, hans, hment, hdl⟩ :
      ∃ (msgs : List (IMsg F EF D K)) (chals : List (UAns K slots width)),
        msgs.length = 4 + (R + 2) ∧ (∀ j < msgs.length, rawAt msgs j = ms j) ∧
        (∀ j < msgs.length, comAt msgs j = (readMsg B (ms j) (committedRow l)).2) ∧
        (∀ j < msgs.length, ansAt chals j = answer f ms j) ∧
        (∀ j < msgs.length, Mentions l₁ j (ms j)) ∧ sdoomedL M sys V θ B msgs chals := by
    have hlen := Transcript.length_msgs
      ((mkT (C := UChal K slots width) ms (answer f ms) (4 + (R + 2))).mapIdx (interp B r l))
    exact ⟨_, _, hlen, fun j hj => rawAt_interp B r l ms _ (hlen ▸ hj),
      fun j hj => comAt_interp B r l ms _ (hlen ▸ hj) (by omega),
      fun j hj => by
        rw [mapIdx_mkT]
        exact ansAt_chalsOf_mkT _ _ (hlen ▸ hj),
      fun j hj => mentions_of_supports_mkT hsup j (hlen ▸ hj), hd⟩
  clear hd hsup
  have hfield : ∀ j < msgs.length, fieldAt chals j = (answer f ms j).field := fun j hj =>
    congrArg UAns.field (hans j hj)
  -- The challenges of the run are the representations of those of the chain.
  have hβ' : β = rep M (fieldAt chals 0) := by rw [hβ, hfield 0 (by omega)]; rfl
  have hγ' : γ = rep M (fieldAt chals 1) := by rw [hγ, hfield 1 (by omega)]; rfl
  have hζ' : ζ = rep M (fieldAt chals 3) := by rw [hζ, hfield 3 (by omega)]; rfl
  have hα : rep M (fieldAt chals 2) = Function.surjInv M.surj (answer f ms 2).field := by
    rw [hfield 2 (by omega)]
    rfl
  subst hsh hR ha hβ' hγ' hζ' hacc
  obtain rfl : bF = _ := funext hbF
  obtain rfl : idx = _ := funext hidx
  -- The executable checks, and the verdict of the model verifier.
  obtain ⟨_, hfinal, hz, hc, hrunf, hpowC, hpowQ⟩ := run_of_check M sys f proof hshape
    (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) _ _ _ hα hζ
    hs h2 h3 h4 h5 hcheck
  obtain rfl : b = true := (hrun.run_eq hf).symm.trans hrunf
  -- The shape is supported.
  have hheight := logMaxHeight_starkShape_le hheightOk hshape M.extData.d
  have hmargin : ∀ m ∈ (starkShape sys M.extData.d proof.active proof.logDegrees).flatten,
      StrictMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ :=
    fun m hm => M.strictMargin_coset ((CertiFri.Exec.le_logMaxHeight hm).trans htwo) hθ
  -- The view of the chain.
  have hactive : proof.active.size = sys.circuits.size := by
    have h := hshape
    simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    exact h.1.1.1.1.1.1.1.1.1.1.2
  have hsv : Supported M sys θ (viewOf M msgs chals
      ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) :=
    ⟨htwo, hfinal, hmargin, hactive, hheight⟩
  have hlen' : msgs.length = 4 + (hsv.params.rounds + 2) := hlen
  have hv2 : proof.stage2Commit = (digestsIn (rawAt msgs 2)).getD 0 default := by
    rw [hraw 2 (by omega), h2, digestsIn_second _ hmid proof]
    rfl
  have hv3 : proof.quotientCommit = (digestsIn (rawAt msgs 3)).getD 0 default := by
    rw [hraw 3 (by omega), h3]
    rfl
  have hva : proof.intermediateAccumulators = ((extsOf (rawAt msgs 2)).drop 1).toArray := by
    rw [hraw 2 (by omega), h2, extsOf_second _ hmid proof]
    rfl
  have hvals : valuesOf msgs =
      claimValues (openingClaims sys proof (rep M (fieldAt chals 3))) := by
    rw [valuesOf, hraw 4 (by omega), h4, extsOf_map_ext]
  -- The rows the chain reads under the commitments of the shard are those of the log.
  have hcol : ¬ LogCollision hashObs l := not_logCollision_of_not_hasBad_hit hgood.2
  have hc0 : ∀ root, root = proof.stage1Commit ∨ sys.preprocessedCommit = some root →
      comAt msgs 0 root = committedRow l root := by
    intro root hroot
    rw [hcom 0 (by omega), h0]
    exact readMsg_snd_of_mem B _ (hroot.elim (fun h => h ▸ hdig) (hdigFixed root))
  have hc2 : comAt msgs 2 ((digestsIn (rawAt msgs 2)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 2)).getD 0 default) := by
    rw [hcom 2 (by omega), hraw 2 (by omega)]
    exact readMsg_snd_of_mem B _ (getD_zero_mem_digestsOf B
      (by rw [h2, digestsIn_second _ hmid proof]; exact List.cons_ne_nil _ _))
  have hc3 : comAt msgs 3 ((digestsIn (rawAt msgs 3)).getD 0 default) =
      committedRow l ((digestsIn (rawAt msgs 3)).getD 0 default) := by
    rw [hcom 3 (by omega), hraw 3 (by omega)]
    exact readMsg_snd_of_mem B _ (getD_zero_mem_digestsOf B
      (by rw [h3]; exact List.cons_ne_nil proof.quotientCommit []))
  have hcomOf : ∀ root, (root = proof.stage1Commit ∨ root = _ ∨ root = _ ∨
      sys.preprocessedCommit = some root) → comOf sys (viewOf M msgs chals
        ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩) msgs root =
        committedRow l root := fun root h => comOf_eq hc0 hc2 hc3 h
  -- The raw messages of the opening protocol.
  obtain ⟨pm, hpm⟩ : ∃ pm : ℕ → RawMsg F EF D, pm = messages sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      ((openingClaims sys proof (rep M (fieldAt chals 3))).map (·.commitment))
      (claimPoints (openingClaims sys proof (rep M (fieldAt chals 3))))
      (claimValues (openingClaims sys proof (rep M (fieldAt chals 3)))) proof.openingProof :=
    ⟨_, rfl⟩
  rw [← hpm] at hrun
  have hpm0 : pm 0 = firstMessage (ShardView.commitments sys (viewOf M msgs chals
      ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩))
      (shapePoints (F := F) (starkShape sys M.extData.d proof.active proof.logDegrees)
        (rep M (fieldAt chals 3))) (valuesOf msgs) := by
    rw [hpm]
    refine (ite_eq_left rfl).trans ?_
    rw [commitments_openingClaims, claimPoints_openingClaims sys proof hshape, ← M.degree_eq,
      ← hvals, hv2, hv3]
    rfl
  have hpmraw : ∀ k ≤ hsv.params.rounds, rawAt msgs (4 + (k + 1)) = pm (k + 1) := fun k hk => by
    rw [hraw _ (by omega), show 4 + (k + 1) = 5 + k by omega, h5 k, hpm]
    exact messages_succ_congr _ _ _ _ _ _ _ _ _ _
  have hpmmin : ∀ j, pm (min j (hsv.params.rounds + 1)) = pm j := fun j => by
    rw [hpm]
    exact messages_min _ _ _ _ _ _ j
  -- The opening protocol accepts.
  have hacc := accepts_pcsT hsv pm (answer f ms) (fun j hj => hans j (by omega)) hpmmin hpm0
    hpmraw hrun (fun h => hcol (h.of_prefix hl₁))
    (fun b k mi d hd => by
      have hopen := (hsv.params.outcome_verifyWith hrun).1 b k
      rw [hpm0] at hopen ⊢
      have h := baseRows_of_opens M hl₁ hcol
        (hcomOf _ (mem_commitments (inputRoots_mem_commitments M _ _ _ b))) hopen hd
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
      have hmem := getD_zero_mem_digestsOf B (m := pm (k + 1))
        (by rw [hpm]; exact digestsIn_messages_ne_nil _ _ _ _ _ _ hk)
      rw [hcom _ hj, hms]
      refine (readMsg_snd_of_mem B _ hmem).trans ?_
      exact committedRow_of_mentions B r l hl₁ hgood.2 (hms ▸ hment _ hj) (by omega) hmem)
  -- The proof-of-work checks pass.
  have hpow : PowPasses (pcsT msgs chals hsv (hsv.params.rounds + 2)) := by
    refine (powPasses_pcsT hsv _).mpr fun i hi => ?_
    rw [hans (4 + i) (by omega)]
    rcases i with _ | i
    · exact bits_eq_zero _ _ (powBits_zero sys.fri _)
    · rcases Nat.lt_or_ge i hsv.params.rounds with hlt | hge
      · refine (congrArg (UAns.bits _ 0) (powBits_succ_of_lt sys.fri _ hlt)).trans ?_
        by_cases hb : sys.fri.commitPowBits = 0
        · exact bits_eq_zero _ _ hb
        · have h := hpowC hb i hlt
          rwa [show 5 + i = 4 + (i + 1) by omega] at h
      · obtain rfl : i = hsv.params.rounds := by omega
        refine (congrArg (UAns.bits _ 0) (powBits_last sys.fri _)).trans ?_
        by_cases hb : sys.fri.queryPowBits = 0
        · exact bits_eq_zero _ _ hb
        · have h : (answer f ms (5 + hsv.params.rounds)).bits 0 sys.fri.queryPowBits = 0 :=
            hpowQ hb
          rwa [show 5 + hsv.params.rounds = 4 + (hsv.params.rounds + 1) by omega] at h
  -- The state function gives the two conclusions.
  have hdec' : V.dec0 (rawAt msgs 0) = some pre := by rw [hraw 0 (by omega), h0]; exact hdec
  have e0 : M.ext.toModel (rep M (fieldAt chals 0)) = fieldAt chals 0 :=
    Function.surjInv_eq M.surj _
  have e1 : M.ext.toModel (rep M (fieldAt chals 1)) = fieldAt chals 1 :=
    Function.surjInv_eq M.surj _
  have hgl := good_of_sdoomedL hfixed hdl hdec' hpre
    (by rw [hraw 2 (by omega)]; exact hhdr) hsv hlen'
    (by
      rw [hvals]
      exact check_of_proof M sys _ proof rfl rfl hv2 hv3 hva rfl hshape hc hz)
    hpow hacc
  refine ⟨fun hfail => hgl ?_, fun hbal => ?_⟩
  · rw [e0, e1, hv2, hv3, hva] at hfail
    exact (constraintFail_congr
      (baseRows_congr M (hcomOf _ (.inl rfl)).symm)
      (baseRows_congr M (hcomOf _ (.inr (.inl rfl))).symm)
      fun root hroot => baseRows_congr M (hcomOf _ (.inr (.inr (.inr hroot)))).symm).mp hfail
  · rw [e0, e1]
    have h := balance_of_sdoomedL hdl hdec' hpre (by omega)
      (by rw [hcom 0 (by omega), h0]; exact hbal)
    rwa [hcom 0 (by omega), h0] at h

/-- **An accepted proof in a good log has no failing constraint.** Nothing is
assumed about the shape of the opening of the proof: that it is supported
follows from the accepting checks, for a system none of whose fixed traces is
taller than the largest trace it supports (`hheightOk`) and an agreement `θ`
inside the unique-decoding radius (`hθ`). The log is good for the rounds of the
longest chain (`hr`). -/
theorem shard_good (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D) (θ : ℝ)
    (B : Bounds) (r : ℕ) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk)
    (hθ : 1 + (1 / 2 : ℝ) ^ sys.fri.logBlowup < 2 * θ) {l : Log (SAns F EF D K slots width)}
    (hgood : GoodLog M sys V θ B r l) {f : ∀ x, SAns F EF D K slots width x}
    (hf : ∀ x y, l.dlookup x = some y → f x = y)
    (proof : Proof F EF D (Array (List D)) (Array (List D))) (m0 mid : RawMsg F EF D)
    (hmid : ∀ o ∈ mid, ∃ a : F, o = .base a)
    -- The queries of the verification are in the log.
    {l₀ l₁ : Log (SAns F EF D K slots width)} {b : Bool}
    (hout : Outcome (shardComp M sys proof m0 mid) l₀ b l₁) (hl₁ : l₁ <+: l)
    -- The preamble and the header.
    {pre : BatchPreamble F D} (hdec : V.dec0 m0 = some pre) (hpre : PreOk sys B pre)
    {hdr : ShardHeader F D}
    (hhdr : pre.headers[V.shard (nextMsg M sys proof m0 mid 2
      (fsTranscriptA f (nextMsg M sys proof m0 mid) 2))]? = some hdr)
    (hactive : hdr.active = proof.active) (hstage1 : hdr.stage1Commit = proof.stage1Commit)
    (hlogs : hdr.logDegrees = proof.logDegrees)
    (hdig : proof.stage1Commit ∈ digestsOf B m0)
    (hdigFixed : ∀ c, sys.preprocessedCommit = some c → c ∈ digestsOf B m0)
    -- The log is good for the rounds of every chain.
    (hr : 4 + (TwoAdicOps.twoAdicity (F := F) + 2) ≤ r)
    -- The run of the executable verifier, from the lookup challenges on.
    (hshape : Stark.shapeOk sys proof = true) (β γ acc : EF) (s : UState F EF D)
    (hβ : β = Function.surjInv M.surj
      (answer f (fun j => nextMsg M sys proof m0 mid j
        (fsTranscriptA f (nextMsg M sys proof m0 mid) j)) 0).field)
    (hγ : γ = Function.surjInv M.surj
      (answer f (fun j => nextMsg M sys proof m0 mid j
        (fsTranscriptA f (nextMsg M sys proof m0 mid) j)) 1).field)
    (hs : UAt (fun j => nextMsg M sys proof m0 mid j
      (fsTranscriptA f (nextMsg M sys proof m0 mid) j)) s 2 (.ext γ :: mid) false 0)
    (hacc : acc = (claimsAccumulator β γ hdr.claims).2)
    (hcheck : checkAfterChallenges (merkleMmcs (inputHasher M.toFieldModel (hasherOf f)))
      (merkleMmcs (friHasher M.toFieldModel (hasherOf f))) (uChallenger f M.toFieldModel) sys
      proof s β γ acc = true) :
    ¬ ConstraintFail M sys θ (M.baseRows (committedRow l)) proof.active proof.logDegrees
        proof.stage1Commit proof.stage2Commit proof.quotientCommit (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc)
        (proof.intermediateAccumulators.map M.ext.toModel) ∧
      (¬ Balanced (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre) →
        ((balPoly (allItems M sys θ (M.baseRows (readMsg B m0 (committedRow l)).2) pre)).eval
          (C (M.ext.toModel β))).eval (M.ext.toModel γ) ≠ 0) := by
  -- The header has the activation, the commitment and the heights of the proof.
  obtain ⟨act, stage1, logs, claims⟩ := hdr
  dsimp only at hactive hstage1 hlogs hacc
  subst hactive hstage1 hlogs
  have hlast := lastField_fsTranscriptA f (nextMsg M sys proof m0 mid)
  -- The checks passed, so the first domain of the opening exists in the field.
  obtain ⟨htwo, -⟩ := run_of_check M sys f proof hshape
    (shape := starkShape sys M.extData.d proof.active proof.logDegrees)
    (fun ζ => by rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]) β γ acc rfl rfl hs
    (show Observation.ext (rep M (lastField (fsTranscriptA f (nextMsg M sys proof m0 mid) 2))) ::
        (mid ++ secondMessage proof) = _ by
      rw [hlast 1, hγ]
      rfl)
    rfl
    (show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (lastField
        (fsTranscriptA f (nextMsg M sys proof m0 mid) 4))))).toList = _ by
      rw [hlast 3]
      rfl)
    (fun j => by
      rw [Nat.add_comm 5 j]
      rfl) hcheck
  -- The queries of the verification: the chain, then the model verifier.
  unfold shardComp at hout
  rw [dite_eq_left htwo, outcome_bind] at hout
  obtain ⟨t, l', hder, hver⟩ := hout
  have hfl₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y h =>
    hf x y (dlookup_of_prefix h hl₁)
  obtain rfl := hder.eq_fsTranscriptA fun x y h => hfl₁ x y (dlookup_of_prefix h hver.prefix)
  have hsup := (supports_of_outcome_deriveA hder).of_prefix hver.prefix
  rw [fsTranscriptA_eq_fsTranscript] at hsup
  have hfield : ∀ j < 4 + ((modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds + 2),
      fieldAt (chalsOf (fsTranscriptA f (nextMsg M sys proof m0 mid) (4 + ((modelParams
        M.toFieldModel sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).rounds + 2)))) j =
        (answer f (fun j => nextMsg M sys proof m0 mid j
          (fsTranscriptA f (nextMsg M sys proof m0 mid) j)) j).field := fun j hj =>
    congrArg UAns.field (ansAt_chalsOf_fsTranscriptA f _ hj)
  have hR : (modelParams M.toFieldModel sys.fri
      (starkShape sys M.extData.d proof.active proof.logDegrees)
      (M.wellFormed sys.fri _ htwo)).rounds =
      numRounds sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees) := rfl
  refine shard_good_aux M sys V θ B r hfixed hheightOk hθ hgood proof m0 mid hmid hl₁ hfl₁ hdec
    hpre
    (ms := fun j => nextMsg M sys proof m0 mid j (fsTranscriptA f (nextMsg M sys proof m0 mid) j))
    hhdr hdig hdigFixed rfl htwo rfl hr hsup hshape β γ acc s hβ hγ
    (congrArg (rep M) (hfield 3 (by omega))) rfl ?_ rfl ?_ (fun j => ?_) hs hacc hcheck
    (hfield 4 (by omega)) (fun i => ite_congr rfl (fun hi => hfield (5 + i) (by omega))
      fun _ => rfl)
    (fun k => congrArg (fun u : UAns K slots width => u.bits _ _)
      (ansAt_chalsOf_fsTranscriptA f _ (by omega))) hver
  · show Observation.ext (rep M (lastField (fsTranscriptA f (nextMsg M sys proof m0 mid) 2))) ::
      (mid ++ secondMessage proof) = _
    rw [hlast 1, hγ]
    rfl
  · show List.map Observation.ext (claimValues (openingClaims sys proof (rep M (lastField
      (fsTranscriptA f (nextMsg M sys proof m0 mid) 4))))).toList = _
    rw [hlast 3, hfield 3 (by omega)]
  · rw [Nat.add_comm 5 j]
    rfl

end CertiFri.Exec.Stark
