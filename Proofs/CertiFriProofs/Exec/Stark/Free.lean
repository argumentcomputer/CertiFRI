import CertiFriProofs.Exec.Transcript
import CertiFriProofs.Theory.Stark.Uniform

/-!
# The idealised challenger with uniform answers

The idealised challenger of `Exec/Setup.lean` (`freeChallenger`) reads its
challenges off answers whose type depends on the parameters of the opening
protocol. The STARK verifier is analysed with one answer type for every round
(`UAns`, `Theory/Stark/Uniform.lean`). This file defines the idealised
challenger over such answers and says what each of its operations returns, as
`Exec/Transcript.lean` does for `freeChallenger`.

## The challenger

`uChallenger f m` keeps what was absorbed, split into rounds: an absorption
after a squeeze closes the current round and starts the next. Every squeeze of
a round reads the one answer of the oracle `f` to the rounds so far and the
absorptions of the current round:

* `sampleExt` returns a representation of the field element of the answer;
* the `k`-th `sampleBits` of the round, asked for `b` bits, returns the `k`-th
  number of the answer reduced to `b` bits (`UAns.bits`).

So the field challenge, the proof-of-work bits and the query indices of a round
are independent uniform values.

## Results

* `UAt ms s i cur squeezed nbits`: the state `s` is in round `i` of the chain
  on the raw messages `ms`. The lemmas `UAt.observe`, `UAt.observeAll`,
  `UAt.observe_next`, `UAt.observeAll_next`, `UAt.sampleExt`, `UAt.sampleBits`,
  `UAt.checkWitness` and `UAt.sampleIndices` give the result of each operation
  and the state it leaves.
* `commitPhase_ufree`, `transcriptTail_ufree`: the challenges of
  `Fri.commitPhase` and of `Fri.transcriptTail`, started in any round of a
  chain, as answers of the chain.

## Not covered

Any concrete challenger. The oracle is a fixed function `f` here; there is no
probability.
-/

namespace CertiFri.Exec.Stark

open Oracle Fri CertiFri.Stark
open CertiFri.Exec.Transcript (answer)

/-- The challenge types of the STARK experiment: the same uniform answer in
every round. -/
abbrev UChal (K : Type) (slots width : ℕ) : ℕ → Type := fun _ => UAns K slots width

/-- The state of the idealised challenger: the number of closed rounds, their
raw messages, the absorptions of the current round, whether the current round
has been squeezed, and the number of samples of bits made in it. -/
structure UState (F EF D : Type) where
  /-- The number of closed rounds. -/
  round : ℕ
  /-- The raw messages of the closed rounds. -/
  hist : ℕ → RawMsg F EF D
  /-- What was absorbed in the current round. -/
  cur : RawMsg F EF D
  /-- Whether the current round has been squeezed. -/
  squeezed : Bool
  /-- The number of samples of bits made in the current round. -/
  nbits : ℕ

/-- The state before anything is absorbed. -/
def UState.init {F EF D : Type} : UState F EF D := ⟨0, fun _ => [], [], false, 0⟩

section Free

variable {F EF D K : Type} {slots width : ℕ}
  (f : ∀ x : FSQuery (RawMsg F EF D) (UChal K slots width) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (UChal K slots width) K D x)

/-- The answer of the oracle `f` for the current round of a state. -/
def uAnswer (s : UState F EF D) : UAns K slots width :=
  f (.chal (fsTranscript f s.hist s.round) s.cur)

variable [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]

/-- **The idealised challenger with uniform answers.** -/
noncomputable def uChallenger (m : FieldModel F EF K) : Challenger (UState F EF D) F EF D where
  observe s o :=
    if s.squeezed then ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], false, 0⟩
    else { s with cur := s.cur ++ [o] }
  sampleExt s :=
    (Function.surjInv m.surj (uAnswer f s).field, { s with squeezed := true })
  sampleBits s b :=
    ((uAnswer f s).bits s.nbits b, { s with squeezed := true, nbits := s.nbits + 1 })

variable {ms : ℕ → RawMsg F EF D}

/-- The state `s` is in round `i` of the chain on the messages `ms`: the closed
rounds are the rounds below `i` with their messages, the current round has
absorbed `cur`, it has been squeezed or not, and `nbits` samples of bits were
made in it. -/
structure UAt (ms : ℕ → RawMsg F EF D) (s : UState F EF D) (i : ℕ) (cur : RawMsg F EF D)
    (squeezed : Bool) (nbits : ℕ) : Prop where
  /-- The number of closed rounds. -/
  round : s.round = i
  /-- The messages of the closed rounds. -/
  hist : ∀ j < i, s.hist j = ms j
  /-- What the current round has absorbed. -/
  cur : s.cur = cur
  /-- Whether the current round has been squeezed. -/
  squeezed : s.squeezed = squeezed
  /-- The number of samples of bits of the current round. -/
  nbits : s.nbits = nbits

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K] in
/-- The initial state is in round `0`, with nothing absorbed. -/
theorem UAt.init : UAt ms (UState.init : UState F EF D) 0 [] false 0 :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl, rfl⟩

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K] in
/-- In a state that has absorbed the message of its round, the answer of the
oracle for the state is the answer of the round in the chain. -/
private theorem uAnswer_mk {i : ℕ} {hist : ℕ → RawMsg F EF D} (hh : ∀ j < i, hist j = ms j)
    (sq : Bool) (k : ℕ) :
    uAnswer f ⟨i, hist, ms i, sq, k⟩ = answer f ms i := by
  unfold uAnswer answer
  rw [Transcript.fsTranscript_congr f hh]

variable (m : FieldModel F EF K)

/-- Before the first squeeze of a round, an absorption extends the round. -/
theorem UAt.observe {s : UState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAt ms s i cur false 0) (o : Observation F EF D) :
    UAt ms ((uChallenger f m).observe s o) i (cur ++ [o]) false 0 := by
  have hs : (uChallenger f m).observe s o = { s with cur := s.cur ++ [o] } :=
    ite_eq_right (by rw [h.squeezed]; exact Bool.false_ne_true)
  rw [hs]
  exact ⟨h.round, h.hist, by rw [← h.cur], h.squeezed, h.nbits⟩

/-- Before the first squeeze of a round, absorbing a list extends the round. -/
theorem UAt.observeAll {s : UState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAt ms s i cur false 0) (l : List (Observation F EF D)) :
    UAt ms ((uChallenger f m).observeAll s l) i (cur ++ l) false 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have h' := ih (h.observe f m o)
    rwa [List.append_assoc] at h'

/-- After a squeeze, an absorption closes the round and starts the next. -/
theorem UAt.observe_next {s : UState F EF D} {i k : ℕ} (h : UAt ms s i (ms i) true k)
    (o : Observation F EF D) :
    UAt ms ((uChallenger f m).observe s o) (i + 1) [o] false 0 := by
  have hs : (uChallenger f m).observe s o =
      ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], false, 0⟩ :=
    ite_eq_left h.squeezed
  rw [hs]
  refine ⟨by rw [← h.round], fun j hj => ?_, rfl, rfl, rfl⟩
  show Function.update s.hist s.round s.cur j = ms j
  rw [h.round, h.cur]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [Function.update_of_ne hj.ne]
    exact h.hist j hj
  · rw [Function.update_self]

/-- After a squeeze, absorbing a nonempty list closes the round and starts the
next with that list. -/
theorem UAt.observeAll_next {s : UState F EF D} {i k : ℕ} (h : UAt ms s i (ms i) true k)
    {l : List (Observation F EF D)} (hl : l ≠ []) :
    UAt ms ((uChallenger f m).observeAll s l) (i + 1) l false 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l => exact (h.observe_next f m o).observeAll f m l

/-- A field challenge of a round is a representation of the field element of
the round's answer. -/
theorem UAt.sampleExt {s : UState F EF D} {i k : ℕ} {sq : Bool} (h : UAt ms s i (ms i) sq k) :
    ((uChallenger f m).sampleExt s).1 = Function.surjInv m.surj (answer f ms i).field ∧
      UAt ms ((uChallenger f m).sampleExt s).2 i (ms i) true k := by
  obtain ⟨r, hist, cur, sq', n⟩ := s
  obtain ⟨hr, hh, hc, hsq, hn⟩ := h
  dsimp only at hr hh hc hsq hn
  subst hr hc hsq hn
  refine ⟨?_, rfl, hh, rfl, rfl, rfl⟩
  show Function.surjInv m.surj (uAnswer f ⟨r, hist, ms r, sq', n⟩).field = _
  rw [uAnswer_mk f hh]

/-- The `k`-th sample of bits of a round is the `k`-th number of the round's
answer, reduced to the bits asked for. -/
theorem UAt.sampleBits {s : UState F EF D} {i k : ℕ} {sq : Bool} (h : UAt ms s i (ms i) sq k)
    (b : ℕ) :
    ((uChallenger f m).sampleBits s b).1 = (answer f ms i).bits k b ∧
      UAt ms ((uChallenger f m).sampleBits s b).2 i (ms i) true (k + 1) := by
  obtain ⟨r, hist, cur, sq', n⟩ := s
  obtain ⟨hr, hh, hc, hsq, hn⟩ := h
  dsimp only at hr hh hc hsq hn
  subst hr hc hsq hn
  refine ⟨?_, rfl, hh, rfl, rfl, rfl⟩
  show (uAnswer f ⟨r, hist, ms r, sq', n⟩).bits n b = _
  rw [uAnswer_mk f hh]

/-- The proof-of-work check of a round. The witness, if there is a check, ends
the message of the round. If the check passes, the first number of the round's
answer, reduced to the bits of the check, is zero. -/
theorem UAt.checkWitness {s : UState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : UAt ms s i cur false 0) (b : ℕ) (w : F)
    (hms : ms i = cur ++ if b = 0 then [] else [.base w]) :
    (((uChallenger f m).checkWitness s b w).1 = true → b ≠ 0 →
        (answer f ms i).bits 0 b = 0) ∧
      UAt ms ((uChallenger f m).checkWitness s b w).2 i (ms i) (decide (b ≠ 0))
        (if b = 0 then 0 else 1) := by
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

/-- The query indices of a round: the `t`-th sample is the number `k + t` of
the round's answer, where `k` samples of bits were made in the round before. -/
theorem UAt.sampleIndices {s : UState F EF D} {i k : ℕ} {sq : Bool}
    (h : UAt ms s i (ms i) sq k) (b count : ℕ) :
    (uChallenger f m).sampleIndices b count s =
      (List.range count).map fun t => (answer f ms i).bits (k + t) b := by
  induction count generalizing s k sq with
  | zero => rfl
  | succ count ih =>
    obtain ⟨hv, hs⟩ := h.sampleBits f m b
    rw [Challenger.sampleIndices, hv, ih hs, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun t _ => ?_)
    rw [Function.comp_apply, Nat.add_right_comm, Nat.add_assoc]

/-- **The commit phase with the idealised challenger**, started after a squeeze
of round `i₀`. If the message of round `i₀ + 1 + i` is the commitment of
folding round `i` followed by its witness when there is a check, the folding
challenges represent the field elements of the answers of the rounds
`i₀ + 1, …, i₀ + r`, the state is in round `i₀ + r` and has been squeezed, and
if every check passes the proof-of-work numbers of these answers are zero. -/
theorem commitPhase_ufree [Inhabited D] (cpb : ℕ) (commits : Array D) (witnesses : Array F)
    (r i₀ : ℕ)
    (hms : ∀ i < r, ms (i₀ + 1 + i) = .digest (commits.getD i default) ::
      (if cpb = 0 then [] else [.base (witnesses.getD i 0)]))
    {s : UState F EF D} {k : ℕ} (h : UAt ms s i₀ (ms i₀) true k) :
    (commitPhase (uChallenger f m) cpb commits witnesses r s).1 =
        ((List.range r).map fun i =>
          Function.surjInv m.surj (answer f ms (i₀ + 1 + i)).field).toArray ∧
      ((commitPhase (uChallenger f m) cpb commits witnesses r s).2.1 = true → cpb ≠ 0 →
        ∀ i < r, (answer f ms (i₀ + 1 + i)).bits 0 cpb = 0) ∧
      ∃ k', UAt ms (commitPhase (uChallenger f m) cpb commits witnesses r s).2.2 (i₀ + r)
        (ms (i₀ + r)) true k' := by
  induction r with
  | zero => exact ⟨rfl, fun _ _ _ hi => absurd hi (Nat.not_lt_zero _), k, h⟩
  | succ r ih =>
    obtain ⟨hβ, hpow, k', hs⟩ := ih fun i hi => hms i (Nat.lt_succ_of_lt hi)
    have e : i₀ + r + 1 = i₀ + 1 + r := Nat.add_right_comm i₀ r 1
    have h1 := hs.observe_next f m (.digest (commits.getD r default))
    rw [e] at h1
    obtain ⟨hw, h2⟩ := h1.checkWitness f m cpb (witnesses.getD r 0)
      (hms r (Nat.lt_succ_self r))
    obtain ⟨hv, h3⟩ := h2.sampleExt f m
    rw [← e] at h3
    refine ⟨?_, fun hok hc i hi => ?_, _, h3⟩
    · rw [commitPhase, hβ, hv, List.push_toArray, List.range_succ, List.map_append,
        List.map_singleton]
    · rw [commitPhase] at hok
      obtain ⟨hok₁, hok₂⟩ := Bool.and_eq_true_iff.mp hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hpow hok₁ hc i hi
      · exact hw hok₂ hc

/-- **The challenges of the opening proof with the idealised challenger.** Let
the state be in round `i₀`, with the message of that round absorbed and no
squeeze made. If the messages of the following rounds are those the opening
proof absorbs, the batching challenge represents the field element of the
answer of round `i₀`, folding challenge `i` that of round `i₀ + 1 + i`, and
query index `t` is the next number of the answer of the last round. If every
proof-of-work check passes, the proof-of-work numbers of the answers are
zero. -/
theorem transcriptTail_ufree [Inhabited D] (params : FriParams) (shape : ClaimShape)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) (i₀ : ℕ)
    {s : UState F EF D} (h : UAt ms s i₀ (ms i₀) false 0)
    (hmC : ∀ i < numRounds params shape,
      ms (i₀ + 1 + i) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]))
    (hmF : ms (i₀ + 1 + numRounds params shape) =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]))
    (hfinal : proof.finalPoly.size ≠ 0) :
    (transcriptTail (uChallenger f m) s params shape proof).alpha =
        Function.surjInv m.surj (answer f ms i₀).field ∧
      (transcriptTail (uChallenger f m) s params shape proof).betas =
        ((List.range (numRounds params shape)).map fun i =>
          Function.surjInv m.surj (answer f ms (i₀ + 1 + i)).field).toArray ∧
      ((transcriptTail (uChallenger f m) s params shape proof).powOk = true →
        (params.commitPowBits ≠ 0 → ∀ i < numRounds params shape,
          (answer f ms (i₀ + 1 + i)).bits 0 params.commitPowBits = 0) ∧
        (params.queryPowBits ≠ 0 →
          (answer f ms (i₀ + 1 + numRounds params shape)).bits 0 params.queryPowBits = 0)) ∧
      (transcriptTail (uChallenger f m) s params shape proof).indices =
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
  obtain ⟨hα, h1⟩ := h.sampleExt f m
  obtain ⟨hβ, hpowC, k, h2⟩ := commitPhase_ufree f m params.commitPowBits
    proof.commitPhaseCommits proof.commitPowWitnesses (numRounds params shape) i₀ hmC h1
  have h3 := h2.observeAll_next f m hne
  rw [e] at h3
  obtain ⟨hpowQ, h4⟩ := h3.checkWitness f m params.queryPowBits proof.queryPowWitness hmF
  have hidx := h4.sampleIndices f m (logMaxHeight params.logBlowup shape) params.numQueries
  refine ⟨hα, hβ, fun hpow => ?_, ?_⟩
  · obtain ⟨hpow₁, hpow₂⟩ := Bool.and_eq_true_iff.mp hpow
    exact ⟨hpowC hpow₁, hpowQ hpow₂⟩
  · exact congrArg List.toArray
      (hidx.trans (List.map_congr_left fun t _ => by rw [Nat.add_comm _ t]))

end Free

end CertiFri.Exec.Stark
