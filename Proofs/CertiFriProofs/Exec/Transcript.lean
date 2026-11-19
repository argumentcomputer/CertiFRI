import CertiFriProofs.Exec.Setup

/-!
# The transcript of the executable verifier and the Fiat–Shamir chain

The executable verifier derives its challenges by running a challenger
(`Fri.transcript`). The model derives them along a Fiat–Shamir chain: the
challenge of round `i` is the answer of the oracle to the transcript of the
first `i` rounds and the message of round `i` (`Oracle.fsTranscript`), and that
answer is a pair of proof-of-work bits and a challenge.

This file proves that the two agree for the idealised challenger
`freeChallenger` of `Exec/Setup.lean`.

* `transcript_free`: on a statement and a proof of the right shape, the
  challenges `Fri.transcript` computes with `freeChallenger` from the state
  `FreeState.init` are those of the chain `fsTranscript f ms (rounds + 2)` on
  the raw messages `ms = messages …`. The batching challenge represents
  `alphaOf` of the chain, folding challenge `i` represents `betasOf` at `i`
  (for every `i`: both are zero where there is no folding round), there is one
  query index per query and it is the index of the query point `queriesOf`
  gives, and if every proof-of-work check of the run passes then `PowPasses`
  holds of the chain.

The helpers are in the namespace `Exec.Transcript`.

* `answer f ms i` is the answer of the oracle in round `i` of the chain.
  `powPasses_fsTranscript`, `alphaOf_ungrind_fsTranscript`,
  `betasOf_ungrind_fsTranscript` and `queriesOf_ungrind_fsTranscript` express
  the model's accessors on a chain through these answers.
* `At ms s i cur k` says that the state `s` of the idealised challenger is in
  round `i` of the chain on `ms`. The lemmas `At.observe`, `At.observe_next`,
  `At.sampleExt`, `At.sampleBits_pow`, `At.sampleBits_query`,
  `At.checkWitness`, `At.sampleIndices` say what each operation of the
  challenger returns in such a state, and which state it leaves.
* `commitPhase_free` and `transcript_eq` give the challenges of
  `Fri.commitPhase` and `Fri.transcript` as answers of the chain, for any
  parameters `P` of the model.

## Assumptions

Of the shape check `shapeOk`, only one fact is used: the final polynomial has
the configured length, so it is not empty. Its first coefficient is what closes
the last folding round in the state of the challenger. The commitments and the
witnesses of the folding rounds are read with a default on both sides, so their
numbers do not matter here.

## Not covered

* Any other challenger than `freeChallenger`; in particular the challenger of
  the Plonky3 instantiation.
* The converse for the proof of work: that the checks of the run pass when
  those of the chain do.
* Probabilities. The oracle is a fixed function `f` here.
-/

namespace CertiFri.Exec

open Oracle Fri
open PcsRbr (Chal GrindChal)

namespace Transcript

/-! ## The answers of a chain -/

section Chain

variable {Msg X' : Type} {C : ℕ → Type} {Y' : X' → Type}
  (f : ∀ x : FSQuery Msg C X', FSAnswer C Y' x) (ms : ℕ → Msg)

/-- The answer of `f` in round `i` of the Fiat–Shamir chain on the messages
`ms`: its answer to the transcript of the first `i` rounds and the message of
round `i`. -/
def answer (i : ℕ) : C i :=
  f (.chal (fsTranscript f ms i) (ms i))

/-- The chain of `i + 1` rounds is the chain of `i` rounds, extended by the
message and the answer of round `i`. -/
theorem fsTranscript_succ (i : ℕ) :
    fsTranscript f ms (i + 1) = (fsTranscript f ms i).snoc (ms i) (answer f ms i) := rfl

variable {ms}

/-- The chain of `i` rounds reads the messages below `i` only. -/
theorem fsTranscript_congr {ms' : ℕ → Msg} {i : ℕ} (h : ∀ j < i, ms j = ms' j) :
    fsTranscript f ms i = fsTranscript f ms' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [fsTranscript, fsTranscript, ih fun j hj => h j (Nat.lt_succ_of_lt hj),
      h i (Nat.lt_succ_self i)]

end Chain

/-- A number below `2 ^ 0` is zero. -/
theorem fin_val_eq_zero {b : ℕ} (hb : b = 0) (x : Fin (2 ^ b)) : (x : ℕ) = 0 := by
  subst hb
  exact Nat.lt_one_iff.mp x.isLt

section Grind

variable {Msg X' : Type} {C : ℕ → Type} {bits : ℕ → ℕ} {Y' : X' → Type}
  (f : ∀ x : FSQuery Msg (GrindChal bits C) X', FSAnswer (GrindChal bits C) Y' x)
  (ms : ℕ → Msg)

/-- Every proof-of-work check of a chain passes exactly when the proof-of-work
bits of the answer of every round are zero. -/
theorem powPasses_fsTranscript (r : ℕ) :
    PcsRbr.PowPasses (fsTranscript f ms r) ↔ ∀ i < r, ((answer f ms i).1 : ℕ) = 0 := by
  induction r with
  | zero => exact ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => trivial⟩
  | succ r ih =>
    rw [fsTranscript_succ, PcsRbr.powPasses_snoc, ih]
    constructor
    · rintro ⟨h, hr⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hr
    · exact fun h => ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h r (Nat.lt_succ_self r)⟩

end Grind

section Accessors

variable {K : Type} [Field K] {Msg X' : Type} {bits : ℕ → ℕ} {S : LdtInstance K} {q : ℕ}
  {Y' : X' → Type}
  (f : ∀ x : FSQuery Msg (GrindChal bits (Chal S q)) X',
    FSAnswer (GrindChal bits (Chal S q)) Y' x)
  (ms : ℕ → Msg)

/-- The batching challenge of a chain is the field element of the answer of
round `0`. -/
theorem alphaOf_ungrind_fsTranscript (r : ℕ) :
    PcsRbr.alphaOf (PcsRbr.ungrind (fsTranscript f ms (r + 1))) = (answer f ms 0).2.field := by
  induction r with
  | zero => rfl
  | succ r ih => rw [fsTranscript_succ, PcsRbr.ungrind_snoc, PcsRbr.alphaOf_snoc_succ, ih]

/-- Folding challenge `i` of a chain of `r` rounds is the field element of the
answer of round `i + 1`, and zero if the chain has no such round. -/
theorem betasOf_ungrind_fsTranscript (r i : ℕ) :
    PcsRbr.betasOf (PcsRbr.ungrind (fsTranscript f ms r)) i =
      if i + 1 < r then (answer f ms (i + 1)).2.field else 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [fsTranscript_succ, PcsRbr.ungrind_snoc, PcsRbr.betasOf_snoc_succ]
      by_cases hi : i = r
      · subst hi
        rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hi, ih]
        by_cases hlt : i + 1 < r + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

/-- Folding challenge `i` of a chain is the field element of the answer of round
`i + 1`, when the chain has that round. -/
theorem betasOf_ungrind_fsTranscript_of_lt {r i : ℕ} (hi : i + 1 < r) :
    PcsRbr.betasOf (PcsRbr.ungrind (fsTranscript f ms r)) i = (answer f ms (i + 1)).2.field := by
  rw [betasOf_ungrind_fsTranscript, ite_eq_left hi]

/-- Folding challenge `i` of a chain is zero from the number of folding rounds
on: the answer of round `i + 1` is then a tuple of query points, or the chain
has no such round. -/
theorem betasOf_ungrind_fsTranscript_of_le (r : ℕ) {i : ℕ} (hi : S.rounds ≤ i) :
    PcsRbr.betasOf (PcsRbr.ungrind (fsTranscript f ms r)) i = 0 := by
  rw [betasOf_ungrind_fsTranscript]
  split
  · exact PcsRbr.Chal.field_of_not_le (by omega) _
  · rfl

/-- The query points of a chain are those of the answer of its last round. -/
theorem queriesOf_ungrind_fsTranscript (r : ℕ) :
    PcsRbr.queriesOf (PcsRbr.ungrind (fsTranscript f ms (r + 1))) = (answer f ms r).2.points :=
  rfl

end Accessors

/-! ## The states of the idealised challenger -/

section Free

variable {F EF D K : Type} [Field K] [DecidableEq K] (P : Compiled.Params K) (bits : ℕ → ℕ)
  (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (GrindChal bits (Chal P.ldt P.queries)) K D x)
  {ms : ℕ → RawMsg F EF D}

/-- The state `s` of the idealised challenger is in round `i` of the chain on
the messages `ms`: the closed rounds are the rounds below `i` with their
messages, the current round has absorbed `cur`, and `k` squeezes were made in
it. -/
structure At (ms : ℕ → RawMsg F EF D) (s : FreeState F EF D) (i : ℕ) (cur : RawMsg F EF D)
    (k : ℕ) : Prop where
  /-- The number of closed rounds. -/
  round : s.round = i
  /-- The messages of the closed rounds. -/
  hist : ∀ j < i, s.hist j = ms j
  /-- What the current round has absorbed. -/
  cur : s.cur = cur
  /-- The number of squeezes of the current round. -/
  nsamp : s.nsamp = k

/-- The initial state is in round `0`, with nothing absorbed. -/
theorem At.init : At ms (FreeState.init : FreeState F EF D) 0 [] 0 :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl, rfl⟩

/-- In a state that has absorbed the message of its round, the answer of the
oracle for the state is the answer of the round in the chain. -/
theorem freeAnswer_mk {i : ℕ} {hist : ℕ → RawMsg F EF D} (hh : ∀ j < i, hist j = ms j)
    (k : ℕ) :
    freeAnswer P bits f ⟨i, hist, ms i, k⟩ = answer f ms i := by
  unfold freeAnswer answer
  rw [fsTranscript_congr f hh]

variable [FieldOps F] [FieldOps EF] [ExtensionOps F EF] (m : FieldModel F EF K)

/-- Before the first squeeze of a round, an absorption extends the round. -/
theorem At.observe {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D} (h : At ms s i cur 0)
    (o : Observation F EF D) :
    At ms ((freeChallenger P bits f m).observe s o) i (cur ++ [o]) 0 := by
  have hs : (freeChallenger P bits f m).observe s o = { s with cur := s.cur ++ [o] } :=
    ite_eq_left h.nsamp
  rw [hs]
  exact ⟨h.round, h.hist, by rw [← h.cur], h.nsamp⟩

/-- Before the first squeeze of a round, absorbing a list extends the round. -/
theorem At.observeAll {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D} (h : At ms s i cur 0)
    (l : List (Observation F EF D)) :
    At ms ((freeChallenger P bits f m).observeAll s l) i (cur ++ l) 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have h' := ih (h.observe P bits f m o)
    rwa [List.append_assoc] at h'

/-- After a squeeze, an absorption closes the round and starts the next. -/
theorem At.observe_next {s : FreeState F EF D} {i k : ℕ} (h : At ms s i (ms i) (k + 1))
    (o : Observation F EF D) :
    At ms ((freeChallenger P bits f m).observe s o) (i + 1) [o] 0 := by
  have hs : (freeChallenger P bits f m).observe s o =
      ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩ :=
    ite_eq_right (by rw [h.nsamp]; exact Nat.succ_ne_zero k)
  rw [hs]
  refine ⟨by rw [← h.round], fun j hj => ?_, rfl, rfl⟩
  show Function.update s.hist s.round s.cur j = ms j
  rw [h.round, h.cur]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [Function.update_of_ne hj.ne]
    exact h.hist j hj
  · rw [Function.update_self]

/-- After a squeeze, absorbing a nonempty list closes the round and starts the
next with that list. -/
theorem At.observeAll_next {s : FreeState F EF D} {i k : ℕ} (h : At ms s i (ms i) (k + 1))
    {l : List (Observation F EF D)} (hl : l ≠ []) :
    At ms ((freeChallenger P bits f m).observeAll s l) (i + 1) l 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l => exact (h.observe_next P bits f m o).observeAll P bits f m l

/-- A field challenge of a round is a representation of the field element of
the round's answer. -/
theorem At.sampleExt {s : FreeState F EF D} {i k : ℕ} (h : At ms s i (ms i) k) :
    ((freeChallenger P bits f m).sampleExt s).1 =
        Function.surjInv m.surj (answer f ms i).2.field ∧
      At ms ((freeChallenger P bits f m).sampleExt s).2 i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  show Function.surjInv m.surj (freeAnswer P bits f ⟨r, hist, ms r, n⟩).2.field = _
  rw [freeAnswer_mk P bits f hh]

/-- In a round with a proof-of-work check, the first sample of bits is the
proof-of-work bits of the round's answer. -/
theorem At.sampleBits_pow {s : FreeState F EF D} {i : ℕ} (h : At ms s i (ms i) 0)
    (hb : bits i ≠ 0) (b : ℕ) :
    ((freeChallenger P bits f m).sampleBits s b).1 = ((answer f ms i).1 : ℕ) ∧
      At ms ((freeChallenger P bits f m).sampleBits s b).2 i (ms i) 1 := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  show (if 0 = 0 ∧ bits r ≠ 0 then ((freeAnswer P bits f ⟨r, hist, ms r, 0⟩).1 : ℕ)
    else _) = _
  rw [ite_eq_left ⟨rfl, hb⟩, freeAnswer_mk P bits f hh]

/-- A sample of bits that is not the proof-of-work sample of its round is the
index of the next query point of the round's answer. -/
theorem At.sampleBits_query {s : FreeState F EF D} {i k : ℕ} (h : At ms s i (ms i) k)
    (hk : k = 0 → bits i = 0) (b : ℕ) :
    ((freeChallenger P bits f m).sampleBits s b).1 =
        P.indexOf (queryPoint P (answer f ms i).2 (k - if bits i = 0 then 0 else 1)) ∧
      At ms ((freeChallenger P bits f m).sampleBits s b).2 i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  show (if n = 0 ∧ bits r ≠ 0 then _ else
    P.indexOf (queryPoint P (freeAnswer P bits f ⟨r, hist, ms r, n⟩).2
      (n - if bits r = 0 then 0 else 1))) = _
  rw [ite_eq_right fun hn => hn.2 (hk hn.1), freeAnswer_mk P bits f hh]

/-- The proof-of-work check of a round. The witness, if there is a check, ends
the message of the round. If the check passes, the proof-of-work bits of the
round's answer are zero. -/
theorem At.checkWitness {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : At ms s i cur 0) (b : ℕ) (w : F)
    (hms : ms i = cur ++ if b = 0 then [] else [.base w]) (hbits : bits i = b) :
    (((freeChallenger P bits f m).checkWitness s b w).1 = true →
        ((answer f ms i).1 : ℕ) = 0) ∧
      At ms ((freeChallenger P bits f m).checkWitness s b w).2 i (ms i)
        (if b = 0 then 0 else 1) := by
  by_cases hb : b = 0
  · rw [ite_eq_left hb, List.append_nil] at hms
    rw [Challenger.checkWitness, ite_eq_left hb, ite_eq_left hb, hms]
    exact ⟨fun _ => fin_val_eq_zero (hbits.trans hb) _, hms ▸ h⟩
  · rw [ite_eq_right hb] at hms
    have h' := h.observe P bits f m (.base w)
    rw [← hms] at h'
    obtain ⟨hv, hs⟩ := h'.sampleBits_pow P bits f m (hbits ▸ hb) b
    rw [Challenger.checkWitness, ite_eq_right hb, ite_eq_right hb]
    refine ⟨fun hz => ?_, hs⟩
    rw [← hv]
    exact eq_of_beq hz

/-- The query indices of a round: the `t`-th sample is the index of the query
point `j + t` of the round's answer, where `j` samples of the round were query
indices before. -/
theorem At.sampleIndices {s : FreeState F EF D} {i k : ℕ} (h : At ms s i (ms i) k) (j : ℕ)
    (hk : k = j + if bits i = 0 then 0 else 1) (b count : ℕ) :
    (freeChallenger P bits f m).sampleIndices b count s =
      (List.range count).map fun t => P.indexOf (queryPoint P (answer f ms i).2 (j + t)) := by
  induction count generalizing s k j with
  | zero => rfl
  | succ count ih =>
    obtain ⟨hv, hs⟩ := h.sampleBits_query P bits f m (by intro h0; split at hk <;> omega) b
    have hj : k - (if bits i = 0 then 0 else 1) = j := by omega
    rw [hj] at hv
    rw [Challenger.sampleIndices, hv, ih hs (j + 1) (by omega), List.range_succ_eq_map,
      List.map_cons, List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun t _ => ?_)
    rw [Function.comp_apply, Nat.add_right_comm, Nat.add_assoc]

/-! ## The commit phase -/

/-- **The commit phase with the idealised challenger.** From a state that has
squeezed in round `0`, if the message of round `1 + i` is the commitment of
folding round `i` followed by its witness when there is a check, then the
folding challenges are representations of the field elements of the answers of
the rounds `1, …, r`, the state is in round `r` and has squeezed, and if every
check passes then the proof-of-work bits of these answers are zero. -/
theorem commitPhase_free [Inhabited D] (cpb : ℕ) (commits : Array D) (witnesses : Array F)
    (r : ℕ)
    (hms : ∀ i < r, ms (i + 1) = .digest (commits.getD i default) ::
      (if cpb = 0 then [] else [.base (witnesses.getD i 0)]))
    (hbits : ∀ i < r, bits (i + 1) = cpb) {s : FreeState F EF D} {k : ℕ}
    (h : At ms s 0 (ms 0) (k + 1)) :
    (commitPhase (freeChallenger P bits f m) cpb commits witnesses r s).1 =
        ((List.range r).map fun i =>
          Function.surjInv m.surj (answer f ms (i + 1)).2.field).toArray ∧
      ((commitPhase (freeChallenger P bits f m) cpb commits witnesses r s).2.1 = true →
        ∀ i < r, ((answer f ms (i + 1)).1 : ℕ) = 0) ∧
      ∃ k', At ms (commitPhase (freeChallenger P bits f m) cpb commits witnesses r s).2.2 r
        (ms r) (k' + 1) := by
  induction r with
  | zero => exact ⟨rfl, fun _ _ hi => absurd hi (Nat.not_lt_zero _), k, h⟩
  | succ r ih =>
    obtain ⟨hβ, hpow, k', hs⟩ := ih (fun i hi => hms i (Nat.lt_succ_of_lt hi))
      (fun i hi => hbits i (Nat.lt_succ_of_lt hi))
    have h1 := hs.observe_next P bits f m (.digest (commits.getD r default))
    obtain ⟨hw, h2⟩ := h1.checkWitness P bits f m cpb (witnesses.getD r 0)
      (hms r (Nat.lt_succ_self r)) (hbits r (Nat.lt_succ_self r))
    obtain ⟨hv, h3⟩ := h2.sampleExt P bits f m
    refine ⟨?_, fun hok i hi => ?_, _, h3⟩
    · rw [commitPhase, hβ, hv, List.push_toArray, List.range_succ, List.map_append,
        List.map_singleton]
    · rw [commitPhase] at hok
      obtain ⟨hok₁, hok₂⟩ := Bool.and_eq_true_iff.mp hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hpow hok₁ i hi
      · exact hw hok₂

/-- The `k`-th query point of a challenge, for `k` below the number of
queries. -/
theorem queryPoint_val {i : ℕ} (c : Chal P.ldt P.queries i) (k : Fin P.queries) :
    queryPoint P c k.val = c.points k :=
  dite_eq_left k.isLt

end Free

/-- Entry `i` of the array of the values of `g` on the numbers below `n`. -/
theorem getD_map_range {α : Type} (g : ℕ → α) (n i : ℕ) (d : α) :
    ((List.range n).map g).toArray.getD i d = if i < n then g i else d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  by_cases h : i < n
  · rw [ite_eq_left h, List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [ite_eq_right h, List.getElem?_eq_none
      (by rw [List.length_map, List.length_range]; exact Nat.le_of_not_lt h)]
    rfl

/-! ## The whole transcript -/

section Run

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  [DecidableEq K] [Inhabited D] (P : Compiled.Params K) (m : FieldModel F EF K)
  (params : FriParams) (shape : ClaimShape)

/-- **The transcript with the idealised challenger, as answers of the chain.**
For any parameters `P` of the model and a proof whose final polynomial is not
empty, the challenges of `Fri.transcript` are read off the answers of the
oracle along the chain on the raw messages of the run: the batching challenge
represents the field element of the answer of round `0`, folding challenge `i`
that of round `i + 1`, and query index `k` is the index of the `k`-th query
point of the answer of the last round. If every proof-of-work check passes, the
proof-of-work bits of every answer are zero. -/
theorem transcript_eq
    (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal (powBits params shape) (Chal P.ldt P.queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal (powBits params shape) (Chal P.ldt P.queries))
        K D x)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (hfinal : proof.finalPoly.size ≠ 0) :
    let ms := messages params shape commitments points values proof
    let ch := transcript (freeChallenger P (powBits params shape) f m) FreeState.init params
      shape commitments points values proof
    ch.alpha = Function.surjInv m.surj (answer f ms 0).2.field ∧
      ch.betas = ((List.range (numRounds params shape)).map fun i =>
        Function.surjInv m.surj (answer f ms (i + 1)).2.field).toArray ∧
      (ch.powOk = true → ∀ i < numRounds params shape + 2, ((answer f ms i).1 : ℕ) = 0) ∧
      ch.indices = ((List.range params.numQueries).map fun k =>
        P.indexOf (queryPoint P (answer f ms (numRounds params shape + 1)).2 k)).toArray := by
  intro ms ch
  have hb0 : powBits params shape 0 = 0 := ite_eq_left rfl
  have hbC : ∀ i < numRounds params shape,
      powBits params shape (i + 1) = params.commitPowBits := fun i hi => by
    rw [powBits, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi)]
  have hbF : powBits params shape (numRounds params shape + 1) = params.queryPowBits := by
    rw [powBits, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.not_succ_le_self _)]
  have hm0 : ms 0 = firstMessage commitments points values := ite_eq_left rfl
  have hmC : ∀ i < numRounds params shape,
      ms (i + 1) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then []
          else [.base (proof.commitPowWitnesses.getD i 0)]) := fun i hi => by
    show messages params shape commitments points values proof (i + 1) = _
    rw [messages, ite_eq_right (Nat.succ_ne_zero i), ite_eq_left (Nat.succ_le_of_lt hi),
      Nat.add_sub_cancel]
  have hmF : ms (numRounds params shape + 1) =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
    show messages params shape commitments points values proof (numRounds params shape + 1) = _
    rw [messages, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.not_succ_le_self _)]
  have hne : finalMessage (F := F) (D := D) (numRounds params shape) proof.finalPoly ≠ [] := by
    intro h
    have hlen := congrArg List.length h
    simp only [finalMessage, List.length_append, List.length_map, Array.length_toList,
      List.length_replicate, List.length_nil] at hlen
    omega
  have h0 : At ms ((freeChallenger P (powBits params shape) f m).observeAll FreeState.init
      (firstMessage commitments points values)) 0 (ms 0) 0 := by
    have h := (At.init (ms := ms)).observeAll P (powBits params shape) f m
      (firstMessage commitments points values)
    rwa [List.nil_append, ← hm0] at h
  obtain ⟨hα, h1⟩ := h0.sampleExt P (powBits params shape) f m
  obtain ⟨hβ, hpowC, k, h2⟩ := commitPhase_free P (powBits params shape) f m
    params.commitPowBits proof.commitPhaseCommits proof.commitPowWitnesses
    (numRounds params shape) hmC hbC h1
  have h3 := h2.observeAll_next P (powBits params shape) f m hne
  obtain ⟨hpowQ, h4⟩ := h3.checkWitness P (powBits params shape) f m params.queryPowBits
    proof.queryPowWitness hmF hbF
  have hidx := h4.sampleIndices P (powBits params shape) f m 0 (by rw [hbF, Nat.zero_add])
    (logMaxHeight params.logBlowup shape) params.numQueries
  refine ⟨hα, hβ, fun hpow i hi => ?_, ?_⟩
  · obtain ⟨hpow₁, hpow₂⟩ := Bool.and_eq_true_iff.mp hpow
    rcases i with _ | i
    · exact fin_val_eq_zero hb0 _
    · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_of_succ_lt_succ hi) with hi | rfl
      · exact hpowC hpow₁ i hi
      · exact hpowQ hpow₂
  · simp only [Nat.zero_add] at hidx
    exact congrArg List.toArray hidx

end Run

end Transcript

/-! ## The executable transcript and the model's chain -/

section Main

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- **The executable transcript is the model's chain.** With the idealised
challenger of the oracle `f`, on a statement and a proof that pass the shape
check, the challenges the executable verifier derives are those of the
Fiat–Shamir chain of `f` on the raw messages of the run:

* the batching challenge represents `alphaOf` of the chain;
* folding challenge `i` represents `betasOf` of the chain at `i`, for every
  `i`: both are zero from the number of folding rounds on;
* if every proof-of-work check of the run passes, every proof-of-work check of
  the chain passes;
* there is one query index per query, and query index `k` is the index of the
  `k`-th query point of the chain. -/
theorem transcript_free
    (f : ∀ x : FSQuery (RawMsg F EF D)
        (GrindChal (powBits params shape)
          (Chal (modelParams m params shape wf).ldt (modelParams m params shape wf).queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D)
        (GrindChal (powBits params shape)
          (Chal (modelParams m params shape wf).ldt (modelParams m params shape wf).queries))
        K D x)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) :
    let t := fsTranscript f (messages params shape commitments points values proof)
      ((modelParams m params shape wf).rounds + 2)
    let ch := transcript
      (freeChallenger (modelParams m params shape wf) (powBits params shape) f m)
      FreeState.init params shape commitments points values proof
    m.ext.toModel ch.alpha = PcsRbr.alphaOf (PcsRbr.ungrind t) ∧
    (∀ i, m.ext.toModel (ch.betas.getD i 0) = PcsRbr.betasOf (PcsRbr.ungrind t) i) ∧
    (ch.powOk = true → PcsRbr.PowPasses t) ∧
    ch.indices.size = params.numQueries ∧
    (∀ k : Fin params.numQueries,
      ch.indices.getD k.val 0 =
        (modelParams m params shape wf).indexOf (PcsRbr.queriesOf (PcsRbr.ungrind t) k)) := by
  have hfinal : proof.finalPoly.size ≠ 0 := by
    have h : proof.finalPoly.size = params.finalPolyLen := by
      simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
      omega
    rw [h]
    exact (Nat.two_pow_pos _).ne'
  obtain ⟨hα, hβ, hpow, hidx⟩ := Transcript.transcript_eq (modelParams m params shape wf) m
    params shape f commitments points values proof hfinal
  refine ⟨?_, fun i => ?_, fun hok => ?_, ?_, fun k => ?_⟩
  · rw [hα, Function.surjInv_eq m.surj]
    exact (Transcript.alphaOf_ungrind_fsTranscript f _ _).symm
  · rw [hβ, Transcript.getD_map_range]
    by_cases hi : i < numRounds params shape
    · rw [ite_eq_left hi, Function.surjInv_eq m.surj]
      exact (Transcript.betasOf_ungrind_fsTranscript_of_lt f _
        (show i + 1 < numRounds params shape + 2 by omega)).symm
    · rw [ite_eq_right hi, m.ext.map_zero]
      exact (Transcript.betasOf_ungrind_fsTranscript_of_le f _ _
        (show numRounds params shape ≤ i from Nat.le_of_not_lt hi)).symm
  · exact (Transcript.powPasses_fsTranscript f _ _).mpr (hpow hok)
  · rw [hidx, List.size_toArray, List.length_map, List.length_range]
  · rw [hidx, Transcript.getD_map_range, ite_eq_left k.isLt]
    exact congrArg _ (Transcript.queryPoint_val (modelParams m params shape wf) _ k)

end Main

end CertiFri.Exec
