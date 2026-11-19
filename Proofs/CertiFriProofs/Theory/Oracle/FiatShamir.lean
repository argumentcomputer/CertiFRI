import CertiFriProofs.Theory.Oracle.BadEvent

/-!
# Fiat–Shamir for round-by-round sound protocols

A public-coin protocol with `r` rounds: in round `i` the prover sends a message
in `Msg` and the verifier answers with a uniform challenge in `Chal i`. A
`Transcript Msg Chal i` holds the first `i` rounds.

A *state function* `doomed i t` marks partial transcripts. It is round-by-round
sound with errors `ε` (`RbrSound`) when, from a doomed transcript of length
`i < r` and any message, at most a fraction `ε i` of the challenges lead to a
transcript that is not doomed.

In the Fiat–Shamir transformation the challenge of a round is the answer of a
random oracle to the transcript so far, *including the earlier challenges*, and
the new message (`FSQuery.chal t m`). This models a chained challenger, each of
whose states is a hash of the previous state and the new input.

The oracle of the experiment also answers queries of a second kind
(`FSQuery.other`), with answer types `Y'`, which the state function ignores.
Hash queries of a commitment scheme go there.

## Results

* `prob_hasFlip_le`: a computation with at most `Q` queries leaves a log with
  a *flip* (a challenge query whose transcript is doomed and whose answer makes
  the extended transcript not doomed) with probability at most `Q * εmax`,
  where `εmax` bounds every `ε i`.
* `doomed_of_supports`: in a log without a flip, every transcript whose chain
  of challenge queries is answered by the log is doomed, if the empty
  transcript is. No probability is involved.
* `prob_not_doomed_le` (**Fiat–Shamir**): an adversary with at most `Q` queries
  outputs messages; the verifier derives the challenges with `r` queries along
  the chain. If the empty transcript is doomed, the transcript is not doomed
  with probability at most `(Q + r) * εmax`.
* `prob_not_doomed_le_add_sum`: the same with the finer bound
  `Q * εmax + ∑ i < r, ε i`, when the errors are nonnegative.
* `prob_accept_le`, `prob_accept_le_add_sum`: the two bounds for an acceptance
  predicate that implies "not doomed".
* `prob_fsExperiment_bind_le`, `prob_fsExperiment_bind_le_add_sum`: the two
  bounds for an event of a computation the verifier runs afterwards.

`fsTranscript f ms` is the transcript a verifier computes from a fixed function
`f` in place of the oracle; the challenges derived in the experiment are these,
for any `f` that agrees with the final log (`OracleComp.Outcome.eq_fsTranscript`).

Not covered: the variant in which a challenge query holds the messages without
the earlier challenges; state functions that depend on the log (see
`FiatShamirInterp.lean` for messages that are read against the log).
-/

namespace CertiFri.Oracle

universe u v u' w w'

/-! ## Transcripts and queries -/

/-- The first `i` rounds of a public-coin protocol: in round `j` a prover
message in `Msg` and a challenge in `Chal j`. -/
inductive Transcript (Msg : Type u) (Chal : ℕ → Type v) : ℕ → Type (max u v)
  /-- The empty transcript. -/
  | nil : Transcript Msg Chal 0
  /-- Extend a transcript of `i` rounds by the message and the challenge of round `i`. -/
  | snoc {i : ℕ} (t : Transcript Msg Chal i) (m : Msg) (c : Chal i) :
    Transcript Msg Chal (i + 1)

/-- The queries of the Fiat–Shamir experiment. -/
inductive FSQuery (Msg : Type u) (Chal : ℕ → Type v) (X' : Type u') : Type (max u v u')
  /-- The query for the challenge of round `i`: the transcript of the first `i`
  rounds and the message of round `i`. -/
  | chal {i : ℕ} (t : Transcript Msg Chal i) (m : Msg) : FSQuery Msg Chal X'
  /-- A query of the second kind. -/
  | other (x : X') : FSQuery Msg Chal X'

variable {Msg : Type u} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}

/-- The answer type of a query: the challenge type of the round, or the answer
type `Y'` of a query of the second kind. -/
def FSAnswer (Chal : ℕ → Type v) (Y' : X' → Type v) : FSQuery Msg Chal X' → Type v
  | .chal (i := i) _ _ => Chal i
  | .other x => Y' x

/-- The answer types are finite when the challenge types and `Y'` are. -/
instance [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)] :
    ∀ x : FSQuery Msg Chal X', Fintype (FSAnswer Chal Y' x)
  | .chal (i := i) _ _ => inferInstanceAs (Fintype (Chal i))
  | .other x => inferInstanceAs (Fintype (Y' x))

/-- The answer types are nonempty when the challenge types and `Y'` are. -/
instance [∀ i, Nonempty (Chal i)] [∀ x, Nonempty (Y' x)] :
    ∀ x : FSQuery Msg Chal X', Nonempty (FSAnswer Chal Y' x)
  | .chal (i := i) _ _ => inferInstanceAs (Nonempty (Chal i))
  | .other x => inferInstanceAs (Nonempty (Y' x))

/-- Equality of transcripts is decidable. -/
def Transcript.decEq [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] :
    {i : ℕ} → (t t' : Transcript Msg Chal i) → Decidable (t = t')
  | _, .nil, .nil => isTrue rfl
  | _, .snoc t m c, .snoc t' m' c' =>
    letI := Transcript.decEq t t'
    decidable_of_iff (t = t' ∧ m = m' ∧ c = c') (by rw [Transcript.snoc.injEq])

/-- Equality of transcripts is decidable. -/
instance [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] {i : ℕ} :
    DecidableEq (Transcript Msg Chal i) :=
  Transcript.decEq

/-- Equality of queries is decidable. -/
instance [DecidableEq Msg] [∀ i, DecidableEq (Chal i)] [DecidableEq X'] :
    DecidableEq (FSQuery Msg Chal X')
  | .chal (i := i) t m, .chal (i := j) t' m' =>
    if h : i = j then by
      subst h
      exact decidable_of_iff (t = t' ∧ m = m') (by rw [FSQuery.chal.injEq]; simp)
    else isFalse fun h' => by
      cases h'
      exact h rfl
  | .chal _ _, .other _ => isFalse fun h => by cases h
  | .other _, .chal _ _ => isFalse fun h => by cases h
  | .other x, .other x' => decidable_of_iff (x = x') (by rw [FSQuery.other.injEq])

/-- The prover messages of a transcript, first round first. -/
def Transcript.msgs : {i : ℕ} → Transcript Msg Chal i → List Msg
  | _, .nil => []
  | _, .snoc t m _ => t.msgs ++ [m]

/-- The empty transcript has no messages. -/
@[simp] theorem Transcript.msgs_nil : (Transcript.nil : Transcript Msg Chal 0).msgs = [] := rfl

/-- The messages of an extended transcript end with the new message. -/
@[simp] theorem Transcript.msgs_snoc {i : ℕ} (t : Transcript Msg Chal i) (m : Msg) (c : Chal i) :
    (t.snoc m c).msgs = t.msgs ++ [m] := rfl

/-- A transcript of `i` rounds has `i` messages. -/
@[simp] theorem Transcript.length_msgs :
    ∀ {i : ℕ} (t : Transcript Msg Chal i), t.msgs.length = i
  | _, .nil => rfl
  | _, .snoc t m c => by
    rw [Transcript.msgs_snoc, List.length_append, t.length_msgs, List.length_singleton]

/-- An observation of the answers to the queries of the second kind, as an
observation of all answers: a challenge is not observed. With this, the
collision bound of `Collision.lean` applies to the hash queries of the
experiment. -/
def FSQuery.liftObs {Z : Type*} (obs : (x : X') → Y' x → Option Z) :
    (x : FSQuery Msg Chal X') → FSAnswer Chal Y' x → Option Z
  | .chal _ _, _ => none
  | .other x, y => obs x y

/-- If at most a fraction `κ` of the answers to a query of the second kind is
observed as any one value, the same holds for all queries. -/
theorem FSQuery.fractionLE_liftObs [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)] {Z : Type*}
    {obs : (x : X') → Y' x → Option Z} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ (x : X') (z : Z), FractionLE (fun y : Y' x => obs x y = some z) κ) :
    ∀ (x : FSQuery Msg Chal X') (z : Z),
      FractionLE (fun y : FSAnswer Chal Y' x => FSQuery.liftObs obs x y = some z) κ
  | .chal _ _, _ => (FractionLE.false.mono_right hκ0).mono_left fun _ h => nomatch h
  | .other x, z => hκ x z

/-! ## Round-by-round soundness -/

/-- Round-by-round soundness of the state function `doomed` for `r` rounds with
error `ε i` in round `i`: from a doomed transcript of `i < r` rounds and any
message, at most a fraction `ε i` of the challenges give a transcript that is
not doomed. -/
def RbrSound [∀ i, Fintype (Chal i)] (r : ℕ) (doomed : ∀ i, Transcript Msg Chal i → Prop)
    (ε : ℕ → ℝ) : Prop :=
  ∀ i < r, ∀ (t : Transcript Msg Chal i) (m : Msg), doomed i t →
    FractionLE (fun c : Chal i => ¬ doomed (i + 1) (t.snoc m c)) (ε i)

/-- The answer `y` to the query `x` flips the state: `x` is a challenge query
of a round below `r` whose transcript is doomed, and the transcript extended by
its message and `y` is not doomed. -/
def Flips (r : ℕ) (doomed : ∀ i, Transcript Msg Chal i → Prop) (x : FSQuery Msg Chal X') :
    FSAnswer Chal Y' x → Prop :=
  match x with
  | .chal (i := i) t m => fun c => i < r ∧ doomed i t ∧ ¬ doomed (i + 1) (t.snoc m c)
  | .other _ => fun _ => False

/-- Some entry of the log flips the state. -/
def HasFlip (r : ℕ) (doomed : ∀ i, Transcript Msg Chal i → Prop)
    (l : Log (FSAnswer (Msg := Msg) Chal Y')) : Prop :=
  ∃ e ∈ l, Flips r doomed e.1 e.2

section Flips

variable {r : ℕ} {doomed : ∀ i, Transcript Msg Chal i → Prop} {ε : ℕ → ℝ} {εmax : ℝ}

/-- `Flips` on a challenge query, unfolded. -/
theorem flips_chal {i : ℕ} {t : Transcript Msg Chal i} {m : Msg} {c : Chal i} :
    Flips (X' := X') (Y' := Y') r doomed (.chal t m) c ↔
      i < r ∧ doomed i t ∧ ¬ doomed (i + 1) (t.snoc m c) :=
  Iff.rfl

/-- Under round-by-round soundness, at most a fraction `εmax` of the answers to
any query flips the state. -/
theorem fractionLE_flips [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)]
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax) :
    ∀ x : FSQuery Msg Chal X', FractionLE (Flips (Y' := Y') r doomed x) εmax
  | .chal (i := i) t m => by
    by_cases h : i < r ∧ doomed i t
    · exact ((hsound i h.1 t m h.2).mono_right (hε i h.1)).mono_left fun c hc => hc.2.2
    · exact (FractionLE.false.mono_right h0).mono_left fun c hc => h ⟨hc.1, hc.2.1⟩
  | .other _ => (FractionLE.false.mono_right h0).mono_left fun _ hc => hc

end Flips

/-! ## The chain of challenge queries -/

section Chain

variable [DecidableEq (FSQuery Msg Chal X')]

/-- The log answers the chain of challenge queries of the transcript `t`: for
each round, the query made of the earlier rounds and the message of the round
has the challenge of the round as its answer. -/
def Supports (l : Log (FSAnswer (Msg := Msg) Chal Y')) :
    {i : ℕ} → Transcript Msg Chal i → Prop
  | _, .nil => True
  | _, .snoc t m c => Supports l t ∧ l.dlookup (.chal t m) = some c

/-- Every log answers the empty chain. -/
@[simp] theorem supports_nil (l : Log (FSAnswer (Msg := Msg) Chal Y')) :
    Supports l (.nil : Transcript Msg Chal 0) :=
  trivial

/-- `Supports` on an extended transcript, unfolded. -/
@[simp] theorem supports_snoc {l : Log (FSAnswer (Msg := Msg) Chal Y')} {i : ℕ}
    {t : Transcript Msg Chal i} {m : Msg} {c : Chal i} :
    Supports l (t.snoc m c) ↔ Supports l t ∧ l.dlookup (.chal t m) = some c :=
  Iff.rfl

/-- A chain answered by a log is answered by every extension of it. -/
theorem Supports.of_prefix {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} (hl : l <+: l') :
    ∀ {i : ℕ} {t : Transcript Msg Chal i}, Supports l t → Supports l' t
  | _, .nil, _ => trivial
  | _, .snoc _ _ _, h => ⟨Supports.of_prefix hl h.1, OracleComp.dlookup_of_prefix h.2 hl⟩

/-- In a log without a flip, every transcript of at most `r` rounds whose chain
of challenge queries the log answers is doomed, if the empty transcript is. -/
theorem doomed_of_supports {r : ℕ} {doomed : ∀ i, Transcript Msg Chal i → Prop}
    {l : Log (FSAnswer (Msg := Msg) Chal Y')} (hflip : ¬ HasFlip r doomed l)
    (hnil : doomed 0 .nil) :
    ∀ {i : ℕ} (t : Transcript Msg Chal i), i ≤ r → Supports l t → doomed i t
  | _, .nil, _, _ => hnil
  | _, .snoc t m c, hi, hs => by
    have ht := doomed_of_supports hflip hnil t (Nat.le_of_succ_le hi) hs.1
    by_contra hnd
    exact hflip ⟨⟨.chal t m, c⟩, List.of_mem_dlookup hs.2, flips_chal.mpr ⟨hi, ht, hnd⟩⟩

end Chain

/-! ## Deriving the challenges -/

/-- The transcript of `i` rounds with the messages `ms 0, …, ms (i - 1)` and the
challenges the function `f` gives along the chain. -/
def fsTranscript (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x) (ms : ℕ → Msg) :
    (i : ℕ) → Transcript Msg Chal i
  | 0 => .nil
  | i + 1 => (fsTranscript f ms i).snoc (ms i) (f (.chal (fsTranscript f ms i) (ms i)))

/-- The messages of `fsTranscript f ms i` are `ms 0, …, ms (i - 1)`. -/
theorem fsTranscript_msgs (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x) (ms : ℕ → Msg)
    (i : ℕ) : (fsTranscript f ms i).msgs = (List.range i).map ms := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, ← ih]
    rfl

open OracleComp

/-- The verifier's part of the experiment: derive the challenges of `i` rounds
for the messages `ms 0, …, ms (i - 1)`, with one query per round along the
chain, and return the transcript. -/
def derive (Y' : X' → Type v) (ms : ℕ → Msg) :
    (i : ℕ) → OracleComp (FSAnswer (Msg := Msg) Chal Y') (Transcript Msg Chal i)
  | 0 => .pure .nil
  | i + 1 => (derive Y' ms i).bind fun t =>
      .queryBind (.chal t (ms i)) fun c => .pure (t.snoc (ms i) c)

/-- Deriving the challenges of `i` rounds takes at most `i` queries. -/
theorem queryBound_derive (ms : ℕ → Msg) :
    ∀ i : ℕ, (derive (Chal := Chal) Y' ms i).QueryBound i
  | 0 => trivial
  | i + 1 => (queryBound_derive ms i).bind fun _ _ => trivial

/-- Against a fixed function, `derive` computes `fsTranscript`. -/
theorem run_derive (f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x) (ms : ℕ → Msg) :
    ∀ i : ℕ, (derive Y' ms i).run f = fsTranscript f ms i
  | 0 => rfl
  | i + 1 => by
    rw [derive, run_bind, run_derive f ms i]
    rfl

section Experiment

variable [DecidableEq (FSQuery Msg Chal X')] {α : Type w} {β : Type w'}

/-- After `derive`, the log answers the chain of the derived transcript. -/
theorem supports_of_outcome_derive {ms : ℕ → Msg} :
    ∀ {i : ℕ} {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {t : Transcript Msg Chal i},
      Outcome (derive Y' ms i) l t l' → Supports l' t
  | 0, _, _, _, h => by
    obtain ⟨rfl, _⟩ := h
    trivial
  | i + 1, l, l', t, h => by
    rw [derive, outcome_bind] at h
    obtain ⟨t₀, l₁, h₀, h⟩ := h
    obtain ⟨c, l₂, hc, rfl, rfl⟩ := outcome_queryBind.mp h
    exact ⟨(supports_of_outcome_derive h₀).of_prefix hc.prefix, hc.dlookup_query⟩

/-- The transcript `derive` returns is the one any function that agrees with
the final log gives. -/
theorem OracleComp.Outcome.eq_fsTranscript {ms : ℕ → Msg} {i : ℕ}
    {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {t : Transcript Msg Chal i}
    (h : Outcome (derive Y' ms i) l t l') {f : ∀ x : FSQuery Msg Chal X', FSAnswer Chal Y' x}
    (hf : ∀ x y, l'.dlookup x = some y → f x = y) : t = fsTranscript f ms i := by
  rw [← run_derive, h.run_eq hf]

/-- The Fiat–Shamir experiment: the adversary `adv` returns `a`, which holds
the prover messages `msgs a 0, …, msgs a (r - 1)`; then the verifier derives
the challenges. The result is the adversary's output and the transcript. -/
def fsExperiment (r : ℕ) (adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α)
    (msgs : α → ℕ → Msg) :
    OracleComp (FSAnswer (Msg := Msg) Chal Y') (α × Transcript Msg Chal r) :=
  adv.bind fun a => (derive Y' (msgs a) r).bind fun t => .pure (a, t)

omit [DecidableEq (FSQuery Msg Chal X')] in
/-- The experiment makes the adversary's queries and one more per round. -/
theorem queryBound_fsExperiment {r Q : ℕ} {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α}
    (hadv : adv.QueryBound Q) (msgs : α → ℕ → Msg) :
    (fsExperiment r adv msgs).QueryBound (Q + r) :=
  hadv.bind fun a => (queryBound_derive (msgs a) r).bind (m := 0) fun _ => trivial

/-- An outcome of the experiment is an outcome of the adversary followed by an
outcome of `derive` on its messages. -/
theorem outcome_fsExperiment {r : ℕ} {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α}
    {msgs : α → ℕ → Msg} {l l' : Log (FSAnswer (Msg := Msg) Chal Y')}
    {out : α × Transcript Msg Chal r} :
    Outcome (fsExperiment r adv msgs) l out l' ↔
      ∃ l₁, Outcome adv l out.1 l₁ ∧ Outcome (derive Y' (msgs out.1) r) l₁ out.2 l' := by
  rw [fsExperiment, outcome_bind]
  constructor
  · rintro ⟨a, l₁, ha, h⟩
    obtain ⟨t, l₂, ht, rfl, rfl⟩ := outcome_bind.mp h
    exact ⟨l₁, ha, ht⟩
  · rintro ⟨l₁, ha, ht⟩
    exact ⟨out.1, l₁, ha, outcome_bind.mpr ⟨out.2, l', ht, rfl, rfl⟩⟩

/-- After the experiment, the log answers the chain of the transcript. -/
theorem supports_of_outcome_fsExperiment {r : ℕ}
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {msgs : α → ℕ → Msg}
    {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {out : α × Transcript Msg Chal r}
    (h : Outcome (fsExperiment r adv msgs) l out l') : Supports l' out.2 := by
  obtain ⟨l₁, _, ht⟩ := outcome_fsExperiment.mp h
  exact supports_of_outcome_derive ht

variable [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)] [∀ x, Fintype (Y' x)]
  [∀ x, Nonempty (Y' x)] {r : ℕ} {doomed : ∀ i, Transcript Msg Chal i → Prop} {ε : ℕ → ℝ}
  {εmax : ℝ}

omit [∀ i, Nonempty (Chal i)] [∀ x, Nonempty (Y' x)] in
/-- If the empty transcript is doomed, the transcript of the experiment is not
doomed only when the final log has a flip. -/
theorem prob_not_doomed_le_prob_hasFlip (hnil : doomed 0 .nil)
    (adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α) (msgs : α → ℕ → Msg)
    (l : Log (FSAnswer (Msg := Msg) Chal Y')) :
    prob (fun out _ => ¬ doomed r out.2) (fsExperiment r adv msgs) l
      ≤ prob (fun _ l' => HasFlip r doomed l') (fsExperiment r adv msgs) l := by
  refine prob_mono_of_outcome fun out l' hout hnd => ?_
  by_contra hno
  exact hnd (doomed_of_supports hno hnil out.2 le_rfl (supports_of_outcome_fsExperiment hout))

/-! ### The bound `(Q + r) * εmax` -/

/-- Under round-by-round soundness with every error at most `εmax`, a
computation that makes at most `Q` queries from the empty log leaves a log with
a flip with probability at most `Q * εmax`. -/
theorem prob_hasFlip_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) {c : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ}
    (hc : c.QueryBound Q) :
    prob (fun _ l => HasFlip r doomed l) c [] ≤ Q * εmax := by
  have h := prob_hasBad_le (bad := fun _ => Flips (Y' := Y') r doomed) (ε := fun _ => εmax)
    (fun _ => h0) (fun _ x _ => fractionLE_flips hsound hε h0 x) hc
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact (prob_mono (fun _ _ hflip => hasBad_const_iff.mpr hflip) c []).trans h

/-- **Fiat–Shamir for round-by-round sound protocols.** The state function
`doomed` is round-by-round sound for `r` rounds with every error at most
`εmax`, and the empty transcript is doomed. An adversary that makes at most `Q`
queries outputs prover messages, and the verifier derives the challenges along
the chain. Then the transcript is not doomed with probability at most
`(Q + r) * εmax`. -/
theorem prob_not_doomed_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg) :
    prob (fun out _ => ¬ doomed r out.2) (fsExperiment r adv msgs) [] ≤ (Q + r) * εmax := by
  have hflip := prob_hasFlip_le hsound hε h0 (queryBound_fsExperiment (r := r) hadv msgs)
  rw [Nat.cast_add] at hflip
  exact (prob_not_doomed_le_prob_hasFlip hnil adv msgs []).trans hflip

/-- **Fiat–Shamir, for an acceptance predicate.** If the verifier only accepts
transcripts that are not doomed, then under the hypotheses of
`prob_not_doomed_le` it accepts with probability at most `(Q + r) * εmax`. The
predicate may depend on the adversary's output and on the final log. -/
theorem prob_accept_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {accept : α → Transcript Msg Chal r → Log (FSAnswer (Msg := Msg) Chal Y') → Prop}
    (haccept : ∀ a t l, accept a t l → ¬ doomed r t) :
    prob (fun out l => accept out.1 out.2 l) (fsExperiment r adv msgs) [] ≤ (Q + r) * εmax :=
  (prob_mono (fun out l h => haccept out.1 out.2 l h) _ _).trans
    (prob_not_doomed_le hsound hε h0 hnil hadv msgs)

/-- **Fiat–Shamir, for a verifier that goes on computing.** After the
experiment the computation `rest` runs on its result, with any number of
queries. If an event `E` of `rest` never happens after an outcome of the
experiment with a doomed transcript, then under the hypotheses of
`prob_not_doomed_le` it happens with probability at most `(Q + r) * εmax`. -/
theorem prob_fsExperiment_bind_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r → OracleComp (FSAnswer (Msg := Msg) Chal Y') β}
    {E : β → Log (FSAnswer (Msg := Msg) Chal Y') → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l → doomed r out.2 →
      Outcome (rest out) l b l' → ¬ E b l') :
    prob E ((fsExperiment r adv msgs).bind rest) [] ≤ (Q + r) * εmax :=
  (prob_bind_le_prob fun out l b l' hout hb hEb hd => hE out l b l' hout hd hb hEb).trans
    (prob_not_doomed_le hsound hε h0 hnil hadv msgs)

/-! ### The bound `Q * εmax + ∑ i < r, ε i`

The verifier's query of round `i` is charged the error of that round instead of
`εmax`. This needs the errors to be nonnegative. -/

omit [DecidableEq (FSQuery Msg Chal X')] [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
  [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)] in
/-- A log with one more entry has a flip if the log has one or the new entry is
one. -/
theorem hasFlip_concat {l : Log (FSAnswer (Msg := Msg) Chal Y')}
    {e : Sigma (FSAnswer (Msg := Msg) Chal Y')} :
    HasFlip r doomed (l ++ [e]) ↔ HasFlip r doomed l ∨ Flips r doomed e.1 e.2 := by
  simp only [HasFlip, List.mem_append, List.mem_singleton, or_and_right, exists_or,
    exists_eq_left]

open Classical in
/-- One challenge query of a round below `r` adds a flip with probability at
most the error of the round. -/
private theorem prob_hasFlip_chal_le (hsound : RbrSound r doomed ε) (hε0 : ∀ i < r, 0 ≤ ε i)
    {i : ℕ} (hi : i < r) (t : Transcript Msg Chal i) (m : Msg) (g : Chal i → β)
    (l : Log (FSAnswer (Msg := Msg) Chal Y')) :
    prob (fun _ l' => HasFlip r doomed l') (.queryBind (.chal t m) fun c => .pure (g c)) l
      ≤ (if HasFlip r doomed l then 1 else 0) + ε i := by
  have hfrac : FractionLE (Flips (X' := X') (Y' := Y') r doomed (.chal t m)) (ε i) := by
    by_cases hd : doomed i t
    · exact (hsound i hi t m hd).mono_left fun c hc => hc.2.2
    · exact (FractionLE.false.mono_right (hε0 i hi)).mono_left fun c hc => hd hc.2.1
  cases hx : l.dlookup (.chal t m) with
  | some c =>
    rw [prob_queryBind_of_lookup hx, prob_pure]
    exact le_add_of_nonneg_right (hε0 i hi)
  | none =>
    have hcard : (0 : ℝ) < Fintype.card (FSAnswer Chal Y' (FSQuery.chal t m)) :=
      Nat.cast_pos.mpr Fintype.card_pos
    rw [prob_queryBind_of_fresh hx, div_le_iff₀ hcard]
    calc _ ≤ ∑ c : FSAnswer Chal Y' (FSQuery.chal t m),
          ((if HasFlip r doomed l then (1 : ℝ) else 0)
            + if Flips (Y' := Y') r doomed (.chal t m) c then 1 else 0) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [prob_pure]
          by_cases h₁ : HasFlip r doomed l <;>
            by_cases h₂ : Flips (Y' := Y') r doomed (.chal t m) c <;>
            simp [hasFlip_concat, h₁, h₂]
      _ = Fintype.card (FSAnswer Chal Y' (FSQuery.chal t m))
            * (if HasFlip r doomed l then (1 : ℝ) else 0)
          + ∑ c : FSAnswer Chal Y' (FSQuery.chal t m),
              if Flips (Y' := Y') r doomed (.chal t m) c then (1 : ℝ) else 0 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ Fintype.card (FSAnswer Chal Y' (FSQuery.chal t m))
            * (if HasFlip r doomed l then (1 : ℝ) else 0)
          + ε i * Fintype.card (FSAnswer Chal Y' (FSQuery.chal t m)) :=
          add_le_add_right hfrac.sum_ite_le _
      _ = _ := by ring

open Classical in
/-- Deriving the challenges of `i ≤ r` rounds adds a flip with probability at
most the sum of the errors of these rounds. -/
private theorem prob_hasFlip_derive_le (hsound : RbrSound r doomed ε)
    (hε0 : ∀ i < r, 0 ≤ ε i) (ms : ℕ → Msg) :
    ∀ i ≤ r, ∀ l : Log (FSAnswer (Msg := Msg) Chal Y'),
      prob (fun _ l' => HasFlip r doomed l') (derive Y' ms i) l
        ≤ (if HasFlip r doomed l then 1 else 0) + ∑ j ∈ Finset.range i, ε j
  | 0, _, l => by
    rw [derive, prob_pure, Finset.range_zero, Finset.sum_empty, add_zero]
  | i + 1, hi, l => by
    rw [derive, prob_bind, Finset.sum_range_succ, ← add_assoc]
    refine le_trans (expect_mono
      (fun t l' => prob_hasFlip_chal_le hsound hε0 hi t (ms i) _ l') _ _) ?_
    rw [expect_add, expect_const]
    exact add_le_add_left (prob_hasFlip_derive_le hsound hε0 ms i (Nat.le_of_succ_le hi) l) _

/-- Under round-by-round soundness with nonnegative errors, each at most
`εmax`, the experiment with an adversary that makes at most `Q` queries leaves
a log with a flip with probability at most `Q * εmax + ∑ i < r, ε i`. -/
theorem prob_hasFlip_fsExperiment_le (hsound : RbrSound r doomed ε)
    (hε : ∀ i < r, ε i ≤ εmax) (hε0 : ∀ i < r, 0 ≤ ε i) (h0 : 0 ≤ εmax)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg) :
    prob (fun _ l => HasFlip r doomed l) (fsExperiment r adv msgs) []
      ≤ Q * εmax + ∑ i ∈ Finset.range r, ε i := by
  classical
  have hstep : ∀ (a : α) (l : Log (FSAnswer (Msg := Msg) Chal Y')),
      prob (fun _ l' => HasFlip r doomed l')
          ((derive Y' (msgs a) r).bind fun t => .pure (a, t)) l
        ≤ (if HasFlip r doomed l then 1 else 0) + ∑ i ∈ Finset.range r, ε i := by
    intro a l
    rw [prob_bind_pure]
    exact prob_hasFlip_derive_le hsound hε0 (msgs a) r le_rfl l
  rw [fsExperiment, prob_bind]
  refine (expect_mono hstep adv []).trans ?_
  rw [expect_add, expect_const]
  exact add_le_add_left (prob_hasFlip_le hsound hε h0 hadv) _

/-- **Fiat–Shamir, with the finer bound.** Under the hypotheses of
`prob_not_doomed_le` and with nonnegative errors, the transcript is not doomed
with probability at most `Q * εmax + ∑ i < r, ε i`. -/
theorem prob_not_doomed_le_add_sum (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (hε0 : ∀ i < r, 0 ≤ ε i) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg) :
    prob (fun out _ => ¬ doomed r out.2) (fsExperiment r adv msgs) []
      ≤ Q * εmax + ∑ i ∈ Finset.range r, ε i :=
  (prob_not_doomed_le_prob_hasFlip hnil adv msgs []).trans
    (prob_hasFlip_fsExperiment_le hsound hε hε0 h0 hadv msgs)

/-- **Fiat–Shamir with the finer bound, for an acceptance predicate.** If the
verifier only accepts transcripts that are not doomed, it accepts with
probability at most `Q * εmax + ∑ i < r, ε i`. -/
theorem prob_accept_le_add_sum (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (hε0 : ∀ i < r, 0 ≤ ε i) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {accept : α → Transcript Msg Chal r → Log (FSAnswer (Msg := Msg) Chal Y') → Prop}
    (haccept : ∀ a t l, accept a t l → ¬ doomed r t) :
    prob (fun out l => accept out.1 out.2 l) (fsExperiment r adv msgs) []
      ≤ Q * εmax + ∑ i ∈ Finset.range r, ε i :=
  (prob_mono (fun out l h => haccept out.1 out.2 l h) _ _).trans
    (prob_not_doomed_le_add_sum hsound hε hε0 h0 hnil hadv msgs)

/-- **Fiat–Shamir with the finer bound, for a verifier that goes on
computing.** If an event `E` of the computation `rest` never happens after an
outcome of the experiment with a doomed transcript, it happens with probability
at most `Q * εmax + ∑ i < r, ε i`. -/
theorem prob_fsExperiment_bind_le_add_sum (hsound : RbrSound r doomed ε)
    (hε : ∀ i < r, ε i ≤ εmax) (hε0 : ∀ i < r, 0 ≤ ε i) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r → OracleComp (FSAnswer (Msg := Msg) Chal Y') β}
    {E : β → Log (FSAnswer (Msg := Msg) Chal Y') → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l → doomed r out.2 →
      Outcome (rest out) l b l' → ¬ E b l') :
    prob E ((fsExperiment r adv msgs).bind rest) []
      ≤ Q * εmax + ∑ i ∈ Finset.range r, ε i :=
  (prob_bind_le_prob fun out l b l' hout hb hEb hd => hE out l b l' hout hd hb hEb).trans
    (prob_not_doomed_le_add_sum hsound hε hε0 h0 hnil hadv msgs)

end Experiment

end CertiFri.Oracle
