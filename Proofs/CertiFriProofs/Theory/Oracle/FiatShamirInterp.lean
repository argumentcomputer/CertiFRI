import CertiFriProofs.Theory.Oracle.FiatShamir

/-!
# Fiat–Shamir when the messages are commitments

In a protocol compiled with a commitment scheme, the prover sends commitments
(Merkle roots), and the state function of the underlying protocol speaks of
what they commit to. In the random-oracle model that is read off the log: the
hash queries made so far determine what a root can be opened to. So the state
function depends on the log, which `FiatShamir.lean` does not allow.

This file extends the Fiat–Shamir theorem to that case.

* `interp l j m` reads the message `m` of round `j` against the log `l`, as a
  message in `Msg₂` of the underlying protocol (for a root: the function it can
  be opened to with the hash entries of `l`).
* `doomed` is a state function on transcripts with messages in `Msg₂`. It does
  not depend on the log, and is round-by-round sound.
* `other` is a second bad event (for a Merkle tree: an answer equal to a digest
  that already occurs in the log).
* `Settles interp other` is what the interpretation has to satisfy: a new
  challenge entry changes nothing, and a new entry that is not bad for `other`
  does not change the reading of a message that occurs in a challenge query
  of the log. For a Merkle tree this says that a root that was sent cannot be
  opened in new places without an answer hitting an earlier digest.

## Results

* `prob_hasBad_interpFlips_le`: a computation with at most `Q` queries leaves a
  log with an *interpreted flip* with probability at most `Q * εmax`.
* `doomed_mapIdx_of_supports`: in a log without an interpreted flip and
  without an entry bad for `other`, every transcript whose chain of challenge
  queries the log answers is doomed when read against that log.
* `prob_fsExperiment_bind_interp_le`: the adversary makes at most `Q` queries,
  the verifier derives the challenges and then runs `rest` with at most `R`
  queries. An event of `rest` that implies "the transcript read against the
  final log is not doomed" happens, without an entry bad for `other`, with
  probability at most `(Q + r + R) * εmax`. The probability of an entry bad
  for `other` is bounded separately, by `prob_hasBad_le`.

The theorem of `FiatShamir.lean` is the case `interp := fun _ _ m => m` with
no bad event (`settles_const`, `Transcript.mapIdx_id`).

Not covered: any particular commitment scheme. That a Merkle tree gives an
interpretation with `Settles`, and that an accepting verifier implies "not
doomed" for it, is proved where the two are composed.
-/

namespace CertiFri.Oracle

universe u u₂ v u' w w'

variable {Msg : Type u} {Msg₂ : Type u₂} {Chal : ℕ → Type v} {X' : Type u'} {Y' : X' → Type v}

/-! ## Reading the messages of a transcript -/

/-- Replace the message `m` of each round `j` by `f j m`. -/
def Transcript.mapIdx (f : ℕ → Msg → Msg₂) :
    {i : ℕ} → Transcript Msg Chal i → Transcript Msg₂ Chal i
  | _, .nil => .nil
  | _, .snoc (i := i) t m c => (t.mapIdx f).snoc (f i m) c

/-- `mapIdx` of the empty transcript. -/
@[simp] theorem Transcript.mapIdx_nil (f : ℕ → Msg → Msg₂) :
    (Transcript.nil : Transcript Msg Chal 0).mapIdx f = .nil := rfl

/-- `mapIdx` of an extended transcript reads the new message with its round. -/
@[simp] theorem Transcript.mapIdx_snoc (f : ℕ → Msg → Msg₂) {i : ℕ} (t : Transcript Msg Chal i)
    (m : Msg) (c : Chal i) : (t.snoc m c).mapIdx f = (t.mapIdx f).snoc (f i m) c := rfl

/-- Reading every message as itself changes nothing. -/
@[simp] theorem Transcript.mapIdx_id :
    ∀ {i : ℕ} (t : Transcript Msg Chal i), t.mapIdx (fun _ m => m) = t
  | _, .nil => rfl
  | _, .snoc t m c => by rw [Transcript.mapIdx_snoc, t.mapIdx_id]

/-- `mapIdx` only depends on the function at the messages of the transcript. -/
theorem Transcript.mapIdx_congr {f g : ℕ → Msg → Msg₂} :
    ∀ {i : ℕ} (t : Transcript Msg Chal i),
      (∀ j m, t.msgs[j]? = some m → f j m = g j m) → t.mapIdx f = t.mapIdx g
  | _, .nil, _ => rfl
  | _, .snoc (i := i) t m c, h => by
    have ht : t.mapIdx f = t.mapIdx g := Transcript.mapIdx_congr t fun j m' hj => h j m' (by
      rw [Transcript.msgs_snoc, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
      exact hj)
    have hm : f i m = g i m := h i m (by
      have hlast := List.getElem?_concat_length (l := t.msgs) (a := m)
      rwa [t.length_msgs] at hlast)
    rw [Transcript.mapIdx_snoc, Transcript.mapIdx_snoc, ht, hm]

/-- The prover messages a query holds, by round: for a challenge query those
of its transcript and the new one. -/
def FSQuery.msgs : FSQuery Msg Chal X' → List Msg
  | .chal t m => t.msgs ++ [m]
  | .other _ => []

/-- A challenge query of the log holds `m` as its message of round `j`. -/
def Mentions (l : Log (FSAnswer (Msg := Msg) Chal Y')) (j : ℕ) (m : Msg) : Prop :=
  ∃ e ∈ l, e.1.msgs[j]? = some m

/-- A message a log mentions is mentioned by every extension of the log. -/
theorem Mentions.of_prefix {l l' : Log (FSAnswer (Msg := Msg) Chal Y')} {j : ℕ} {m : Msg}
    (h : Mentions l j m) (hl : l <+: l') : Mentions l' j m := by
  obtain ⟨e, he, hm⟩ := h
  exact ⟨e, hl.subset he, hm⟩

/-! ## Interpretations -/

/-- The interpretation `interp` is settled by the challenge queries, up to the
bad event `other`. -/
structure Settles (interp : Log (FSAnswer (Msg := Msg) Chal Y') → ℕ → Msg → Msg₂)
    (other : Log (FSAnswer (Msg := Msg) Chal Y') →
      (x : FSQuery Msg Chal X') → FSAnswer Chal Y' x → Prop) : Prop where
  /-- A new challenge entry changes no reading. -/
  chal : ∀ (l : Log (FSAnswer (Msg := Msg) Chal Y')) {i : ℕ} (t : Transcript Msg Chal i)
    (m : Msg) (c : Chal i) (j : ℕ) (m' : Msg),
    interp (l ++ [⟨.chal t m, c⟩]) j m' = interp l j m'
  /-- A new entry that is not bad does not change the reading of a message that
  a challenge query of the log holds. -/
  stable : ∀ (l : Log (FSAnswer (Msg := Msg) Chal Y'))
    (e : Sigma (FSAnswer (Msg := Msg) Chal Y')) (j : ℕ) (m : Msg),
    Mentions l j m → ¬ other l e.1 e.2 → interp (l ++ [e]) j m = interp l j m

/-- An interpretation that ignores the log is settled, with no bad event. -/
theorem settles_const (f : ℕ → Msg → Msg₂) :
    Settles (Chal := Chal) (Y' := Y') (fun _ => f) (fun _ _ _ => False) :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The answer `y` to the query `x` flips the state as read against the log
`l`: `x` is a challenge query of a round below `r` whose transcript, read
against `l`, is doomed, and extended by its message and `y` it is not. -/
def InterpFlips (r : ℕ) (doomed : ∀ i, Transcript Msg₂ Chal i → Prop)
    (interp : Log (FSAnswer (Msg := Msg) Chal Y') → ℕ → Msg → Msg₂)
    (l : Log (FSAnswer (Msg := Msg) Chal Y')) (x : FSQuery Msg Chal X') :
    FSAnswer Chal Y' x → Prop :=
  match x with
  | .chal (i := i) t m => fun c => i < r ∧ doomed i (t.mapIdx (interp l)) ∧
      ¬ doomed (i + 1) ((t.mapIdx (interp l)).snoc (interp l i m) c)
  | .other _ => fun _ => False

section Interp

variable {r : ℕ} {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
  {interp : Log (FSAnswer (Msg := Msg) Chal Y') → ℕ → Msg → Msg₂}
  {other : Log (FSAnswer (Msg := Msg) Chal Y') →
    (x : FSQuery Msg Chal X') → FSAnswer Chal Y' x → Prop}
  {ε : ℕ → ℝ} {εmax : ℝ}

/-- `InterpFlips` on a challenge query, unfolded. -/
theorem interpFlips_chal {l : Log (FSAnswer (Msg := Msg) Chal Y')} {i : ℕ}
    {t : Transcript Msg Chal i} {m : Msg} {c : Chal i} :
    InterpFlips r doomed interp l (.chal t m) c ↔
      i < r ∧ doomed i (t.mapIdx (interp l)) ∧
        ¬ doomed (i + 1) ((t.mapIdx (interp l)).snoc (interp l i m) c) :=
  Iff.rfl

/-- Under round-by-round soundness, at most a fraction `εmax` of the answers to
any query is an interpreted flip, whatever the log. -/
theorem fractionLE_interpFlips [∀ i, Fintype (Chal i)] [∀ x, Fintype (Y' x)]
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax)
    (l : Log (FSAnswer (Msg := Msg) Chal Y')) :
    ∀ x : FSQuery Msg Chal X', FractionLE (InterpFlips r doomed interp l x) εmax
  | .chal (i := i) t m => by
    by_cases h : i < r ∧ doomed i (t.mapIdx (interp l))
    · exact ((hsound i h.1 _ (interp l i m) h.2).mono_right (hε i h.1)).mono_left
        fun c hc => hc.2.2
    · exact (FractionLE.false.mono_right h0).mono_left fun c hc => h ⟨hc.1, hc.2.1⟩
  | .other _ => (FractionLE.false.mono_right h0).mono_left fun _ hc => hc

/-- Entries that are not bad do not change the reading of a message that a
challenge query of the log holds. -/
theorem Settles.interp_append (hset : Settles interp other)
    {l s : Log (FSAnswer (Msg := Msg) Chal Y')} {j : ℕ} {m : Msg}
    (hno : ¬ HasBadFrom other l.length (l ++ s)) (hm : Mentions l j m) :
    interp (l ++ s) j m = interp l j m := by
  induction s using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton s e ih =>
    rw [← List.append_assoc] at hno ⊢
    have hno' := mt hasBadFrom_concat.mpr hno
    rw [hset.stable (l ++ s) e j m (hm.of_prefix (List.prefix_append l s))
      fun h => hno' (.inr ⟨by simp, h⟩)]
    exact ih fun h => hno' (.inl h)

/-- In a log without an interpreted flip and without an entry bad for `other`,
every transcript of at most `r` rounds whose chain of challenge queries the log
answers is doomed when read against the log, if the empty transcript is. -/
theorem doomed_mapIdx_of_supports [DecidableEq (FSQuery Msg Chal X')]
    (hset : Settles interp other) {l : Log (FSAnswer (Msg := Msg) Chal Y')}
    (hflip : ¬ HasBad (InterpFlips r doomed interp) l) (hother : ¬ HasBad other l)
    (hnil : doomed 0 .nil) :
    ∀ {i : ℕ} (t : Transcript Msg Chal i), i ≤ r → Supports l t →
      doomed i (t.mapIdx (interp l))
  | _, .nil, _, _ => hnil
  | _, .snoc (i := i) t m c, hi, hs => by
    have ht := doomed_mapIdx_of_supports hset hflip hother hnil t (Nat.le_of_succ_le hi) hs.1
    have hmem := List.of_mem_dlookup hs.2
    generalize he : (⟨FSQuery.chal t m, c⟩ : Sigma (FSAnswer (Msg := Msg) Chal Y')) = e at hmem
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
    -- Once the query is in the log it holds every message of the extended
    -- transcript, so the log reads them as the log before the query does.
    have hinterp : ∀ j m', (t.msgs ++ [m])[j]? = some m' →
        interp (l₁ ++ e :: l₂) j m' = interp l₁ j m' := by
      intro j m' hj
      have hment : Mentions (l₁ ++ [e]) j m' := ⟨e, by simp, by rw [← he]; exact hj⟩
      have hno : ¬ HasBadFrom other (l₁ ++ [e]).length ((l₁ ++ [e]) ++ l₂) := fun h =>
        hother (by simpa using h.hasBad)
      rw [← List.singleton_append, ← List.append_assoc, hset.interp_append hno hment, ← he,
        hset.chal]
    have hmap : t.mapIdx (interp (l₁ ++ e :: l₂)) = t.mapIdx (interp l₁) :=
      Transcript.mapIdx_congr t fun j m' hj => hinterp j m' (by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]
        exact hj)
    have hm : interp (l₁ ++ e :: l₂) i m = interp l₁ i m := hinterp i m (by
      have hlast := List.getElem?_concat_length (l := t.msgs) (a := m)
      rwa [t.length_msgs] at hlast)
    rw [Transcript.mapIdx_snoc, hmap, hm]
    rw [hmap] at ht
    by_contra hnd
    subst he
    exact hflip (hasBad_iff.mpr ⟨l₁, _, l₂, rfl, interpFlips_chal.mpr ⟨hi, ht, hnd⟩⟩)

end Interp

/-! ## The bounds -/

section Bound

open OracleComp

variable [DecidableEq (FSQuery Msg Chal X')] [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
  [∀ x, Fintype (Y' x)] [∀ x, Nonempty (Y' x)] {α : Type w} {β : Type w'} {r : ℕ}
  {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
  {interp : Log (FSAnswer (Msg := Msg) Chal Y') → ℕ → Msg → Msg₂}
  {other : Log (FSAnswer (Msg := Msg) Chal Y') →
    (x : FSQuery Msg Chal X') → FSAnswer Chal Y' x → Prop}
  {ε : ℕ → ℝ} {εmax : ℝ}

/-- Under round-by-round soundness with every error at most `εmax`, a
computation that makes at most `Q` queries from the empty log leaves a log with
an interpreted flip with probability at most `Q * εmax`. -/
theorem prob_hasBad_interpFlips_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) {c : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ}
    (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (InterpFlips r doomed interp) l) c [] ≤ Q * εmax := by
  have h := prob_hasBad_le (bad := InterpFlips r doomed interp) (ε := fun _ => εmax)
    (fun _ => h0) (fun l x _ => fractionLE_interpFlips hsound hε h0 l x) hc
  rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h

/-- **Fiat–Shamir with interpreted messages.** The state function `doomed` of
the underlying protocol is round-by-round sound for `r` rounds with every error
at most `εmax`, the empty transcript is doomed, and the interpretation is
settled up to the bad event `other`. An adversary makes at most `Q` queries and
outputs prover messages, the verifier derives the challenges and then runs
`rest`, with at most `R` queries. Suppose that after an outcome of the
experiment, the event `E` of `rest` in a log without an entry bad for `other`
implies that the transcript, read against that log, is not doomed. Then `E`
happens without an entry bad for `other` with probability at most
`(Q + r + R) * εmax`. -/
theorem prob_fsExperiment_bind_interp_le (hsound : RbrSound r doomed ε)
    (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil)
    (hset : Settles interp other) {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ}
    (hadv : adv.QueryBound Q) (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r → OracleComp (FSAnswer (Msg := Msg) Chal Y') β} {R : ℕ}
    (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (FSAnswer (Msg := Msg) Chal Y') → Prop}
    (hE : ∀ out l b l', Outcome (fsExperiment r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' → ¬ HasBad other l' →
      ¬ doomed r (out.2.mapIdx (interp l'))) :
    prob (fun b l => E b l ∧ ¬ HasBad other l) ((fsExperiment r adv msgs).bind rest) []
      ≤ (Q + r + R) * εmax := by
  have hflip := prob_hasBad_interpFlips_le (interp := interp) hsound hε h0
    ((queryBound_fsExperiment (r := r) hadv msgs).bind hrest)
  rw [Nat.cast_add, Nat.cast_add] at hflip
  refine le_trans (prob_mono_of_outcome fun b l' hout hb => ?_) hflip
  obtain ⟨out, l, hexp, hrun⟩ := outcome_bind.mp hout
  by_contra hno
  exact hE out l b l' hexp hrun hb.1 hb.2 (doomed_mapIdx_of_supports hset hno hb.2 hnil out.2
    le_rfl ((supports_of_outcome_fsExperiment hexp).of_prefix hrun.prefix))

/-- **Fiat–Shamir with interpreted messages, without a continuation.** Under
the hypotheses of `prob_fsExperiment_bind_interp_le`, the transcript of the
experiment, read against the final log, is not doomed, without an entry bad for
`other`, with probability at most `(Q + r) * εmax`. -/
theorem prob_not_doomed_mapIdx_le (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax)
    (h0 : 0 ≤ εmax) (hnil : doomed 0 .nil) (hset : Settles interp other)
    {adv : OracleComp (FSAnswer (Msg := Msg) Chal Y') α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg) :
    prob (fun out l => ¬ doomed r (out.2.mapIdx (interp l)) ∧ ¬ HasBad other l)
      (fsExperiment r adv msgs) [] ≤ (Q + r) * εmax := by
  have hflip := prob_hasBad_interpFlips_le (interp := interp) hsound hε h0
    (queryBound_fsExperiment (r := r) hadv msgs)
  rw [Nat.cast_add] at hflip
  refine le_trans (prob_mono_of_outcome fun out l' hout hb => ?_) hflip
  by_contra hno
  exact hb.1 (doomed_mapIdx_of_supports hset hno hb.2 hnil out.2 le_rfl
    (supports_of_outcome_fsExperiment hout))

end Bound

end CertiFri.Oracle
