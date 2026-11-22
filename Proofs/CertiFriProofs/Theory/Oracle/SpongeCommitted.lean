import CertiFriProofs.Theory.Oracle.MerkleCommitted

/-!
# Incremental sponge Fiat–Shamir with Merkle commitments (`c = 3 / 2`)

This file builds the incremental sponge analogue of `FiatShamirInterp.lean` and
`MerkleCommitted.lean` on top of the `SpongeQuery` / `JointHit` theory proved
in `MerkleFrozen.lean`.

In an incremental sponge, each challenge step `i` queries `.chal i prev m`
with only the previous chaining digest `prev : D` and step `i`'s message `m`
(carrying at most `M ≤ 3` Merkle digests — specifically **`M = 1`** when each
root is absorbed individually), receiving `(nextState, chal_i) : D × Chal i`.

## Main results (zero `sorry`)

* `spongeSupports_unique_transcript`: in any log without `SpongeHit`, every
  chaining state `s` supports at most one transcript `t` from `s₀`.
* `spongeSupports_prefix_of_snoc`: in any log without `SpongeHit`, the chain
  leading to `prev` at a `.chal i prev m` entry already lies strictly before
  that entry in the log.
* `doomed_mapIdx_of_spongeSupports`: in a log without `SpongeInterpFlips` and
  without `JointHit`, every sponge-supported transcript of `≤ r` steps is doomed
  when read from the log's committed rows.
* `prob_spongeExperiment_bind_committedRow_le`:
  whenever each step brings at most `M ≤ 3` digests (in particular `M = 1`),
  ```
  prob E ((spongeExperiment s₀ r adv msgs).bind rest) []
    ≤ (Q + r + R) * εmax + 3 * (Q + r + R) ^ 2 / (2 * Fintype.card D)
  ```
-/

namespace CertiFri.Oracle

universe u u₂ w w'

open OracleComp Merkle MerkleRO

/-! ## Incremental sponge Fiat–Shamir derivation and support -/

section SpongeFS

variable {Msg : Type u} {Msg₂ : Type u₂} {Chal : ℕ → Type} {D : Type}
  {X' : Type} {Y' : X' → Type}

/-- The transcript and final sponge chaining state produced by running the
incremental sponge oracle `f` from `s₀` on messages `ms 0, …, ms (i - 1)`. -/
def spongeTranscript (f : ∀ x : SpongeQuery Msg D X', SpongeAnswer Chal D Y' x)
    (s₀ : D) (ms : ℕ → Msg) : (i : ℕ) → Transcript Msg Chal i × D
  | 0 => (.nil, s₀)
  | i + 1 =>
    let (t, prev) := spongeTranscript f s₀ ms i
    let (next, c) := f (.chal i prev (ms i))
    (t.snoc (ms i) c, next)

/-- Oracle computation deriving the `i`-step incremental sponge transcript and
final chaining state from `s₀` on `ms`. -/
def spongeDerive (Y' : X' → Type) (s₀ : D) (ms : ℕ → Msg) :
    (i : ℕ) → OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') (Transcript Msg Chal i × D)
  | 0 => .pure (.nil, s₀)
  | i + 1 =>
    (spongeDerive Y' s₀ ms i).bind fun (t, prev) =>
      .queryBind (.chal i prev (ms i)) fun (next, c) =>
        .pure (t.snoc (ms i) c, next)

/-- The incremental sponge Fiat–Shamir experiment: the adversary runs and
returns `a`, and the verifier derives the `r`-step sponge transcript for
`msgs a`. -/
def spongeExperiment {α : Type w} (s₀ : D) (r : ℕ)
    (adv : OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') α) (msgs : α → ℕ → Msg) :
    OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') (α × Transcript Msg Chal r × D) :=
  adv.bind fun a => (spongeDerive Y' s₀ (msgs a) r).bind fun ts => .pure (a, ts)

theorem queryBound_spongeDerive (s₀ : D) (ms : ℕ → Msg) :
    ∀ i, (spongeDerive (Chal := Chal) Y' s₀ ms i).QueryBound i
  | 0 => trivial
  | i + 1 =>
    (queryBound_spongeDerive s₀ ms i).bind fun _ =>
      fun _ => trivial

theorem queryBound_spongeExperiment {α : Type w} {s₀ : D} {r Q : ℕ}
    {adv : OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') α} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg) :
    (spongeExperiment s₀ r adv msgs).QueryBound (Q + r) :=
  hadv.bind fun a =>
    (queryBound_spongeDerive s₀ (msgs a) r).bind (m := 0) fun _ => trivial

/-- Inductive witness that log `l` contains a valid incremental sponge chain
from `s₀` to `s` producing transcript `t`. -/
inductive SpongeSupports (s₀ : D) (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) :
    {i : ℕ} → Transcript Msg Chal i → D → Prop
  | nil : SpongeSupports s₀ l .nil s₀
  | snoc {i : ℕ} {t : Transcript Msg Chal i} {prev next : D} {m : Msg} {c : Chal i} :
      SpongeSupports s₀ l t prev →
      (⟨SpongeQuery.chal i prev m, (next, c)⟩ : Sigma (SpongeAnswer Chal D Y')) ∈ l →
      SpongeSupports s₀ l (t.snoc m c) next

theorem SpongeSupports.mono {s₀ : D} {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hl : l ⊆ l') {i : ℕ} {t : Transcript Msg Chal i} {s : D}
    (h : SpongeSupports s₀ l t s) : SpongeSupports s₀ l' t s := by
  induction h with
  | nil => exact .nil
  | snoc _ hmem ih => exact .snoc ih (hl hmem)

theorem SpongeSupports.of_prefix {s₀ : D} {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hl : l <+: l') {i : ℕ} {t : Transcript Msg Chal i} {s : D}
    (h : SpongeSupports s₀ l t s) : SpongeSupports s₀ l' t s :=
  h.mono hl.subset

/-- A `.chal` entry of `l` holds `m` at step `j`. -/
def SpongeMentions (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) (j : ℕ) (m : Msg) : Prop :=
  ∃ prev next c,
    (⟨SpongeQuery.chal j prev m, (next, c)⟩ : Sigma (SpongeAnswer Chal D Y')) ∈ l

theorem SpongeMentions.mono {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')} {j : ℕ} {m : Msg}
    (h : SpongeMentions l j m) (hl : l ⊆ l') : SpongeMentions l' j m := by
  obtain ⟨prev, next, c, hmem⟩ := h
  exact ⟨prev, next, c, hl hmem⟩

theorem SpongeMentions.of_prefix {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')} {j : ℕ}
    {m : Msg} (h : SpongeMentions l j m) (hl : l <+: l') : SpongeMentions l' j m :=
  h.mono hl.subset

/-- Every message in a sponge-supported transcript is mentioned by the log. -/
theorem SpongeSupports.mentions {s₀ : D} {l : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    {i : ℕ} {t : Transcript Msg Chal i} {s : D} (h : SpongeSupports s₀ l t s) :
    ∀ j m, t.msgs[j]? = some m → SpongeMentions l j m := by
  induction h with
  | nil =>
    intro j m hj
    simp [Transcript.msgs] at hj
  | @snoc i t prev next m c hsup hmem ih =>
    intro j m' hj
    rw [Transcript.msgs_snoc] at hj
    by_cases hlt : j < t.msgs.length
    · rw [List.getElem?_append_left hlt] at hj
      exact ih j m' hj
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hj
      have hlen : t.msgs.length = i := t.length_msgs
      rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hlt) with rfl | hgt
      · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [hlen]
        exact ⟨prev, next, c, hmem⟩
      · have : j - t.msgs.length ≠ 0 := by omega
        cases hsub : j - t.msgs.length with
        | zero => omega
        | succ k => rw [hsub] at hj; simp at hj

section Outcome

variable [DecidableEq (SpongeQuery Msg D X')]

theorem outcome_spongeDerive_supports {s₀ : D} {ms : ℕ → Msg} :
    ∀ {i : ℕ} {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
      {ts : Transcript Msg Chal i × D},
      Outcome (spongeDerive Y' s₀ ms i) l ts l' →
      SpongeSupports s₀ l' ts.1 ts.2 ∧ ts.1.msgs = (List.range i).map ms
  | 0, _, _, _, h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil, rfl⟩
  | i + 1, l, l', ts, h => by
    rw [spongeDerive, outcome_bind] at h
    obtain ⟨⟨t, prev⟩, l₁, h₁, h₂⟩ := h
    obtain ⟨⟨next, c⟩, l₂, hc, rfl, rfl⟩ := outcome_queryBind.mp h₂
    obtain ⟨hsup, hmsgs⟩ := outcome_spongeDerive_supports h₁
    refine ⟨.snoc (hsup.of_prefix hc.prefix) (List.of_mem_dlookup hc.dlookup_query), ?_⟩
    rw [Transcript.msgs_snoc, hmsgs, List.range_succ, List.map_append, List.map_singleton]

theorem outcome_spongeDerive_eq_transcript {s₀ : D} {ms : ℕ → Msg}
    (f : ∀ x : SpongeQuery Msg D X', SpongeAnswer Chal D Y' x) :
    ∀ {i : ℕ} {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
      {ts : Transcript Msg Chal i × D},
      Outcome (spongeDerive Y' s₀ ms i) l ts l' →
      (∀ x y, l'.dlookup x = some y → f x = y) →
      ts = spongeTranscript f s₀ ms i
  | 0, _, _, _, h, _ => by
    obtain ⟨rfl, _⟩ := h
    rfl
  | i + 1, l, l', ts, h, hf => by
    rw [spongeDerive, outcome_bind] at h
    obtain ⟨⟨t, prev⟩, l₁, h₁, h₂⟩ := h
    obtain ⟨⟨next, c⟩, l₂, hc, rfl, rfl⟩ := outcome_queryBind.mp h₂
    have hf₁ : ∀ x y, l₁.dlookup x = some y → f x = y := fun x y hxy =>
      hf x y (dlookup_of_prefix hxy hc.prefix)
    have hprev := outcome_spongeDerive_eq_transcript f h₁ hf₁
    have hstep := hf _ _ hc.dlookup_query
    rw [spongeTranscript, ← hprev]
    dsimp only
    rw [hstep]

theorem outcome_spongeExperiment {α : Type w} {s₀ : D} {r : ℕ}
    {adv : OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') α} {msgs : α → ℕ → Msg}
    {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    {out : α × Transcript Msg Chal r × D}
    (h : Outcome (spongeExperiment s₀ r adv msgs) l out l') :
    ∃ l₁, Outcome adv l out.1 l₁ ∧
      Outcome (spongeDerive Y' s₀ (msgs out.1) r) l₁ out.2 l' := by
  rw [spongeExperiment, outcome_bind] at h
  obtain ⟨a, l₁, ha, hd⟩ := h
  rw [outcome_bind] at hd
  obtain ⟨ts, l₂, hts, rfl, rfl⟩ := hd
  exact ⟨l₁, ha, hts⟩

theorem eq_spongeTranscript_of_outcome_spongeExperiment {α : Type w} {s₀ : D} {r : ℕ}
    {adv : OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') α} {msgs : α → ℕ → Msg}
    {l₀ l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    {out : α × Transcript Msg Chal r × D}
    (h : Outcome (spongeExperiment s₀ r adv msgs) l₀ out l) (hl : l <+: l')
    (f : ∀ x : SpongeQuery Msg D X', SpongeAnswer Chal D Y' x) :
    out.2 = spongeTranscript (l'.toFun f) s₀ (msgs out.1) r := by
  obtain ⟨_, -, hd⟩ := outcome_spongeExperiment h
  exact outcome_spongeDerive_eq_transcript (l'.toFun f) hd fun x y hxy =>
    Log.toFun_of_dlookup f (dlookup_of_prefix hxy hl)

end Outcome

/-! ## Uniqueness and chronological ordering under `¬ HasBad (SpongeHit s₀)` -/

/-- No `.chal` entry outputs `s₀` when `¬ HasBad (SpongeHit s₀) l`. -/
theorem sponge_next_ne_init {s₀ : D} {l : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hno : ¬ HasBad (SpongeHit s₀) l) {i : ℕ} {prev next : D} {m : Msg} {c : Chal i}
    (hmem : (⟨SpongeQuery.chal i prev m, (next, c)⟩ : Sigma (SpongeAnswer Chal D Y')) ∈ l) :
    next ≠ s₀ := by
  intro heq
  subst heq
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
  exact hno (hasBad_iff.mpr ⟨l₁, ⟨.chal i prev m, (next, c)⟩, l₂, rfl, Or.inl rfl⟩)

/-- If two `.chal` entries in `l` output the same chaining state `next` and
`¬ HasBad (SpongeHit s₀) l`, then they must occur at the same position in `l`
(and hence be equal). -/
theorem sponge_chal_eq_of_next_eq {s₀ : D} {l : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hno : ¬ HasBad (SpongeHit s₀) l)
    {i₁ i₂ : ℕ} {prev₁ prev₂ next : D} {m₁ m₂ : Msg} {c₁ : Chal i₁} {c₂ : Chal i₂}
    (h₁ : (⟨SpongeQuery.chal i₁ prev₁ m₁, (next, c₁)⟩ : Sigma (SpongeAnswer Chal D Y')) ∈ l)
    (h₂ : (⟨SpongeQuery.chal i₂ prev₂ m₂, (next, c₂)⟩ : Sigma (SpongeAnswer Chal D Y')) ∈ l) :
    (⟨SpongeQuery.chal i₁ prev₁ m₁, (next, c₁)⟩ : Sigma (SpongeAnswer Chal D Y')) =
      ⟨SpongeQuery.chal i₂ prev₂ m₂, (next, c₂)⟩ := by
  obtain ⟨p₁, hp₁, he₁⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨p₂, hp₂, he₂⟩ := List.mem_iff_getElem.mp h₂
  rcases lt_trichotomy p₁ p₂ with hlt | rfl | hgt
  · exfalso
    have hsplit : l = l.take p₂ ++ l[p₂] :: l.drop (p₂ + 1) := by
      rw [← List.drop_eq_getElem_cons hp₂, List.take_append_drop]
    have hmem₁ : l[p₁] ∈ l.take p₂ := by
      rw [List.mem_iff_getElem]
      exact ⟨p₁, by simp [hlt]; omega, by simp [List.getElem_take]⟩
    refine hno (hasBad_iff.mpr ⟨l.take p₂, l[p₂], l.drop (p₂ + 1), hsplit, ?_⟩)
    rw [he₂]
    exact Or.inr ⟨l[p₁], hmem₁, by rw [he₁]; simp [spongeStates]⟩
  · exact he₁.symm.trans he₂
  · exfalso
    have hsplit : l = l.take p₁ ++ l[p₁] :: l.drop (p₁ + 1) := by
      rw [← List.drop_eq_getElem_cons hp₁, List.take_append_drop]
    have hmem₂ : l[p₂] ∈ l.take p₁ := by
      rw [List.mem_iff_getElem]
      exact ⟨p₂, by simp [hgt]; omega, by simp [List.getElem_take]⟩
    refine hno (hasBad_iff.mpr ⟨l.take p₁, l[p₁], l.drop (p₁ + 1), hsplit, ?_⟩)
    rw [he₁]
    exact Or.inr ⟨l[p₂], hmem₂, by rw [he₂]; simp [spongeStates]⟩

/-- **Uniqueness of sponge-supported transcripts.** In a log without
`SpongeHit`, any chaining state `s` supports at most one transcript of a given
length `i`. -/
theorem spongeSupports_unique {s₀ : D} {l : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hno : ¬ HasBad (SpongeHit s₀) l) :
    ∀ {i : ℕ} {t₁ t₂ : Transcript Msg Chal i} {s : D},
      SpongeSupports s₀ l t₁ s → SpongeSupports s₀ l t₂ s → t₁ = t₂
  | 0, .nil, .nil, _, _, _ => rfl
  | i + 1, .snoc t₁ m₁ c₁, .snoc t₂ m₂ c₂, s, h₁, h₂ => by
    cases h₁ with
    | snoc hsup₁ hmem₁ =>
      cases h₂ with
      | snoc hsup₂ hmem₂ =>
        have heq := sponge_chal_eq_of_next_eq hno hmem₁ hmem₂
        have hq : SpongeQuery.chal i _ m₁ = SpongeQuery.chal i _ m₂ := congrArg Sigma.fst heq
        injection hq with _ hprev hm
        subst hprev
        subst hm
        have ha : (s, c₁) = (s, c₂) := eq_of_heq (Sigma.mk.inj heq).2
        injection ha with _ hc
        subst hc
        rw [spongeSupports_unique hno hsup₁ hsup₂]

/-- **Chronological ordering of sponge chains.** In a log without `SpongeHit`,
if `e = ⟨.chal i prev m, (next, c)⟩` appears as `l₁ ++ e :: l₂` and `t` is
supported in the full log at `prev`, then `t` is already supported in the
strict prefix `l₁` before `e`. -/
theorem spongeSupports_prefix_of_snoc {s₀ : D} :
    ∀ {i : ℕ} {t : Transcript Msg Chal i} {prev next : D} {m : Msg} {c : Chal i}
      {l₁ l₂ : Log (SpongeAnswer (Msg := Msg) Chal D Y')},
      ¬ HasBad (SpongeHit s₀) (l₁ ++ ⟨.chal i prev m, (next, c)⟩ :: l₂) →
      SpongeSupports s₀ (l₁ ++ ⟨.chal i prev m, (next, c)⟩ :: l₂) t prev →
      SpongeSupports s₀ l₁ t prev
  | 0, .nil, _, _, _, _, _, _, _, hsup => by
    cases hsup
    exact .nil
  | i + 1, .snoc t' m' c', prev, next, m, c, l₁, l₂, hno, hsup => by
    cases hsup with
    | @snoc _ _ prev' _ _ _ hsup' hmem' =>
      have hne : (⟨SpongeQuery.chal i prev' m', (prev, c')⟩ : Sigma (SpongeAnswer Chal D Y')) ≠
          ⟨SpongeQuery.chal (i + 1) prev m, (next, c)⟩ := by
        intro heq
        have := congrArg Sigma.fst heq
        injection this with hi
        omega
      have hnot_l₂ : (⟨SpongeQuery.chal i prev' m', (prev, c')⟩ :
          Sigma (SpongeAnswer Chal D Y')) ∉ l₂ := by
        intro hl₂
        obtain ⟨l₂a, l₂b, rfl⟩ := List.append_of_mem hl₂
        refine hno (hasBad_iff.mpr
          ⟨l₁ ++ ⟨.chal (i + 1) prev m, (next, c)⟩ :: l₂a,
           ⟨.chal i prev' m', (prev, c')⟩, l₂b, by simp [List.append_assoc], ?_⟩)
        refine Or.inr ⟨⟨.chal (i + 1) prev m, (next, c)⟩, by simp, ?_⟩
        simp [spongeStates]
      have hl₁ : (⟨SpongeQuery.chal i prev' m', (prev, c')⟩ :
          Sigma (SpongeAnswer Chal D Y')) ∈ l₁ := by
        rcases List.mem_append.mp hmem' with h | h
        · exact h
        · rcases List.mem_cons.mp h with heq | hl₂
          · exact absurd heq hne
          · exact absurd hl₂ hnot_l₂
      obtain ⟨l₁a, l₁b, rfl⟩ := List.append_of_mem hl₁
      have hno' : ¬ HasBad (SpongeHit s₀)
          (l₁a ++ ⟨.chal i prev' m', (prev, c')⟩ :: (l₁b ++ ⟨.chal (i + 1) prev m, (next, c)⟩ :: l₂)) := by
        simpa [List.append_assoc] using hno
      have hsup'' : SpongeSupports s₀
          (l₁a ++ ⟨.chal i prev' m', (prev, c')⟩ :: (l₁b ++ ⟨.chal (i + 1) prev m, (next, c)⟩ :: l₂))
          t' prev' := by
        simpa [List.append_assoc] using hsup'
      have hpre := spongeSupports_prefix_of_snoc hno' hsup''
      exact .snoc (hpre.mono (by simp)) (by simp)

/-! ## Settled interpretations and sponge interpreted flips -/

/-- Settling property for an interpretation of messages against a sponge log. -/
structure SpongeSettles (interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂)
    (other : Log (SpongeAnswer (Msg := Msg) Chal D Y') →
      (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → Prop) : Prop where
  /-- A new challenge entry changes no reading. -/
  chal : ∀ (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) {i : ℕ} (prev : D) (m : Msg)
    (y : D × Chal i) (j : ℕ) (m' : Msg),
    interp (l ++ [⟨.chal i prev m, y⟩]) j m' = interp l j m'
  /-- A new entry that is not bad does not change the reading of a message
  mentioned by a challenge entry of `l`. -/
  stable : ∀ (l : Log (SpongeAnswer (Msg := Msg) Chal D Y'))
    (e : Sigma (SpongeAnswer (Msg := Msg) Chal D Y')) (j : ℕ) (m : Msg),
    SpongeMentions l j m → ¬ other l e.1 e.2 → interp (l ++ [e]) j m = interp l j m

theorem SpongeSettles.interp_append
    {interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂}
    {other : Log (SpongeAnswer (Msg := Msg) Chal D Y') →
      (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → Prop}
    (hset : SpongeSettles interp other)
    {l s : Log (SpongeAnswer (Msg := Msg) Chal D Y')} {j : ℕ} {m : Msg}
    (hno : ¬ HasBadFrom other l.length (l ++ s)) (hm : SpongeMentions l j m) :
    interp (l ++ s) j m = interp l j m := by
  induction s using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton s e ih =>
    rw [← List.append_assoc] at hno ⊢
    have hno' := mt hasBadFrom_concat.mpr hno
    rw [hset.stable (l ++ s) e j m (hm.of_prefix (List.prefix_append l s))
      fun h => hno' (.inr ⟨by simp, h⟩)]
    exact ih fun h => hno' (.inl h)

/-- An interpreted flip in a sponge log: a `.chal i prev m` query whose
chaining state `prev` uniquely supports a doomed transcript `t` in `l`, and
whose returned challenge `c` flips the state to not doomed. -/
def SpongeInterpFlips (s₀ : D) (r : ℕ) (doomed : ∀ i, Transcript Msg₂ Chal i → Prop)
    (interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂)
    (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) :
    (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → Prop
  | .chal i prev m, (_, c) =>
      i < r ∧ ∃ t : Transcript Msg Chal i,
        SpongeSupports s₀ l t prev ∧
        (∀ t' : Transcript Msg Chal i, SpongeSupports s₀ l t' prev → t' = t) ∧
        doomed i (t.mapIdx (interp l)) ∧
        ¬ doomed (i + 1) ((t.mapIdx (interp l)).snoc (interp l i m) c)
  | .other _, _ => False

theorem fractionLE_spongeInterpFlips [Fintype D] [Nonempty D] [∀ i, Fintype (Chal i)]
    [∀ q, Fintype (Y' q)] {s₀ : D} {r : ℕ} {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
    {interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂}
    {ε : ℕ → ℝ} {εmax : ℝ}
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax)
    (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) :
    ∀ x : SpongeQuery Msg D X',
      FractionLE (SpongeInterpFlips s₀ r doomed interp l x) εmax
  | .chal i prev m => by
    by_cases h : i < r ∧ ∃ t : Transcript Msg Chal i,
        SpongeSupports s₀ l t prev ∧
        (∀ t' : Transcript Msg Chal i, SpongeSupports s₀ l t' prev → t' = t) ∧
        doomed i (t.mapIdx (interp l))
    · obtain ⟨hi, t, hsup, huniq, hdoom⟩ := h
      have hbad := (hsound i hi (t.mapIdx (interp l)) (interp l i m) hdoom).mono_right (hε i hi)
      obtain ⟨S, hScard, hSmem⟩ := hbad
      refine ⟨(Finset.univ : Finset D) ×ˢ S, ?_, fun y hy => ?_⟩
      · show (((Finset.univ : Finset D) ×ˢ S).card : ℝ) ≤ εmax * (Fintype.card (D × Chal i) : ℝ)
        rw [Finset.card_product, Finset.card_univ, Fintype.card_prod]
        have hD0 : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
        push_cast
        calc (Fintype.card D : ℝ) * (S.card : ℝ)
            ≤ (Fintype.card D : ℝ) * (εmax * Fintype.card (Chal i)) :=
              mul_le_mul_of_nonneg_left hScard hD0
          _ = εmax * ((Fintype.card D : ℝ) * Fintype.card (Chal i)) := by ring
      · obtain ⟨_, t', hsup', _, _, hnd⟩ := hy
        have hteq : t' = t := huniq t' hsup'
        subst hteq
        exact Finset.mem_product.mpr ⟨Finset.mem_univ y.1, hSmem y.2 hnd⟩
    · refine (FractionLE.false.mono_right h0).mono_left fun y hy => ?_
      obtain ⟨hi, t, hsup, huniq, hdoom, _⟩ := hy
      exact h ⟨hi, t, hsup, huniq, hdoom⟩
  | .other _ => (FractionLE.false.mono_right h0).mono_left fun _ hc => hc

theorem prob_hasBad_spongeInterpFlips_le [DecidableEq (SpongeQuery Msg D X')]
    [Fintype D] [Nonempty D] [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    [∀ q, Fintype (Y' q)] [∀ q, Nonempty (Y' q)]
    {s₀ : D} {r : ℕ} {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
    {interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂}
    {ε : ℕ → ℝ} {εmax : ℝ} {α : Type w}
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax)
    {c : OracleComp (SpongeAnswer (Msg := Msg) Chal D Y') α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (SpongeInterpFlips s₀ r doomed interp) l) c [] ≤ Q * εmax := by
  have h := prob_hasBad_le (bad := SpongeInterpFlips s₀ r doomed interp) (ε := fun _ => εmax)
    (fun _ => h0) (fun l x _ => fractionLE_spongeInterpFlips hsound hε h0 l x) hc
  rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h

/-- **Main inductive invariant for incremental sponge Fiat–Shamir.**
In any log without `SpongeInterpFlips`, `SpongeHit`, or `other`, every
sponge-supported transcript of `≤ r` rounds is doomed when read against `l`. -/
theorem doomed_mapIdx_of_spongeSupports
    {s₀ : D} {r : ℕ} {doomed : ∀ i, Transcript Msg₂ Chal i → Prop}
    {interp : Log (SpongeAnswer (Msg := Msg) Chal D Y') → ℕ → Msg → Msg₂}
    {other : Log (SpongeAnswer (Msg := Msg) Chal D Y') →
      (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → Prop}
    (hset : SpongeSettles interp other)
    {l : Log (SpongeAnswer (Msg := Msg) Chal D Y')}
    (hflip : ¬ HasBad (SpongeInterpFlips s₀ r doomed interp) l)
    (hsponge : ¬ HasBad (SpongeHit s₀) l)
    (hother : ¬ HasBad other l)
    (hnil : doomed 0 .nil) :
    ∀ {i : ℕ} {t : Transcript Msg Chal i} {s : D},
      i ≤ r → SpongeSupports s₀ l t s → doomed i (t.mapIdx (interp l))
  | 0, .nil, _, _, _ => hnil
  | i + 1, .snoc t m c, s, hi, hsup => by
    cases hsup with
    | @snoc _ _ prev _ _ _ hsup_prev hmem =>
      have ht := doomed_mapIdx_of_spongeSupports hset hflip hsponge hother hnil
        (Nat.le_of_succ_le hi) hsup_prev
      obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
      have hsup₁ : SpongeSupports s₀ l₁ t prev :=
        spongeSupports_prefix_of_snoc hsponge hsup_prev
      have hsponge₁ : ¬ HasBad (SpongeHit s₀) l₁ := fun h =>
        hsponge (by
          obtain ⟨a, e, b, heq, hbad⟩ := hasBad_iff.mp h
          exact hasBad_iff.mpr ⟨a, e,
            b ++ (⟨SpongeQuery.chal i prev m, (s, c)⟩ : Sigma (SpongeAnswer Chal D Y')) :: l₂,
            by rw [heq, List.append_assoc, List.cons_append], hbad⟩)
      have huniq₁ : ∀ t' : Transcript Msg Chal i, SpongeSupports s₀ l₁ t' prev → t' = t :=
        fun t' ht' => spongeSupports_unique hsponge₁ ht' hsup₁
      let e₀ : Sigma (SpongeAnswer (Msg := Msg) Chal D Y') := ⟨.chal i prev m, (s, c)⟩
      have hno_other : ¬ HasBadFrom other (l₁ ++ [e₀]).length ((l₁ ++ [e₀]) ++ l₂) := fun h =>
        hother (by simpa [e₀] using h.hasBad)
      have hinterp_prev : ∀ j m', t.msgs[j]? = some m' →
          interp (l₁ ++ ⟨.chal i prev m, (s, c)⟩ :: l₂) j m' = interp l₁ j m' := by
        intro j m' hj
        have hment₁ : SpongeMentions l₁ j m' := hsup₁.mentions j m' hj
        have hment : SpongeMentions (l₁ ++ [e₀]) j m' :=
          hment₁.of_prefix (List.prefix_append l₁ _)
        rw [← List.singleton_append, ← List.append_assoc]
        exact (hset.interp_append hno_other hment).trans (hset.chal l₁ prev m (s, c) j m')
      have hmap : t.mapIdx (interp (l₁ ++ ⟨.chal i prev m, (s, c)⟩ :: l₂)) =
          t.mapIdx (interp l₁) :=
        Transcript.mapIdx_congr t hinterp_prev
      have hm : interp (l₁ ++ ⟨.chal i prev m, (s, c)⟩ :: l₂) i m = interp l₁ i m := by
        have hment : SpongeMentions (l₁ ++ [e₀]) i m :=
          ⟨prev, s, c, by simp [e₀]⟩
        rw [← List.singleton_append, ← List.append_assoc]
        exact (hset.interp_append hno_other hment).trans (hset.chal l₁ prev m (s, c) i m)
      rw [Transcript.mapIdx_snoc, hmap, hm]
      rw [hmap] at ht
      by_contra hnd
      exact hflip (hasBad_iff.mpr ⟨l₁, ⟨.chal i prev m, (s, c)⟩, l₂, rfl,
        hi, t, hsup₁, huniq₁, ht, hnd⟩)

end SpongeFS

/-! ## Sponge Merkle openings, binding, stability, and committed rows -/

section SpongeMerkle

variable {Msg : Type u} {Msg₂ : Type u₂} {Chal : ℕ → Type} {T D : Type}

/-- Observation reading the digest of every hash entry of a sponge-Merkle log. -/
def spongeHashObs :
    (x : SpongeQuery Msg D (HashQuery T D)) → SpongeMerkleAnswer Msg Chal T D x → Option D
  | .chal _ _ _, _ => none
  | .other _, y => some y

/-- A sponge hash collision triggers `JointHit` (specifically `SpongeMerkleHit`). -/
theorem hasBad_jointHit_of_logCollision {s₀ : D} {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    (h : LogCollision spongeHashObs l) : HasBad (JointHit s₀ stepDigestsOf r) l := by
  refine (logCollision_iff_hasBad.mp h).imp fun l₁ x y hhit => ?_
  obtain ⟨⟨x', y'⟩, he, _, z, hz, hy⟩ := hhit
  cases x with
  | chal _ _ _ => cases hy
  | other q =>
    cases x' with
    | chal _ _ _ => cases hz
    | other q' =>
      obtain rfl : y' = z := Option.some.inj hz
      obtain rfl : y = y' := Option.some.inj hy
      exact ⟨⟨.other q', y⟩, he, List.mem_append_right _ (by
        cases q' with
        | rows _ => exact List.mem_singleton_self y
        | node _ _ => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self y)))⟩

theorem not_logCollision_sponge_of_not_jointHit {s₀ : D} {stepDigestsOf : ℕ → Msg → List D}
    {r : ℕ} {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    (h : ¬ HasBad (JointHit s₀ stepDigestsOf r) l) : ¬ LogCollision spongeHashObs l :=
  fun hc => h (hasBad_jointHit_of_logCollision hc)

variable [DecidableEq (SpongeQuery Msg D (HashQuery T D))]

/-- Answer the sponge log holds for hash query `q`. -/
def spongeHashLookup (l : Log (SpongeMerkleAnswer Msg Chal T D)) (q : HashQuery T D) : Option D :=
  List.dlookup (SpongeQuery.other q) l

theorem spongeHashLookup_of_prefix {l l' : Log (SpongeMerkleAnswer Msg Chal T D)} (hl : l <+: l')
    {q : HashQuery T D} {y : D} (h : spongeHashLookup l q = some y) :
    spongeHashLookup l' q = some y :=
  dlookup_of_prefix h hl

theorem spongeHashLookup_append_chal (l : Log (SpongeMerkleAnswer Msg Chal T D)) {i : ℕ}
    (prev : D) (m : Msg) (y : D × Chal i) (q : HashQuery T D) :
    spongeHashLookup (l ++ [⟨.chal i prev m, y⟩]) q = spongeHashLookup l q := by
  unfold spongeHashLookup
  rw [List.dlookup_append, List.dlookup_cons_ne _ _ (by simp), List.dlookup_nil, Option.or_none]

/-- The Merkle hasher of a sponge log (reusing `MerkleRO.Dig`). -/
def spongeLogHasher (l : Log (SpongeMerkleAnswer Msg Chal T D)) : MerkleHasher T (Dig T D) where
  hashRows xs := (spongeHashLookup l (.rows xs)).elim (.leaf xs) .known
  compress a b :=
    match a, b with
    | .known a', .known b' => (spongeHashLookup l (.node a' b')).elim (.pair a b) .known
    | _, _ => .pair a b

private theorem spongeLogHasher_hashRows_eq_known {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    {xs : Array T} {y : D} :
    (spongeLogHasher l).hashRows xs = .known y ↔ spongeHashLookup l (.rows xs) = some y := by
  simp only [spongeLogHasher]
  cases spongeHashLookup l (.rows xs) <;> simp

private theorem spongeLogHasher_compress_eq_known {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    {a b : Dig T D} {y : D} :
    (spongeLogHasher l).compress a b = .known y ↔
      ∃ a' b', a = .known a' ∧ b = .known b' ∧ spongeHashLookup l (.node a' b') = some y := by
  cases a <;> cases b <;> try simp [spongeLogHasher]
  next a' b' => cases spongeHashLookup l (.node a' b') <;> simp

private theorem spongeLogCollision_of_collides {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    (h : (spongeLogHasher l).Collides) : LogCollision spongeHashObs l := by
  rcases h with ⟨xs, ys, hne, heq⟩ | ⟨⟨a, b⟩, ⟨a', b'⟩, hne, heq⟩
  · cases hx : spongeHashLookup l (.rows xs) with
    | none =>
      cases hy : spongeHashLookup l (.rows ys) with
      | none =>
        simp [spongeLogHasher, hx, hy] at heq
        exact absurd heq hne
      | some y => simp [spongeLogHasher, hx, hy] at heq
    | some y =>
      have hy : spongeHashLookup l (.rows ys) = some y := by
        refine spongeLogHasher_hashRows_eq_known.mp ?_
        rw [← heq]
        exact spongeLogHasher_hashRows_eq_known.mpr hx
      exact ⟨⟨.other (.rows xs), y⟩, List.of_mem_dlookup hx,
        ⟨.other (.rows ys), y⟩, List.of_mem_dlookup hy,
        fun h => hne (HashQuery.rows.inj (SpongeQuery.other.inj h)), y, rfl, rfl⟩
  · simp only at heq
    by_cases hkx : ∃ y, (spongeLogHasher l).compress a b = .known y
    · obtain ⟨y, hy⟩ := hkx
      obtain ⟨a₀, b₀, rfl, rfl, hq⟩ := spongeLogHasher_compress_eq_known.mp hy
      obtain ⟨a₁, b₁, rfl, rfl, hq'⟩ := spongeLogHasher_compress_eq_known.mp (heq ▸ hy)
      refine ⟨⟨.other (.node a₀ b₀), y⟩, List.of_mem_dlookup hq,
        ⟨.other (.node a₁ b₁), y⟩, List.of_mem_dlookup hq', fun h => hne ?_, y, rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := HashQuery.node.inj (SpongeQuery.other.inj h)
      rfl
    · have ha : (spongeLogHasher l).compress a b = .pair a b := by
        cases a <;> cases b <;> simp only [spongeLogHasher]
        next a₀ b₀ =>
          cases hq : spongeHashLookup l (.node a₀ b₀) with
          | none => rfl
          | some y => exact absurd ⟨y, by simp [spongeLogHasher, hq]⟩ hkx
      have hb : (spongeLogHasher l).compress a' b' = .pair a' b' := by
        cases a' <;> cases b' <;> simp only [spongeLogHasher]
        next a₁ b₁ =>
          cases hq : spongeHashLookup l (.node a₁ b₁) with
          | none => rfl
          | some y =>
            have : (spongeLogHasher l).compress (.known a₁) (.known b₁) = .known y := by
              simp [spongeLogHasher, hq]
            exact absurd ⟨y, heq.trans this⟩ hkx
      rw [ha, hb] at heq
      obtain ⟨rfl, rfl⟩ := Dig.pair.inj heq
      exact absurd rfl hne

open Classical in
/-- Opening held by a sponge-Merkle log. -/
def SpongeOpens (l : Log (SpongeMerkleAnswer Msg Chal T D)) (root : D)
    (dims : Array Dimensions) (index : ℕ) (rows : Array (Array T)) : Prop :=
  ∃ path : List D,
    Merkle.verifyOpening (spongeLogHasher l) (.known root) dims index rows (path.map .known) = true

theorem spongeOpens_iff {l : Log (SpongeMerkleAnswer Msg Chal T D)} {root : D}
    {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)} :
    SpongeOpens l root dims index rows ↔ ∃ path : List D,
      dims.size ≠ 0 ∧ widthsMatch dims.toList rows.toList = true
        ∧ path.length = maxLogHeight dims.toList ∧ index < 2 ^ maxLogHeight dims.toList
        ∧ climb (spongeLogHasher l) dims.toList rows.toList (maxLogHeight dims.toList) index
            (groupDigest (spongeLogHasher l) dims.toList rows.toList (maxLogHeight dims.toList))
            (path.map .known) = .known root := by
  unfold SpongeOpens Merkle.verifyOpening
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, List.length_map,
    and_assoc, ne_eq, Array.size_eq_zero_iff]

theorem SpongeOpens.size_rows {l : Log (SpongeMerkleAnswer Msg Chal T D)} {root : D}
    {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)}
    (h : SpongeOpens l root dims index rows) : rows.size = dims.size := by
  obtain ⟨_, _, hw, _⟩ := spongeOpens_iff.mp h
  simpa only [Array.length_toList] using widthsMatch_length hw

theorem SpongeOpens.row_eq {l : Log (SpongeMerkleAnswer Msg Chal T D)} {root : D}
    {dims : Array Dimensions} {index index' : ℕ} {rows rows' : Array (Array T)}
    (hl : ¬ LogCollision spongeHashObs l)
    (h : SpongeOpens l root dims index rows) (h' : SpongeOpens l root dims index' rows')
    {m : ℕ} {d : Dimensions} (hd : dims[m]? = some d)
    (hindex : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight)) :
    rows[m]? = rows'[m]? := by
  classical
  obtain ⟨path, hpath⟩ := h
  obtain ⟨path', hpath'⟩ := h'
  exact (Merkle.verifyOpening_binding hpath hpath' hd hindex).resolve_right
    fun hc => hl (spongeLogCollision_of_collides hc)

private theorem sponge_climb_transfer {l l' : Log (SpongeMerkleAnswer Msg Chal T D)}
    {P : D → Prop}
    (hA : ∀ q y, P y → spongeHashLookup l' q = some y → spongeHashLookup l q = some y)
    (hB : ∀ a b y, P y → spongeHashLookup l' (.node a b) = some y → P a ∧ P b)
    (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List (Dig T D)) (h index : ℕ) (digest : Dig T D) (y : D), P y →
      climb (spongeLogHasher l') dims rows h index digest path = .known y →
      ∃ d, P d ∧ digest = .known d ∧
        climb (spongeLogHasher l) dims rows h index (.known d) path = .known y
  | [], _, _, _, y, hy, hc => ⟨y, hy, hc, rfl⟩
  | sibling :: path, h, index, digest, y, hy, hc => by
    rw [climb] at hc
    obtain ⟨d₁, hd₁, hinject, hclimb⟩ :=
      sponge_climb_transfer hA hB dims rows path (h - 1) (index / 2) _ y hy hc
    have ⟨d₂, hd₂, hparent, hinject'⟩ :
        ∃ d₂, P d₂ ∧ parent (spongeLogHasher l') index digest sibling = .known d₂ ∧
          inject (spongeLogHasher l) dims rows (h - 1) (.known d₂) = .known d₁ := by
      by_cases hg : hasHeight dims (h - 1) = true
      · simp only [inject, hg, ↓reduceIte] at hinject ⊢
        obtain ⟨a', b', ha', hb', hq⟩ := spongeLogHasher_compress_eq_known.mp hinject
        obtain ⟨haP, hbP⟩ := hB a' b' d₁ hd₁ hq
        refine ⟨a', haP, ha', ?_⟩
        rw [show groupDigest (spongeLogHasher l) dims rows (h - 1) = .known b' from
          spongeLogHasher_hashRows_eq_known.mpr (hA _ b' hbP (spongeLogHasher_hashRows_eq_known.mp hb'))]
        exact spongeLogHasher_compress_eq_known.mpr ⟨a', b', rfl, rfl, hA _ d₁ hd₁ hq⟩
      · simp only [inject, hg, Bool.false_eq_true, ↓reduceIte] at hinject ⊢
        exact ⟨d₁, hd₁, hinject, rfl⟩
    have ⟨d, hd, hdig, hparent'⟩ :
        ∃ d, P d ∧ digest = .known d ∧
          parent (spongeLogHasher l) index (.known d) sibling = .known d₂ := by
      by_cases hpar : index % 2 = 0
      · simp only [parent, hpar, ↓reduceIte] at hparent ⊢
        obtain ⟨a', b', ha', hb', hq⟩ := spongeLogHasher_compress_eq_known.mp hparent
        obtain ⟨haP, _⟩ := hB a' b' d₂ hd₂ hq
        exact ⟨a', haP, ha', by
          rw [hb']
          exact spongeLogHasher_compress_eq_known.mpr ⟨a', b', rfl, rfl, hA _ d₂ hd₂ hq⟩⟩
      · simp only [parent, hpar, ↓reduceIte] at hparent ⊢
        obtain ⟨a', b', ha', hb', hq⟩ := spongeLogHasher_compress_eq_known.mp hparent
        obtain ⟨_, hbP⟩ := hB a' b' d₂ hd₂ hq
        exact ⟨b', hbP, hb', by
          rw [ha']
          exact spongeLogHasher_compress_eq_known.mpr ⟨a', b', rfl, rfl, hA _ d₂ hd₂ hq⟩⟩
    exact ⟨d, hd, hdig, by rw [climb, hparent', hinject', hclimb]⟩

theorem SpongeOpens.transfer {l l' : Log (SpongeMerkleAnswer Msg Chal T D)} {P : D → Prop}
    {root : D} {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)}
    (hA : ∀ q y, P y → spongeHashLookup l' q = some y → spongeHashLookup l q = some y)
    (hB : ∀ a b y, P y → spongeHashLookup l' (.node a b) = some y → P a ∧ P b)
    (hroot : P root) (h : SpongeOpens l' root dims index rows) :
    SpongeOpens l root dims index rows := by
  obtain ⟨path, hsize, hw, hlen, hindex, hclimb⟩ := spongeOpens_iff.mp h
  obtain ⟨d, hd, hleaf, hclimb'⟩ := sponge_climb_transfer hA hB _ _ _ _ _ _ root hroot hclimb
  refine spongeOpens_iff.mpr ⟨path, hsize, hw, hlen, hindex, ?_⟩
  rw [show groupDigest (spongeLogHasher l) dims.toList rows.toList (maxLogHeight dims.toList)
    = .known d from
    spongeLogHasher_hashRows_eq_known.mpr (hA _ d hd (spongeLogHasher_hashRows_eq_known.mp hleaf))]
  exact hclimb'

theorem SpongeOpens.of_prefix {l l' : Log (SpongeMerkleAnswer Msg Chal T D)} (hl : l <+: l')
    {root : D} {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)}
    (h : SpongeOpens l root dims index rows) : SpongeOpens l' root dims index rows :=
  h.transfer (P := fun _ => True) (fun _ _ _ hq => spongeHashLookup_of_prefix hl hq)
    (fun _ _ _ _ _ => ⟨trivial, trivial⟩) trivial

theorem spongeOpens_append_chal {l : Log (SpongeMerkleAnswer Msg Chal T D)} {i : ℕ}
    (prev : D) (m : Msg) (y : D × Chal i) {root : D} {dims : Array Dimensions}
    {index : ℕ} {rows : Array (Array T)} :
    SpongeOpens (l ++ [⟨.chal i prev m, y⟩]) root dims index rows ↔
      SpongeOpens l root dims index rows :=
  ⟨fun h => h.transfer (P := fun _ => True)
      (fun q _ _ hq => by rwa [spongeHashLookup_append_chal] at hq)
      (fun _ _ _ _ _ => ⟨trivial, trivial⟩) trivial,
   SpongeOpens.of_prefix (List.prefix_append l _)⟩

/-- Stability of sponge Merkle openings when no entry after `l` triggers `SpongeMerkleHit`. -/
theorem spongeOpens_append_iff_of_not_merkleHit
    {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l t : Log (SpongeMerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions}
    {index : ℕ} {rows : Array (Array T)}
    (hroot : SpongeMerklePresent stepDigestsOf r l root)
    (hno : ¬ HasBadFrom (SpongeMerkleHit stepDigestsOf r) l.length (l ++ t)) :
    SpongeOpens (l ++ t) root dims index rows ↔ SpongeOpens l root dims index rows := by
  refine ⟨fun h => ?_, SpongeOpens.of_prefix (List.prefix_append l t)⟩
  have hA : ∀ q y, SpongeMerklePresent stepDigestsOf r l y →
      spongeHashLookup (l ++ t) q = some y → spongeHashLookup l q = some y := by
    intro q y hy hq
    unfold spongeHashLookup at hq ⊢
    rw [List.dlookup_append] at hq
    cases hl : List.dlookup (SpongeQuery.other q) l with
    | some y' => rwa [hl, Option.some_or] at hq
    | none =>
      rw [hl, Option.none_or] at hq
      obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem (List.of_mem_dlookup hq)
      exact absurd ⟨l ++ t₁, ⟨.other q, y⟩, t₂, by rw [List.append_assoc], by simp,
        hy.mono (List.subset_append_left l t₁)⟩ hno
  refine h.transfer (P := SpongeMerklePresent stepDigestsOf r l) hA (fun a b y hy hq => ?_) hroot
  have hmem := List.of_mem_dlookup (hA (.node a b) y hy hq)
  exact ⟨⟨_, hmem, List.mem_append_right _ (by simp [spongeHashDigests])⟩,
    ⟨_, hmem, List.mem_append_right _ (by simp [spongeHashDigests])⟩⟩

/-- Some opening in the sponge log `l` under `root` shows `row` as row `i` of matrix `m`. -/
def SpongeShowsRow (l : Log (SpongeMerkleAnswer Msg Chal T D)) (root : D)
    (dims : Array Dimensions) (m i : ℕ) (row : Array T) : Prop :=
  ∃ index rows d, SpongeOpens l root dims index rows ∧ dims[m]? = some d
    ∧ index >>> (maxLogHeight dims.toList - d.logHeight) = i ∧ rows[m]? = some row

open Classical in
/-- The row `i` of matrix `m` committed under `root` in a sponge log `l`. -/
noncomputable def spongeCommittedRow (l : Log (SpongeMerkleAnswer Msg Chal T D)) (root : D)
    (dims : Array Dimensions) (m i : ℕ) : Option (Array T) :=
  if h : ∃ row, SpongeShowsRow l root dims m i row then some (Classical.choose h) else none

theorem spongeCommittedRow_of_opens {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    {root : D} {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)}
    {m : ℕ} {d : Dimensions} (hl : ¬ LogCollision spongeHashObs l)
    (h : SpongeOpens l root dims index rows) (hd : dims[m]? = some d) :
    spongeCommittedRow l root dims m (index >>> (maxLogHeight dims.toList - d.logHeight))
      = rows[m]? := by
  have hm : m < rows.size := by
    rw [h.size_rows]
    exact (Array.getElem?_eq_some_iff.mp hd).1
  have hex : ∃ row, SpongeShowsRow l root dims m
      (index >>> (maxLogHeight dims.toList - d.logHeight)) row :=
    ⟨rows[m], index, rows, d, h, hd, rfl, Array.getElem?_eq_getElem hm⟩
  obtain ⟨index', rows', d', h', hd', hindex', hrow'⟩ := Classical.choose_spec hex
  obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
  rw [spongeCommittedRow, dite_eq_left hex, ← hrow']
  exact h'.row_eq hl h hd hindex'

private theorem spongeCommittedRow_congr {l l' : Log (SpongeMerkleAnswer Msg Chal T D)}
    {root : D} {dims : Array Dimensions}
    (h : ∀ index rows, SpongeOpens l root dims index rows ↔ SpongeOpens l' root dims index rows) :
    spongeCommittedRow l root dims = spongeCommittedRow l' root dims := by
  have hopens : SpongeOpens l root dims = SpongeOpens l' root dims :=
    funext fun index => funext fun rows => propext (h index rows)
  funext m i
  unfold spongeCommittedRow SpongeShowsRow
  rw [hopens]

theorem spongeCommittedRow_append_chal (l : Log (SpongeMerkleAnswer Msg Chal T D)) {i : ℕ}
    (prev : D) (m : Msg) (y : D × Chal i) (root : D) (dims : Array Dimensions) :
    spongeCommittedRow (l ++ [⟨.chal i prev m, y⟩]) root dims = spongeCommittedRow l root dims :=
  spongeCommittedRow_congr fun _ _ => spongeOpens_append_chal prev m y

theorem spongeCommittedRow_concat_of_not_merkleHit {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l : Log (SpongeMerkleAnswer Msg Chal T D)} {e : Sigma (SpongeMerkleAnswer Msg Chal T D)}
    {root : D} (hroot : SpongeMerklePresent stepDigestsOf r l root)
    (he : ¬ SpongeMerkleHit stepDigestsOf r l e.1 e.2) (dims : Array Dimensions) :
    spongeCommittedRow (l ++ [e]) root dims = spongeCommittedRow l root dims :=
  spongeCommittedRow_congr fun _ _ =>
    spongeOpens_append_iff_of_not_merkleHit hroot fun h =>
      (hasBadFrom_concat.mp h).elim (not_hasBadFrom_of_length_le le_rfl) fun h' => he h'.2

theorem spongeSettles_of_committedRow (stepDigestsOf : ℕ → Msg → List D) (r : ℕ)
    (read : ℕ → Msg → (D → Array Dimensions → ℕ → ℕ → Option (Array T)) → Msg₂)
    (hread : ∀ j m c c', j < r → (∀ root ∈ stepDigestsOf j m, c root = c' root) →
      read j m c = read j m c')
    (hconst : ∀ j m c c', r ≤ j → read j m c = read j m c') :
    SpongeSettles
      (fun (l : Log (SpongeMerkleAnswer Msg Chal T D)) j m => read j m (spongeCommittedRow l))
      (SpongeMerkleHit stepDigestsOf r) where
  chal l _ prev m y j m' :=
    congrArg (read j m') (funext fun root => funext fun dims =>
      spongeCommittedRow_append_chal l prev m y root dims)
  stable l e j m hm he := by
    rcases Nat.lt_or_ge j r with hj | hj
    · refine hread j m _ _ hj fun root hroot => funext fun dims => ?_
      obtain ⟨prev, next, c, hmem⟩ := hm
      have hpres : SpongeMerklePresent stepDigestsOf r l root :=
        ⟨⟨.chal j prev m, (next, c)⟩, hmem,
          List.mem_append_left _ (by simp [spongeChalDigests, hj, hroot])⟩
      exact spongeCommittedRow_concat_of_not_merkleHit hpres he dims
    · exact hconst j m _ _ hj

/-! ## Master incremental-sponge Fiat–Shamir + Merkle soundness bound (`c = 3 / 2`) -/

section Bound

variable [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)] [Fintype D] [Nonempty D]
  {α : Type w} {β : Type w'} {r : ℕ}
  {doomed : ∀ i, Transcript Msg₂ Chal i → Prop} {ε : ℕ → ℝ} {εmax : ℝ}

/-- **Incremental sponge Fiat–Shamir for Merkle-committed messages (`c = 3 / 2`).**
When every sponge step `i < r` brings at most `M ≤ 3` digests into play
(in particular **`M = 1`**, single-root absorption), any adversary making at
most `Q` queries followed by `r` sponge derivations and `R` verifier queries
triggers event `E` with probability at most
`N * εmax + 3 * N ^ 2 / (2 * Fintype.card D)`, where `N = Q + r + R`. -/
theorem prob_spongeExperiment_bind_committedRow_le {s₀ : D}
    (hsound : RbrSound r doomed ε) (hε : ∀ i < r, ε i ≤ εmax) (h0 : 0 ≤ εmax)
    (hnil : doomed 0 .nil)
    {stepDigestsOf : ℕ → Msg → List D} {M : ℕ} (hM3 : M ≤ 3)
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    {read : ℕ → Msg → (D → Array Dimensions → ℕ → ℕ → Option (Array T)) → Msg₂}
    (hread : ∀ j m c c', (∀ root ∈ stepDigestsOf j m, c root = c' root) →
      read j m c = read j m c')
    {adv : OracleComp (SpongeMerkleAnswer Msg Chal T D) α} {Q : ℕ} (hadv : adv.QueryBound Q)
    (msgs : α → ℕ → Msg)
    {rest : α × Transcript Msg Chal r × D → OracleComp (SpongeMerkleAnswer Msg Chal T D) β}
    {R : ℕ} (hrest : ∀ out, (rest out).QueryBound R)
    {E : β → Log (SpongeMerkleAnswer Msg Chal T D) → Prop}
    (hE : ∀ (out : α × Transcript Msg Chal r × D) (l : Log (SpongeMerkleAnswer Msg Chal T D))
      (b : β) (l' : Log (SpongeMerkleAnswer Msg Chal T D)),
      Outcome (spongeExperiment s₀ r adv msgs) [] out l →
      Outcome (rest out) l b l' → E b l' →
      ¬ HasBad (JointHit s₀ stepDigestsOf r) l' →
      ¬ doomed r (out.2.1.mapIdx fun j m => read j m (spongeCommittedRow l'))) :
    prob E ((spongeExperiment s₀ r adv msgs).bind rest) []
      ≤ (Q + r + R) * εmax + 3 * ((Q : ℝ) + r + R) ^ 2 / (2 * Fintype.card D) := by
  let interp : Log (SpongeMerkleAnswer Msg Chal T D) → ℕ → Msg → Msg₂ :=
    fun l j m => read j m (if j < r then spongeCommittedRow l else fun _ _ _ _ => none)
  have hset := spongeSettles_of_committedRow (Chal := Chal) stepDigestsOf r
    (fun j m c => read j m (if j < r then c else fun _ _ _ _ => none))
    (fun j m c c' hj hc => by simp only [hj, ↓reduceIte]; exact hread j m c c' hc)
    (fun j m c c' hj => by simp only [Nat.not_lt.mpr hj, ↓reduceIte])
  have hqb := (queryBound_spongeExperiment (s₀ := s₀) (r := r) hadv msgs).bind hrest
  have hflip : prob (fun b l' => E b l' ∧ ¬ HasBad (JointHit s₀ stepDigestsOf r) l')
      ((spongeExperiment s₀ r adv msgs).bind rest) [] ≤ (Q + r + R) * εmax := by
    refine le_trans (prob_mono_of_outcome fun b l' hout ⟨hb, hno⟩ => ?_)
      (by
        have h := prob_hasBad_spongeInterpFlips_le (s₀ := s₀) (interp := interp) hsound hε h0 hqb
        simpa [Nat.cast_add, add_assoc] using h)
    rw [outcome_bind] at hout
    obtain ⟨out, l, hexp, hrun⟩ := hout
    obtain ⟨_, -, hder⟩ := outcome_spongeExperiment hexp
    obtain ⟨hsup, _⟩ := outcome_spongeDerive_supports hder
    have hsup' : SpongeSupports s₀ l' out.2.1 out.2.2 := hsup.of_prefix hrun.prefix
    have hsponge : ¬ HasBad (SpongeHit s₀) l' := fun h =>
      hno (h.imp fun _ _ _ => jointHit_of_spongeHit)
    have hmerkle : ¬ HasBad (SpongeMerkleHit stepDigestsOf r) l' := fun h =>
      hno (h.imp fun _ _ _ => jointHit_of_spongeMerkleHit)
    by_contra hnf
    have hdoom := doomed_mapIdx_of_spongeSupports hset hnf hsponge hmerkle hnil le_rfl hsup'
    have hcongr : out.2.1.mapIdx (interp l') =
        out.2.1.mapIdx (fun j m => read j m (spongeCommittedRow l')) :=
      Transcript.mapIdx_congr out.2.1 fun j m hj => by
        have hjr : j < r := out.2.1.length_msgs ▸ (List.getElem?_eq_some_iff.mp hj).1
        simp only [interp, hjr, ↓reduceIte]
    rw [hcongr] at hdoom
    exact hE out l b l' hexp hrun hb hno hdoom
  have hhit := prob_hasBad_jointHit_le (s₀ := s₀) hM3 hM hqb
  rw [show ((Q + r + R : ℕ) : ℝ) = (Q : ℝ) + r + R by push_cast; ring] at hhit
  exact (prob_le_prob_and_not_add E (fun _ l => HasBad (JointHit s₀ stepDigestsOf r) l) _ _).trans
    (add_le_add hflip hhit)

end Bound

end SpongeMerkle

end CertiFri.Oracle
