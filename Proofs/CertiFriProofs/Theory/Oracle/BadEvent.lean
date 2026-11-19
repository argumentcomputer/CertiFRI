import CertiFriProofs.Theory.Oracle.Prob

/-!
# The bad-event theorem

A *bad event* is a property `bad l x y` of a fresh query `x`, its answer `y`,
and the log `l` just before the query. If, for every log and every fresh query,
at most a fraction `ε l.length` of the answers is bad, then a computation that
makes at most `Q` queries leaves a log with a bad entry with probability at
most the sum of `ε` over the `Q` log lengths it can pass through
(`prob_hasBadFrom_le`, and `prob_hasBad_le` from the empty log).

The event is stated on the final log: `HasBadFrom bad n l` says some entry of
`l` at position `n` or later is bad with respect to the entries before it. The
entries from position `n` on are those a run from a log of length `n` samples.

`FractionLE p ε` is the counting hypothesis: the elements of a finite type that
satisfy `p` lie in a set holding at most a fraction `ε` of the type.

The bound counts every query the computation makes, also the repeated ones,
which sample nothing.
-/

namespace CertiFri.Oracle

universe u v w

/-! ## Fractions of a finite type -/

/-- At most a fraction `ε` of the finite type `β` satisfies `p`: the elements
that do lie in a set of at most `ε * card β` elements. -/
def FractionLE {β : Type*} [Fintype β] (p : β → Prop) (ε : ℝ) : Prop :=
  ∃ B : Finset β, (B.card : ℝ) ≤ ε * Fintype.card β ∧ ∀ b, p b → b ∈ B

namespace FractionLE

variable {β : Type*} [Fintype β] {p q : β → Prop} {ε ε' : ℝ}

/-- A property that implies one with fraction at most `ε` has fraction at most `ε`. -/
theorem mono_left (h : FractionLE p ε) (hq : ∀ b, q b → p b) : FractionLE q ε := by
  obtain ⟨B, hB, hp⟩ := h
  exact ⟨B, hB, fun b hb => hp b (hq b hb)⟩

/-- A fraction bound can be raised. -/
theorem mono_right (h : FractionLE p ε) (hε : ε ≤ ε') : FractionLE p ε' := by
  obtain ⟨B, hB, hp⟩ := h
  exact ⟨B, hB.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)), hp⟩

/-- No element satisfies `False`. -/
protected theorem false : FractionLE (fun _ : β => False) 0 :=
  ⟨∅, by simp, fun _ h => h.elim⟩

/-- The fractions of two properties add up to a bound for their disjunction. -/
protected theorem or (hp : FractionLE p ε) (hq : FractionLE q ε') :
    FractionLE (fun b => p b ∨ q b) (ε + ε') := by
  classical
  obtain ⟨B, hB, hp⟩ := hp
  obtain ⟨B', hB', hq⟩ := hq
  refine ⟨B ∪ B', ?_, fun b hb => Finset.mem_union.mpr (hb.imp (hp b) (hq b))⟩
  have hcard : ((B ∪ B').card : ℝ) ≤ B.card + B'.card := by
    exact_mod_cast Finset.card_union_le B B'
  linarith [add_mul ε ε' (Fintype.card β : ℝ)]

/-- A property that holds for one of the members of a list, each with fraction
at most `ε`, has fraction at most the length of the list times `ε`. -/
theorem exists_mem_list {ι : Type*} {p : ι → β → Prop} (l : List ι)
    (h : ∀ i ∈ l, FractionLE (p i) ε) : FractionLE (fun b => ∃ i ∈ l, p i b) (l.length * ε) := by
  induction l with
  | nil =>
    refine (FractionLE.false.mono_left fun b hb => ?_).mono_right (by simp)
    simp at hb
  | cons a l ih =>
    have hor := (h a List.mem_cons_self).or (ih fun i hi => h i (List.mem_cons_of_mem a hi))
    refine (hor.mono_left fun b hb => ?_).mono_right (le_of_eq ?_)
    · obtain ⟨i, hi, hb⟩ := hb
      rcases List.mem_cons.mp hi with rfl | hi
      · exact .inl hb
      · exact .inr ⟨i, hi, hb⟩
    · rw [List.length_cons]
      push_cast
      ring

/-- An injective function takes a given value on at most one element. -/
theorem of_injective {γ : Type*} {g : β → γ} (hg : Function.Injective g) (z : γ) :
    FractionLE (fun b => g b = z) (1 / Fintype.card β) := by
  by_cases h : ∃ b₀, g b₀ = z
  · obtain ⟨b₀, rfl⟩ := h
    have hcard : (Fintype.card β : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨b₀⟩).ne'
    refine ⟨{b₀}, ?_, fun b hb => Finset.mem_singleton.mpr (hg hb)⟩
    rw [Finset.card_singleton, one_div, inv_mul_cancel₀ hcard, Nat.cast_one]
  · refine ⟨∅, ?_, fun b hb => (h ⟨b, hb⟩).elim⟩
    rw [Finset.card_empty, Nat.cast_zero]
    positivity

/-- A single element is a fraction `1 / card β` of `β`. -/
protected theorem eq (z : β) : FractionLE (fun b => b = z) (1 / Fintype.card β) :=
  of_injective Function.injective_id z

/-- A fraction bound on a nonempty type is nonnegative. -/
theorem nonneg [Nonempty β] (h : FractionLE p ε) : 0 ≤ ε := by
  obtain ⟨B, hB, _⟩ := h
  have hcard : (0 : ℝ) < Fintype.card β := Nat.cast_pos.mpr Fintype.card_pos
  exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg _).trans hB) hcard

/-- The number of elements that satisfy `p` is at most `ε * card β`. -/
theorem card_filter_le [DecidablePred p] (h : FractionLE p ε) :
    ((Finset.univ.filter p).card : ℝ) ≤ ε * Fintype.card β := by
  obtain ⟨B, hB, hp⟩ := h
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun b hb => ?_)) hB
  exact hp b (Finset.mem_filter.mp hb).2

/-- `FractionLE` is a bound on the number of elements that satisfy `p`. -/
theorem _root_.CertiFri.Oracle.fractionLE_iff_card_filter [DecidablePred p] :
    FractionLE p ε ↔ ((Finset.univ.filter p).card : ℝ) ≤ ε * Fintype.card β :=
  ⟨card_filter_le, fun h => ⟨Finset.univ.filter p, h, fun b hb =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩⟩⟩

/-- `FractionLE` of a negation: outside a set of at most `ε * card β` elements,
`p` holds. -/
theorem _root_.CertiFri.Oracle.fractionLE_not_iff :
    FractionLE (fun b => ¬ p b) ε ↔
      ∃ B : Finset β, (B.card : ℝ) ≤ ε * Fintype.card β ∧ ∀ b ∉ B, p b :=
  exists_congr fun _ => and_congr_right fun _ => forall_congr' fun _ => not_imp_comm

/-- The sum of the indicator of `p` is at most `ε * card β`. -/
theorem sum_ite_le [DecidablePred p] (h : FractionLE p ε) :
    (∑ b, if p b then (1 : ℝ) else 0) ≤ ε * Fintype.card β := by
  rw [Finset.sum_boole]
  exact h.card_filter_le

end FractionLE

/-! ## Bad entries of a log -/

variable {X : Type u} {Y : X → Type v} {α : Type w}

/-- Some entry of the log `l`, at position `n` or later, is bad with respect to
the entries before it. -/
def HasBadFrom (bad : Log Y → (x : X) → Y x → Prop) (n : ℕ) (l : Log Y) : Prop :=
  ∃ l₁ e l₂, l = l₁ ++ e :: l₂ ∧ n ≤ l₁.length ∧ bad l₁ e.1 e.2

/-- Some entry of the log `l` is bad with respect to the entries before it. -/
def HasBad (bad : Log Y → (x : X) → Y x → Prop) (l : Log Y) : Prop :=
  HasBadFrom bad 0 l

section HasBad

variable {bad : Log Y → (x : X) → Y x → Prop} {n m : ℕ} {l l' : Log Y}

/-- `HasBad` unfolded: the log splits around an entry that is bad with respect to
the entries before it. -/
theorem hasBad_iff : HasBad bad l ↔ ∃ l₁ e l₂, l = l₁ ++ e :: l₂ ∧ bad l₁ e.1 e.2 := by
  simp only [HasBad, HasBadFrom, Nat.zero_le, true_and]

/-- For a bad event that ignores the log, a log has a bad entry when one of its
entries is bad. -/
theorem hasBad_const_iff {b : (x : X) → Y x → Prop} :
    HasBad (fun _ => b) l ↔ ∃ e ∈ l, b e.1 e.2 := by
  rw [hasBad_iff]
  constructor
  · rintro ⟨l₁, e, l₂, rfl, hb⟩
    exact ⟨e, by simp, hb⟩
  · rintro ⟨e, he, hb⟩
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
    exact ⟨l₁, e, l₂, rfl, hb⟩

/-- `HasBadFrom` by position: the entry at some position `i ≥ n` is bad with
respect to the first `i` entries. -/
theorem hasBadFrom_iff_getElem :
    HasBadFrom bad n l ↔
      ∃ (i : ℕ) (h : i < l.length), n ≤ i ∧ bad (l.take i) l[i].1 l[i].2 := by
  constructor
  · rintro ⟨l₁, e, l₂, rfl, hn, hb⟩
    have he : (l₁ ++ e :: l₂)[l₁.length]'(by simp) = e := by simp
    refine ⟨l₁.length, by simp, hn, ?_⟩
    rw [he, List.take_left' rfl]
    exact hb
  · rintro ⟨i, hi, hn, hb⟩
    refine ⟨l.take i, l[i], l.drop (i + 1), ?_, ?_, hb⟩
    · rw [List.getElem_cons_drop, List.take_append_drop]
    · rw [List.length_take, Nat.min_eq_left hi.le]
      exact hn

/-- A bad entry at position `m` or later is one at position `n ≤ m` or later. -/
theorem HasBadFrom.mono (h : HasBadFrom bad m l) (hnm : n ≤ m) : HasBadFrom bad n l := by
  obtain ⟨l₁, e, l₂, hl, hm, hb⟩ := h
  exact ⟨l₁, e, l₂, hl, hnm.trans hm, hb⟩

/-- A bad entry from some position on is a bad entry. -/
theorem HasBadFrom.hasBad (h : HasBadFrom bad n l) : HasBad bad l :=
  h.mono (Nat.zero_le n)

/-- A log with an entry bad for one event has an entry bad for any event it
implies. -/
theorem HasBadFrom.imp {bad' : Log Y → (x : X) → Y x → Prop} (h : HasBadFrom bad n l)
    (himp : ∀ l x y, bad l x y → bad' l x y) : HasBadFrom bad' n l := by
  obtain ⟨l₁, e, l₂, hl, hn, hb⟩ := h
  exact ⟨l₁, e, l₂, hl, hn, himp _ _ _ hb⟩

/-- An entry is bad for the disjunction of two events when it is bad for one of
them. -/
theorem hasBadFrom_or_iff {bad' : Log Y → (x : X) → Y x → Prop} :
    HasBadFrom (fun l x y => bad l x y ∨ bad' l x y) n l ↔
      HasBadFrom bad n l ∨ HasBadFrom bad' n l := by
  constructor
  · rintro ⟨l₁, e, l₂, hl, hn, hb | hb⟩
    · exact .inl ⟨l₁, e, l₂, hl, hn, hb⟩
    · exact .inr ⟨l₁, e, l₂, hl, hn, hb⟩
  · rintro (h | h)
    · exact h.imp fun _ _ _ => .inl
    · exact h.imp fun _ _ _ => .inr

/-- A bad entry stays bad when the log grows. -/
theorem HasBadFrom.of_prefix (h : HasBadFrom bad n l) (hl : l <+: l') : HasBadFrom bad n l' := by
  obtain ⟨l₁, e, l₂, rfl, hn, hb⟩ := h
  obtain ⟨t, rfl⟩ := hl
  exact ⟨l₁, e, l₂ ++ t, by rw [List.append_assoc, List.cons_append], hn, hb⟩

/-- A log has no entry at a position past its end. -/
theorem not_hasBadFrom_of_length_le (h : l.length ≤ n) : ¬ HasBadFrom bad n l := by
  rintro ⟨l₁, e, l₂, rfl, hn, _⟩
  rw [List.length_append, List.length_cons] at h
  omega

/-- The bad entries of a log with one more entry: those of the log, and the new
entry if it is bad with respect to the log. -/
theorem hasBadFrom_concat {e : Sigma Y} :
    HasBadFrom bad n (l ++ [e]) ↔ HasBadFrom bad n l ∨ (n ≤ l.length ∧ bad l e.1 e.2) := by
  constructor
  · rintro ⟨l₁, e', l₂, hl, hn, hb⟩
    rcases List.eq_nil_or_concat l₂ with rfl | ⟨l₂, e'', rfl⟩
    · obtain ⟨rfl, he⟩ := List.append_inj' hl rfl
      obtain rfl : e = e' := by simpa using he
      exact .inr ⟨hn, hb⟩
    · rw [List.concat_eq_append, ← List.cons_append, ← List.append_assoc] at hl
      obtain ⟨rfl, _⟩ := List.append_inj' hl rfl
      exact .inl ⟨l₁, e', l₂, rfl, hn, hb⟩
  · rintro (h | ⟨hn, hb⟩)
    · exact h.of_prefix (List.prefix_append l [e])
    · exact ⟨l, e, [], rfl, hn, hb⟩

/-- A bad entry of an extended log is in the old log or among the new entries. -/
theorem hasBadFrom_append {t : Log Y} (h : HasBadFrom bad n (l ++ t)) :
    HasBadFrom bad n l ∨ HasBadFrom bad l.length (l ++ t) := by
  induction t using List.reverseRecOn with
  | nil => exact .inl (by rwa [List.append_nil] at h)
  | append_singleton t e ih =>
    rw [← List.append_assoc] at h ⊢
    rcases hasBadFrom_concat.mp h with h | ⟨_, hb⟩
    · exact (ih h).imp id fun h => hasBadFrom_concat.mpr (.inl h)
    · exact .inr (hasBadFrom_concat.mpr (.inr ⟨by simp, hb⟩))

/-- Among the entries after `l`, the bad ones are the first, if it is bad with
respect to `l`, and those after it. -/
theorem hasBadFrom_length_cons {e : Sigma Y} {t : Log Y}
    (h : HasBadFrom bad l.length (l ++ e :: t)) :
    bad l e.1 e.2 ∨ HasBadFrom bad (l.length + 1) (l ++ e :: t) := by
  obtain ⟨l₁, e', l₂, hl, hn, hb⟩ := h
  rcases Nat.eq_or_lt_of_le hn with hn | hn
  · obtain ⟨rfl, he⟩ := List.append_inj hl hn
    obtain ⟨rfl, _⟩ := List.cons.inj he
    exact .inl hb
  · exact .inr ⟨l₁, e', l₂, hl, hn, hb⟩

end HasBad

/-! ## The bound -/

section Bound

open OracleComp

variable [DecidableEq X] [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]

/-- **The bad-event theorem.** Suppose that for every log `l` and every query
`x` not in `l`, at most a fraction `ε l.length` of the answers to `x` is bad
with respect to `l`. Then a computation that makes at most `Q` queries, run
from the log `l`, samples an entry that is bad with respect to the entries
before it with probability at most `∑ i < Q, ε (l.length + i)`. -/
theorem prob_hasBadFrom_le {bad : Log Y → (x : X) → Y x → Prop} {ε : ℕ → ℝ}
    (hε : ∀ n, 0 ≤ ε n)
    (hbad : ∀ (l : Log Y) (x : X), l.dlookup x = none → FractionLE (bad l x) (ε l.length))
    {c : OracleComp Y α} {Q : ℕ} (hc : c.QueryBound Q) (l : Log Y) :
    prob (fun _ l' => HasBadFrom bad l.length l') c l
      ≤ ∑ i ∈ Finset.range Q, ε (l.length + i) := by
  classical
  induction c generalizing l Q with
  | pure a =>
    rw [prob_pure, ite_eq_right (not_hasBadFrom_of_length_le le_rfl)]
    exact Finset.sum_nonneg fun i _ => hε _
  | queryBind x k ih =>
    cases Q with
    | zero => exact absurd hc (queryBound_queryBind_zero x k)
    | succ Q =>
      cases hx : l.dlookup x with
      | some y =>
        rw [prob_queryBind_of_lookup hx, Finset.sum_range_succ]
        exact (ih y (hc y) l).trans (le_add_of_nonneg_right (hε _))
      | none =>
        -- The sum over the later queries, from a log with one more entry.
        set S := ∑ i ∈ Finset.range Q, ε (l.length + 1 + i) with hS
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hε _
        have hsum : ∑ i ∈ Finset.range (Q + 1), ε (l.length + i) = ε l.length + S := by
          rw [Finset.sum_range_succ', Nat.add_zero, add_comm, hS]
          exact congrArg _ (Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm]; rfl)
        have hcard : (0 : ℝ) < Fintype.card (Y x) := Nat.cast_pos.mpr Fintype.card_pos
        -- With the answer `y`: the new entry is bad, or a later one is.
        have hstep : ∀ y : Y x,
            prob (fun _ l' => HasBadFrom bad l.length l') (k y) (l ++ [⟨x, y⟩])
              ≤ (if bad l x y then 1 else 0) + S := by
          intro y
          by_cases hb : bad l x y
          · rw [ite_eq_left hb]
            exact (prob_le_one _ _ _).trans (le_add_of_nonneg_right hS0)
          · rw [ite_eq_right hb, zero_add]
            refine le_trans (prob_mono_of_outcome fun a l' ha h => ?_)
              ((ih y (hc y) (l ++ [⟨x, y⟩])).trans (le_of_eq ?_))
            · obtain ⟨t, rfl⟩ := ha.prefix
              rw [List.append_assoc, List.singleton_append] at h ⊢
              rw [List.length_append, List.length_singleton]
              exact (hasBadFrom_length_cons h).resolve_left hb
            · rw [List.length_append, List.length_singleton]
        rw [prob_queryBind_of_fresh hx, hsum, div_le_iff₀ hcard]
        calc ∑ y, prob (fun _ l' => HasBadFrom bad l.length l') (k y) (l ++ [⟨x, y⟩])
            ≤ ∑ y, ((if bad l x y then 1 else 0) + S) := Finset.sum_le_sum fun y _ => hstep y
          _ = (∑ y, if bad l x y then (1 : ℝ) else 0) + Fintype.card (Y x) * S := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ ≤ ε l.length * Fintype.card (Y x) + Fintype.card (Y x) * S :=
            add_le_add_left (hbad l x hx).sum_ite_le _
          _ = (ε l.length + S) * Fintype.card (Y x) := by ring

/-- **The bad-event theorem, from the empty log.** If at most a fraction
`ε l.length` of the answers to a fresh query is bad with respect to the log
`l`, then a computation that makes at most `Q` queries leaves a log with a bad
entry with probability at most `∑ i < Q, ε i`. -/
theorem prob_hasBad_le {bad : Log Y → (x : X) → Y x → Prop} {ε : ℕ → ℝ}
    (hε : ∀ n, 0 ≤ ε n)
    (hbad : ∀ (l : Log Y) (x : X), l.dlookup x = none → FractionLE (bad l x) (ε l.length))
    {c : OracleComp Y α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l' => HasBad bad l') c [] ≤ ∑ i ∈ Finset.range Q, ε i := by
  have h := prob_hasBadFrom_le hε hbad hc []
  simpa only [HasBad, List.length_nil, Nat.zero_add] using h

/-- The bad-event theorem for a bad event in the log the run starts from or in
what it samples: the probability is at most `∑ i < Q, ε (l.length + i)` unless
the starting log already has a bad entry from position `n` on. -/
theorem prob_hasBadFrom_le_of_not {bad : Log Y → (x : X) → Y x → Prop} {ε : ℕ → ℝ}
    (hε : ∀ n, 0 ≤ ε n)
    (hbad : ∀ (l : Log Y) (x : X), l.dlookup x = none → FractionLE (bad l x) (ε l.length))
    {c : OracleComp Y α} {Q : ℕ} (hc : c.QueryBound Q) {l : Log Y} {n : ℕ}
    (hl : ¬ HasBadFrom bad n l) :
    prob (fun _ l' => HasBadFrom bad n l') c l ≤ ∑ i ∈ Finset.range Q, ε (l.length + i) := by
  refine le_trans (prob_mono_of_outcome fun a l' ha h => ?_) (prob_hasBadFrom_le hε hbad hc l)
  obtain ⟨t, rfl⟩ := ha.prefix
  exact (hasBadFrom_append h).resolve_left hl

end Bound

end CertiFri.Oracle
