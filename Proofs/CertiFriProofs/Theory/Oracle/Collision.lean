import CertiFriProofs.Theory.Oracle.BadEvent

/-!
# Collisions among the answers of a random oracle

An observation `obs x y : Option Z` picks out the answers that count as digests
and says which digest an answer is; `none` marks the answers that do not count.
A *collision* in a log is two entries with different queries and the same
digest (`LogCollision`).

If, for every query `x` and digest `z`, at most a fraction `κ` of the answers
to `x` is observed as `z`, then a computation that makes at most `Q` queries
from the empty log leaves a log with a collision with probability at most
`κ * Q * (Q - 1) / 2` (`prob_logCollision_le`). From a collision-free log `l`
the bound is `∑ i < Q, κ * (l.length + i)` (`prob_logCollision_le_sum`).

This is the bad-event theorem for the event "the answer has the digest of an
earlier entry" (`HitsDigest`): a log has a collision exactly when it has such an
entry (`logCollision_iff_hasBad`).

For a hash oracle whose answers are all digests of one type `D`, take
`obs := fun _ d => some d` and `κ := 1 / card D`.
-/

namespace CertiFri.Oracle

universe u v w

variable {X : Type u} {Y : X → Type v} {α : Type w} {Z : Type*}

/-- Two entries of the log `l` with different queries have the same digest. -/
def LogCollision (obs : (x : X) → Y x → Option Z) (l : Log Y) : Prop :=
  ∃ e₁ ∈ l, ∃ e₂ ∈ l, e₁.1 ≠ e₂.1 ∧ ∃ z, obs e₁.1 e₁.2 = some z ∧ obs e₂.1 e₂.2 = some z

/-- The answer `y` to the query `x` has the digest of an entry of `l` with
another query. -/
def HitsDigest (obs : (x : X) → Y x → Option Z) (l : Log Y) (x : X) (y : Y x) : Prop :=
  ∃ e ∈ l, e.1 ≠ x ∧ ∃ z, obs e.1 e.2 = some z ∧ obs x y = some z

section Log

variable {obs : (x : X) → Y x → Option Z} {l : Log Y}

/-- In a log without a collision, entries with the same digest have the same
query. -/
theorem eq_of_not_logCollision (h : ¬ LogCollision obs l) {e₁ e₂ : Sigma Y} (h₁ : e₁ ∈ l)
    (h₂ : e₂ ∈ l) {z : Z} (hz₁ : obs e₁.1 e₁.2 = some z) (hz₂ : obs e₂.1 e₂.2 = some z) :
    e₁.1 = e₂.1 :=
  not_not.mp fun hne => h ⟨e₁, h₁, e₂, h₂, hne, z, hz₁, hz₂⟩

/-- The empty log has no collision. -/
theorem not_logCollision_nil : ¬ LogCollision obs ([] : Log Y) := by
  rintro ⟨e₁, h₁, _⟩
  simp at h₁

/-- A collision stays one when the log grows. -/
theorem LogCollision.of_prefix {l' : Log Y} (h : LogCollision obs l) (hl : l <+: l') :
    LogCollision obs l' := by
  obtain ⟨e₁, h₁, e₂, h₂, h⟩ := h
  exact ⟨e₁, hl.subset h₁, e₂, hl.subset h₂, h⟩

/-- A log with one more entry has a collision if the log has one or the new
entry has the digest of an earlier one. -/
theorem logCollision_concat {e : Sigma Y} :
    LogCollision obs (l ++ [e]) ↔ LogCollision obs l ∨ HitsDigest obs l e.1 e.2 := by
  constructor
  · rintro ⟨e₁, h₁, e₂, h₂, hne, z, hz₁, hz₂⟩
    rw [List.mem_append, List.mem_singleton] at h₁ h₂
    rcases h₁ with h₁ | rfl <;> rcases h₂ with h₂ | rfl
    · exact .inl ⟨e₁, h₁, e₂, h₂, hne, z, hz₁, hz₂⟩
    · exact .inr ⟨e₁, h₁, hne, z, hz₁, hz₂⟩
    · exact .inr ⟨e₂, h₂, hne.symm, z, hz₂, hz₁⟩
    · exact absurd rfl hne
  · rintro (h | ⟨e', h', hne, z, hz₁, hz₂⟩)
    · exact h.of_prefix (List.prefix_append l [e])
    · exact ⟨e', List.mem_append_left _ h', e, List.mem_append_right _ (List.mem_singleton_self e),
        hne, z, hz₁, hz₂⟩

/-- A collision in an extended log is in the old log, or one of the new entries
has the digest of an entry before it. -/
theorem logCollision_append_iff {t : Log Y} :
    LogCollision obs (l ++ t) ↔
      LogCollision obs l ∨ HasBadFrom (HitsDigest obs) l.length (l ++ t) := by
  induction t using List.reverseRecOn with
  | nil =>
    rw [List.append_nil]
    exact (or_iff_left (not_hasBadFrom_of_length_le le_rfl)).symm
  | append_singleton t e ih =>
    have hlen : l.length ≤ (l ++ t).length := by simp
    rw [← List.append_assoc, logCollision_concat, hasBadFrom_concat, ih, or_assoc,
      and_iff_right hlen]

/-- A log has a collision exactly when one of its entries has the digest of an
entry before it. -/
theorem logCollision_iff_hasBad : LogCollision obs l ↔ HasBad (HitsDigest obs) l := by
  have h := logCollision_append_iff (obs := obs) (l := []) (t := l)
  simpa only [HasBad, List.nil_append, not_logCollision_nil, false_or, List.length_nil] using h

/-- For a fresh or repeated query alike, at most a fraction `κ * l.length` of
the answers has the digest of an entry of `l`. -/
theorem fractionLE_hitsDigest [∀ x, Fintype (Y x)] {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ (x : X) (z : Z), FractionLE (fun y : Y x => obs x y = some z) κ)
    (l : Log Y) (x : X) : FractionLE (HitsDigest obs l x) (κ * l.length) := by
  have hentry : ∀ e ∈ l, FractionLE
      (fun y : Y x => e.1 ≠ x ∧ ∃ z, obs e.1 e.2 = some z ∧ obs x y = some z) κ := by
    intro e _
    cases he : obs e.1 e.2 with
    | none =>
      refine (FractionLE.false.mono_left fun y hy => ?_).mono_right hκ0
      obtain ⟨_, z, hz, _⟩ := hy
      simp at hz
    | some z =>
      refine (hκ x z).mono_left fun y hy => ?_
      obtain ⟨_, z', hz, hy⟩ := hy
      rw [hy, ← Option.some.inj hz]
  rw [mul_comm]
  exact (FractionLE.exists_mem_list l hentry).mono_left fun y hy => hy

end Log

section Bound

open OracleComp

variable [DecidableEq X] [∀ x, Fintype (Y x)] [∀ x, Nonempty (Y x)]
  {obs : (x : X) → Y x → Option Z} {κ : ℝ}

/-- The sum of `κ * i` over `i < Q`. -/
private theorem sum_range_mul_cast (κ : ℝ) (Q : ℕ) :
    ∑ i ∈ Finset.range Q, κ * (i : ℝ) = κ * Q * (Q - 1) / 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- **Collisions, from a collision-free log.** If at most a fraction `κ` of
the answers to any query is observed as any one digest, then a computation that
makes at most `Q` queries from a log `l` without a collision leaves a log with
a collision with probability at most `∑ i < Q, κ * (l.length + i)`. -/
theorem prob_logCollision_le_sum (hκ0 : 0 ≤ κ)
    (hκ : ∀ (x : X) (z : Z), FractionLE (fun y : Y x => obs x y = some z) κ)
    {c : OracleComp Y α} {Q : ℕ} (hc : c.QueryBound Q) {l : Log Y}
    (hl : ¬ LogCollision obs l) :
    prob (fun _ l' => LogCollision obs l') c l
      ≤ ∑ i ∈ Finset.range Q, κ * ((l.length + i : ℕ) : ℝ) := by
  have hbound := prob_hasBadFrom_le (bad := HitsDigest obs) (ε := fun n => κ * (n : ℝ))
    (fun n => mul_nonneg hκ0 (Nat.cast_nonneg n))
    (fun l x _ => fractionLE_hitsDigest hκ0 hκ l x) hc l
  refine le_trans (prob_mono_of_outcome fun a l' ha h => ?_) hbound
  obtain ⟨t, rfl⟩ := ha.prefix
  exact (logCollision_append_iff.mp h).resolve_left hl

/-- **Collisions.** If at most a fraction `κ` of the answers to any query is
observed as any one digest, then a computation that makes at most `Q` queries
from the empty log leaves a log with a collision with probability at most
`κ * Q * (Q - 1) / 2`. -/
theorem prob_logCollision_le (hκ0 : 0 ≤ κ)
    (hκ : ∀ (x : X) (z : Z), FractionLE (fun y : Y x => obs x y = some z) κ)
    {c : OracleComp Y α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l' => LogCollision obs l') c [] ≤ κ * Q * (Q - 1) / 2 := by
  refine (prob_logCollision_le_sum hκ0 hκ hc not_logCollision_nil).trans (le_of_eq ?_)
  simp only [List.length_nil, Nat.zero_add]
  exact sum_range_mul_cast κ Q

end Bound

end CertiFri.Oracle
