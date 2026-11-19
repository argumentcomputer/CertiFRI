import CertiFriProofs.Theory.Oracle.Basic

/-!
# Probabilities against a lazily sampled random oracle

`expect f c l` is the expectation of `f (result, final log)` when the
computation `c` runs from the log `l` against a random oracle: a query found in
the log gets the logged answer, a fresh query gets each answer of its (finite,
nonempty) answer type with equal probability, and the answer is appended to the
log. `prob E c l` is the probability of the event `E` of the result and the
final log. Both are defined by recursion on the computation, with values in
`ℝ`.

The laws proved here:

* probabilities lie in `[0, 1]` (`prob_nonneg`, `prob_le_one`), `prob_true`,
  `prob_add_prob_not`;
* monotonicity (`prob_mono`) and the union bound (`prob_or_le`);
* a probability only depends on the event on the outcomes of the run
  (`prob_mono_of_outcome`, `prob_congr_of_outcome`, `prob_eq_one_of_outcome`);
* the bind rule (`prob_bind`, `expect_bind`), and `prob_bind_le_prob` for an
  event that can only follow an event of the first computation;
* a run with at most `n` queries appends at most `n` entries to the log
  (`prob_exists_append`).

Not covered: distributions other than the uniform one on each answer type, and
conditional probabilities.
-/

namespace CertiFri.Oracle

universe u v w w'

namespace OracleComp

variable {X : Type u} {Y : X → Type v} {α : Type w} {β : Type w'}

/-! ## Expectation -/

section Prob

variable [DecidableEq X] [∀ x, Fintype (Y x)]

/-- The expectation of `f (result, final log)` when `c` runs from the log `l`
against a lazily sampled random oracle: a query found in the log gets the
logged answer, a fresh query gets each answer with equal probability, and the
answer is appended to the log. -/
noncomputable def expect (f : α → Log Y → ℝ) : OracleComp Y α → Log Y → ℝ
  | .pure a, l => f a l
  | .queryBind x k, l =>
    match l.dlookup x with
    | some y => expect f (k y) l
    | none => (∑ y, expect f (k y) (l ++ [⟨x, y⟩])) / Fintype.card (Y x)

open Classical in
/-- The probability that `E (result, final log)` holds when `c` runs from the
log `l` against a lazily sampled random oracle. -/
noncomputable def prob (E : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) : ℝ :=
  expect (fun a l' => if E a l' then 1 else 0) c l

/-- The expectation over a computation that returns `a` is the value at `a` and
the log. -/
@[simp] theorem expect_pure (f : α → Log Y → ℝ) (a : α) (l : Log Y) :
    expect f (.pure a : OracleComp Y α) l = f a l := rfl

/-- A query found in the log is answered with the logged answer. -/
theorem expect_queryBind_of_lookup {x : X} {y : Y x} {l : Log Y} (h : l.dlookup x = some y)
    (f : α → Log Y → ℝ) (k : Y x → OracleComp Y α) :
    expect f (.queryBind x k) l = expect f (k y) l := by
  simp only [expect, h]

/-- A query not in the log is answered uniformly, and the answer is appended. -/
theorem expect_queryBind_of_fresh {x : X} {l : Log Y} (h : l.dlookup x = none)
    (f : α → Log Y → ℝ) (k : Y x → OracleComp Y α) :
    expect f (.queryBind x k) l
      = (∑ y, expect f (k y) (l ++ [⟨x, y⟩])) / Fintype.card (Y x) := by
  simp only [expect, h]

/-- The expectation only depends on the values on the outcomes, monotonically. -/
theorem expect_mono_of_outcome {f g : α → Log Y → ℝ} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → f a l' ≤ g a l') : expect f c l ≤ expect g c l := by
  induction c generalizing l with
  | pure a => exact h a l ⟨rfl, rfl⟩
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y =>
      rw [expect_queryBind_of_lookup hx, expect_queryBind_of_lookup hx]
      exact ih y fun a l' ha => h a l' ((outcome_queryBind_of_lookup hx k a l').mpr ha)
    | none =>
      rw [expect_queryBind_of_fresh hx, expect_queryBind_of_fresh hx]
      refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun y _ => ih y fun a l' ha => ?_)
        (Nat.cast_nonneg _)
      exact h a l' ((outcome_queryBind_of_fresh hx k a l').mpr ⟨y, ha⟩)

/-- The expectation only depends on the values on the outcomes. -/
theorem expect_congr_of_outcome {f g : α → Log Y → ℝ} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → f a l' = g a l') : expect f c l = expect g c l :=
  le_antisymm (expect_mono_of_outcome fun a l' ha => (h a l' ha).le)
    (expect_mono_of_outcome fun a l' ha => (h a l' ha).ge)

/-- The expectation is monotone in the function. -/
theorem expect_mono {f g : α → Log Y → ℝ} (h : ∀ a l', f a l' ≤ g a l')
    (c : OracleComp Y α) (l : Log Y) : expect f c l ≤ expect g c l :=
  expect_mono_of_outcome fun a l' _ => h a l'

/-- The expectation is additive. -/
theorem expect_add (f g : α → Log Y → ℝ) (c : OracleComp Y α) (l : Log Y) :
    expect (fun a l' => f a l' + g a l') c l = expect f c l + expect g c l := by
  induction c generalizing l with
  | pure a => rfl
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y => simp only [expect_queryBind_of_lookup hx, ih]
    | none => simp only [expect_queryBind_of_fresh hx, ih, Finset.sum_add_distrib, add_div]

/-- A constant factor comes out of the expectation. -/
theorem expect_const_mul (r : ℝ) (f : α → Log Y → ℝ) (c : OracleComp Y α) (l : Log Y) :
    expect (fun a l' => r * f a l') c l = r * expect f c l := by
  induction c generalizing l with
  | pure a => rfl
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y => simp only [expect_queryBind_of_lookup hx, ih]
    | none => simp only [expect_queryBind_of_fresh hx, ih, ← Finset.mul_sum, mul_div_assoc]

/-- The bind rule: the expectation over `c.bind g` is the expectation over `c`
of the expectation over `g`. -/
theorem expect_bind (f : β → Log Y → ℝ) (c : OracleComp Y α) (g : α → OracleComp Y β)
    (l : Log Y) : expect f (c.bind g) l = expect (fun a l' => expect f (g a) l') c l := by
  induction c generalizing l with
  | pure a => rfl
  | queryBind x k ih =>
    rw [queryBind_bind]
    cases hx : l.dlookup x with
    | some y => simp only [expect_queryBind_of_lookup hx, ih]
    | none => simp only [expect_queryBind_of_fresh hx, ih]

variable [∀ x, Nonempty (Y x)]

/-- The expectation of a constant is the constant. -/
theorem expect_const (r : ℝ) (c : OracleComp Y α) (l : Log Y) :
    expect (fun _ _ => r) c l = r := by
  induction c generalizing l with
  | pure a => rfl
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y => rw [expect_queryBind_of_lookup hx, ih]
    | none =>
      have hcard : (Fintype.card (Y x) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      simp only [expect_queryBind_of_fresh hx, ih, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      exact mul_div_cancel_left₀ r hcard

/-- An expectation is at most any bound that holds on every outcome. -/
theorem expect_le_of_outcome {f : α → Log Y → ℝ} {c : OracleComp Y α} {l : Log Y} {r : ℝ}
    (h : ∀ a l', Outcome c l a l' → f a l' ≤ r) : expect f c l ≤ r :=
  (expect_mono_of_outcome h).trans (expect_const r c l).le

/-- An expectation is at least any bound that holds on every outcome. -/
theorem le_expect_of_outcome {f : α → Log Y → ℝ} {c : OracleComp Y α} {l : Log Y} {r : ℝ}
    (h : ∀ a l', Outcome c l a l' → r ≤ f a l') : r ≤ expect f c l :=
  (expect_const r c l).ge.trans (expect_mono_of_outcome h)

/-! ## Probability -/

omit [∀ x, Nonempty (Y x)] in
/-- For a computation that returns `a`, the probability of an event is one if
it holds of `a` and the log, and zero otherwise. -/
@[simp] theorem prob_pure (E : α → Log Y → Prop) (a : α) (l : Log Y) [Decidable (E a l)] :
    prob E (.pure a : OracleComp Y α) l = if E a l then 1 else 0 := by
  simp only [prob, expect_pure]
  congr

omit [∀ x, Nonempty (Y x)] in
/-- A query found in the log is answered with the logged answer. -/
theorem prob_queryBind_of_lookup {x : X} {y : Y x} {l : Log Y} (h : l.dlookup x = some y)
    (E : α → Log Y → Prop) (k : Y x → OracleComp Y α) :
    prob E (.queryBind x k) l = prob E (k y) l :=
  expect_queryBind_of_lookup h _ k

omit [∀ x, Nonempty (Y x)] in
/-- A query not in the log is answered uniformly, and the answer is appended. -/
theorem prob_queryBind_of_fresh {x : X} {l : Log Y} (h : l.dlookup x = none)
    (E : α → Log Y → Prop) (k : Y x → OracleComp Y α) :
    prob E (.queryBind x k) l
      = (∑ y, prob E (k y) (l ++ [⟨x, y⟩])) / Fintype.card (Y x) :=
  expect_queryBind_of_fresh h _ k

/-- A probability is nonnegative. -/
theorem prob_nonneg (E : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) :
    0 ≤ prob E c l :=
  le_expect_of_outcome fun a l' _ => by split <;> norm_num

/-- A probability is at most one. -/
theorem prob_le_one (E : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) :
    prob E c l ≤ 1 :=
  expect_le_of_outcome fun a l' _ => by split <;> norm_num

omit [∀ x, Nonempty (Y x)] in
/-- The probability only depends on the event on the outcomes, monotonically. -/
theorem prob_mono_of_outcome {E E' : α → Log Y → Prop} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → E a l' → E' a l') : prob E c l ≤ prob E' c l := by
  refine expect_mono_of_outcome fun a l' ha => ?_
  by_cases hE : E a l'
  · rw [ite_eq_left hE, ite_eq_left (h a l' ha hE)]
  · rw [ite_eq_right hE]
    split <;> norm_num

omit [∀ x, Nonempty (Y x)] in
/-- The probability is monotone in the event. -/
theorem prob_mono {E E' : α → Log Y → Prop} (h : ∀ a l', E a l' → E' a l')
    (c : OracleComp Y α) (l : Log Y) : prob E c l ≤ prob E' c l :=
  prob_mono_of_outcome fun a l' _ => h a l'

omit [∀ x, Nonempty (Y x)] in
/-- The probability only depends on the event on the outcomes. -/
theorem prob_congr_of_outcome {E E' : α → Log Y → Prop} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → (E a l' ↔ E' a l')) : prob E c l = prob E' c l :=
  le_antisymm (prob_mono_of_outcome fun a l' ha => (h a l' ha).mp)
    (prob_mono_of_outcome fun a l' ha => (h a l' ha).mpr)

/-- An event that holds on every outcome has probability one. -/
theorem prob_eq_one_of_outcome {E : α → Log Y → Prop} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → E a l') : prob E c l = 1 :=
  le_antisymm (prob_le_one E c l)
    (le_expect_of_outcome fun a l' ha => by rw [ite_eq_left (h a l' ha)])

/-- An event that fails on every outcome has probability zero. -/
theorem prob_eq_zero_of_outcome {E : α → Log Y → Prop} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → ¬ E a l') : prob E c l = 0 :=
  le_antisymm (expect_le_of_outcome fun a l' ha => by rw [ite_eq_right (h a l' ha)])
    (prob_nonneg E c l)

/-- The event `True` has probability one. -/
theorem prob_true (c : OracleComp Y α) (l : Log Y) : prob (fun _ _ => True) c l = 1 :=
  prob_eq_one_of_outcome fun _ _ _ => trivial

/-- The event `False` has probability zero. -/
theorem prob_false (c : OracleComp Y α) (l : Log Y) : prob (fun _ _ => False) c l = 0 :=
  prob_eq_zero_of_outcome fun _ _ _ => id

omit [∀ x, Nonempty (Y x)] in
/-- The union bound. -/
theorem prob_or_le (E E' : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) :
    prob (fun a l' => E a l' ∨ E' a l') c l ≤ prob E c l + prob E' c l := by
  unfold prob
  rw [← expect_add]
  refine expect_mono (fun a l' => ?_) c l
  by_cases hE : E a l' <;> by_cases hE' : E' a l' <;> simp [hE, hE']

omit [∀ x, Nonempty (Y x)] in
/-- An event that, on every outcome, implies one of two others has at most the
sum of their probabilities. -/
theorem prob_le_add_of_outcome {E E₁ E₂ : α → Log Y → Prop} {c : OracleComp Y α} {l : Log Y}
    (h : ∀ a l', Outcome c l a l' → E a l' → E₁ a l' ∨ E₂ a l') :
    prob E c l ≤ prob E₁ c l + prob E₂ c l :=
  (prob_mono_of_outcome h).trans (prob_or_le E₁ E₂ c l)

omit [∀ x, Nonempty (Y x)] in
/-- Splitting off an event `B`: `E` happens without `B`, or `B` happens. -/
theorem prob_le_prob_and_not_add (E B : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) :
    prob E c l ≤ prob (fun a l' => E a l' ∧ ¬ B a l') c l + prob B c l :=
  prob_le_add_of_outcome fun a l' _ hE => (em (B a l')).symm.imp (fun hB => ⟨hE, hB⟩) id

/-- The probabilities of an event and of its negation add up to one. -/
theorem prob_add_prob_not (E : α → Log Y → Prop) (c : OracleComp Y α) (l : Log Y) :
    prob E c l + prob (fun a l' => ¬ E a l') c l = 1 := by
  unfold prob
  rw [← expect_add]
  refine (expect_congr_of_outcome fun a l' _ => ?_).trans (expect_const 1 c l)
  by_cases hE : E a l' <;> simp [hE]

omit [∀ x, Nonempty (Y x)] in
/-- The bind rule: the probability of an event of `c.bind g` is the expectation
over `c` of its probability under `g`. -/
theorem prob_bind (E : β → Log Y → Prop) (c : OracleComp Y α) (g : α → OracleComp Y β)
    (l : Log Y) : prob E (c.bind g) l = expect (fun a l' => prob E (g a) l') c l :=
  expect_bind _ c g l

omit [∀ x, Nonempty (Y x)] in
/-- Applying a function to the result changes the event accordingly. -/
theorem prob_bind_pure (E : β → Log Y → Prop) (c : OracleComp Y α) (f : α → β) (l : Log Y) :
    prob E (c.bind fun a => .pure (f a)) l = prob (fun a l' => E (f a) l') c l := by
  rw [prob_bind]
  rfl

/-- A bound on the probability under `g` from every outcome of `c` is a bound
on the probability under `c.bind g`. -/
theorem prob_bind_le {E : β → Log Y → Prop} {c : OracleComp Y α} {g : α → OracleComp Y β}
    {l : Log Y} {r : ℝ} (h : ∀ a l', Outcome c l a l' → prob E (g a) l' ≤ r) :
    prob E (c.bind g) l ≤ r := by
  rw [prob_bind]
  exact expect_le_of_outcome h

/-- If the event `E` of `c.bind g` only happens after an outcome of `c` in `P`,
its probability is at most that of `P`. -/
theorem prob_bind_le_prob {E : β → Log Y → Prop} {P : α → Log Y → Prop} {c : OracleComp Y α}
    {g : α → OracleComp Y β} {l : Log Y}
    (h : ∀ a l' b l'', Outcome c l a l' → Outcome (g a) l' b l'' → E b l'' → P a l') :
    prob E (c.bind g) l ≤ prob P c l := by
  rw [prob_bind]
  refine expect_mono_of_outcome fun a l' ha => ?_
  by_cases hP : P a l'
  · rw [ite_eq_left hP]
    exact prob_le_one _ _ _
  · rw [ite_eq_right hP]
    exact (prob_eq_zero_of_outcome fun b l'' hb hE => hP (h a l' b l'' ha hb hE)).le

/-- A run with at most `n` queries appends at most `n` entries to the log, with
probability one. -/
theorem prob_exists_append {c : OracleComp Y α} {n : ℕ} (hc : c.QueryBound n) (l : Log Y) :
    prob (fun _ l' => ∃ t, l' = l ++ t ∧ t.length ≤ n) c l = 1 :=
  prob_eq_one_of_outcome fun _ _ h => h.exists_append hc

end Prob

end OracleComp

end CertiFri.Oracle
