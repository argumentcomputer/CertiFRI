import Mathlib

/-!
# Oracle computations

Computations that query an oracle, and what a run against a lazily sampled
oracle can produce. Probabilities are in `Prob.lean`.

* The oracle answers a query `x : X` with a value of the type `Y x`. `X` may
  be infinite, so a random oracle is never sampled as a function. Instead a
  `Log` records the queries answered so far with their answers, oldest first.
* `OracleComp Y α` is a computation that makes queries and returns an `α`. It
  is a monad. `QueryBound c n` says `c` makes at most `n` queries on every
  path.
* `c.run f` is the result of `c` when the oracle is the function `f`.
* `Outcome c l a l'` says a run of `c` from the log `l` can end with the result
  `a` and the log `l'`: a query found in the log gets the logged answer, a fresh
  query gets any answer, which is appended to the log.

The main facts: an outcome of `c.bind g` is an outcome of `g` after one of `c`
(`outcome_bind`); a run extends the log by at most the query bound
(`Outcome.exists_append`) and keeps its queries distinct (`Outcome.nodupKeys`);
the result is the one the computation gives against any function that agrees
with the final log (`Outcome.run_eq`).

Not covered: computational notions (running time, the size of queries).
-/

namespace CertiFri.Oracle

universe u v w w'

/-- The log of an oracle with answer types `Y`: the queries answered so far with
their answers, oldest first. -/
abbrev Log {X : Type u} (Y : X → Type v) : Type (max u v) := List (Sigma Y)

/-- The function that answers a query as the log `l` if it holds an answer, and
as `f` otherwise. -/
def Log.toFun {X : Type u} {Y : X → Type v} [DecidableEq X] (l : Log Y) (f : ∀ x, Y x)
    (x : X) : Y x :=
  (l.dlookup x).getD (f x)

/-- Where the log holds an answer, the completed function gives it. -/
theorem Log.toFun_of_dlookup {X : Type u} {Y : X → Type v} [DecidableEq X] {l : Log Y}
    (f : ∀ x, Y x) {x : X} {y : Y x} (h : l.dlookup x = some y) : l.toFun f x = y := by
  rw [Log.toFun, h, Option.getD_some]

/-- A computation that returns an `α` and may query an oracle that answers
`x : X` with a value in `Y x`. It either returns, or makes a query and continues
with the answer. -/
inductive OracleComp {X : Type u} (Y : X → Type v) (α : Type w) : Type (max u v w)
  /-- Return `a` without a further query. -/
  | pure (a : α) : OracleComp Y α
  /-- Query `x` and continue with `k y`, where `y` is the answer. -/
  | queryBind (x : X) (k : Y x → OracleComp Y α) : OracleComp Y α

namespace OracleComp

variable {X : Type u} {Y : X → Type v} {α : Type w} {β : Type w'}

/-! ## The monad -/

/-- Run `c`, then run `g` on its result. -/
protected def bind : OracleComp Y α → (α → OracleComp Y β) → OracleComp Y β
  | .pure a, g => g a
  | .queryBind x k, g => .queryBind x fun y => (k y).bind g

/-- Make the single query `x` and return the answer. -/
def query (x : X) : OracleComp Y (Y x) := .queryBind x .pure

/-- Returning `a` and then running `g` is running `g a`. -/
@[simp] theorem pure_bind (a : α) (g : α → OracleComp Y β) :
    (OracleComp.pure a : OracleComp Y α).bind g = g a := rfl

/-- `bind` goes under a query. -/
@[simp] theorem queryBind_bind (x : X) (k : Y x → OracleComp Y α) (g : α → OracleComp Y β) :
    (OracleComp.queryBind x k).bind g = .queryBind x fun y => (k y).bind g := rfl

/-- A query followed by `g` is the query that continues with `g`. -/
@[simp] theorem query_bind (x : X) (g : Y x → OracleComp Y β) :
    (query x).bind g = .queryBind x g := rfl

/-- Running `c` and returning its result is `c`. -/
@[simp] theorem bind_pure (c : OracleComp Y α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | queryBind x k ih => simp only [queryBind_bind, ih]

/-- `bind` is associative. -/
theorem bind_assoc {γ : Type*} (c : OracleComp Y α) (g : α → OracleComp Y β)
    (h : β → OracleComp Y γ) : (c.bind g).bind h = c.bind fun a => (g a).bind h := by
  induction c with
  | pure a => rfl
  | queryBind x k ih => simp only [queryBind_bind, ih]

/-- Oracle computations form a monad, so `do` notation applies when the results
live in one universe. -/
instance : Monad (OracleComp Y) where
  pure := .pure
  bind := .bind

/-- `pure` of the monad is the constructor `OracleComp.pure`. -/
theorem pure_def (a : α) : (Pure.pure a : OracleComp Y α) = .pure a := rfl

/-- `>>=` of the monad is `OracleComp.bind`. -/
theorem bind_def {β : Type w} (c : OracleComp Y α) (g : α → OracleComp Y β) :
    c >>= g = c.bind g := rfl

/-- The monad laws hold. -/
instance : LawfulMonad (OracleComp Y) :=
  LawfulMonad.mk' _ (id_map := fun c => bind_pure c) (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c g h => bind_assoc c g h)

/-! ## Counting queries -/

/-- `c` makes at most `n` queries on every path. A repeated query counts each
time it is made. -/
def QueryBound : OracleComp Y α → ℕ → Prop
  | .pure _, _ => True
  | .queryBind _ _, 0 => False
  | .queryBind _ k, n + 1 => ∀ y, QueryBound (k y) n

/-- A computation that returns at once meets every query bound. -/
@[simp] theorem queryBound_pure (a : α) (n : ℕ) :
    (OracleComp.pure a : OracleComp Y α).QueryBound n := trivial

/-- A computation that makes a query does not meet the bound zero. -/
@[simp] theorem queryBound_queryBind_zero (x : X) (k : Y x → OracleComp Y α) :
    ¬ (OracleComp.queryBind x k).QueryBound 0 := id

/-- A query followed by `k` meets the bound `n + 1` when every `k y` meets `n`. -/
@[simp] theorem queryBound_queryBind_succ (x : X) (k : Y x → OracleComp Y α) (n : ℕ) :
    (OracleComp.queryBind x k).QueryBound (n + 1) ↔ ∀ y, (k y).QueryBound n := Iff.rfl

/-- A single query meets the bound one. -/
theorem queryBound_query (x : X) : (query x : OracleComp Y (Y x)).QueryBound 1 :=
  fun _ => trivial

/-- A query bound can be raised. -/
theorem QueryBound.mono {c : OracleComp Y α} {n m : ℕ} (h : c.QueryBound n) (hnm : n ≤ m) :
    c.QueryBound m := by
  induction c generalizing n m with
  | pure a => trivial
  | queryBind x k ih =>
    cases n with
    | zero => exact absurd h (queryBound_queryBind_zero x k)
    | succ n =>
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact fun y => ih y (h y) (by omega)

/-- Query bounds add along `bind`. -/
theorem QueryBound.bind {c : OracleComp Y α} {g : α → OracleComp Y β} {n m : ℕ}
    (hc : c.QueryBound n) (hg : ∀ a, (g a).QueryBound m) : (c.bind g).QueryBound (n + m) := by
  induction c generalizing n with
  | pure a => exact (hg a).mono (Nat.le_add_left m n)
  | queryBind x k ih =>
    cases n with
    | zero => exact absurd hc (queryBound_queryBind_zero x k)
    | succ n =>
      rw [queryBind_bind, Nat.add_right_comm]
      exact fun y => ih y (hc y)

/-! ## Running against a fixed function -/

/-- The result of `c` when the oracle is the function `f`. -/
def run (f : ∀ x, Y x) : OracleComp Y α → α
  | .pure a => a
  | .queryBind x k => run f (k (f x))

/-- Against a function, a computation that returns `a` gives `a`. -/
@[simp] theorem run_pure (f : ∀ x, Y x) (a : α) :
    (OracleComp.pure a : OracleComp Y α).run f = a := rfl

/-- Against the function `f`, the query `x` is answered with `f x`. -/
@[simp] theorem run_queryBind (f : ∀ x, Y x) (x : X) (k : Y x → OracleComp Y α) :
    (OracleComp.queryBind x k).run f = (k (f x)).run f := rfl

/-- Against the function `f`, the single query `x` gives `f x`. -/
@[simp] theorem run_query (f : ∀ x, Y x) (x : X) : (query x).run f = f x := rfl

/-- Against a function, `c.bind g` gives what `g` gives on the result of `c`. -/
@[simp] theorem run_bind (f : ∀ x, Y x) (c : OracleComp Y α) (g : α → OracleComp Y β) :
    (c.bind g).run f = (g (c.run f)).run f := by
  induction c with
  | pure a => rfl
  | queryBind x k ih => simp only [queryBind_bind, run_queryBind, ih]

/-! ## Outcomes of a lazily sampled run -/

section Outcome

variable [DecidableEq X]

/-- Started from the log `l`, the computation `c` can return `a` and leave the
log `l'`. A query found in the log gets the logged answer; a fresh query may
get any answer, which is appended to the log. -/
def Outcome : OracleComp Y α → Log Y → α → Log Y → Prop
  | .pure a, l, a', l' => a' = a ∧ l' = l
  | .queryBind x k, l, a', l' =>
    match l.dlookup x with
    | some y => Outcome (k y) l a' l'
    | none => ∃ y, Outcome (k y) (l ++ [⟨x, y⟩]) a' l'

/-- A computation that returns `a` has the one outcome `a`, with the log unchanged. -/
@[simp] theorem outcome_pure {a a' : α} {l l' : Log Y} :
    Outcome (.pure a : OracleComp Y α) l a' l' ↔ a' = a ∧ l' = l := Iff.rfl

/-- A query found in the log continues with the logged answer. -/
theorem outcome_queryBind_of_lookup {x : X} {y : Y x} {l : Log Y} (h : l.dlookup x = some y)
    (k : Y x → OracleComp Y α) (a : α) (l' : Log Y) :
    Outcome (.queryBind x k) l a l' ↔ Outcome (k y) l a l' := by
  simp only [Outcome, h]

/-- A query not in the log continues with any answer, appended to the log. -/
theorem outcome_queryBind_of_fresh {x : X} {l : Log Y} (h : l.dlookup x = none)
    (k : Y x → OracleComp Y α) (a : α) (l' : Log Y) :
    Outcome (.queryBind x k) l a l' ↔ ∃ y, Outcome (k y) (l ++ [⟨x, y⟩]) a l' := by
  simp only [Outcome, h]

/-- The outcomes of a single query: the logged answer with the log unchanged,
or any answer, appended to the log, when the query is fresh. -/
theorem outcome_query {x : X} {y : Y x} {l l' : Log Y} :
    Outcome (query x) l y l' ↔
      (l.dlookup x = some y ∧ l' = l) ∨ (l.dlookup x = none ∧ l' = l ++ [⟨x, y⟩]) := by
  unfold query
  cases h : l.dlookup x with
  | some y' =>
    rw [outcome_queryBind_of_lookup h, outcome_pure]
    simp only [Option.some.injEq, reduceCtorEq, false_and, or_false]
    exact and_congr_left fun _ => eq_comm
  | none =>
    rw [outcome_queryBind_of_fresh h]
    simp only [outcome_pure, reduceCtorEq, false_and, true_and, false_or]
    constructor
    · rintro ⟨y', rfl, rfl⟩
      rfl
    · rintro rfl
      exact ⟨y, rfl, rfl⟩

/-- An outcome of `c.bind g` is an outcome of `g` started from an outcome of `c`. -/
theorem outcome_bind {c : OracleComp Y α} {g : α → OracleComp Y β} {l l'' : Log Y} {b : β} :
    Outcome (c.bind g) l b l'' ↔ ∃ a l', Outcome c l a l' ∧ Outcome (g a) l' b l'' := by
  induction c generalizing l with
  | pure a =>
    constructor
    · exact fun h => ⟨a, l, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨_, _, ⟨rfl, rfl⟩, h⟩
      exact h
  | queryBind x k ih =>
    rw [queryBind_bind]
    cases h : l.dlookup x with
    | some y =>
      rw [outcome_queryBind_of_lookup h, ih]
      simp only [outcome_queryBind_of_lookup h]
    | none =>
      rw [outcome_queryBind_of_fresh h]
      simp only [ih, outcome_queryBind_of_fresh h]
      constructor
      · rintro ⟨y, a, l', h₁, h₂⟩
        exact ⟨a, l', ⟨y, h₁⟩, h₂⟩
      · rintro ⟨a, l', ⟨y, h₁⟩, h₂⟩
        exact ⟨y, a, l', h₁, h₂⟩

/-- An outcome of a query followed by `k` is an outcome of `k` started from an
outcome of the query. -/
theorem outcome_queryBind {x : X} {k : Y x → OracleComp Y α} {l l' : Log Y} {a : α} :
    Outcome (.queryBind x k) l a l' ↔
      ∃ y l₁, Outcome (query x) l y l₁ ∧ Outcome (k y) l₁ a l' :=
  outcome_bind (c := query x) (g := k)

/-- After a query, the log holds its answer. -/
theorem Outcome.dlookup_query {x : X} {y : Y x} {l l' : Log Y} (h : Outcome (query x) l y l') :
    l'.dlookup x = some y := by
  rcases outcome_query.mp h with ⟨hx, rfl⟩ | ⟨hx, rfl⟩
  · exact hx
  · rw [List.dlookup_append, hx, Option.none_or, List.dlookup_cons_eq]

/-- A run only appends to the log. -/
theorem Outcome.prefix {c : OracleComp Y α} {l l' : Log Y} {a : α} (h : Outcome c l a l') :
    l <+: l' := by
  induction c generalizing l with
  | pure a => exact h.2 ▸ List.prefix_refl l
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y => exact ih y ((outcome_queryBind_of_lookup hx k a l').mp h)
    | none =>
      obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hx k a l').mp h
      exact (List.prefix_append l _).trans (ih y hy)

/-- A run with at most `n` queries appends at most `n` entries to the log. -/
theorem Outcome.exists_append {c : OracleComp Y α} {l l' : Log Y} {a : α} {n : ℕ}
    (h : Outcome c l a l') (hc : c.QueryBound n) : ∃ t, l' = l ++ t ∧ t.length ≤ n := by
  induction c generalizing l n with
  | pure a => exact ⟨[], by rw [h.2, List.append_nil], Nat.zero_le n⟩
  | queryBind x k ih =>
    cases n with
    | zero => exact absurd hc (queryBound_queryBind_zero x k)
    | succ n =>
      cases hx : l.dlookup x with
      | some y =>
        obtain ⟨t, ht, hlen⟩ := ih y ((outcome_queryBind_of_lookup hx k a l').mp h) (hc y)
        exact ⟨t, ht, hlen.trans (Nat.le_succ n)⟩
      | none =>
        obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hx k a l').mp h
        obtain ⟨t, ht, hlen⟩ := ih y hy (hc y)
        exact ⟨⟨x, y⟩ :: t, by rw [ht, List.append_assoc, List.singleton_append],
          Nat.succ_le_succ hlen⟩

/-- The length of the final log exceeds the initial one by at most the query bound. -/
theorem Outcome.length_le {c : OracleComp Y α} {l l' : Log Y} {a : α} {n : ℕ}
    (h : Outcome c l a l') (hc : c.QueryBound n) : l'.length ≤ l.length + n := by
  obtain ⟨t, rfl, ht⟩ := h.exists_append hc
  rw [List.length_append]
  exact Nat.add_le_add_left ht _

/-- An answer in the log stays the answer when the log grows. -/
theorem dlookup_of_prefix {l l' : Log Y} {x : X} {y : Y x} (h : l.dlookup x = some y)
    (hl : l <+: l') : l'.dlookup x = some y := by
  obtain ⟨t, rfl⟩ := hl
  rw [List.dlookup_append, h, Option.some_or]

/-- The result of a run is the result against any function that agrees with
the final log. -/
theorem Outcome.run_eq {c : OracleComp Y α} {l l' : Log Y} {a : α} (h : Outcome c l a l')
    {f : ∀ x, Y x} (hf : ∀ x y, l'.dlookup x = some y → f x = y) : c.run f = a := by
  induction c generalizing l with
  | pure a => exact h.1.symm
  | queryBind x k ih =>
    rw [run_queryBind]
    cases hx : l.dlookup x with
    | some y =>
      rw [outcome_queryBind_of_lookup hx] at h
      rw [hf x y (dlookup_of_prefix hx h.prefix)]
      exact ih y h
    | none =>
      obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hx k a l').mp h
      have hy' : (l ++ [(⟨x, y⟩ : Sigma Y)]).dlookup x = some y := by
        rw [List.dlookup_append, hx, Option.none_or, List.dlookup_cons_eq]
      rw [hf x y (dlookup_of_prefix hy' hy.prefix)]
      exact ih y hy

/-- The result of a run is the result against the final log completed to a
function. -/
theorem Outcome.run_toFun {c : OracleComp Y α} {l l' : Log Y} {a : α} (h : Outcome c l a l')
    (f : ∀ x, Y x) : c.run (Log.toFun l' f) = a :=
  h.run_eq fun _ _ hxy => Log.toFun_of_dlookup f hxy

/-- Appending a fresh query keeps the queries of the log distinct. -/
theorem nodupKeys_concat {l : Log Y} {x : X} (y : Y x) (hl : l.NodupKeys)
    (hx : l.dlookup x = none) : (l ++ [(⟨x, y⟩ : Sigma Y)]).NodupKeys := by
  rw [List.dlookup_eq_none] at hx
  rw [List.NodupKeys, List.keys_append, List.nodup_append]
  refine ⟨hl, by simp [List.keys], ?_⟩
  intro a ha b hb
  simp only [List.keys, List.map_cons, List.map_nil, List.mem_singleton] at hb
  rintro rfl
  exact hx (hb ▸ ha)

/-- A run from a log without a repeated query leaves a log without one. So an
entry is in the final log exactly when it is the answer the log gives
(`List.mem_dlookup_iff`). -/
theorem Outcome.nodupKeys {c : OracleComp Y α} {l l' : Log Y} {a : α} (h : Outcome c l a l')
    (hl : l.NodupKeys) : l'.NodupKeys := by
  induction c generalizing l with
  | pure a => exact h.2 ▸ hl
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y => exact ih y ((outcome_queryBind_of_lookup hx k a l').mp h) hl
    | none =>
      obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hx k a l').mp h
      exact ih y hy (nodupKeys_concat y hl hx)

end Outcome

end OracleComp

end CertiFri.Oracle
