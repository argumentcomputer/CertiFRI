import CertiFriProofs.Theory.Oracle.Basic

/-!
# Replaying a run from a later log

A run of an oracle computation leaves every query it made in the log, with the
answer it got. So the run can be repeated from any log that extends its final
log: every query is found in the log, with the same answer, the result is the
same, and no entry is added.

* `OracleComp.Outcome.replay`: if `c`, run from `l`, can return `a` and leave
  the log `l₁`, then from any log `l'` with `l₁ <+: l'` it returns `a` and
  leaves `l'`.

With this, a statement about the log right after a run (for instance, what an
accepting verifier leaves behind) applies to the log after any computation that
follows the run.

No assumption is made on the logs. Not covered: probabilities.
-/

namespace CertiFri.Oracle.OracleComp

universe u v w

variable {X : Type u} {Y : X → Type v} {α : Type w} [DecidableEq X]

/-- **A run can be replayed from any later log.** If the computation `c`, run
from the log `l`, can return `a` and leave the log `l₁`, then run from a log
`l'` that extends `l₁` it returns `a` and adds no entry: `l'` answers every
query of the run as the run was answered. -/
theorem Outcome.replay {c : OracleComp Y α} {l l₁ l' : Log Y} {a : α} (h : Outcome c l a l₁)
    (hl : l₁ <+: l') : Outcome c l' a l' := by
  induction c generalizing l with
  | pure a' => exact ⟨h.1, rfl⟩
  | queryBind x k ih =>
    cases hx : l.dlookup x with
    | some y =>
      have h' := (outcome_queryBind_of_lookup hx k a l₁).mp h
      exact (outcome_queryBind_of_lookup (dlookup_of_prefix hx (h'.prefix.trans hl)) k a l').mpr
        (ih y h')
    | none =>
      obtain ⟨y, hy⟩ := (outcome_queryBind_of_fresh hx k a l₁).mp h
      have hy' : (l ++ [(⟨x, y⟩ : Sigma Y)]).dlookup x = some y := by
        rw [List.dlookup_append, hx, Option.none_or, List.dlookup_cons_eq]
      exact (outcome_queryBind_of_lookup (dlookup_of_prefix hy' (hy.prefix.trans hl)) k a l').mpr
        (ih y hy)

end CertiFri.Oracle.OracleComp
