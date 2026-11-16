/-!
# Folding schedule

Port of `compute_log_arity_for_round` and `fold_schedule` from Plonky3
(`fri/src/config.rs`).

The schedule is the list of log-arities of the commit rounds. Both sides derive
it from the parameters and the claimed heights, so it is never read from a
proof. Plonky3's verifier relies on two properties of the derivation:

* the arities sum to the distance from the tallest input to the final height
  (`foldSchedule_sum`);
* every round folds by at least one bit and at most the configured cap
  (`foldSchedule_bounds`).

Plonky3 checks both by sweeping every height set below `2 ^ 10`. Here they are
theorems for strictly decreasing input heights and a positive arity cap.
-/

namespace CertiFri

/-- Log-arity of one commit round.

A round is capped by the distance to the final height, by the distance down to
the next input waiting to be rolled in (`nextInput`), and by `maxLogArity`. -/
def logArityForRound (logHeight : Nat) (nextInput : Option Nat)
    (logFinalHeight maxLogArity : Nat) : Nat :=
  let toTarget := logHeight - logFinalHeight
  let maxFold :=
    match nextInput with
    | none => toTarget
    | some next => min (logHeight - next) toTarget
  min maxFold maxLogArity

/-- The rounds from `logHeight` down to `logFinalHeight`, where `pending` holds
the inputs not yet rolled in, tallest first. `fuel` bounds the number of rounds. -/
def foldScheduleFrom (logFinalHeight maxLogArity : Nat) :
    (fuel logHeight : Nat) → (pending : List Nat) → List Nat
  | 0, _, _ => []
  | fuel + 1, logHeight, pending =>
    if logHeight ≤ logFinalHeight then []
    else
      let logArity := logArityForRound logHeight pending.head? logFinalHeight maxLogArity
      let folded := logHeight - logArity
      -- An input whose height the fold just reached is rolled in here.
      let pending := if pending.head? = some folded then pending.tail else pending
      logArity :: foldScheduleFrom logFinalHeight maxLogArity fuel folded pending

/-- One log-arity per commit round, in round order.

`inputLogHeights` are the log-heights of the folding inputs, strictly
decreasing. Folding starts at the tallest and stops at `logFinalHeight`.

Plonky3 panics when the heights are not strictly decreasing or `maxLogArity` is
zero. This function is total, and its value on such inputs is unspecified: the
theorems below assume both preconditions. `deriveShape` establishes sortedness;
the future verifier must also validate the arity cap. -/
def foldSchedule (inputLogHeights : List Nat) (logFinalHeight maxLogArity : Nat) : List Nat :=
  match inputLogHeights with
  | [] => []
  | tallest :: rest =>
    -- Every round folds at least one bit away, so this many rounds suffice.
    foldScheduleFrom logFinalHeight maxLogArity (tallest - logFinalHeight) tallest rest

/-! ## Plonky3's unit-test vectors -/

example : foldSchedule [10] 2 3 = [3, 3, 2] := by decide
example : foldSchedule [10] 2 1 = List.replicate 8 1 := by decide
example : foldSchedule [10, 6] 2 3 = [3, 1, 3, 1] := by decide
example : foldSchedule [] 2 3 = [] := by decide

/-! ## The two invariants the verifier relies on -/

theorem logArityForRound_le_cap (logHeight : Nat) (nextInput : Option Nat)
    (logFinalHeight maxLogArity : Nat) :
    logArityForRound logHeight nextInput logFinalHeight maxLogArity ≤ maxLogArity := by
  unfold logArityForRound
  cases nextInput <;> simp only <;> omega

theorem logArityForRound_le_toTarget (logHeight : Nat) (nextInput : Option Nat)
    (logFinalHeight maxLogArity : Nat) :
    logArityForRound logHeight nextInput logFinalHeight maxLogArity
      ≤ logHeight - logFinalHeight := by
  unfold logArityForRound
  cases nextInput <;> simp only <;> omega

theorem logArityForRound_le_toNext (logHeight next logFinalHeight maxLogArity : Nat) :
    logArityForRound logHeight (some next) logFinalHeight maxLogArity ≤ logHeight - next := by
  unfold logArityForRound
  simp only
  omega

theorem logArityForRound_pos {logHeight : Nat} {nextInput : Option Nat}
    {logFinalHeight maxLogArity : Nat} (hfinal : logFinalHeight < logHeight)
    (hcap : 0 < maxLogArity) (hnext : ∀ next, nextInput = some next → next < logHeight) :
    0 < logArityForRound logHeight nextInput logFinalHeight maxLogArity := by
  unfold logArityForRound
  cases nextInput with
  | none => simp only; omega
  | some next =>
    have := hnext next rfl
    simp only
    omega

/-- The invariant of the round loop: the remaining rounds account exactly for
the remaining distance, and each stays within the arity bounds. -/
theorem foldScheduleFrom_spec {logFinalHeight maxLogArity : Nat} (hcap : 0 < maxLogArity) :
    ∀ (fuel logHeight : Nat) (pending : List Nat),
      logHeight - logFinalHeight ≤ fuel →
      pending.Pairwise (· > ·) →
      (∀ x ∈ pending, x < logHeight) →
      (foldScheduleFrom logFinalHeight maxLogArity fuel logHeight pending).sum
          = logHeight - logFinalHeight ∧
        ∀ a ∈ foldScheduleFrom logFinalHeight maxLogArity fuel logHeight pending,
          1 ≤ a ∧ a ≤ maxLogArity := by
  intro fuel
  induction fuel with
  | zero =>
    intro logHeight pending hfuel _ _
    simp only [foldScheduleFrom, List.sum_nil, List.not_mem_nil, false_imp_iff, implies_true,
      and_true]
    omega
  | succ fuel ih =>
    intro logHeight pending hfuel hsorted hbelow
    unfold foldScheduleFrom
    by_cases hdone : logHeight ≤ logFinalHeight
    · simp only [hdone, ite_true, List.sum_nil, List.not_mem_nil, false_imp_iff, implies_true,
        and_true]
      omega
    · simp only [hdone, ite_false]
      have hpos : 0 < logArityForRound logHeight pending.head? logFinalHeight maxLogArity :=
        logArityForRound_pos (by omega) hcap (fun next hnext =>
          hbelow next (List.mem_of_mem_head? hnext))
      have hcap' := logArityForRound_le_cap logHeight pending.head? logFinalHeight maxLogArity
      have htarget :=
        logArityForRound_le_toTarget logHeight pending.head? logFinalHeight maxLogArity
      -- The inputs still pending after this round stay sorted and below the folded height.
      have hpending :
          (if pending.head? = some
                (logHeight - logArityForRound logHeight pending.head? logFinalHeight maxLogArity)
              then pending.tail else pending).Pairwise (· > ·) ∧
            ∀ x ∈ (if pending.head? = some
                (logHeight - logArityForRound logHeight pending.head? logFinalHeight maxLogArity)
              then pending.tail else pending),
              x < logHeight - logArityForRound logHeight pending.head? logFinalHeight
                maxLogArity := by
        cases pending with
        | nil => simp
        | cons next rest =>
          have hnext := logArityForRound_le_toNext logHeight next logFinalHeight maxLogArity
          have hlt : next < logHeight := hbelow next (List.mem_cons_self ..)
          rw [List.pairwise_cons] at hsorted
          simp only [List.head?_cons, List.tail_cons, Option.some.injEq]
          split
          · next heq =>
            refine ⟨hsorted.2, fun x hx => ?_⟩
            have := hsorted.1 x hx
            omega
          · next hne =>
            refine ⟨List.pairwise_cons.mpr hsorted, fun x hx => ?_⟩
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have := hsorted.1 x hx
              omega
      obtain ⟨hsum, hmem⟩ := ih _ _ (by omega) hpending.1 hpending.2
      refine ⟨?_, ?_⟩
      · rw [List.sum_cons, hsum]
        omega
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨hpos, hcap'⟩
        · exact hmem a ha

/-- The arities account for the whole distance: folding from the tallest input
lands exactly on the final height. -/
theorem foldSchedule_sum {tallest : Nat} {rest : List Nat} {logFinalHeight maxLogArity : Nat}
    (hsorted : (tallest :: rest).Pairwise (· > ·)) (hcap : 0 < maxLogArity) :
    (foldSchedule (tallest :: rest) logFinalHeight maxLogArity).sum
      = tallest - logFinalHeight := by
  rw [List.pairwise_cons] at hsorted
  exact (foldScheduleFrom_spec hcap _ _ _ (Nat.le_refl _) hsorted.2 hsorted.1).1

/-- Every round folds by at least one bit and at most the configured cap. -/
theorem foldSchedule_bounds {tallest : Nat} {rest : List Nat} {logFinalHeight maxLogArity : Nat}
    (hsorted : (tallest :: rest).Pairwise (· > ·)) (hcap : 0 < maxLogArity) :
    ∀ a ∈ foldSchedule (tallest :: rest) logFinalHeight maxLogArity,
      1 ≤ a ∧ a ≤ maxLogArity := by
  rw [List.pairwise_cons] at hsorted
  exact (foldScheduleFrom_spec hcap _ _ _ (Nat.le_refl _) hsorted.2 hsorted.1).2

/-- A list of ones is determined by its sum. -/
private theorem eq_replicate_one_of_forall_eq_one :
    ∀ l : List Nat, (∀ a ∈ l, a = 1) → l = List.replicate l.sum 1
  | [], _ => rfl
  | a :: l, h => by
    have ha : a = 1 := h a (List.mem_cons_self ..)
    have hl := eq_replicate_one_of_forall_eq_one l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    subst ha
    rw [List.sum_cons, Nat.add_comm, List.replicate_succ]
    exact congrArg _ hl

/-- With binary folding the schedule is one round per level, whatever the
heights of the inputs. -/
theorem foldSchedule_binary {tallest : Nat} {rest : List Nat} {logFinalHeight : Nat}
    (hsorted : (tallest :: rest).Pairwise (· > ·)) :
    foldSchedule (tallest :: rest) logFinalHeight 1
      = List.replicate (tallest - logFinalHeight) 1 := by
  have hones : ∀ a ∈ foldSchedule (tallest :: rest) logFinalHeight 1, a = 1 := fun a ha => by
    have := foldSchedule_bounds hsorted (Nat.zero_lt_one) a ha
    omega
  rw [← foldSchedule_sum hsorted (Nat.zero_lt_one)]
  exact eq_replicate_one_of_forall_eq_one _ hones

end CertiFri
