import CertiFri.Schedule
import CertiFri.Verifier

/-!
# Multi-arity tensor-batched FRI verifier

Generalizes `CertiFri/Verifier.lean` from binary folding (`logArity = 1`) to
arbitrary per-round variable arity schedules `arities : List Nat` with
`1 ≤ a ≤ params.maxLogArity` (in particular `logArity ∈ {1, 2, 3}`, fold
factors `2, 4, 8`), matching `multi-stark`'s `verify_fri_with_batching_inner`
(`src/p3_adapter/fri_batching.rs`) and `TwoAdicFriFolding::fold_row`.

## Design

* `scheduleOfShape params shape` derives the canonical Plonky3 / `multi-stark`
  folding schedule via `CertiFri.foldSchedule` on the strictly-decreasing
  distinct input log-heights of `shape`.
* `foldRowMulti` evaluates the `2 ^ a`-ary fold on a bit-reversed coset row by
  iterating `a` binary `foldRow` passes with challenges `β, β ^ 2, …, β ^ (2 ^ (a - 1))`,
  matching both `multi-stark`'s GPU kernel and Plonky3's Lagrange interpolation
  on the `2 ^ a`-coset. When an input reduced opening joins at the folded
  height, it is added with weight `fieldPowTwo beta a` (`β ^ (2 ^ a)`).
* `verifyTensorWithSchedule` / `verifyFromTensorWithSchedule` accept any valid
  per-round schedule `arities : List Nat`; `verifyTensorMultiArity` /
  `verifyFromTensorMultiArity` instantiate them with the canonical schedule
  `scheduleOfShape params shape`.
* Concrete compact multi-arity FRI parameter sets `FriParams.compact400KBBalanced`
  and `FriParams.ultraCompact400KBZk` (`logBlowup = 4`, `maxLogArity = 3`,
  `logFinalPolyLen = 8`, `numQueries = 58 / 55`, `queryPowBits = 28 / 30`) are
  defined in `CertiFri.FriParams`.
-/

namespace CertiFri

namespace FriParams

/-- Compact 400KB balanced multi-arity FRI parameters: blowup `16` (`logBlowup = 4`),
up to 8-ary folding (`maxLogArity = 3`), final polynomial length `256`
(`logFinalPolyLen = 8`), `58` queries, and `28`-bit query PoW. -/
def compact400KBBalanced : FriParams where
  logBlowup := 4
  logFinalPolyLen := 8
  maxLogArity := 3
  numQueries := 58
  commitPowBits := 0
  queryPowBits := 28

/-- Ultra-compact 400KB ZK multi-arity FRI parameters: blowup `16` (`logBlowup = 4`),
up to 8-ary folding (`maxLogArity = 3`), final polynomial length `256`
(`logFinalPolyLen = 8`), `55` queries, and `30`-bit query PoW. -/
def ultraCompact400KBZk : FriParams where
  logBlowup := 4
  logFinalPolyLen := 8
  maxLogArity := 3
  numQueries := 55
  commitPowBits := 0
  queryPowBits := 30

end FriParams

namespace Fri

/-! ## Per-round arity schedules -/

/-- Insert `x` into a strictly decreasing list, keeping it strictly decreasing
and without duplicates. -/
def insertDesc (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys =>
    if y < x then x :: y :: ys
    else if x == y then y :: ys
    else y :: insertDesc x ys

/-- The distinct log-heights of all matrices in `shape`, strictly decreasing. -/
def distinctLogHeights (logBlowup : Nat) (shape : ClaimShape) : List Nat :=
  (shape.flatten.map fun m => m.logDegree + logBlowup).foldr insertDesc []

/-- Canonical per-round log-arity schedule for `(params, shape)`, derived by
`CertiFri.foldSchedule` on `distinctLogHeights`. -/
def scheduleOfShape (params : FriParams) (shape : ClaimShape) : List Nat :=
  foldSchedule (distinctLogHeights params.logBlowup shape)
    params.logFinalHeight params.maxLogArity

/-- Cumulative log-arity folded before round `i`: the sum of the first `i`
entries of `arities`. -/
def cumLogArity (arities : List Nat) (i : Nat) : Nat :=
  (arities.take i).sum

/-- Whether `arities` is a valid folding schedule for `(params, shape)`:
every round folds by `1 .. maxLogArity`, the total reduction reaches
`params.logFinalHeight` from `logMaxHeight`, and every input matrix height lands
on a round boundary `n - cumLogArity arities r`. -/
def scheduleValid (params : FriParams) (shape : ClaimShape) (arities : List Nat) : Bool :=
  let n := logMaxHeight params.logBlowup shape
  arities.all (fun a => decide (1 ≤ a ∧ a ≤ params.maxLogArity))
    && arities.sum + params.logFinalHeight == n
    && shape.flatten.all fun m =>
      (List.range (arities.length + 1)).any fun r =>
        m.logDegree + params.logBlowup + cumLogArity arities r == n

/-! ## Schedule lemmas -/

theorem mem_insertDesc {x y : Nat} {l : List Nat} :
    y ∈ insertDesc x l ↔ y = x ∨ y ∈ l := by
  induction l with
  | nil => simp [insertDesc]
  | cons z zs ih =>
    unfold insertDesc
    split
    · simp
    · split
      · next hlt heq =>
        have hxz : x = z := beq_iff_eq.mp heq
        subst hxz
        simp only [List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | rfl | h)
          · exact Or.inl rfl
          · exact Or.inl rfl
          · exact Or.inr h
      · simp only [List.mem_cons, ih]
        constructor
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)
        · rintro (rfl | rfl | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr h)

theorem insertDesc_pairwise {x : Nat} {l : List Nat} (h : l.Pairwise (· > ·)) :
    (insertDesc x l).Pairwise (· > ·) := by
  induction l with
  | nil => simp [insertDesc]
  | cons z zs ih =>
    rw [List.pairwise_cons] at h
    unfold insertDesc
    split
    · next hlt =>
      rw [List.pairwise_cons]
      refine ⟨fun w hw => ?_, List.pairwise_cons.mpr h⟩
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hlt
      · exact Nat.lt_trans (h.1 w hw) hlt
    · split
      · exact List.pairwise_cons.mpr h
      · next hge hne =>
        have hxz : x < z := by
          have hne' : x ≠ z := fun heq => hne (beq_iff_eq.mpr heq)
          omega
        rw [List.pairwise_cons]
        refine ⟨fun w hw => ?_, ih h.2⟩
        rcases mem_insertDesc.mp hw with rfl | hw
        · exact hxz
        · exact h.1 w hw

private theorem foldr_insertDesc_pairwise (l : List Nat) :
    (l.foldr insertDesc []).Pairwise (· > ·) := by
  induction l with
  | nil => simp
  | cons a as ih => exact insertDesc_pairwise ih

private theorem mem_foldr_insertDesc {x : Nat} {l : List Nat} :
    x ∈ l.foldr insertDesc [] ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldr_cons, mem_insertDesc, List.mem_cons, ih]

theorem distinctLogHeights_pairwise (logBlowup : Nat) (shape : ClaimShape) :
    (distinctLogHeights logBlowup shape).Pairwise (· > ·) :=
  foldr_insertDesc_pairwise _

theorem mem_distinctLogHeights {logBlowup : Nat} {shape : ClaimShape} {h : Nat} :
    h ∈ distinctLogHeights logBlowup shape ↔
      ∃ m ∈ shape.flatten, m.logDegree + logBlowup = h := by
  unfold distinctLogHeights
  rw [mem_foldr_insertDesc, List.mem_map]

theorem distinctLogHeights_ne_nil {logBlowup : Nat} {shape : ClaimShape}
    (hne : shape.flatten ≠ []) :
    distinctLogHeights logBlowup shape ≠ [] := by
  cases hf : shape.flatten with
  | nil => exact absurd hf hne
  | cons m ms =>
    intro hnil
    have hmem : m.logDegree + logBlowup ∈ distinctLogHeights logBlowup shape :=
      mem_distinctLogHeights.mpr ⟨m, by rw [hf]; exact List.mem_cons_self, rfl⟩
    rw [hnil] at hmem
    cases hmem

private theorem le_foldr_max_of_mem_nat {l : List Nat} {x : Nat} (hx : x ∈ l) :
    x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hx
  | cons a as ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; omega

private theorem foldr_max_le_of_forall_nat {l : List Nat} {b : Nat}
    (h : ∀ x ∈ l, x ≤ b) : l.foldr max 0 ≤ b := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    simp only [List.foldr_cons]
    have ha := h a List.mem_cons_self
    have has := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

theorem distinctLogHeights_head_eq {logBlowup : Nat} {shape : ClaimShape}
    {tallest : Nat} {rest : List Nat}
    (heq : distinctLogHeights logBlowup shape = tallest :: rest) :
    tallest = logMaxHeight logBlowup shape := by
  have hp := distinctLogHeights_pairwise logBlowup shape
  rw [heq, List.pairwise_cons] at hp
  have hmem : tallest ∈ distinctLogHeights logBlowup shape := by
    rw [heq]; exact List.mem_cons_self
  obtain ⟨m₀, hm₀, hdeg₀⟩ := mem_distinctLogHeights.mp hmem
  have hle1 : tallest ≤ logMaxHeight logBlowup shape := by
    rw [← hdeg₀, logMaxHeight]
    exact le_foldr_max_of_mem_nat (List.mem_map.mpr ⟨m₀, hm₀, rfl⟩)
  have hle2 : logMaxHeight logBlowup shape ≤ tallest := by
    rw [logMaxHeight]
    refine foldr_max_le_of_forall_nat fun h hh => ?_
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hh
    have hm' : m.logDegree + logBlowup ∈ distinctLogHeights logBlowup shape :=
      mem_distinctLogHeights.mpr ⟨m, hm, rfl⟩
    rw [heq, List.mem_cons] at hm'
    rcases hm' with h1 | h2
    · omega
    · exact Nat.le_of_lt (hp.1 _ h2)
  omega

@[simp]
theorem cumLogArity_zero (arities : List Nat) : cumLogArity arities 0 = 0 := rfl

theorem cumLogArity_succ (arities : List Nat) {i : Nat} (hi : i < arities.length) :
    cumLogArity arities (i + 1) = cumLogArity arities i + arities[i] := by
  unfold cumLogArity
  rw [List.take_succ_eq_append_getElem hi, List.sum_append, List.sum_singleton]

theorem cumLogArity_cons_succ (a : Nat) (as : List Nat) (i : Nat) :
    cumLogArity (a :: as) (i + 1) = a + cumLogArity as i := by
  simp [cumLogArity, List.take_succ_cons, List.sum_cons]

theorem cumLogArity_length (arities : List Nat) :
    cumLogArity arities arities.length = arities.sum := by
  simp [cumLogArity]

theorem cumLogArity_le_sum (arities : List Nat) (i : Nat) :
    cumLogArity arities i ≤ arities.sum := by
  unfold cumLogArity
  have h := congrArg List.sum (List.take_append_drop i arities)
  rw [List.sum_append] at h
  omega

theorem cumLogArity_mono (arities : List Nat) {i j : Nat} (hij : i ≤ j) :
    cumLogArity arities i ≤ cumLogArity arities j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step k _ ih =>
    unfold cumLogArity at ih ⊢
    by_cases hk : k < arities.length
    · rw [List.take_succ_eq_append_getElem hk, List.sum_append, List.sum_singleton]
      omega
    · have h1 : arities.take (k + 1) = arities := List.take_of_length_le (by omega)
      have h2 : arities.take k = arities := List.take_of_length_le (by omega)
      rw [h1]
      rw [h2] at ih
      exact ih

theorem cumLogArity_strictMono {arities : List Nat} (hpos : ∀ a ∈ arities, 0 < a)
    {i j : Nat} (hij : i < j) (hj : j ≤ arities.length) :
    cumLogArity arities i < cumLogArity arities j := by
  have hi : i < arities.length := Nat.lt_of_lt_of_le hij hj
  have h1 : cumLogArity arities (i + 1) ≤ cumLogArity arities j := cumLogArity_mono arities hij
  rw [cumLogArity_succ arities hi] at h1
  have ha : 0 < arities[i] := hpos _ (List.getElem_mem hi)
  omega

/-- Every pending input height at or above `logFinalHeight` is hit by a round
boundary of `foldScheduleFrom`. -/
theorem foldScheduleFrom_hits {logFinalHeight maxLogArity : Nat} (hcap : 0 < maxLogArity) :
    ∀ (fuel logHeight : Nat) (pending : List Nat),
      logHeight - logFinalHeight ≤ fuel →
      pending.Pairwise (· > ·) →
      (∀ x ∈ pending, x < logHeight) →
      ∀ h ∈ pending, logFinalHeight ≤ h →
        ∃ r ≤ (foldScheduleFrom logFinalHeight maxLogArity fuel logHeight pending).length,
          h + cumLogArity (foldScheduleFrom logFinalHeight maxLogArity fuel logHeight pending) r =
            logHeight := by
  intro fuel
  induction fuel with
  | zero =>
    intro logHeight pending hfuel _ hbelow h hh hfin
    have hlt := hbelow h hh
    omega
  | succ fuel ih =>
    intro logHeight pending hfuel hsorted hbelow h hh hfin
    unfold foldScheduleFrom
    have hlt_h : h < logHeight := hbelow h hh
    have hndone : ¬ logHeight ≤ logFinalHeight := by omega
    simp only [hndone, ite_false]
    let a := logArityForRound logHeight pending.head? logFinalHeight maxLogArity
    have hpos : 0 < a :=
      logArityForRound_pos (by omega) hcap (fun next hnext =>
        hbelow next (List.mem_of_mem_head? hnext))
    have htarget : a ≤ logHeight - logFinalHeight :=
      logArityForRound_le_toTarget logHeight pending.head? logFinalHeight maxLogArity
    cases pending with
    | nil => cases hh
    | cons next rest =>
      have hnext_le : a ≤ logHeight - next :=
        logArityForRound_le_toNext logHeight next logFinalHeight maxLogArity
      have hnext_lt : next < logHeight := hbelow next List.mem_cons_self
      rw [List.pairwise_cons] at hsorted
      simp only [List.head?_cons, List.tail_cons, Option.some.injEq] at a hpos htarget hnext_le ⊢
      change ∃ r ≤ (a :: foldScheduleFrom logFinalHeight maxLogArity fuel (logHeight - a)
          (if next = logHeight - a then rest else next :: rest)).length,
        h + cumLogArity (a :: foldScheduleFrom logFinalHeight maxLogArity fuel (logHeight - a)
          (if next = logHeight - a then rest else next :: rest)) r = logHeight
      by_cases hhit : next = logHeight - a
      · simp only [hhit, ↓reduceIte]
        rcases List.mem_cons.mp hh with rfl | hrest
        · refine ⟨1, by simp, ?_⟩
          rw [cumLogArity_cons_succ, cumLogArity_zero]
          omega
        · have hbelow' : ∀ x ∈ rest, x < logHeight - a := fun x hx => by
            have := hsorted.1 x hx; omega
          obtain ⟨r, hr, hsum⟩ := ih (logHeight - a) rest (by omega) hsorted.2 hbelow' h hrest hfin
          refine ⟨r + 1, by simp; omega, ?_⟩
          rw [cumLogArity_cons_succ]
          omega
      · simp only [hhit, ↓reduceIte]
        have hbelow' : ∀ x ∈ next :: rest, x < logHeight - a := fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · have := hsorted.1 x hx; omega
        obtain ⟨r, hr, hsum⟩ := ih (logHeight - a) (next :: rest) (by omega)
          (List.pairwise_cons.mpr hsorted) hbelow' h hh hfin
        refine ⟨r + 1, by simp; omega, ?_⟩
        rw [cumLogArity_cons_succ]
        omega

/-- Every matrix height in `shape` lands on a round boundary of `scheduleOfShape`. -/
theorem scheduleOfShape_hits {params : FriParams} {shape : ClaimShape}
    (hcap : 0 < params.maxLogArity)
    (hfin : ∀ m ∈ shape.flatten, params.logFinalHeight ≤ m.logDegree + params.logBlowup) :
    ∀ m ∈ shape.flatten,
      ∃ r ≤ (scheduleOfShape params shape).length,
        m.logDegree + params.logBlowup + cumLogArity (scheduleOfShape params shape) r =
          logMaxHeight params.logBlowup shape := by
  intro m hm
  have hne : shape.flatten ≠ [] := fun hnil => by rw [hnil] at hm; cases hm
  cases hdh : distinctLogHeights params.logBlowup shape with
  | nil => exact absurd hdh (distinctLogHeights_ne_nil hne)
  | cons tallest rest =>
    have htall : tallest = logMaxHeight params.logBlowup shape := distinctLogHeights_head_eq hdh
    have hp := distinctLogHeights_pairwise params.logBlowup shape
    rw [hdh, List.pairwise_cons] at hp
    have hmem : m.logDegree + params.logBlowup ∈ tallest :: rest := by
      rw [← hdh]
      exact mem_distinctLogHeights.mpr ⟨m, hm, rfl⟩
    unfold scheduleOfShape
    rw [hdh, foldSchedule]
    rcases List.mem_cons.mp hmem with heq | hrest
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [cumLogArity_zero, Nat.add_zero, heq, htall]
    · obtain ⟨r, hr, hsum⟩ := foldScheduleFrom_hits hcap (tallest - params.logFinalHeight)
        tallest rest (Nat.le_refl _) hp.2 hp.1 _ hrest (hfin m hm)
      exact ⟨r, hr, htall ▸ hsum⟩

/-- `scheduleOfShape` always passes `scheduleValid` for well-formed parameters and shape. -/
theorem scheduleValid_scheduleOfShape {params : FriParams} {shape : ClaimShape}
    (hcap : 0 < params.maxLogArity) (hne : shape.flatten ≠ [])
    (hfin : ∀ m ∈ shape.flatten, params.logFinalHeight ≤ m.logDegree + params.logBlowup) :
    scheduleValid params shape (scheduleOfShape params shape) = true := by
  cases hdh : distinctLogHeights params.logBlowup shape with
  | nil => exact absurd hdh (distinctLogHeights_ne_nil hne)
  | cons tallest rest =>
    have htall : tallest = logMaxHeight params.logBlowup shape := distinctLogHeights_head_eq hdh
    have hp := distinctLogHeights_pairwise params.logBlowup shape
    rw [hdh] at hp
    have hsum : (scheduleOfShape params shape).sum = tallest - params.logFinalHeight := by
      unfold scheduleOfShape; rw [hdh]; exact foldSchedule_sum hp hcap
    have hbounds : ∀ a ∈ scheduleOfShape params shape, 1 ≤ a ∧ a ≤ params.maxLogArity := by
      unfold scheduleOfShape; rw [hdh]; exact foldSchedule_bounds hp hcap
    have hmem0 : tallest ∈ distinctLogHeights params.logBlowup shape := by
      rw [hdh]; exact List.mem_cons_self
    obtain ⟨m₀, hm₀, hm₀_deg⟩ := mem_distinctLogHeights.mp hmem0
    have hfin_tall : params.logFinalHeight ≤ tallest := hm₀_deg ▸ hfin m₀ hm₀
    unfold scheduleValid
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.any_eq_true, List.mem_range]
    refine ⟨⟨hbounds, by omega⟩, fun m hm => ?_⟩
    obtain ⟨r, hr, hhit⟩ := scheduleOfShape_hits hcap hfin m hm
    exact ⟨r, by omega, hhit⟩

/-- With `maxLogArity = 1`, `scheduleOfShape` reduces to binary folding. -/
theorem scheduleOfShape_binary {params : FriParams} {shape : ClaimShape}
    (hmax1 : params.maxLogArity = 1) (hne : shape.flatten ≠ []) :
    scheduleOfShape params shape = List.replicate (numRounds params shape) 1 := by
  cases hdh : distinctLogHeights params.logBlowup shape with
  | nil => exact absurd hdh (distinctLogHeights_ne_nil hne)
  | cons tallest rest =>
    have htall : tallest = logMaxHeight params.logBlowup shape := distinctLogHeights_head_eq hdh
    have hp := distinctLogHeights_pairwise params.logBlowup shape
    rw [hdh] at hp
    unfold scheduleOfShape numRounds
    rw [hdh, hmax1, ← htall]
    exact foldSchedule_binary hp

/-! ## Schedule unit tests (including compact 400KB `maxLogArity = 3` schedules) -/

example :
    scheduleOfShape FriParams.compact400KBBalanced [[⟨16, 10, 2⟩]] = [3, 3, 2] := by decide
example :
    scheduleOfShape FriParams.compact400KBBalanced [[⟨20, 10, 2⟩]] = [3, 3, 3, 3] := by decide
example :
    scheduleOfShape FriParams.ultraCompact400KBZk [[⟨16, 10, 2⟩, ⟨12, 8, 2⟩]] = [3, 1, 3, 1] := by
  decide

/-! ## Multi-arity folding arithmetic -/

section MultiArityArith

variable {F EF : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]

/-- Reconstruct a row of `arity = 2 ^ a` coset evaluations from the folded value
at `indexInGroup` and the `arity - 1` sibling values in ascending slot order
(matching `multi-stark/src/p3_adapter/fri_batching.rs`). -/
def placeRowMulti (arity : Nat) (folded : EF) (siblings : Array EF)
    (indexInGroup : Nat) : Array EF :=
  Array.ofFn (n := arity) fun j =>
    if j.val = indexInGroup then folded
    else if j.val < indexInGroup then siblings.getD j.val 0
    else siblings.getD (j.val - 1) 0

/-- Multi-arity `fold_row` for `arity = 2 ^ logArity` by iterating `logArity`
binary `foldRow` passes with challenges `β, β ^ 2, …, β ^ (2 ^ (logArity - 1))`.

For `evals` holding the `2 ^ logArity` evaluations at the bit-reversed coset
indices `groupIdx * 2 ^ logArity + r` (`r < 2 ^ logArity`) of level `curLevel`
(log-height `n - curLevel`), this agrees identically with Lagrange interpolation
on the coset evaluated at `beta` (Plonky3's `TwoAdicFriFolding::fold_row` and
`multi-stark`'s GPU folding kernel). -/
def foldRowMulti (n : Nat) : (logArity curLevel groupIdx : Nat) → EF → Array EF → EF
  | 0, _, _, _, evals => evals.getD 0 0
  | a + 1, curLevel, groupIdx, beta, evals =>
    let next := Array.ofFn (n := 2 ^ a) fun r =>
      foldRow beta (domainPoint (F := F) n curLevel (2 * (groupIdx * 2 ^ a + r.val)))
        (evals.getD (2 * r.val) 0) (evals.getD (2 * r.val + 1) 0)
    foldRowMulti n a (curLevel + 1) groupIdx (beta * beta) next

/-- Multi-arity fold chain of one query (`fold_query`), given per-round log-arity
schedule `arities`, reduced openings `ros` (indexed by round `0 .. arities.length`),
sibling arrays `sibs i`, folding challenges `betas`, and query index `index`.

In round `i` with log-arity `a = arities.getD i 1` and cumulative folded bits
`cum = cumLogArity arities i`:
* the group index at the folded height is `groupIdx = index >>> (cum + a)`;
* the position within the `2 ^ a`-row is `idxInGroup = (index >>> cum) % 2 ^ a`;
* the reconstructed `2 ^ a`-row is folded via `foldRowMulti` with `betas[i]`;
* the next reduced opening `ros[i + 1]` is added with factor `fieldPowTwo (betas[i]) a`
  (`β ^ (2 ^ a)`). -/
def foldChainMulti (n : Nat) (arities : List Nat) (ros : Array EF)
    (sibs : Nat → Array EF) (betas : Array EF) (index : Nat) :
    Nat → EF × List (Array EF)
  | 0 => (ros.getD 0 0, [])
  | i + 1 =>
    let prev := foldChainMulti n arities ros sibs betas index i
    let a := arities.getD i 1
    let cum := cumLogArity arities i
    let groupIdx := index >>> (cum + a)
    let idxInGroup := (index >>> cum) % 2 ^ a
    let row := placeRowMulti (2 ^ a) prev.1 (sibs i) idxInGroup
    let beta := betas.getD i 0
    (foldRowMulti (F := F) n a cum groupIdx beta row +
        fieldPowTwo beta a * ros.getD (i + 1) 0,
      prev.2 ++ [row])

end MultiArityArith

/-! ## Multi-arity transcript and verifier checks -/

section MultiArityTranscript

variable {σ F EF D : Type} [FieldOps F] [FieldOps EF]

/-- What the multi-arity verifier absorbs after the last folding challenge:
the final polynomial coefficients, followed by `Val::from_usize(log_arity)` for
each round in `arities` (`multi-stark/src/p3_adapter/fri_batching.rs`). -/
def finalMessageMulti (arities : List Nat) (finalPoly : Array EF) :
    List (Observation F EF D) :=
  finalPoly.toList.map .ext ++ arities.map fun a => .base (fieldOfNat a)

/-- Multi-arity tensor-batched counterpart of `transcriptTailTensor`. -/
def transcriptTailTensorMulti [Inhabited D] (chal : Challenger σ F EF D) (s : σ)
    (params : FriParams) (shape : ClaimShape) (arities : List Nat)
    {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) : TensorChallenges EF :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := arities.length
  let sched := TensorSchedule.sample chal s (maxWidth shape)
    (maxOpeningsPerHeight params.logBlowup shape)
  let commit := commitPhase chal params.commitPowBits proof.commitPhaseCommits
    proof.commitPowWitnesses rounds sched.2
  let s := chal.observeAll commit.2.2 (finalMessageMulti arities proof.finalPoly)
  let pow := chal.checkWitness s params.queryPowBits proof.queryPowWitness
  { schedule := sched.1
    betas := commit.1
    powOk := commit.2.1 && pow.1
    indices := (chal.sampleIndices n params.numQueries pow.2).toArray }

/-- Multi-arity tensor-batched counterpart of `transcriptTensor`. -/
def transcriptTensorMulti [Inhabited D] (chal : Challenger σ F EF D) (init : σ)
    (params : FriParams) (shape : ClaimShape) (arities : List Nat)
    (commitments : Array D) (points values : Array EF)
    {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) : TensorChallenges EF :=
  transcriptTailTensorMulti chal (chal.observeAll init (firstMessage commitments points values))
    params shape arities proof

/-- Multi-arity tensor-batched counterpart of `transcriptFromTensor`. -/
def transcriptFromTensorMulti [Inhabited D] (chal : Challenger σ F EF D) (s : σ)
    (params : FriParams) (shape : ClaimShape) (arities : List Nat)
    (values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) : TensorChallenges EF :=
  transcriptTailTensorMulti chal (chal.observeAll s (values.toList.map .ext))
    params shape arities proof

end MultiArityTranscript

section MultiArityChecks

variable {F EF D : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  {InputProof CommitProof : Type}

/-- The sibling values of query `t` in folding round `i`; empty if absent. -/
def siblingsMulti (proof : FriProof F EF D InputProof CommitProof) (i t : Nat) : Array EF :=
  match proof.commitPhaseOpenings[i]? with
  | some o => o.siblingValues.getD t #[]
  | none => #[]

/-- Tensor-batched reduced openings indexed by folding round `r ≤ arities.length`:
round `r` corresponds to domain level `j = cumLogArity arities r`. -/
def reducedOpeningsTensorMulti (n : Nat) (arities : List Nat)
    (levels : Nat → List OpeningRef) (sched : TensorSchedule EF)
    (points values : Array EF) (rows : Array (Array (Array F))) (index : Nat) :
    Array EF :=
  Array.ofFn (n := arities.length + 1) fun r =>
    let j := cumLogArity arities r.val
    let x := cosetPoint (F := F) n j (index >>> j)
    let ops := (levels r.val).zipIdx.map fun (o, oIdx) =>
      (oIdx, points.getD o.pointIdx 0, claimedRow values o, openedRow rows o.batch o.matrix)
    reducedOpeningTensor sched x ops

/-- Result of checking one multi-arity query. -/
structure QueryResultMulti (EF : Type) where
  /-- Whether the query's own checks pass. -/
  ok : Bool
  /-- The `2 ^ a`-entry rows reconstructed for each folding round. -/
  rows : List (Array EF)

/-- Multi-arity counterpart of `checkQueryTensor`. -/
def checkQueryTensorMulti (params : FriParams) (shape : ClaimShape) (arities : List Nat)
    (levels : Nat → List OpeningRef) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) (ch : TensorChallenges EF)
    (t index : Nat) : QueryResultMulti EF :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := arities.length
  let rows := queryRows proof t
  let ros := reducedOpeningsTensorMulti (F := F) n arities levels ch.schedule points values
    rows index
  let chain := foldChainMulti (F := F) n arities ros (fun i => siblingsMulti proof i t)
    ch.betas index rounds
  let widthsOk := (openingRefs params.logBlowup shape).all fun o =>
    (openedRow rows o.batch o.matrix).size == o.width
  let distinct := (pointRefs params.logBlowup shape).zipIdx.all fun (p, pointIdx) =>
    !(points.getD pointIdx 0 -
      cosetPoint (F := F) n (n - p.logHeight) (index >>> (n - p.logHeight)) == 0)
  let constOk := params.logFinalPolyLen != 0 || ros.getD rounds 0 == 0
  let finalOk := chain.1 ==
    horner proof.finalPoly
      (ExtensionOps.embed (domainPoint (F := F) n arities.sum (index >>> arities.sum)))
  { ok := widthsOk && distinct && constOk && finalOk, rows := chain.2 }

/-- Multi-arity commitment checks of the folding rounds: round `i` commits a
matrix of width `2 ^ a` and log-height `n - cumLogArity arities (i + 1)`. -/
def commitChecksMulti (friMmcs : Mmcs EF D) (numQueries n : Nat) (arities : List Nat)
    (commits : Array D) (openings : Array (CommitPhaseStep EF friMmcs.MultiProof))
    (indices : Array Nat) (rows : Array (List (Array EF))) : Bool :=
  (List.range arities.length).all fun i =>
    match commits[i]?, openings[i]? with
    | some root, some opening =>
      let a := arities.getD i 1
      let cumNext := cumLogArity arities (i + 1)
      friMmcs.verifyMultiBatch root #[⟨2 ^ a, n - cumNext⟩]
        (Array.ofFn (n := numQueries) fun t => indices.getD t.val 0 >>> cumNext)
        (Array.ofFn (n := numQueries) fun t => #[(rows.getD t.val []).getD i #[]])
        opening.openingProof
    | _, _ => false

/-- Multi-arity shape check for a fixed per-round schedule `arities`. -/
def shapeOkMultiArity (arities : List Nat) (params : FriParams) (shape : ClaimShape)
    (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) : Bool :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := arities.length
  params.numQueries != 0 && params.maxLogArity != 0
    && !shape.flatten.isEmpty
    && shape.flatten.all (fun m =>
      m.numPoints != 0 && decide (params.logFinalHeight ≤ m.logDegree + params.logBlowup))
    && decide (n ≤ TwoAdicOps.twoAdicity (F := F))
    && scheduleValid params shape arities
    && commitments.size == shape.length
    && points.size == (pointRefs params.logBlowup shape).length
    && values.size == (claimRefs params.logBlowup shape).length
    && proof.commitPhaseCommits.size == rounds
    && proof.commitPowWitnesses.size == rounds
    && proof.commitPhaseOpenings.size == rounds
    && (List.range rounds).all (fun i =>
      match proof.commitPhaseOpenings[i]? with
      | some o =>
        let a := arities.getD i 1
        o.logArity == a && o.siblingValues.size == params.numQueries
          && o.siblingValues.all (·.size == 2 ^ a - 1)
      | none => false)
    && proof.finalPoly.size == params.finalPolyLen
    && proof.inputOpenings.size == shape.length
    && (List.range shape.length).all (fun b =>
      match proof.inputOpenings[b]? with
      | some o => o.openedValues.size == params.numQueries
          && o.openedValues.all (·.size == (shape.getD b []).length)
      | none => false)

/-- Multi-arity counterpart of `verifyWithTensor`. -/
def verifyWithTensorMulti (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (params : FriParams)
    (shape : ClaimShape) (arities : List Nat) (commitments : Array D)
    (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof)
    (ch : TensorChallenges EF) : Bool :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := arities.length
  let levelArr := Array.ofFn (n := rounds + 1) fun r =>
    levelOpenings params.logBlowup shape n (cumLogArity arities r.val)
  let results := Array.ofFn (n := params.numQueries) fun t =>
    checkQueryTensorMulti (F := F) params shape arities (fun r => levelArr.getD r [])
      points values proof ch t.val (ch.indices.getD t.val 0)
  ch.powOk && ch.indices.size == params.numQueries
    && (List.range params.numQueries).all (fun t => decide (ch.indices.getD t 0 < 2 ^ n))
    && inputChecks inputMmcs params shape commitments proof.inputOpenings ch.indices
    && results.all (·.ok)
    && commitChecksMulti friMmcs params.numQueries n arities proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices (results.map (·.rows))

/-- **Multi-arity tensor-batched FRI verifier for an explicit schedule `arities`.** -/
def verifyTensorWithSchedule {σ : Type} [Inhabited D] (inputMmcs : Mmcs F D)
    (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D) (init : σ) (params : FriParams)
    (shape : ClaimShape) (arities : List Nat) (commitments : Array D)
    (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  shapeOkMultiArity (F := F) arities params shape commitments points values proof
    && verifyWithTensorMulti inputMmcs friMmcs params shape arities commitments points values proof
      (transcriptTensorMulti chal init params shape arities commitments points values proof)

/-- **Multi-arity tensor-batched FRI verifier inside a larger protocol, for an
explicit schedule `arities`.** -/
def verifyFromTensorWithSchedule {σ : Type} [Inhabited D] (inputMmcs : Mmcs F D)
    (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D) (s : σ) (params : FriParams)
    (shape : ClaimShape) (arities : List Nat) (commitments : Array D)
    (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  shapeOkMultiArity (F := F) arities params shape commitments points values proof
    && verifyWithTensorMulti inputMmcs friMmcs params shape arities commitments points values proof
      (transcriptFromTensorMulti chal s params shape arities values proof)

/-- **Multi-arity tensor-batched FRI verifier** using the canonical Plonky3 /
`multi-stark` schedule `scheduleOfShape params shape` (covering `maxLogArity ∈ {1, 2, 3, …}`). -/
def verifyTensorMultiArity {σ : Type} [Inhabited D] (inputMmcs : Mmcs F D)
    (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D) (init : σ) (params : FriParams)
    (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  verifyTensorWithSchedule inputMmcs friMmcs chal init params shape
    (scheduleOfShape params shape) commitments points values proof

/-- **Multi-arity tensor-batched FRI verifier inside a larger protocol** using
the canonical schedule `scheduleOfShape params shape`. -/
def verifyFromTensorMultiArity {σ : Type} [Inhabited D] (inputMmcs : Mmcs F D)
    (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D) (s : σ) (params : FriParams)
    (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  verifyFromTensorWithSchedule inputMmcs friMmcs chal s params shape
    (scheduleOfShape params shape) commitments points values proof

end MultiArityChecks

end Fri

end CertiFri
