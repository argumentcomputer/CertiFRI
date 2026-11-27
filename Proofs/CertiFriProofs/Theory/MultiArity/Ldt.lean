import CertiFri.MultiArity
import CertiFriProofs.Theory.MultiArity.Fold
import CertiFriProofs.Theory.SoundnessCount

/-!
# Multi-arity low-degree test: query soundness and round-by-round doom

Generalizes `Theory/Soundness.lean` and `Theory/SoundnessCount.lean` from
binary folding (`LdtInstance`) to variable per-round folding arities
`2 ^ (S.logArity i)` (`MultiLdtInstance`), covering arbitrary schedules
`arities : List ℕ` with `∀ a ∈ arities, 0 < a` (in particular `a ∈ {1, 2, 3}`,
fold factors `2, 4, 8`).
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Multi-arity low-degree test instance -/

/-- A variable-arity low-degree test instance: round `i < rounds` folds by
factor `2 ^ logArity i` using primitive `2 ^ logArity i`-th root of unity
`zeta i`, mapping `domain i` onto `domain (i + 1)` and dividing the degree
bound by `2 ^ logArity i`. -/
structure MultiLdtInstance (F : Type*) [Field F] where
  rounds : ℕ
  logArity : ℕ → ℕ
  arity_pos : ∀ i < rounds, 0 < logArity i
  domain : ℕ → Finset F
  degree : ℕ → ℕ
  zeta : ℕ → F
  step : ∀ i < rounds, PowStep (2 ^ logArity i) (zeta i) (domain i) (domain (i + 1))
  degree_step : ∀ i < rounds, degree i = 2 ^ logArity i * degree (i + 1)

namespace MultiLdtInstance

/-- Cumulative log-arity folded before round `i`. -/
def cumLog (S : MultiLdtInstance F) : ℕ → ℕ
  | 0 => 0
  | i + 1 => S.cumLog i + S.logArity i

@[simp] theorem cumLog_zero (S : MultiLdtInstance F) : S.cumLog 0 = 0 := rfl

@[simp] theorem cumLog_succ (S : MultiLdtInstance F) (i : ℕ) :
    S.cumLog (i + 1) = S.cumLog i + S.logArity i := rfl

end MultiLdtInstance

/-- Two-adic multi-arity low-degree test instance for an arbitrary positive
per-round log-arity schedule `arities : List ℕ` with `arities.sum ≤ n`. -/
def twoAdicMultiInstance [DecidableEq F] (ω : F) (n : ℕ) (arities : List ℕ)
    (finalDegree : ℕ) (hω : IsPrimitiveRoot ω (2 ^ n))
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ n) :
    MultiLdtInstance F where
  rounds := arities.length
  logArity i := arities.getD i 0
  arity_pos i hi := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hpos _ (List.getElem_mem hi)
  domain i := twoAdicDomain ω n (Fri.cumLogArity arities i)
  degree i := 2 ^ (arities.sum - Fri.cumLogArity arities i) * finalDegree
  zeta i := ω ^ 2 ^ (n - arities.getD i 0)
  step i hi := by
    have hget : arities.getD i 0 = arities[i] := List.getD_eq_getElem _ _ hi
    have ha : 0 < arities.getD i 0 := hget ▸ hpos _ (List.getElem_mem hi)
    have hsucc : Fri.cumLogArity arities (i + 1) =
        Fri.cumLogArity arities i + arities.getD i 0 := by
      rw [hget]
      exact Fri.cumLogArity_succ arities hi
    have hle : Fri.cumLogArity arities i + arities.getD i 0 ≤ n := by
      rw [← hsucc]
      exact (Fri.cumLogArity_le_sum arities (i + 1)).trans hsum
    rw [hsucc]
    exact powStep_twoAdicDomain hω ha hle
  degree_step i hi := by
    have hget : arities.getD i 0 = arities[i] := List.getD_eq_getElem _ _ hi
    have hsucc : Fri.cumLogArity arities (i + 1) =
        Fri.cumLogArity arities i + arities.getD i 0 := by
      rw [hget]
      exact Fri.cumLogArity_succ arities hi
    have hle : Fri.cumLogArity arities (i + 1) ≤ arities.sum :=
      Fri.cumLogArity_le_sum arities (i + 1)
    have hexp : arities.sum - Fri.cumLogArity arities i =
        arities.getD i 0 + (arities.sum - Fri.cumLogArity arities (i + 1)) := by
      omega
    rw [hexp, pow_add, mul_assoc]

theorem cumLog_twoAdicMultiInstance [DecidableEq F] (ω : F) (n : ℕ) (arities : List ℕ)
    (finalDegree : ℕ) (hω : IsPrimitiveRoot ω (2 ^ n))
    (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ n) :
    ∀ i ≤ arities.length,
      (twoAdicMultiInstance ω n arities finalDegree hω hpos hsum).cumLog i =
        Fri.cumLogArity arities i
  | 0, _ => rfl
  | i + 1, hi => by
    rw [MultiLdtInstance.cumLog_succ,
      cumLog_twoAdicMultiInstance ω n arities finalDegree hω hpos hsum i (Nat.le_of_succ_le hi),
      Fri.cumLogArity_succ arities hi]
    show Fri.cumLogArity arities i + arities.getD i 0 = Fri.cumLogArity arities i + arities[i]
    rw [List.getD_eq_getElem _ _ hi]

/-! ## Multi-arity query acceptance and soundness -/

/-- What the multi-arity verifier checks on query `x ∈ S.domain 0`. -/
def QueryAcceptsMulti (S : MultiLdtInstance F) (ro c : ℕ → F → F) (β : ℕ → F) (x : F) : Prop :=
  c 0 x = ro 0 x ∧
    ∀ i < S.rounds,
      c (i + 1) (x ^ 2 ^ S.cumLog (i + 1)) =
        foldAtPow (S.zeta i) (2 ^ S.logArity i) (c i) (β i) (x ^ 2 ^ S.cumLog i) +
          β i ^ (2 ^ S.logArity i) * ro (i + 1) (x ^ 2 ^ S.cumLog (i + 1))

namespace MultiLdtInstance

/-- A point of the first domain, raised to `2 ^ cumLog i`, lies in `domain i`. -/
theorem pow_mem (S : MultiLdtInstance F) {x : F} (hx : x ∈ S.domain 0) {i : ℕ}
    (hi : i ≤ S.rounds) : x ^ 2 ^ S.cumLog i ∈ S.domain i := by
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [cumLog_succ, pow_add, pow_mul]
    exact (S.step i hi).pow_mem _ (ih (Nat.le_of_succ_le hi))

/-- Above a subset `B ⊆ domain i`, there are `2 ^ cumLog i * B.card` points of `domain 0`. -/
theorem card_filter_pow [DecidableEq F] (S : MultiLdtInstance F) {i : ℕ} (hi : i ≤ S.rounds)
    {B : Finset F} (hB : B ⊆ S.domain i) :
    ((S.domain 0).filter fun x => x ^ 2 ^ S.cumLog i ∈ B).card =
      2 ^ S.cumLog i * B.card := by
  induction i generalizing B with
  | zero =>
    simp only [cumLog_zero, pow_zero, pow_one, one_mul, Finset.filter_mem_eq_inter]
    rw [Finset.inter_eq_right.mpr hB]
  | succ i ih =>
    have hfilter : ((S.domain 0).filter fun x => x ^ 2 ^ S.cumLog (i + 1) ∈ B) =
        (S.domain 0).filter fun x =>
          x ^ 2 ^ S.cumLog i ∈ (S.domain i).filter fun y => y ^ 2 ^ S.logArity i ∈ B := by
      refine Finset.filter_congr fun x hx => ?_
      rw [Finset.mem_filter, cumLog_succ, pow_add, pow_mul]
      exact (and_iff_right (S.pow_mem hx (Nat.le_of_succ_le hi))).symm
    rw [hfilter, ih (Nat.le_of_succ_le hi) (Finset.filter_subset _ _),
      (S.step i hi).card_filter_pow hB, cumLog_succ, pow_add, mul_assoc]

/-- The first domain is `2 ^ cumLog i` times as large as `domain i`. -/
theorem card_domain (S : MultiLdtInstance F) {i : ℕ} (hi : i ≤ S.rounds) :
    (S.domain 0).card = 2 ^ S.cumLog i * (S.domain i).card := by
  classical
  rw [← S.card_filter_pow hi (Finset.Subset.refl _),
    Finset.filter_true_of_mem fun x hx => S.pow_mem hx hi]

/-- Density is preserved under `x ↦ x ^ 2 ^ cumLog i`. -/
theorem dense_image [DecidableEq F] (S : MultiLdtInstance F) {θ : ℝ} {A : Finset F}
    (hA : A ⊆ S.domain 0) (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ}
    (hi : i ≤ S.rounds) :
    θ * (S.domain i).card ≤ (A.image fun x => x ^ 2 ^ S.cumLog i).card := by
  have hsub : A ⊆ (S.domain 0).filter fun x =>
      x ^ 2 ^ S.cumLog i ∈ A.image fun x => x ^ 2 ^ S.cumLog i :=
    fun x hx => Finset.mem_filter.mpr ⟨hA hx, Finset.mem_image_of_mem _ hx⟩
  have himage : (A.image fun x => x ^ 2 ^ S.cumLog i) ⊆ S.domain i := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact S.pow_mem (hA ha) hi
  have hcard : (A.card : ℝ) ≤ 2 ^ S.cumLog i * (A.image fun x => x ^ 2 ^ S.cumLog i).card := by
    have := Finset.card_le_card hsub
    rw [S.card_filter_pow hi himage] at this
    exact_mod_cast this
  have hdom : ((S.domain 0).card : ℝ) = 2 ^ S.cumLog i * (S.domain i).card := by
    exact_mod_cast S.card_domain hi
  rw [hdom] at hdense
  have hpos : (0 : ℝ) < 2 ^ S.cumLog i := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (2 : ℝ) ^ S.cumLog i * (θ * (S.domain i).card)
      = θ * (2 ^ S.cumLog i * (S.domain i).card) := by ring
    _ ≤ A.card := hdense
    _ ≤ 2 ^ S.cumLog i * (A.image fun x => x ^ 2 ^ S.cumLog i).card := hcard

theorem closeToCode_of_image [DecidableEq F] (S : MultiLdtInstance F) {θ : ℝ} {A : Finset F}
    (hA : A ⊆ S.domain 0) (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ}
    (hi : i ≤ S.rounds) {f : F → F}
    (h : ∃ p : F[X], p.degree < S.degree i ∧
      ∀ a ∈ A, f (a ^ 2 ^ S.cumLog i) = p.eval (a ^ 2 ^ S.cumLog i)) :
    CloseToCode (S.domain i) (S.degree i) θ f := by
  obtain ⟨p, hp, hf⟩ := h
  refine ⟨p, hp, A.image fun a => a ^ 2 ^ S.cumLog i, fun y hy => ?_,
    S.dense_image hA hdense hi, fun y hy => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact S.pow_mem (hA ha) hi
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hf a ha

/-- One backward-induction step for an arbitrary `2 ^ logArity i`-ary fold round. -/
theorem fold_step [DecidableEq F] (S : MultiLdtInstance F) {θ : ℝ} (ro c : ℕ → F → F)
    (β : ℕ → F) {A : Finset F} (hA : A ⊆ S.domain 0)
    (haccept : ∀ x ∈ A, QueryAcceptsMulti S ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ} (hi : i < S.rounds)
    (hgood : GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
      (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i))
    {w : F[X]} (hw : w.degree < S.degree (i + 1))
    (hcw : ∀ a ∈ A, c (i + 1) (a ^ 2 ^ S.cumLog (i + 1)) = w.eval (a ^ 2 ^ S.cumLog (i + 1))) :
    (∃ p : F[X], p.degree < S.degree i ∧
        ∀ a ∈ A, c i (a ^ 2 ^ S.cumLog i) = p.eval (a ^ 2 ^ S.cumLog i)) ∧
      ∃ p : F[X], p.degree < S.degree (i + 1) ∧
        ∀ a ∈ A, ro (i + 1) (a ^ 2 ^ S.cumLog (i + 1)) = p.eval (a ^ 2 ^ S.cumLog (i + 1)) := by
  have hBsub : (A.image fun a => a ^ 2 ^ S.cumLog (i + 1)) ⊆ S.domain (i + 1) := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact S.pow_mem (hA ha) (Nat.succ_le_of_lt hi)
  have hpow : ∀ a : F, a ^ 2 ^ S.cumLog (i + 1) = (a ^ 2 ^ S.cumLog i) ^ 2 ^ S.logArity i :=
    fun a => by rw [cumLog_succ, pow_add, pow_mul]
  have hst := S.step i hi
  obtain ⟨⟨p₀, hp₀, h₀⟩, p₁, hp₁, h₁⟩ := hgood w hw _ hBsub
    (S.dense_image hA hdense (Nat.succ_le_of_lt hi)) fun x hxD hxB => by
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxB
      have hfold : foldAtPow (S.zeta i) (2 ^ S.logArity i) (c i) (β i) x =
          foldAtPow (S.zeta i) (2 ^ S.logArity i) (c i) (β i) (a ^ 2 ^ S.cumLog i) :=
        foldAtPow_eq_of_pow_eq hst.prim hst.m_pos (c i) (β i) (hst.ne_zero x hxD)
          (hax.symm.trans (hpow a))
      rw [hfold, ← hax, ← (haccept a ha).2 i hi, hcw a ha]
  refine ⟨⟨p₀, ?_, fun a ha => h₀ _ (S.pow_mem (hA ha) hi.le) ?_⟩,
    p₁, hp₁, fun a ha => h₁ _ (Finset.mem_image_of_mem _ ha)⟩
  · rwa [S.degree_step i hi]
  · rw [← hpow]
    exact Finset.mem_image_of_mem _ ha

theorem agree_on_image [DecidableEq F] (S : MultiLdtInstance F) {θ : ℝ} (ro c : ℕ → F → F)
    (β : ℕ → F)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds,
      GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i))
    (A : Finset F) (hA : A ⊆ S.domain 0) (haccept : ∀ x ∈ A, QueryAcceptsMulti S ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) :
    ∀ i ≤ S.rounds, ∃ p : F[X], p.degree < S.degree i ∧
      ∀ a ∈ A, ro i (a ^ 2 ^ S.cumLog i) = p.eval (a ^ 2 ^ S.cumLog i) := by
  have hc : ∀ i, i ≤ S.rounds →
      ∃ w : F[X], w.degree < S.degree i ∧
        ∀ a ∈ A, c i (a ^ 2 ^ S.cumLog i) = w.eval (a ^ 2 ^ S.cumLog i) := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
      obtain ⟨w, hw, hcw⟩ := hfinal
      exact ⟨w, hw, fun a ha => hcw _ (S.pow_mem (hA ha) le_rfl)⟩
    | of_succ k hk ih =>
      obtain ⟨w, hw, hcw⟩ := ih
      exact (S.fold_step ro c β hA haccept hdense hk (hgood k hk) hw hcw).1
  intro i hi
  cases i with
  | zero =>
    obtain ⟨w, hw, hcw⟩ := hc 0 hi
    refine ⟨w, hw, fun a ha => ?_⟩
    rw [← hcw a ha, cumLog_zero, pow_zero, pow_one, (haccept a ha).1]
  | succ i =>
    obtain ⟨w, hw, hcw⟩ := hc (i + 1) hi
    exact (S.fold_step ro c β hA haccept hdense hi (hgood i hi) hw hcw).2

/-- **Multi-arity query-phase soundness.** -/
theorem query_soundness (S : MultiLdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds,
      GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i))
    (A : Finset F) (hA : A ⊆ S.domain 0) (haccept : ∀ x ∈ A, QueryAcceptsMulti S ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) :
    ∀ i ≤ S.rounds, CloseToCode (S.domain i) (S.degree i) θ (ro i) := by
  classical
  exact fun i hi => S.closeToCode_of_image hA hdense hi
    (S.agree_on_image ro c β hfinal hgood A hA haccept hdense i hi)

theorem card_accepting_lt (S : MultiLdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    [DecidablePred fun x => QueryAcceptsMulti S ro c β x]
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds,
      GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) :
    (((S.domain 0).filter fun x => QueryAcceptsMulti S ro c β x).card : ℝ) <
      θ * (S.domain 0).card := by
  by_contra hlt
  obtain ⟨i, hi, hfar⟩ := hfar
  exact hfar (S.query_soundness ro c β hfinal hgood _ (Finset.filter_subset _ _)
    (fun x hx => (Finset.mem_filter.mp hx).2) (not_lt.mp hlt) i hi)

theorem card_accepting_queries_le (S : MultiLdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    [DecidablePred fun x => QueryAcceptsMulti S ro c β x]
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds,
      GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i))
    (hfar : ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) (q : ℕ) :
    ((Finset.univ.filter fun xs : Fin q → ↥(S.domain 0) =>
        ∀ t, QueryAcceptsMulti S ro c β (xs t)).card : ℝ) ≤ (θ * (S.domain 0).card) ^ q := by
  rw [Soundness.card_filter_forall, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (S.card_accepting_lt ro c β hfinal hgood hfar).le q

/-! ## Round-by-round doom state -/

/-- The doomed state of a multi-arity LDT after `k` folding rounds. -/
def Doomed (S : MultiLdtInstance F) (θ : ℝ) (ro c : ℕ → F → F) (β : ℕ → F) (k : ℕ) : Prop :=
  (∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i)) ∧
    ∀ i < k,
      GoodChallengeArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (ro (i + 1)) (c i) (β i)

theorem doomed_zero_iff (S : MultiLdtInstance F) (θ : ℝ) (ro c : ℕ → F → F) (β : ℕ → F) :
    S.Doomed θ ro c β 0 ↔
      ∃ i ≤ S.rounds, ¬ CloseToCode (S.domain i) (S.degree i) θ (ro i) :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩⟩

theorem doomed_succ_iff (S : MultiLdtInstance F) (θ : ℝ) (ro c : ℕ → F → F) (β : ℕ → F)
    (k : ℕ) :
    S.Doomed θ ro c β (k + 1) ↔ S.Doomed θ ro c β k ∧
      GoodChallengeArity (2 ^ S.logArity k) (S.zeta k) (S.domain k) (S.domain (k + 1))
        (S.degree (k + 1)) θ (ro (k + 1)) (c k) (β k) := by
  refine ⟨fun h => ⟨⟨h.1, fun i hi => h.2 i (Nat.lt_succ_of_lt hi)⟩, h.2 k (Nat.lt_succ_self k)⟩,
    fun h => ⟨h.1.1, fun i hi => ?_⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
  · exact h.1.2 i hlt
  · exact h.2

theorem Doomed.congr {S : MultiLdtInstance F} {θ : ℝ} {ro c c' : ℕ → F → F}
    {β β' : ℕ → F} {k : ℕ} (h : S.Doomed θ ro c β k) (hc : ∀ i < k, c' i = c i)
    (hβ : ∀ i < k, β' i = β i) : S.Doomed θ ro c' β' k :=
  ⟨h.1, fun i hi => by rw [hc i hi, hβ i hi]; exact h.2 i hi⟩

open Classical in
theorem StepMCAArityFor.card_bad_le [Fintype F] {m : ℕ} {ζ : F} {D D' : Finset F} {d' : ℕ}
    {θ ε : ℝ} {ro : F → F} (h : StepMCAArityFor m ζ D D' d' θ ε ro) (c : F → F) :
    ((Finset.univ.filter fun β : F => ¬ GoodChallengeArity m ζ D D' d' θ ro c β).card : ℝ) ≤
      ε * Fintype.card F := by
  obtain ⟨bad, hcard, hbad⟩ := h c
  refine le_trans ?_ hcard
  exact_mod_cast Finset.card_le_card fun β hβ => by
    by_contra hmem
    exact (Finset.mem_filter.mp hβ).2 (hbad β hmem)

open Classical in
theorem Doomed.card_escape_le [Fintype F] {S : MultiLdtInstance F} {θ : ℝ}
    {ro c : ℕ → F → F} {β : ℕ → F} {k : ℕ} (h : S.Doomed θ ro c β k) {ε : ℝ}
    (hmca : StepMCAArityFor (2 ^ S.logArity k) (S.zeta k) (S.domain k) (S.domain (k + 1))
      (S.degree (k + 1)) θ ε (ro (k + 1))) :
    ((Finset.univ.filter fun b : F =>
        ¬ S.Doomed θ ro c (Function.update β k b) (k + 1)).card : ℝ) ≤
      ε * Fintype.card F := by
  refine le_trans ?_ (StepMCAArityFor.card_bad_le hmca (c k))
  exact_mod_cast Finset.card_le_card fun b hb => by
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨hb.1, fun hgood => hb.2 ((S.doomed_succ_iff θ ro c _ k).mpr ⟨?_, ?_⟩)⟩
    · exact h.congr (fun _ _ => rfl) fun i hi => Function.update_of_ne hi.ne _ _
    · rwa [Function.update_self]

theorem Doomed.card_accepting_queries_le {S : MultiLdtInstance F} {θ : ℝ}
    {ro c : ℕ → F → F} {β : ℕ → F}
    [DecidablePred fun x => QueryAcceptsMulti S ro c β x]
    (h : S.Doomed θ ro c β S.rounds)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds)) (q : ℕ) :
    ((Finset.univ.filter fun xs : Fin q → ↥(S.domain 0) =>
        ∀ t, QueryAcceptsMulti S ro c β (xs t)).card : ℝ) ≤ (θ * (S.domain 0).card) ^ q :=
  S.card_accepting_queries_le ro c β hfinal h.2 h.1 q

end MultiLdtInstance

end CertiFri
