import CertiFriProofs.Theory.Basic

/-!
# Soundness of the low-degree test: the query phase

The model is the oracle model of `Theory/Basic.lean`: the committed codewords
`c i` are arbitrary functions, the inputs are `ro i`, and `β i` folds level `i`
into level `i + 1`.

The main theorem is `query_soundness`. If the final message is a codeword,
every folding challenge is good in the sense of `GoodChallenge`, and a set of
accepting query points holds at least a fraction `θ` of the first domain, then
every input `ro i` agrees with a codeword on at least a fraction `θ` of its own
domain. `Soundness.agree_on_image` is the same statement with the agreement set
named: it is the image of the accepting set in domain `i`.

The file starts with the cardinalities of the domains: squaring is two-to-one
at each step (`SquareStep.card_filter_sq`, `SquareStep.card_eq`), so the first
domain is `2 ^ i` times as large as domain `i` (`LdtInstance.card_domain`).

What is assumed: that the challenges are good. The file does not show that a
random challenge is good; that is the proximity hypothesis `StepMCAFor`, and the
counting over challenges is in `Theory/SoundnessCount.lean`. Nothing here is
about Merkle trees, Fiat–Shamir, or the distance of Reed–Solomon codes.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Cardinalities of a square step -/

/-- Above a subset `B` of the squares there are exactly twice as many points:
each `y` in `B` has the two square roots `x` and `-x` in `D`. -/
theorem SquareStep.card_filter_sq [DecidableEq F] {D D' : Finset F} (h : SquareStep D D')
    {B : Finset F} (hB : B ⊆ D') : (D.filter fun x => x ^ 2 ∈ B).card = 2 * B.card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x ^ 2)
    (s := D.filter fun x => x ^ 2 ∈ B) (t := B) fun x hx => (Finset.mem_filter.mp hx).2,
    mul_comm]
  refine Finset.sum_const_nat fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := h.exists_sq y (hB hy)
  have hne : x ≠ -x := fun hxx =>
    (mul_ne_zero h.two_ne_zero (h.ne_zero x hx)) (by linear_combination hxx)
  have hfibre : ((D.filter fun a => a ^ 2 ∈ B).filter fun a => a ^ 2 = x ^ 2) = {x, -x} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun ha => sq_eq_sq_iff_eq_or_eq_neg.mp ha.2, ?_⟩
    rintro (rfl | rfl)
    · exact ⟨⟨hx, hy⟩, rfl⟩
    · exact ⟨⟨h.neg_mem x hx, by rwa [neg_sq]⟩, neg_sq x⟩
  rw [hfibre, Finset.card_pair hne]

/-- A square step halves the domain. -/
theorem SquareStep.card_eq {D D' : Finset F} (h : SquareStep D D') : D.card = 2 * D'.card := by
  classical
  rw [← h.card_filter_sq (Finset.Subset.refl D'), Finset.filter_true_of_mem h.sq_mem]

namespace Soundness

/-- A point of the first domain, squared `i` times, is in domain `i`. -/
theorem pow_mem (S : LdtInstance F) {x : F} (hx : x ∈ S.domain 0) {i : ℕ}
    (hi : i ≤ S.rounds) : x ^ 2 ^ i ∈ S.domain i := by
  induction i with
  | zero => rwa [pow_zero, pow_one]
  | succ i ih =>
    rw [pow_succ, pow_mul]
    exact (S.step i hi).sq_mem _ (ih (Nat.le_of_succ_le hi))

/-- Above a subset `B` of domain `i` there are exactly `2 ^ i` times as many
points of the first domain. -/
theorem card_filter_pow [DecidableEq F] (S : LdtInstance F) {i : ℕ} (hi : i ≤ S.rounds)
    {B : Finset F} (hB : B ⊆ S.domain i) :
    ((S.domain 0).filter fun x => x ^ 2 ^ i ∈ B).card = 2 ^ i * B.card := by
  induction i generalizing B with
  | zero =>
    simp only [pow_zero, pow_one, one_mul, Finset.filter_mem_eq_inter]
    rw [Finset.inter_eq_right.mpr hB]
  | succ i ih =>
    have hfilter : ((S.domain 0).filter fun x => x ^ 2 ^ (i + 1) ∈ B) =
        (S.domain 0).filter fun x => x ^ 2 ^ i ∈ (S.domain i).filter fun y => y ^ 2 ∈ B := by
      refine Finset.filter_congr fun x hx => ?_
      rw [Finset.mem_filter, pow_succ, pow_mul]
      exact (and_iff_right (pow_mem S hx (Nat.le_of_succ_le hi))).symm
    rw [hfilter, ih (Nat.le_of_succ_le hi) (Finset.filter_subset _ _),
      (S.step i hi).card_filter_sq hB, pow_succ, mul_assoc]

end Soundness

/-- The first domain is `2 ^ i` times as large as domain `i`. -/
theorem LdtInstance.card_domain (S : LdtInstance F) {i : ℕ} (hi : i ≤ S.rounds) :
    (S.domain 0).card = 2 ^ i * (S.domain i).card := by
  classical
  rw [← Soundness.card_filter_pow S hi (Finset.Subset.refl _),
    Finset.filter_true_of_mem fun x hx => Soundness.pow_mem S hx hi]

/-! ## The query phase -/

namespace Soundness

/-- If a set `A` holds at least a fraction `θ` of the first domain, its image in
domain `i` holds at least a fraction `θ` of domain `i`. -/
theorem dense_image [DecidableEq F] (S : LdtInstance F) {θ : ℝ} {A : Finset F}
    (hA : A ⊆ S.domain 0) (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ}
    (hi : i ≤ S.rounds) :
    θ * (S.domain i).card ≤ (A.image fun x => x ^ 2 ^ i).card := by
  have hsub : A ⊆ (S.domain 0).filter fun x => x ^ 2 ^ i ∈ A.image fun x => x ^ 2 ^ i :=
    fun x hx => Finset.mem_filter.mpr ⟨hA hx, Finset.mem_image_of_mem _ hx⟩
  have himage : (A.image fun x => x ^ 2 ^ i) ⊆ S.domain i := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact pow_mem S (hA ha) hi
  have hcard : (A.card : ℝ) ≤ 2 ^ i * (A.image fun x => x ^ 2 ^ i).card := by
    have := Finset.card_le_card hsub
    rw [card_filter_pow S hi himage] at this
    exact_mod_cast this
  have hdom : ((S.domain 0).card : ℝ) = 2 ^ i * (S.domain i).card := by
    exact_mod_cast S.card_domain hi
  rw [hdom] at hdense
  have hpos : (0 : ℝ) < 2 ^ i := by positivity
  refine le_of_mul_le_mul_left ?_ hpos
  calc (2 : ℝ) ^ i * (θ * (S.domain i).card) = θ * (2 ^ i * (S.domain i).card) := by ring
    _ ≤ A.card := hdense
    _ ≤ 2 ^ i * (A.image fun x => x ^ 2 ^ i).card := hcard

/-- A function that agrees with a codeword on the image in domain `i` of a set
holding at least a fraction `θ` of the first domain is `θ`-close to the code. -/
theorem closeToCode_of_image [DecidableEq F] (S : LdtInstance F) {θ : ℝ} {A : Finset F}
    (hA : A ⊆ S.domain 0) (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ}
    (hi : i ≤ S.rounds) {f : F → F}
    (h : ∃ p : F[X], p.degree < S.degree i ∧ ∀ a ∈ A, f (a ^ 2 ^ i) = p.eval (a ^ 2 ^ i)) :
    CloseToCode (S.domain i) (S.degree i) θ f := by
  obtain ⟨p, hp, hf⟩ := h
  refine ⟨p, hp, A.image fun a => a ^ 2 ^ i, fun y hy => ?_, dense_image S hA hdense hi,
    fun y hy => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact pow_mem S (hA ha) hi
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact hf a ha

/-- One step of the backward induction. Suppose the points of `A` accept, and
codeword `i + 1` agrees with a polynomial `w` on the image of `A` in domain
`i + 1`. If the challenge of round `i` is good, then codeword `i` agrees with a
polynomial on the image of `A` in domain `i`, and the input of level `i + 1`
agrees with a polynomial on the image of `A` in domain `i + 1`. -/
theorem fold_step [DecidableEq F] (S : LdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    {A : Finset F} (hA : A ⊆ S.domain 0) (haccept : ∀ x ∈ A, QueryAccepts S.rounds ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) {i : ℕ} (hi : i < S.rounds)
    (hgood : GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i))
    {w : F[X]} (hw : w.degree < S.degree (i + 1))
    (hcw : ∀ a ∈ A, c (i + 1) (a ^ 2 ^ (i + 1)) = w.eval (a ^ 2 ^ (i + 1))) :
    (∃ p : F[X], p.degree < S.degree i ∧ ∀ a ∈ A, c i (a ^ 2 ^ i) = p.eval (a ^ 2 ^ i)) ∧
      ∃ p : F[X], p.degree < S.degree (i + 1) ∧
        ∀ a ∈ A, ro (i + 1) (a ^ 2 ^ (i + 1)) = p.eval (a ^ 2 ^ (i + 1)) := by
  have hBsub : (A.image fun a => a ^ 2 ^ (i + 1)) ⊆ S.domain (i + 1) := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
    exact pow_mem S (hA ha) (Nat.succ_le_of_lt hi)
  have hsq : ∀ a : F, a ^ 2 ^ (i + 1) = (a ^ 2 ^ i) ^ 2 := fun a => by rw [pow_succ, pow_mul]
  obtain ⟨⟨p₀, hp₀, h₀⟩, p₁, hp₁, h₁⟩ := hgood w hw _ hBsub
    (dense_image S hA hdense (Nat.succ_le_of_lt hi)) fun x _ hxB => by
      obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hxB
      have hfold : foldAt (c i) (β i) x = foldAt (c i) (β i) (a ^ 2 ^ i) := by
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hax.symm.trans (hsq a)) with h | h
        · rw [h]
        · rw [h, foldAt_neg]
      rw [hfold, ← hax, ← (haccept a ha).2 i hi, hcw a ha]
  refine ⟨⟨p₀, ?_, fun a ha => h₀ _ (pow_mem S (hA ha) hi.le) ?_⟩,
    p₁, hp₁, fun a ha => h₁ _ (Finset.mem_image_of_mem _ ha)⟩
  · rwa [S.degree_step i hi]
  · rw [← hsq]
    exact Finset.mem_image_of_mem _ ha

/-- `query_soundness` with the agreement sets named: under its hypotheses, each
input `ro i` agrees with a codeword on the image of `A` in domain `i`, the set
of `a ^ 2 ^ i` for `a` in `A`. -/
theorem agree_on_image (S : LdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds, GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i))
    (A : Finset F) (hA : A ⊆ S.domain 0) (haccept : ∀ x ∈ A, QueryAccepts S.rounds ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) :
    ∀ i ≤ S.rounds, ∃ p : F[X], p.degree < S.degree i ∧
      ∀ a ∈ A, ro i (a ^ 2 ^ i) = p.eval (a ^ 2 ^ i) := by
  classical
  -- Each committed codeword agrees with a polynomial on the image of `A`.
  have hc : ∀ i, i ≤ S.rounds →
      ∃ w : F[X], w.degree < S.degree i ∧ ∀ a ∈ A, c i (a ^ 2 ^ i) = w.eval (a ^ 2 ^ i) := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self =>
      obtain ⟨w, hw, hcw⟩ := hfinal
      exact ⟨w, hw, fun a ha => hcw _ (pow_mem S (hA ha) le_rfl)⟩
    | of_succ k hk ih =>
      obtain ⟨w, hw, hcw⟩ := ih
      exact (fold_step S ro c β hA haccept hdense hk (hgood k hk) hw hcw).1
  intro i hi
  cases i with
  | zero =>
    obtain ⟨w, hw, hcw⟩ := hc 0 hi
    refine ⟨w, hw, fun a ha => ?_⟩
    rw [← hcw a ha, pow_zero, pow_one, (haccept a ha).1]
  | succ i =>
    obtain ⟨w, hw, hcw⟩ := hc (i + 1) hi
    exact (fold_step S ro c β hA haccept hdense hi (hgood i hi) hw hcw).2

end Soundness

/-- Soundness of the query phase. Suppose the final message is a codeword and
every folding challenge is good. If the points of a set `A` holding at least a
fraction `θ` of the first domain all pass the verifier's query check, then every
input `ro i` is `θ`-close to its code. -/
theorem query_soundness (S : LdtInstance F) {θ : ℝ} (ro c : ℕ → F → F) (β : ℕ → F)
    (hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) (c S.rounds))
    (hgood : ∀ i < S.rounds, GoodChallenge (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ
      (ro (i + 1)) (c i) (β i))
    (A : Finset F) (hA : A ⊆ S.domain 0) (haccept : ∀ x ∈ A, QueryAccepts S.rounds ro c β x)
    (hdense : θ * (S.domain 0).card ≤ A.card) :
    ∀ i ≤ S.rounds, CloseToCode (S.domain i) (S.degree i) θ (ro i) := by
  classical
  exact fun i hi => Soundness.closeToCode_of_image S hA hdense hi
    (Soundness.agree_on_image S ro c β hfinal hgood A hA haccept hdense i hi)

end CertiFri
