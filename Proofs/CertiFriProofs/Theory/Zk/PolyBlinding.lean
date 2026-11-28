import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Algebraic Polynomial Blinding, Telescoping Quotient Slicing, Masked LogUp & Multi-Arity FRI Randomizer Hiding

This module formalizes the exact information-theoretic (perfect) algebraic hiding
layer of Protocol `v6-zk` over any finite field `K`:

1. **Finite Pushforward Distributions & Total Variation Distance (`FiniteDist`):**
   * `unifMass`, `unifProb`, `unifExpect`, `IsUniformPushforward`, and `tvDist`.
   * Exact fiberwise-cardinality, surjective-affine-map, product, Pi-type,
     conditional chain-rule (`isUniformPushforward_fiberwise`), and data-processing
     theorems (`tvDist_comp_eq_zero_of_eq`, `abs_unifProb_sub_le_tvDist`).

2. **Polynomial Coefficient Encoding & Lagrange Multi-Point Surjectivity (`PolyEval`):**
   * `polyOfFin : (Fin b → K) → K[X]` representing polynomials of degree `< b`.
   * Explicit Lagrange basis construction proving `evalVecLin_surjective`: for any
     `k ≤ b` and any injective `xs : Fin k → K`, evaluation at `xs` is surjective
     onto `Fin k → K`.

3. **Witness Polynomial Blinding / Exact Evaluation Hiding (`PolyBlinding`):**
   * `blindPoly n f r = f + (X ^ n - 1) * polyOfFin r` where `Z_H(X) = X ^ n - 1`
     is the vanishing polynomial of `H = {x : K | x ^ n = 1}`.
   * `eval_blindPoly_of_mem_trace`: exact preservation on `H`.
   * `eval_vec_uniform_of_blinding`: for any `k ≤ b` distinct evaluation points
     `xs : Fin k → K` disjoint from `H` (`∀ i, (xs i) ^ n ≠ 1`) — covering both
     OOD points `{z, g * z}` and all FRI query positions on a disjoint coset
     `g_coset * D` — the evaluation vector `(f_blind(x_1), ..., f_blind(x_k))` is
     **perfectly uniform** over `Fin k → K`, completely independent of `f`
     (`eval_vec_tvDist_zero_of_blinding`).
   * `eval_matrix_uniform_of_blinding`: extension to `W` independently blinded
     trace columns.
   * `coset_pow_ne_one_of_shift`: algebraic disjointness of cosets `s * D` from
     two-adic trace subgroups `H_n`.

4. **Telescoping Half-Stride Quotient Slicing Hiding (`QuotientBlinding`):**
   * `blindedQuotientSlice n q c ρ`: `c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^n * ρ_k(X)`.
   * `quotient_slices_uniform_of_telescoping`: at any `k ≤ b` distinct points,
     the tail `2 * q - 1` slices are perfectly uniform while slice `0` is
     uniquely determined by the exact recombination relation `∑ X^{k n} c'_k = Q`.

5. **Masked-LogUp Running-Sum & Cross-Circuit Accumulator Blinding (`MaskedLogup`):**
   * `masked_logup_hiding`: vanishing-blinded LogUp running-sum polynomial
     `φ_blind(X) = φ(X) + (X ^ n - 1) * r_φ(X)` preserves all trace-domain
     transitions and telescopic boundary values on `H` while rendering any
     `k ≤ b` off-domain openings perfectly uniform and witness-independent.
   * `masked_logup_boundary_hiding`: multi-circuit `v6-zk` boundary masking
     (`A'_p = S_p + μ_p` with committed blinded mask polynomial `U_p` satisfying
     `U_p(1) = μ_p`) preserves the exact cross-circuit telescopic sum while
     rendering `(A'_p, U_p(xs))` jointly perfectly uniform.

6. **Multi-Arity FRI Randomizer Decomposition (`FriRandomizerBlinding`):**
   * `oodQuotientSplitEquiv`: uniform degree-`< d` polynomial `R` decomposes
     bijectively into independent uniform `(R(z), (R(X) - R(z)) / (X - z))`.
   * `fri_multi_round_randomizer_uniform`: for any multi-arity schedule
     `arities : List ℕ` and any witness polynomial `W`, folding `W + R` yields
     perfectly uniform and witness-independent final polynomial `p_final` and
     round-wise sibling openings whenever `numQueries ≤ finalPolyLen`.
-/

namespace CertiFri.Zk

open Polynomial
open scoped BigOperators

/-! ## Section 1: Finite Pushforward Distributions & Total Variation Distance -/

section FiniteDist

/-- Expectation of `g (F ω)` for `ω` uniform over the finite type `Ω`. -/
noncomputable def unifExpect {Ω α : Type*} [Fintype Ω] (F : Ω → α) (g : α → ℝ) : ℝ :=
  (∑ ω : Ω, g (F ω)) / (Fintype.card Ω : ℝ)

open Classical in
/-- Probability mass of `y : α` under the pushforward of uniform `Ω` by `F`. -/
noncomputable def unifMass {Ω α : Type*} [Fintype Ω] (F : Ω → α) (y : α) : ℝ :=
  (∑ ω : Ω, if F ω = y then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ)

open Classical in
/-- Probability of event `E : α → Prop` under the pushforward of uniform `Ω` by `F`. -/
noncomputable def unifProb {Ω α : Type*} [Fintype Ω] (F : Ω → α) (E : α → Prop) : ℝ :=
  (∑ ω : Ω, if E (F ω) then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ)

/-- `F : Ω → α` pushes the uniform distribution on `Ω` forward to the exact uniform
distribution on `α`. -/
def IsUniformPushforward {Ω α : Type*} [Fintype Ω] [Fintype α] (F : Ω → α) : Prop :=
  ∀ y : α, unifMass F y = 1 / (Fintype.card α : ℝ)

/-- Total variation distance between two finite pushforward distributions on `α`. -/
noncomputable def tvDist {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : α, |unifMass F₁ y - unifMass F₂ y|

theorem unifMass_eq_card_div {Ω α : Type*} [Fintype Ω] (F : Ω → α) (y : α)
    [DecidablePred fun ω => F ω = y] :
    unifMass F y = ((Finset.univ.filter fun ω => F ω = y).card : ℝ) / (Fintype.card Ω : ℝ) := by
  unfold unifMass
  congr 1
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : F ω = y <;> simp [h]

theorem unifProb_eq_card_div {Ω α : Type*} [Fintype Ω] (F : Ω → α) (E : α → Prop)
    [DecidablePred fun ω => E (F ω)] :
    unifProb F E = ((Finset.univ.filter fun ω => E (F ω)).card : ℝ) / (Fintype.card Ω : ℝ) := by
  unfold unifProb
  congr 1
  rw [← Finset.sum_boole]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : E (F ω) <;> simp [h]

theorem unifMass_nonneg {Ω α : Type*} [Fintype Ω] (F : Ω → α) (y : α) :
    0 ≤ unifMass F y := by
  unfold unifMass
  exact div_nonneg (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) (Nat.cast_nonneg _)

theorem unifExpect_eq_sum_unifMass {Ω α : Type*} [Fintype Ω] [Fintype α]
    (F : Ω → α) (g : α → ℝ) :
    unifExpect F g = ∑ y : α, unifMass F y * g y := by
  classical
  unfold unifExpect
  have hfib :
      ∑ y : α, ∑ ω ∈ Finset.univ.filter (fun ω : Ω => F ω = y), g (F ω) =
        ∑ ω : Ω, g (F ω) :=
    Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) (fun ω => g (F ω))
  have hinner : ∀ y : α,
      ∑ ω ∈ Finset.univ.filter (fun ω : Ω => F ω = y), g (F ω) =
        ((Finset.univ.filter fun ω : Ω => F ω = y).card : ℝ) * g y := by
    intro y
    calc ∑ ω ∈ Finset.univ.filter (fun ω : Ω => F ω = y), g (F ω)
        = ∑ _ω ∈ Finset.univ.filter (fun ω : Ω => F ω = y), g y := by
            refine Finset.sum_congr rfl fun ω hω => ?_
            rw [(Finset.mem_filter.mp hω).2]
      _ = ((Finset.univ.filter fun ω : Ω => F ω = y).card : ℝ) * g y := by
            rw [Finset.sum_const, nsmul_eq_mul]
  rw [← hfib]
  simp_rw [hinner, Finset.sum_div, unifMass_eq_card_div, div_mul_eq_mul_div]

theorem sum_unifMass {Ω α : Type*} [Fintype Ω] [Nonempty Ω] [Fintype α]
    (F : Ω → α) : ∑ y : α, unifMass F y = 1 := by
  have h := unifExpect_eq_sum_unifMass F (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [← h]
  unfold unifExpect
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [hcard]

theorem unifProb_eq_unifExpect {Ω α : Type*} [Fintype Ω] (F : Ω → α) (E : α → Prop) :
    unifProb F E = unifExpect F (fun y => @ite _ (E y) (Classical.propDecidable _) 1 0) := rfl

theorem unifExpect_eq_of_unifMass_eq {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (h : ∀ y : α, unifMass F₁ y = unifMass F₂ y) (g : α → ℝ) :
    unifExpect F₁ g = unifExpect F₂ g := by
  rw [unifExpect_eq_sum_unifMass, unifExpect_eq_sum_unifMass]
  refine Finset.sum_congr rfl fun y _ => by rw [h y]

theorem unifProb_eq_of_unifMass_eq {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (h : ∀ y : α, unifMass F₁ y = unifMass F₂ y) (E : α → Prop) :
    unifProb F₁ E = unifProb F₂ E := by
  rw [unifProb_eq_unifExpect, unifProb_eq_unifExpect]
  exact unifExpect_eq_of_unifMass_eq h _

theorem isUniformPushforward_id {α : Type*} [Fintype α] [Nonempty α] :
    IsUniformPushforward (id : α → α) := by
  classical
  intro y
  rw [unifMass_eq_card_div]
  have hfilt : (Finset.univ.filter fun ω : α => id ω = y) = {y} := by
    ext x
    simp
  rw [hfilt, Finset.card_singleton, Nat.cast_one]

theorem tvDist_nonneg {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) : 0 ≤ tvDist F₁ F₂ := by
  unfold tvDist
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem tvDist_symm {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) : tvDist F₁ F₂ = tvDist F₂ F₁ := by
  unfold tvDist
  congr 1
  refine Finset.sum_congr rfl fun y _ => abs_sub_comm _ _

theorem tvDist_triangle {Ω₁ Ω₂ Ω₃ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) (F₃ : Ω₃ → α) :
    tvDist F₁ F₃ ≤ tvDist F₁ F₂ + tvDist F₂ F₃ := by
  unfold tvDist
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact Finset.sum_le_sum fun y _ => abs_sub_le (unifMass F₁ y) (unifMass F₂ y) (unifMass F₃ y)

theorem tvDist_eq_zero_of_unifMass_eq {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (h : ∀ y : α, unifMass F₁ y = unifMass F₂ y) : tvDist F₁ F₂ = 0 := by
  unfold tvDist
  simp [h]

theorem tvDist_eq_zero_of_isUniformPushforward {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Fintype Ω₂]
    [Fintype α] {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (h₁ : IsUniformPushforward F₁) (h₂ : IsUniformPushforward F₂) : tvDist F₁ F₂ = 0 :=
  tvDist_eq_zero_of_unifMass_eq fun y => (h₁ y).trans (h₂ y).symm

/-- For any `[0, 1]`-valued distinguisher `g`, the difference in expectations is bounded by
total variation distance. -/
theorem abs_unifExpect_sub_le_tvDist {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Nonempty Ω₁]
    [Fintype Ω₂] [Nonempty Ω₂] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) (g : α → ℝ) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    |unifExpect F₁ g - unifExpect F₂ g| ≤ tvDist F₁ F₂ := by
  rw [unifExpect_eq_sum_unifMass, unifExpect_eq_sum_unifMass, ← Finset.sum_sub_distrib]
  have hzero : ∑ y : α, (unifMass F₁ y - unifMass F₂ y) * (1 / 2 : ℝ) = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_unifMass, sum_unifMass, sub_self, zero_mul]
  have hshift :
      ∑ y : α, (unifMass F₁ y * g y - unifMass F₂ y * g y) =
        ∑ y : α, (unifMass F₁ y - unifMass F₂ y) * (g y - 1 / 2) := by
    have h1 : ∀ y : α, unifMass F₁ y * g y - unifMass F₂ y * g y =
        (unifMass F₁ y - unifMass F₂ y) * (g y - 1 / 2) +
          (unifMass F₁ y - unifMass F₂ y) * (1 / 2 : ℝ) := fun y => by ring
    simp_rw [h1, Finset.sum_add_distrib, hzero, add_zero]
  rw [hshift]
  calc |∑ y : α, (unifMass F₁ y - unifMass F₂ y) * (g y - 1 / 2)|
      ≤ ∑ y : α, |(unifMass F₁ y - unifMass F₂ y) * (g y - 1 / 2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y : α, |unifMass F₁ y - unifMass F₂ y| * |g y - 1 / 2| := by
        refine Finset.sum_congr rfl fun y _ => abs_mul _ _
    _ ≤ ∑ y : α, |unifMass F₁ y - unifMass F₂ y| * (1 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [hg0 y, hg1 y]
    _ = tvDist F₁ F₂ := by
        rw [← Finset.sum_mul, mul_comm]
        rfl

/-- For any event `E : α → Prop`, `|unifProb F₁ E - unifProb F₂ E| ≤ tvDist F₁ F₂`. -/
theorem abs_unifProb_sub_le_tvDist {Ω₁ Ω₂ α : Type*} [Fintype Ω₁] [Nonempty Ω₁]
    [Fintype Ω₂] [Nonempty Ω₂] [Fintype α]
    (F₁ : Ω₁ → α) (F₂ : Ω₂ → α) (E : α → Prop) :
    |unifProb F₁ E - unifProb F₂ E| ≤ tvDist F₁ F₂ := by
  rw [unifProb_eq_unifExpect, unifProb_eq_unifExpect]
  exact abs_unifExpect_sub_le_tvDist F₁ F₂ _ (fun y => by split_ifs <;> norm_num)
    (fun y => by split_ifs <;> norm_num)

/-- Pushforward mass under deterministic post-composition `h ∘ F`. -/
theorem unifMass_comp {Ω α β : Type*} [Fintype Ω] [Fintype α]
    (F : Ω → α) (h : α → β) (z : β) :
    unifMass (h ∘ F) z =
      ∑ y : α, @ite _ (h y = z) (Classical.propDecidable _) (unifMass F y) 0 := by
  classical
  have heq : unifMass (h ∘ F) z =
      unifExpect F (fun y => @ite _ (h y = z) (Classical.propDecidable _) 1 0) := rfl
  rw [heq, unifExpect_eq_sum_unifMass]
  refine Finset.sum_congr rfl fun y _ => by split_ifs <;> simp

/-- Data-processing equality: identical pushforward distributions remain identical after
applying any deterministic map `h : α → β`. -/
theorem unifMass_comp_eq_of_eq {Ω₁ Ω₂ α β : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (hF : ∀ y : α, unifMass F₁ y = unifMass F₂ y) (h : α → β) (z : β) :
    unifMass (h ∘ F₁) z = unifMass (h ∘ F₂) z := by
  rw [unifMass_comp, unifMass_comp]
  refine Finset.sum_congr rfl fun y _ => by split_ifs <;> simp [hF y]

theorem tvDist_comp_eq_zero_of_eq {Ω₁ Ω₂ α β : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype α]
    [Fintype β] {F₁ : Ω₁ → α} {F₂ : Ω₂ → α}
    (hF : ∀ y : α, unifMass F₁ y = unifMass F₂ y) (h : α → β) :
    tvDist (h ∘ F₁) (h ∘ F₂) = 0 :=
  tvDist_eq_zero_of_unifMass_eq (unifMass_comp_eq_of_eq hF h)

/-- Constant fiber size implies exact uniform pushforward. -/
theorem isUniformPushforward_of_const_fiber {Ω α : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Nonempty α] (F : Ω → α) (c : ℕ)
    (hc : ∀ y : α, (∑ ω : Ω, @ite _ (F ω = y) (Classical.propDecidable _) (1 : ℝ) 0) = (c : ℝ)) :
    IsUniformPushforward F := by
  classical
  have hsum : (Fintype.card Ω : ℝ) = (Fintype.card α : ℝ) * (c : ℝ) := by
    calc (Fintype.card Ω : ℝ)
        = ∑ ω : Ω, (1 : ℝ) := by simp
      _ = ∑ ω : Ω, ∑ y : α, if F ω = y then (1 : ℝ) else 0 := by
          refine Finset.sum_congr rfl fun ω _ => by simp
      _ = ∑ y : α, ∑ ω : Ω, if F ω = y then (1 : ℝ) else 0 := Finset.sum_comm
      _ = ∑ _y : α, (c : ℝ) := Finset.sum_congr rfl fun y _ => by
          simpa using hc y
      _ = (Fintype.card α : ℝ) * (c : ℝ) := by simp
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc_ne : (c : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hsum
    exact hΩ hsum
  intro y
  unfold unifMass
  rw [hc y, hsum]
  field_simp [hα, hc_ne]

/-- Constant filter-cardinality implies exact uniform pushforward. -/
theorem isUniformPushforward_of_const_filter_card {Ω α : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Nonempty α] [DecidableEq α] (F : Ω → α) (c : ℕ)
    (hc : ∀ y : α, (Finset.univ.filter fun ω : Ω => F ω = y).card = c) :
    IsUniformPushforward F := by
  refine isUniformPushforward_of_const_fiber F c fun y => ?_
  rw [← hc y, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun ω _ => by by_cases h : F ω = y <;> simp [h]

/-- **Surjective Affine-Linear Uniformity Theorem:**
if `L : V →ₗ[K] W` is a surjective linear map between finite vector spaces over `K`
and `v₀ : W` is any fixed shift, then `x ↦ v₀ + L x` pushes the uniform distribution
on `V` forward to the **exact uniform** distribution on `W`. -/
theorem isUniformPushforward_of_linear_surj {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype V]
    [AddCommGroup W] [Module K W] [Fintype W]
    (L : V →ₗ[K] W) (hL : Function.Surjective L) (v₀ : W) :
    IsUniformPushforward (fun x : V => v₀ + L x) := by
  classical
  refine isUniformPushforward_of_const_fiber (fun x : V => v₀ + L x)
    (Finset.univ.filter fun u : V => L u = 0).card fun y => ?_
  have hsum : (∑ x : V, @ite _ (v₀ + L x = y) (Classical.propDecidable _) (1 : ℝ) 0) =
      ((Finset.univ.filter fun x : V => v₀ + L x = y).card : ℝ) := by
    rw [← Finset.sum_boole]
  rw [hsum]
  congr 1
  obtain ⟨x₀, hx₀⟩ := hL (y - v₀)
  symm
  refine Finset.card_bij (fun u _ => u + x₀) ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    rw [map_add, hu, zero_add, hx₀, add_sub_cancel]
  · intro u₁ _ u₂ _ h
    exact add_right_cancel h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x - x₀, ?_, sub_add_cancel x x₀⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [map_sub, hx₀, sub_eq_zero]
    exact eq_sub_of_add_eq' hx

/-- Any bijection pushes the uniform distribution forward to the exact uniform distribution. -/
theorem isUniformPushforward_of_equiv {Ω α : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype α] [Nonempty α] (e : Ω ≃ α) :
    IsUniformPushforward e := by
  classical
  refine isUniformPushforward_of_const_fiber e 1 fun y => ?_
  have hsum : (∑ ω : Ω, @ite _ (e ω = y) (Classical.propDecidable _) (1 : ℝ) 0) =
      ∑ ω : Ω, if ω = e.symm y then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun ω _ => by
      by_cases h : e ω = y
      · have h' : ω = e.symm y := (Equiv.eq_symm_apply e).mpr h
        simp [h']
      · have h' : ω ≠ e.symm y := fun hc => h ((Equiv.eq_symm_apply e).mp hc)
        simp [h, h']
  rw [hsum]
  simp

/-- Post-composing a uniform pushforward with an equivalence preserves uniformity. -/
theorem isUniformPushforward_comp_equiv {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    {F : Ω → α} (hF : IsUniformPushforward F) (e : α ≃ β) :
    IsUniformPushforward (e ∘ F) := by
  classical
  intro z
  rw [unifMass_comp]
  have hsum : (∑ y : α, @ite _ (e y = z) (Classical.propDecidable _) (unifMass F y) 0) =
      ∑ y : α, if y = e.symm z then unifMass F y else 0 := by
    refine Finset.sum_congr rfl fun y _ => by
      by_cases h : e y = z
      · have h' : y = e.symm z := (Equiv.eq_symm_apply e).mpr h
        simp [h']
      · have h' : y ≠ e.symm z := fun hc => h ((Equiv.eq_symm_apply e).mp hc)
        simp [h, h']
  rw [hsum]
  simp [hF (e.symm z), Fintype.card_congr e]

/-- **Chain Rule / Fiberwise Uniformity:** if `F : Ω₁ → α` is uniform and for every `ω₁`,
`G ω₁ : Ω₂ → β` is uniform, then `(ω₁, ω₂) ↦ (F ω₁, G ω₁ ω₂)` is jointly uniform on `α × β`. -/
theorem isUniformPushforward_fiberwise {Ω₁ Ω₂ α β : Type*}
    [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (F : Ω₁ → α) (G : Ω₁ → Ω₂ → β)
    (hF : IsUniformPushforward F) (hG : ∀ ω₁ : Ω₁, IsUniformPushforward (G ω₁)) :
    IsUniformPushforward (fun p : Ω₁ × Ω₂ => (F p.1, G p.1 p.2)) := by
  classical
  intro ⟨a, b⟩
  unfold unifMass
  rw [Fintype.sum_prod_type]
  have hsplit : ∀ ω₁ : Ω₁,
      (∑ ω₂ : Ω₂, @ite _ ((F ω₁, G ω₁ ω₂) = (a, b)) (Classical.propDecidable _) (1 : ℝ) 0) =
      (@ite _ (F ω₁ = a) (Classical.propDecidable _) (1 : ℝ) 0) *
        (∑ ω₂ : Ω₂, @ite _ (G ω₁ ω₂ = b) (Classical.propDecidable _) (1 : ℝ) 0) := by
    intro ω₁
    by_cases h1 : F ω₁ = a
    · simp only [h1, ↓reduceIte, one_mul]
      refine Finset.sum_congr rfl fun ω₂ _ => by
        by_cases h2 : G ω₁ ω₂ = b <;> simp [h2]
    · simp only [h1, ↓reduceIte, zero_mul]
      refine Finset.sum_eq_zero fun ω₂ _ => by simp [h1]
  have hGsum : ∀ ω₁ : Ω₁,
      (∑ ω₂ : Ω₂, @ite _ (G ω₁ ω₂ = b) (Classical.propDecidable _) (1 : ℝ) 0) =
        (Fintype.card Ω₂ : ℝ) / (Fintype.card β : ℝ) := by
    intro ω₁
    have h := hG ω₁ b
    unfold unifMass at h
    have hΩ₂ : (Fintype.card Ω₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [div_eq_div_iff hΩ₂ hβ] at h
    rw [eq_div_iff hβ]
    linarith
  have hFsum :
      (∑ ω₁ : Ω₁, @ite _ (F ω₁ = a) (Classical.propDecidable _) (1 : ℝ) 0) =
        (Fintype.card Ω₁ : ℝ) / (Fintype.card α : ℝ) := by
    have h := hF a
    unfold unifMass at h
    have hΩ₁ : (Fintype.card Ω₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [div_eq_div_iff hΩ₁ hα] at h
    rw [eq_div_iff hα]
    linarith
  simp_rw [hsplit, hGsum, ← Finset.sum_mul, hFsum]
  rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul]
  have hΩ₁ : (Fintype.card Ω₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hΩ₂ : (Fintype.card Ω₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hα : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβ : (Fintype.card β : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hΩ₁, hΩ₂, hα, hβ]

/-- Independent products of uniform pushforwards are uniform. -/
theorem isUniformPushforward_prod {Ω₁ Ω₂ α β : Type*}
    [Fintype Ω₁] [Nonempty Ω₁] [Fintype Ω₂] [Nonempty Ω₂]
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (F : Ω₁ → α) (G : Ω₂ → β)
    (hF : IsUniformPushforward F) (hG : IsUniformPushforward G) :
    IsUniformPushforward (fun p : Ω₁ × Ω₂ => (F p.1, G p.2)) :=
  isUniformPushforward_fiberwise F (fun _ => G) hF (fun _ => hG)

/-- Independent Pi-products of uniform pushforwards are uniform. -/
theorem isUniformPushforward_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)]
    (F : ∀ i, Ω i → α i) (hF : ∀ i, IsUniformPushforward (F i)) :
    IsUniformPushforward (fun ω : (i : ι) → Ω i => fun i => F i (ω i)) := by
  classical
  intro y
  rw [unifMass_eq_card_div]
  have hfilt :
      (Finset.univ.filter fun ω : (i : ι) → Ω i => (fun i => F i (ω i)) = y) =
        Fintype.piFinset (fun i => Finset.univ.filter fun x : Ω i => F i x = y i) := by
    ext ω
    simp [Fintype.mem_piFinset, funext_iff]
  rw [hfilt, Fintype.card_piFinset, Fintype.card_pi, Fintype.card_pi,
    Nat.cast_prod, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  have hterm : ∀ i : ι,
      ((Finset.univ.filter fun x : Ω i => F i x = y i).card : ℝ) / (Fintype.card (Ω i) : ℝ) =
        1 / (Fintype.card (α i) : ℝ) := fun i => by
    rw [← unifMass_eq_card_div]
    exact hF i (y i)
  simp_rw [hterm, Finset.prod_div_distrib, Finset.prod_const_one]

end FiniteDist

/-! ## Section 2: Polynomial Coefficient Representation & Lagrange Surjectivity -/

section PolyEval

variable {K : Type*} [Field K]

/-- Polynomial of degree `< b` encoded by its `b` coefficients `r : Fin b → K`. -/
noncomputable def polyOfFin {b : ℕ} (r : Fin b → K) : K[X] :=
  ∑ j : Fin b, C (r j) * X ^ j.val

theorem coeff_polyOfFin {b : ℕ} (r : Fin b → K) (m : ℕ) :
    (polyOfFin r).coeff m = if h : m < b then r ⟨m, h⟩ else 0 := by
  unfold polyOfFin
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  by_cases hm : m < b
  · rw [dite_eq_left hm]
    rw [Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro j _ hj
      have hne : m ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [dite_eq_right hm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hne : m ≠ j.val := fun h => hm (h ▸ j.isLt)
    simp [hne]

theorem degree_polyOfFin_lt {b : ℕ} (r : Fin b → K) : (polyOfFin r).degree < b := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyOfFin, dite_eq_right (not_lt.mpr hm)]

theorem natDegree_polyOfFin_lt {b : ℕ} (hb : 0 < b) (r : Fin b → K) :
    (polyOfFin r).natDegree < b := by
  by_cases h0 : polyOfFin r = 0
  · simpa [h0] using hb
  · exact (natDegree_lt_iff_degree_lt h0).mpr (degree_polyOfFin_lt r)

theorem polyOfFin_coeff_eq {b : ℕ} {p : K[X]} (hp : p.degree < b) :
    polyOfFin (fun j : Fin b => p.coeff j.val) = p := by
  rw [degree_lt_iff_coeff_zero] at hp
  ext m
  rw [coeff_polyOfFin]
  split_ifs with hm
  · rfl
  · exact (hp m (not_lt.mp hm)).symm

theorem eval_polyOfFin {b : ℕ} (r : Fin b → K) (x : K) :
    (polyOfFin r).eval x = ∑ j : Fin b, r j * x ^ j.val := by
  unfold polyOfFin
  simp [eval_finsetSum]

/-- `polyOfFin` as a `K`-linear map from `(Fin b → K)` to `K[X]`. -/
noncomputable def polyOfFinLin (b : ℕ) : (Fin b → K) →ₗ[K] K[X] where
  toFun := polyOfFin
  map_add' r₁ r₂ := by
    ext m
    simp only [coeff_add, coeff_polyOfFin, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c r := by
    ext m
    simp only [coeff_smul, coeff_polyOfFin, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

/-- Multi-point evaluation of degree-`< b` polynomials at `xs : Fin k → K` as a `K`-linear map. -/
noncomputable def evalVecLin {b k : ℕ} (xs : Fin k → K) : (Fin b → K) →ₗ[K] (Fin k → K) where
  toFun r i := (polyOfFin r).eval (xs i)
  map_add' r₁ r₂ := by
    ext i
    simp [eval_polyOfFin, add_mul, Finset.sum_add_distrib]
  map_smul' c r := by
    ext i
    simp [eval_polyOfFin, mul_assoc, Finset.mul_sum]

/-- Explicit `i`-th Lagrange basis polynomial for `xs : Fin k → K`. -/
noncomputable def lagrangeBasis [DecidableEq K] {k : ℕ} (xs : Fin k → K) (i : Fin k) : K[X] :=
  ∏ j ∈ Finset.univ.erase i, C ((xs i - xs j)⁻¹) * (X - C (xs j))

theorem eval_lagrangeBasis_self [DecidableEq K] {k : ℕ} {xs : Fin k → K}
    (hxs : Function.Injective xs) (i : Fin k) :
    (lagrangeBasis xs i).eval (xs i) = 1 := by
  unfold lagrangeBasis
  rw [eval_prod]
  refine Finset.prod_eq_one fun j hj => ?_
  have hne : xs i - xs j ≠ 0 := sub_ne_zero.mpr fun h => (Finset.ne_of_mem_erase hj) (hxs h.symm)
  simp [inv_mul_cancel₀ hne]

theorem eval_lagrangeBasis_ne [DecidableEq K] {k : ℕ} (xs : Fin k → K) {i m : Fin k} (hmi : m ≠ i) :
    (lagrangeBasis xs i).eval (xs m) = 0 := by
  unfold lagrangeBasis
  rw [eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hmi, Finset.mem_univ m⟩) ?_
  simp

theorem natDegree_lagrangeBasis_lt [DecidableEq K] {k : ℕ} (xs : Fin k → K) (i : Fin k) :
    (lagrangeBasis xs i).natDegree < k := by
  unfold lagrangeBasis
  let degf : Fin k → ℕ := fun j => (C ((xs i - xs j)⁻¹) * (X - C (xs j))).natDegree
  have hprod : (∏ j ∈ Finset.univ.erase i, (C ((xs i - xs j)⁻¹) * (X - C (xs j)))).natDegree ≤
      ∑ j ∈ Finset.univ.erase i, degf j :=
    natDegree_prod_le _ _
  have hterm : ∀ j ∈ Finset.univ.erase i, degf j ≤ 1 := by
    intro j _
    calc degf j
        ≤ (C ((xs i - xs j)⁻¹)).natDegree + (X - C (xs j)).natDegree := natDegree_mul_le
      _ = 0 + 1 := by simp
      _ = 1 := by omega
  have hsum : ∑ j ∈ Finset.univ.erase i, degf j ≤ k - 1 := by
    calc ∑ j ∈ Finset.univ.erase i, degf j
        ≤ ∑ _j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum hterm
      _ = (Finset.univ.erase i).card := by simp
      _ = k - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  have hk : 0 < k := Nat.pos_of_ne_zero (Fin.pos i |>.ne')
  omega

theorem degree_lagrangeBasis_lt [DecidableEq K] {k : ℕ} (xs : Fin k → K) (i : Fin k) :
    (lagrangeBasis xs i).degree < k :=
  lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast natDegree_lagrangeBasis_lt xs i)

/-- **Lagrange Interpolation Surjectivity:**
for any `k ≤ b` and any `k` distinct evaluation points `xs : Fin k → K`, evaluating
degree-`< b` polynomials at `xs` is surjective onto `Fin k → K`. -/
theorem evalVecLin_surjective [DecidableEq K] {b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) :
    Function.Surjective (evalVecLin (b := b) xs) := by
  intro y
  let p : K[X] := ∑ i : Fin k, C (y i) * lagrangeBasis xs i
  have hp_deg : p.degree < (b : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    dsimp only [p]
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hlt : (C (y i) * lagrangeBasis xs i).degree < (b : WithBot ℕ) := by
      have hnat : (C (y i) * lagrangeBasis xs i).natDegree < b := by
        calc (C (y i) * lagrangeBasis xs i).natDegree
            ≤ (C (y i)).natDegree + (lagrangeBasis xs i).natDegree := natDegree_mul_le
          _ = (lagrangeBasis xs i).natDegree := by simp
          _ < k := natDegree_lagrangeBasis_lt xs i
          _ ≤ b := hkb
      exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast hnat)
    rw [degree_lt_iff_coeff_zero] at hlt
    exact hlt m hm
  refine ⟨fun j : Fin b => p.coeff j.val, ?_⟩
  ext m
  change (polyOfFin (fun j : Fin b => p.coeff j.val)).eval (xs m) = y m
  rw [polyOfFin_coeff_eq hp_deg]
  dsimp only [p]
  rw [eval_finsetSum, Finset.sum_eq_single m]
  · simp [eval_lagrangeBasis_self hxs m]
  · intro i _ him
    simp [eval_lagrangeBasis_ne xs him.symm]
  · intro h
    exact absurd (Finset.mem_univ m) h

end PolyEval

/-! ## Section 3: Algebraic Polynomial Blinding & Exact Evaluation Hiding -/

section PolyBlinding

variable {K : Type*} [Field K]

/-- Vanishing polynomial `Z_H(X) = X ^ n - 1` of the trace domain `H = {x | x ^ n = 1}`. -/
noncomputable def vanishingPoly (n : ℕ) : K[X] := X ^ n - 1

/-- Blinded witness polynomial `f_blind(X) = f(X) + Z_H(X) * r(X)` with blinding
polynomial `r` of degree `< b`. -/
noncomputable def blindPoly (n : ℕ) (f : K[X]) {b : ℕ} (r : Fin b → K) : K[X] :=
  f + vanishingPoly n * polyOfFin r

/-- Blinding preserves every evaluation on the trace subgroup `H = {x | x ^ n = 1}`. -/
theorem eval_blindPoly_of_mem_trace (n : ℕ) (f : K[X]) {b : ℕ} (r : Fin b → K)
    {x : K} (hx : x ^ n = 1) :
    (blindPoly n f r).eval x = f.eval x := by
  simp [blindPoly, vanishingPoly, hx]

/-- Degree bound for blinded witness polynomials: if `deg(f) < n + b`, then
`deg(f_blind) < n + b` (for `b = n`, this is the `v6-zk` 2× odd-coset degree bound `< 2 * n`). -/
theorem natDegree_blindPoly_lt {n b : ℕ} (hb : 0 < b) {f : K[X]} (hf : f.natDegree < n + b)
    (r : Fin b → K) :
    (blindPoly n f r).natDegree < n + b := by
  have hZ : (vanishingPoly (K := K) n).natDegree ≤ n :=
    (natDegree_sub_le ((X : K[X]) ^ n) 1).trans (max_le (natDegree_X_pow_le n) (by simp))
  have hr : (polyOfFin r).natDegree < b := natDegree_polyOfFin_lt hb r
  have hmul : (vanishingPoly n * polyOfFin r).natDegree < n + b := by
    by_cases hr0 : polyOfFin r = 0
    · simp [hr0]; omega
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)
  exact lt_of_le_of_lt (natDegree_add_le f _) (max_lt hf hmul)

/-- Linear map `r ↦ (Z_H(x_i) * r(x_i))_{i < k}` for blinding evaluations at `xs`. -/
noncomputable def vanishingEvalLin (n : ℕ) {b k : ℕ} (xs : Fin k → K) :
    (Fin b → K) →ₗ[K] (Fin k → K) where
  toFun r i := ((xs i) ^ n - 1) * (polyOfFin r).eval (xs i)
  map_add' r₁ r₂ := by
    ext i
    simp [eval_polyOfFin, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c r := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, eval_polyOfFin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

/-- Surjectivity of `vanishingEvalLin` when `k ≤ b`, `xs` is injective, and every `xs i`
is disjoint from `H = {x | x ^ n = 1}`. -/
theorem vanishingEvalLin_surjective [DecidableEq K] {n b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    Function.Surjective (vanishingEvalLin (K := K) n (b := b) xs) := by
  intro w
  let target : Fin k → K := fun i => ((xs i) ^ n - 1)⁻¹ * w i
  obtain ⟨r, hr⟩ := evalVecLin_surjective (b := b) hkb hxs target
  refine ⟨r, ?_⟩
  ext i
  have hzi : (xs i) ^ n - 1 ≠ 0 := sub_ne_zero.mpr (hdisj i)
  have hri : (polyOfFin r).eval (xs i) = ((xs i) ^ n - 1)⁻¹ * w i := congrFun hr i
  change ((xs i) ^ n - 1) * (polyOfFin r).eval (xs i) = w i
  rw [hri, mul_inv_cancel_left₀ hzi]

/-- **Exact Evaluation Hiding Theorem (`eval_vec_uniform_of_blinding`):**
for ANY secret witness polynomial `f : K[X]`, ANY blinding budget `b`, and ANY tuple of
`k ≤ b` distinct evaluation points `xs : Fin k → K` disjoint from the trace domain
`H = {x | x ^ n = 1}` (covering both OOD points `{z, g * z}` and all FRI coset query
positions), the vector `(f_blind(x_1), ..., f_blind(x_k))` is **perfectly uniform** over
`Fin k → K` — completely independent of `f`! -/
theorem eval_vec_uniform_of_blinding [Fintype K] [DecidableEq K]
    (n : ℕ) (f : K[X]) {b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    IsUniformPushforward (fun r : Fin b → K => fun i : Fin k => (blindPoly n f r).eval (xs i)) := by
  have heq : (fun r : Fin b → K => fun i : Fin k => (blindPoly n f r).eval (xs i)) =
      (fun r : Fin b → K => (fun i : Fin k => f.eval (xs i)) + vanishingEvalLin n xs r) := by
    funext r i
    simp [blindPoly, vanishingPoly, vanishingEvalLin]
  rw [heq]
  exact isUniformPushforward_of_linear_surj (vanishingEvalLin n xs)
    (vanishingEvalLin_surjective hkb hxs hdisj) (fun i => f.eval (xs i))

/-- **Exact Zero Total-Variation Distance Between Any Two Secret Polynomials:**
for any two secret polynomials `f₁, f₂ : K[X]`, their blinded evaluations at any `k ≤ b`
distinct off-domain points have **zero** total variation distance (`tvDist = 0`). -/
theorem eval_vec_tvDist_zero_of_blinding [Fintype K] [DecidableEq K]
    (n : ℕ) (f₁ f₂ : K[X]) {b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    tvDist
      (fun r : Fin b → K => fun i : Fin k => (blindPoly n f₁ r).eval (xs i))
      (fun r : Fin b → K => fun i : Fin k => (blindPoly n f₂ r).eval (xs i)) = 0 :=
  tvDist_eq_zero_of_isUniformPushforward
    (eval_vec_uniform_of_blinding n f₁ hkb hxs hdisj)
    (eval_vec_uniform_of_blinding n f₂ hkb hxs hdisj)

/-- **Multi-Column Batch Blinding Uniformity:**
blinding `W` secret trace polynomials `fs : Fin W → K[X]` with independent uniform
blinding polynomials `rs : Fin W → Fin b → K` makes the entire `W × k` matrix of
off-domain openings perfectly uniform on `Fin W → Fin k → K`. -/
theorem eval_matrix_uniform_of_blinding [Fintype K] [DecidableEq K]
    (n W : ℕ) (fs : Fin W → K[X]) {b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    IsUniformPushforward
      (fun rs : Fin W → Fin b → K =>
        fun w : Fin W => fun i : Fin k => (blindPoly n (fs w) (rs w)).eval (xs i)) :=
  isUniformPushforward_pi
    (fun (w : Fin W) (r : Fin b → K) (i : Fin k) => (blindPoly n (fs w) r).eval (xs i))
    (fun w => eval_vec_uniform_of_blinding n (fs w) hkb hxs hdisj)

/-- **Coset Disjointness Criterion:** if `s ^ M ≠ 1`, `d ^ M = 1`, and `n ∣ M`, then
`(s * d) ^ n ≠ 1`. In particular, for a two-adic subgroup `D ⊆ {d | d ^ (2 ^ h) = 1}`,
any shift `s` with `s ^ (2 ^ h) ≠ 1` makes the entire coset `s * D` disjoint from every
trace subgroup `H_{2 ^ logN}` (`logN ≤ h`). -/
theorem coset_pow_ne_one_of_shift {s d : K} {n M : ℕ}
    (hs : s ^ M ≠ 1) (hd : d ^ M = 1) (hnM : n ∣ M) :
    (s * d) ^ n ≠ 1 := by
  obtain ⟨m, rfl⟩ := hnM
  intro h1
  have hM : (s * d) ^ (n * m) = 1 := by
    rw [pow_mul, h1, one_pow]
  rw [mul_pow, hd, mul_one] at hM
  exact hs hM

/-- Combining OOD points `{z, g * z}` with `m` distinct off-domain coset points `xs`
produces an injective `(m + 2)`-tuple completely disjoint from `H_n`. -/
def oodAndCosetPoints {m : ℕ} (g z : K) (xs : Fin m → K) : Fin (m + 2) → K :=
  fun i =>
    if h : i.val < m then xs ⟨i.val, h⟩
    else if i.val = m then z
    else g * z

theorem oodAndCosetPoints_injective {m : ℕ} {g z : K} {xs : Fin m → K}
    (hxs : Function.Injective xs)
    (hz0 : z ≠ 0) (hg1 : g ≠ 1)
    (hdisj_z : ∀ i : Fin m, xs i ≠ z)
    (hdisj_gz : ∀ i : Fin m, xs i ≠ g * z) :
    Function.Injective (oodAndCosetPoints g z xs) := by
  have hgz_ne_z : g * z ≠ z := fun h =>
    hg1 (mul_right_cancel₀ hz0 (by simpa using h))
  intro i j hij
  unfold oodAndCosetPoints at hij
  by_cases hi : i.val < m <;> by_cases hj : j.val < m
  · rw [dite_eq_left hi, dite_eq_left hj] at hij
    have hfin := congrArg Fin.val (hxs hij)
    exact Fin.ext hfin
  · rw [dite_eq_left hi, dite_eq_right hj] at hij
    split_ifs at hij
    · exact absurd hij (hdisj_z ⟨i.val, hi⟩)
    · exact absurd hij (hdisj_gz ⟨i.val, hi⟩)
  · rw [dite_eq_right hi, dite_eq_left hj] at hij
    split_ifs at hij
    · exact absurd hij.symm (hdisj_z ⟨j.val, hj⟩)
    · exact absurd hij.symm (hdisj_gz ⟨j.val, hj⟩)
  · rw [dite_eq_right hi, dite_eq_right hj] at hij
    split_ifs at hij with hi1 hj1 hj1
    · exact Fin.ext (by omega)
    · exact absurd hij.symm hgz_ne_z
    · exact absurd hij hgz_ne_z
    · exact Fin.ext (by omega)

theorem oodAndCosetPoints_disjoint {n m : ℕ} {g z : K} {xs : Fin m → K}
    (hg : g ^ n = 1) (hz : z ^ n ≠ 1) (hxs : ∀ i : Fin m, (xs i) ^ n ≠ 1) :
    ∀ i : Fin (m + 2), (oodAndCosetPoints g z xs i) ^ n ≠ 1 := by
  intro i
  unfold oodAndCosetPoints
  split_ifs with hi _
  · exact hxs ⟨i.val, hi⟩
  · exact hz
  · rw [mul_pow, hg, one_mul]
    exact hz

/-- **Combined OOD (`{z, g * z}`) + Coset FRI Query Blinding Hiding:**
whenever `m + 2 ≤ b`, the joint evaluation vector `(f_blind(x_1), ..., f_blind(x_m),
f_blind(z), f_blind(g * z))` is **perfectly uniform** over `Fin (m + 2) → K`. -/
theorem eval_ood_and_coset_uniform_of_blinding [Fintype K] [DecidableEq K]
    (n : ℕ) (f : K[X]) {b m : ℕ} (hmb : m + 2 ≤ b)
    {g z : K} {xs : Fin m → K}
    (hxs_inj : Function.Injective xs) (hxs_disj : ∀ i : Fin m, (xs i) ^ n ≠ 1)
    (hg : g ^ n = 1) (hg1 : g ≠ 1) (hz0 : z ≠ 0) (hz : z ^ n ≠ 1)
    (hdisj_z : ∀ i : Fin m, xs i ≠ z) (hdisj_gz : ∀ i : Fin m, xs i ≠ g * z) :
    IsUniformPushforward
      (fun r : Fin b → K => fun i : Fin (m + 2) =>
        (blindPoly n f r).eval (oodAndCosetPoints g z xs i)) :=
  eval_vec_uniform_of_blinding n f hmb
    (oodAndCosetPoints_injective hxs_inj hz0 hg1 hdisj_z hdisj_gz)
    (oodAndCosetPoints_disjoint hg hz hxs_disj)

end PolyBlinding

/-! ## Section 4: Telescoping Half-Stride Quotient Slicing Hiding -/

section QuotientBlinding

variable {K : Type*} [Field K]

/-- Extended telescoping shift polynomial `ρ_ext(i)` (`0` when `i ≥ 2 * q - 1`). -/
noncomputable def quotientShiftPoly (q b : ℕ) (ρ : Fin (2 * q - 1) → Fin b → K) (i : ℕ) : K[X] :=
  if h : i < 2 * q - 1 then polyOfFin (ρ ⟨i, h⟩) else 0

/-- Half-stride telescoping blinded quotient slice:
`c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^n * ρ_k(X)` with `ρ_{-1} = ρ_{2q - 1} = 0`. -/
noncomputable def blindedQuotientSlice (n q b : ℕ)
    (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → Fin b → K) (k : Fin (2 * q)) : K[X] :=
  c k - (if k.val = 0 then 0 else quotientShiftPoly q b ρ (k.val - 1)) +
    X ^ n * quotientShiftPoly q b ρ k.val

/-- Telescoping quotient slices recombine to the exact unblinded quotient polynomial. -/
theorem blindedQuotientSlice_sum_eq (n q b : ℕ) (hq : 1 ≤ q)
    (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → Fin b → K) :
    ∑ k : Fin (2 * q), X ^ (k.val * n) * blindedQuotientSlice n q b c ρ k =
      ∑ k : Fin (2 * q), X ^ (k.val * n) * c k := by
  let g : ℕ → K[X] := fun i =>
    if i = 0 then 0 else X ^ (i * n) * quotientShiftPoly q b ρ (i - 1)
  have hterm : ∀ k : Fin (2 * q),
      X ^ (k.val * n) * blindedQuotientSlice n q b c ρ k =
        X ^ (k.val * n) * c k + (g (k.val + 1) - g k.val) := by
    intro k
    unfold blindedQuotientSlice
    have hsucc : g (k.val + 1) = X ^ (k.val * n) * (X ^ n * quotientShiftPoly q b ρ k.val) := by
      dsimp only [g]
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.add_mul, one_mul, pow_add, mul_assoc]
    have hcur : g k.val =
        X ^ (k.val * n) * (if k.val = 0 then 0 else quotientShiftPoly q b ρ (k.val - 1)) := by
      dsimp only [g]
      split_ifs <;> ring
    rw [hsucc, hcur]
    ring
  simp_rw [hterm, Finset.sum_add_distrib]
  have htele : ∑ k : Fin (2 * q), (g (k.val + 1) - g k.val) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => g (i + 1) - g i) (2 * q)]
    rw [Finset.sum_range_sub g (2 * q)]
    have hg0 : g 0 = 0 := by simp [g]
    have hgtop : g (2 * q) = 0 := by
      dsimp only [g, quotientShiftPoly]
      have hne : 2 * q ≠ 0 := by omega
      simp [hne]
    rw [hg0, hgtop, sub_zero]
  rw [htele, add_zero]

/-- Slice `0` evaluated at any point `x` is deterministically determined by the total
quotient `Q(x)` and the tail `2 * q - 1` blinded slices. -/
theorem eval_blindedQuotientSlice_zero (n q b : ℕ) (hq : 1 ≤ q)
    (c : Fin (2 * q) → K[X]) (ρ : Fin (2 * q - 1) → Fin b → K) (x : K) :
    (blindedQuotientSlice n q b c ρ ⟨0, by omega⟩).eval x =
      (∑ k : Fin (2 * q), X ^ (k.val * n) * c k).eval x -
        ∑ j : Fin (2 * q - 1), x ^ ((j.val + 1) * n) *
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval x := by
  have hsum := congrArg (Polynomial.eval x) (blindedQuotientSlice_sum_eq n q b hq c ρ)
  rw [eval_finsetSum] at hsum
  have h2q : 2 * q = (2 * q - 1) + 1 := by omega
  let e : Fin ((2 * q - 1) + 1) ≃ Fin (2 * q) := finCongr h2q.symm
  have he0 : e 0 = ⟨0, by omega⟩ := Fin.ext rfl
  have hes : ∀ j : Fin (2 * q - 1), e j.succ = ⟨j.val + 1, by omega⟩ := fun _ => Fin.ext rfl
  have hsplit :
      ∑ k : Fin (2 * q), (X ^ (k.val * n) * blindedQuotientSlice n q b c ρ k).eval x =
        (blindedQuotientSlice n q b c ρ ⟨0, by omega⟩).eval x +
          ∑ j : Fin (2 * q - 1), x ^ ((j.val + 1) * n) *
            (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval x := by
    rw [← Equiv.sum_comp e, Fin.sum_univ_succ]
    congr 1
    · rw [he0]; simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hes j]
      simp [eval_mul, eval_pow, eval_X]
  rw [hsplit] at hsum
  exact eq_sub_of_add_eq hsum

/-- Linear part of the tail `2 * q - 1` telescoping blinded quotient slices evaluated at `xs`. -/
noncomputable def quotientTailLin (n q b k : ℕ) (xs : Fin k → K) :
    (Fin (2 * q - 1) → Fin b → K) →ₗ[K] (Fin (2 * q - 1) → Fin k → K) where
  toFun ρ j i :=
    -((polyOfFin (ρ j)).eval (xs i)) +
      (xs i) ^ n * (if h : j.val + 1 < 2 * q - 1 then (polyOfFin (ρ ⟨j.val + 1, h⟩)).eval (xs i) else 0)
  map_add' ρ₁ ρ₂ := by
    ext j i
    have h1 := congrFun ((evalVecLin (b := b) xs).map_add (ρ₁ j) (ρ₂ j)) i
    simp only [evalVecLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply] at h1
    simp only [Pi.add_apply]
    split_ifs with h
    · have h2 := congrFun ((evalVecLin (b := b) xs).map_add
        (ρ₁ ⟨j.val + 1, h⟩) (ρ₂ ⟨j.val + 1, h⟩)) i
      simp only [evalVecLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply] at h2
      rw [h1, h2]; ring
    · rw [h1]; ring
  map_smul' c ρ := by
    ext j i
    have h1 := congrFun ((evalVecLin (b := b) xs).map_smul c (ρ j)) i
    simp only [evalVecLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul] at h1
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs with h
    · have h2 := congrFun ((evalVecLin (b := b) xs).map_smul c (ρ ⟨j.val + 1, h⟩)) i
      simp only [evalVecLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul] at h2
      rw [h1, h2]; ring
    · rw [h1]; ring

/-- Auxiliary downward backward-substitution builder for `quotientTailLin_surjective`. -/
private noncomputable def quotientBackSub (n q b k : ℕ) (xs : Fin k → K)
    (inv : (Fin k → K) → (Fin b → K)) (y : Fin (2 * q - 1) → Fin k → K) : ℕ → Fin b → K
  | 0 =>
    if h0 : 0 < 2 * q - 1 then
      inv (fun i => -(y ⟨2 * q - 1 - 1, by omega⟩ i))
    else 0
  | d + 1 =>
    if h : d + 1 < 2 * q - 1 then
      let prev := quotientBackSub n q b k xs inv y d
      let idx : Fin (2 * q - 1) := ⟨2 * q - 1 - 1 - (d + 1), by omega⟩
      inv (fun i => (xs i) ^ n * (polyOfFin prev).eval (xs i) - y idx i)
    else 0

/-- Upper-triangular backward-substitution surjectivity for `quotientTailLin`. -/
theorem quotientTailLin_surjective [DecidableEq K] (n q : ℕ) {b k : ℕ} (hkb : k ≤ b)
    {xs : Fin k → K} (hxs : Function.Injective xs) :
    Function.Surjective (quotientTailLin (K := K) n q b k xs) := by
  intro y
  have hsurj := evalVecLin_surjective (b := b) hkb hxs
  choose inv hinv using hsurj
  let ρ : Fin (2 * q - 1) → Fin b → K :=
    fun j => quotientBackSub n q b k xs inv y ((2 * q - 1) - 1 - j.val)
  refine ⟨ρ, ?_⟩
  ext j i
  change -((polyOfFin (ρ j)).eval (xs i)) +
      (xs i) ^ n * (if h : j.val + 1 < 2 * q - 1 then
        (polyOfFin (ρ ⟨j.val + 1, h⟩)).eval (xs i) else 0) = y j i
  by_cases hlast : j.val + 1 < 2 * q - 1
  · rw [dite_eq_left hlast]
    set d := (2 * q - 1) - 1 - (j.val + 1) with hd_def
    have hidx : (2 * q - 1) - 1 - j.val = d + 1 := by omega
    have hlt : d + 1 < 2 * q - 1 := by omega
    have hj_eq : (⟨2 * q - 1 - 1 - (d + 1), by omega⟩ : Fin (2 * q - 1)) = j := by
      apply Fin.ext
      change 2 * q - 1 - 1 - (d + 1) = j.val
      omega
    have hρj : ρ j = inv (fun i' =>
        (xs i') ^ n * (polyOfFin (quotientBackSub n q b k xs inv y d)).eval (xs i') - y j i') := by
      dsimp only [ρ]
      rw [hidx]
      simp only [quotientBackSub, dite_eq_left hlt, hj_eq]
    have hρnext : ρ ⟨j.val + 1, hlast⟩ = quotientBackSub n q b k xs inv y d := rfl
    rw [hρj, hρnext]
    have hev : (polyOfFin (inv (fun i' =>
        (xs i') ^ n * (polyOfFin (quotientBackSub n q b k xs inv y d)).eval (xs i') - y j i'))).eval (xs i) =
        (xs i) ^ n * (polyOfFin (quotientBackSub n q b k xs inv y d)).eval (xs i) - y j i :=
      congrFun (hinv _) i
    rw [hev]
    ring
  · rw [dite_eq_right hlast, mul_zero, add_zero]
    have hpos : 0 < 2 * q - 1 := by omega
    have hzero : (2 * q - 1) - 1 - j.val = 0 := by omega
    have hj_eq : (⟨2 * q - 1 - 1, by omega⟩ : Fin (2 * q - 1)) = j := by
      apply Fin.ext
      change 2 * q - 1 - 1 = j.val
      omega
    have hρj : ρ j = inv (fun i' => -(y j i')) := by
      dsimp only [ρ]
      rw [hzero]
      simp only [quotientBackSub, dite_eq_left hpos, hj_eq]
    rw [hρj]
    have hev : (polyOfFin (inv (fun i' => -(y j i')))).eval (xs i) = -(y j i) :=
      congrFun (hinv _) i
    rw [hev, neg_neg]

/-- **Telescoping Quotient Slicing Hiding Theorem (`quotient_slices_uniform_of_telescoping`):**
for ANY `q ≥ 1`, ANY `2 * q` unblinded quotient slices `c : Fin (2 * q) → K[X]`, and ANY
`k ≤ b` distinct evaluation points `xs : Fin k → K`, the tail `2 * q - 1` blinded quotient
slices evaluated at `xs` are **perfectly uniform** on `Fin (2 * q - 1) → Fin k → K`
(while slice `0` is uniquely fixed by the verifier's recombination equation
`eval_blindedQuotientSlice_zero`). -/
theorem quotient_slices_uniform_of_telescoping [Fintype K] [DecidableEq K]
    (n q : ℕ) (hq : 1 ≤ q) (c : Fin (2 * q) → K[X]) {b k : ℕ} (hkb : k ≤ b)
    {xs : Fin k → K} (hxs : Function.Injective xs) :
    IsUniformPushforward
      (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        fun j : Fin (2 * q - 1) => fun i : Fin k =>
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval (xs i)) := by
  have heq :
      (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        fun j : Fin (2 * q - 1) => fun i : Fin k =>
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval (xs i)) =
      (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        (fun j : Fin (2 * q - 1) => fun i : Fin k =>
          (c ⟨j.val + 1, by omega⟩).eval (xs i)) + quotientTailLin n q b k xs ρ) := by
    funext ρ j i
    simp only [Pi.add_apply, blindedQuotientSlice, quotientTailLin, LinearMap.coe_mk,
      AddHom.coe_mk, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, quotientShiftPoly, j.isLt, ↓reduceDIte, eval_add, eval_sub,
      eval_mul, eval_pow, eval_X]
    split_ifs with h <;> simp [sub_eq_add_neg, add_assoc]
  rw [heq]
  exact isUniformPushforward_of_linear_surj (quotientTailLin n q b k xs)
    (quotientTailLin_surjective n q hkb hxs) _

end QuotientBlinding

/-! ## Section 5: Masked-LogUp Running-Sum & Cross-Circuit Boundary Hiding -/

section MaskedLogup

variable {K : Type*} [Field K]

/-- **Masked-LogUp Running-Sum Hiding (`masked_logup_hiding`):**
for any secret LogUp running-sum polynomial `φ : K[X]` on trace domain `H = {x | x ^ n = 1}`,
blinding via `φ_blind(X) = φ(X) + (X ^ n - 1) * r_φ(X)` with uniform `r_φ : Fin b → K`:
1. agrees identically with `φ` on every row of `H` (preserving every LogUp transition
   constraint and telescopic sum on `H`),
2. renders the opened LogUp trace values at ANY `k ≤ b` distinct off-domain points
   `xs : Fin k → K` disjoint from `H` **perfectly uniform** on `Fin k → K`, and
3. achieves **exact zero** total variation distance between any two secret LogUp witnesses
   `φ₁, φ₂ : K[X]`. -/
theorem masked_logup_hiding [Fintype K] [DecidableEq K]
    (n : ℕ) (φ₁ φ₂ : K[X]) {b k : ℕ} (hkb : k ≤ b)
    {xs : Fin k → K} (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    (∀ (r_φ : Fin b → K) (x : K), x ^ n = 1 → (blindPoly n φ₁ r_φ).eval x = φ₁.eval x) ∧
    IsUniformPushforward
      (fun r_φ : Fin b → K => fun i : Fin k => (blindPoly n φ₁ r_φ).eval (xs i)) ∧
    tvDist
      (fun r_φ : Fin b → K => fun i : Fin k => (blindPoly n φ₁ r_φ).eval (xs i))
      (fun r_φ : Fin b → K => fun i : Fin k => (blindPoly n φ₂ r_φ).eval (xs i)) = 0 :=
  ⟨fun r_φ _ hx => eval_blindPoly_of_mem_trace n φ₁ r_φ hx,
   eval_vec_uniform_of_blinding n φ₁ hkb hxs hdisj,
   eval_vec_tvDist_zero_of_blinding n φ₁ φ₂ hkb hxs hdisj⟩

/-- Helper: boundary-masked circuit accumulator sequence `A'_p` for `M` active circuits,
with initial accumulator `S_init`, final public accumulator `S_final`, secret interior sums
`S : Fin (M - 1) → K`, and uniform boundary masks `μ : Fin (M - 1) → K`. -/
def maskedBoundaryAcc {M : ℕ} (S_init S_final : K)
    (S μ : Fin (M - 1) → K) (p : ℕ) : K :=
  if p = 0 then S_init
  else if h : p - 1 < M - 1 then S ⟨p - 1, h⟩ + μ ⟨p - 1, h⟩
  else S_final

/-- Helper: true (unmasked) circuit accumulator sequence `S_p`. -/
def trueBoundaryAcc {M : ℕ} (S_init S_final : K)
    (S : Fin (M - 1) → K) (p : ℕ) : K :=
  if p = 0 then S_init
  else if h : p - 1 < M - 1 then S ⟨p - 1, h⟩
  else S_final

/-- Helper: boundary mask value `U_p(1)` (`μ_p` for interior boundaries `0 < p < M`, `0` at
the outer boundaries `p = 0` and `p = M`). -/
def boundaryMaskVal {M : ℕ} (μ : Fin (M - 1) → K) (p : ℕ) : K :=
  if p = 0 then 0
  else if h : p - 1 < M - 1 then μ ⟨p - 1, h⟩
  else 0

/-- **Cross-Circuit Masked-LogUp Boundary Telescoping Identity:**
subtracting `U_p(1) - U_{p-1}(1)` from the masked delta `A'_p - A'_{p-1}` recovers the
exact unmasked circuit delta `S_p - S_{p-1}` for every circuit `p < M`, so the sum across
all `M` circuits telescopes identically to `S_final - S_init`. -/
theorem masked_logup_boundary_telescoping {M : ℕ} (hM : 1 ≤ M)
    (S_init S_final : K) (S μ : Fin (M - 1) → K) :
    (∀ p < M,
      (maskedBoundaryAcc (M := M) S_init S_final S μ (p + 1) -
        maskedBoundaryAcc (M := M) S_init S_final S μ p) -
      (boundaryMaskVal (M := M) μ (p + 1) - boundaryMaskVal (M := M) μ p) =
      trueBoundaryAcc (M := M) S_init S_final S (p + 1) -
        trueBoundaryAcc (M := M) S_init S_final S p) ∧
    (∑ p ∈ Finset.range M,
      ((maskedBoundaryAcc (M := M) S_init S_final S μ (p + 1) -
        maskedBoundaryAcc (M := M) S_init S_final S μ p) -
      (boundaryMaskVal (M := M) μ (p + 1) - boundaryMaskVal (M := M) μ p))) =
      S_final - S_init := by
  have hpoint : ∀ p : ℕ,
      maskedBoundaryAcc (M := M) S_init S_final S μ p - boundaryMaskVal (M := M) μ p =
        trueBoundaryAcc (M := M) S_init S_final S p := by
    intro p
    unfold maskedBoundaryAcc boundaryMaskVal trueBoundaryAcc
    split_ifs <;> ring
  have hdelta : ∀ p < M,
      (maskedBoundaryAcc (M := M) S_init S_final S μ (p + 1) -
        maskedBoundaryAcc (M := M) S_init S_final S μ p) -
      (boundaryMaskVal (M := M) μ (p + 1) - boundaryMaskVal (M := M) μ p) =
      trueBoundaryAcc (M := M) S_init S_final S (p + 1) -
        trueBoundaryAcc (M := M) S_init S_final S p := by
    intro p _
    have h1 := hpoint (p + 1)
    have h2 := hpoint p
    linear_combination h1 - h2
  refine ⟨hdelta, ?_⟩
  rw [Finset.sum_congr rfl fun p hp => hdelta p (Finset.mem_range.mp hp)]
  rw [Finset.sum_range_sub (trueBoundaryAcc (M := M) S_init S_final S) M]
  have h0 : trueBoundaryAcc (M := M) S_init S_final S 0 = S_init := by
    simp [trueBoundaryAcc]
  have htop : trueBoundaryAcc (M := M) S_init S_final S M = S_final := by
    unfold trueBoundaryAcc
    have hM0 : M ≠ 0 := by omega
    simp [hM0]
  rw [h0, htop]

/-- **Multi-Circuit `v6-zk` Masked-LogUp Boundary Hiding (`masked_logup_boundary_hiding`):**
for `M` active circuits with secret intermediate sums `S : Fin (M - 1) → K`, uniform
masks `μ : Fin (M - 1) → K`, and committed blinded mask polynomials
`U_p(X) = U₀(p, μ_p)(X) + (X ^ n - 1) * r_U(p)(X)` (where `U₀(p, μ_p)(1) = μ_p`),
the joint distribution of:
* all published masked intermediate accumulators `A'_p = S_p + μ_p`, AND
* all opened evaluations of `U_p` at ANY `k ≤ b` distinct off-domain points `xs`
  disjoint from `H_n`
is **perfectly uniform** on `(Fin (M - 1) → K) × (Fin (M - 1) → Fin k → K)` — completely
independent of the secret intermediate sums `S`! -/
theorem masked_logup_boundary_hiding [Fintype K] [DecidableEq K]
    (n M : ℕ) (S : Fin (M - 1) → K)
    (U₀ : Fin (M - 1) → K → K[X])
    {b k : ℕ} (hkb : k ≤ b) {xs : Fin k → K}
    (hxs : Function.Injective xs) (hdisj : ∀ i : Fin k, (xs i) ^ n ≠ 1) :
    IsUniformPushforward
      (fun rand : (Fin (M - 1) → K) × (Fin (M - 1) → Fin b → K) =>
        (fun p : Fin (M - 1) => S p + rand.1 p,
         fun p : Fin (M - 1) => fun i : Fin k =>
           (blindPoly n (U₀ p (rand.1 p)) (rand.2 p)).eval (xs i))) :=
  isUniformPushforward_fiberwise
    (fun μ : Fin (M - 1) → K => fun p : Fin (M - 1) => S p + μ p)
    (fun (μ : Fin (M - 1) → K) (rU : Fin (M - 1) → Fin b → K) (p : Fin (M - 1)) (i : Fin k) =>
      (blindPoly n (U₀ p (μ p)) (rU p)).eval (xs i))
    (isUniformPushforward_of_linear_surj (LinearMap.id (R := K)) Function.surjective_id S)
    (fun μ => eval_matrix_uniform_of_blinding n (M - 1) (fun p => U₀ p (μ p)) hkb hxs hdisj)

end MaskedLogup

/-! ## Section 6: OOD Quotient Split & Multi-Arity FRI Randomizer Blinding -/

section FriRandomizerBlinding

variable {K : Type*} [Field K]

/-- Splits a degree-`< d` polynomial `R` (`d ≥ 1`) at OOD point `z` into `(R(z), R_q)`
where `R(X) = C (R(z)) + (X - C z) * R_q(X)` (`deg R_q < d - 1`). -/
noncomputable def oodQuotientCombine (d : ℕ) (_hd : 1 ≤ d) (z : K)
    (p : K × (Fin (d - 1) → K)) : Fin d → K :=
  fun j => (C p.1 + (X - C z) * polyOfFin p.2).coeff j.val

theorem polyOfFin_oodQuotientCombine (d : ℕ) (hd : 1 ≤ d) (z : K)
    (p : K × (Fin (d - 1) → K)) :
    polyOfFin (oodQuotientCombine d hd z p) = C p.1 + (X - C z) * polyOfFin p.2 := by
  refine polyOfFin_coeff_eq ?_
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hd)
  · calc ((X - C z) * polyOfFin p.2).degree
        ≤ (X - C z).degree + (polyOfFin p.2).degree := degree_mul_le _ _
      _ = (1 : WithBot ℕ) + (polyOfFin p.2).degree := by rw [degree_X_sub_C]
      _ < (1 : WithBot ℕ) + ((d - 1 : ℕ) : WithBot ℕ) :=
          WithBot.add_lt_add_left (by simp) (degree_polyOfFin_lt p.2)
      _ = (d : WithBot ℕ) := by
          norm_cast
          omega

theorem oodQuotientCombine_injective (d : ℕ) (hd : 1 ≤ d) (z : K) :
    Function.Injective (oodQuotientCombine d hd z) := by
  intro ⟨c₁, q₁⟩ ⟨c₂, q₂⟩ h
  have hpoly : C c₁ + (X - C z) * polyOfFin q₁ = C c₂ + (X - C z) * polyOfFin q₂ := by
    rw [← polyOfFin_oodQuotientCombine d hd z (c₁, q₁),
      ← polyOfFin_oodQuotientCombine d hd z (c₂, q₂), h]
  have hc : c₁ = c₂ := by
    have hev := congrArg (Polynomial.eval z) hpoly
    simpa using hev
  subst hc
  have hmul : (X - C z) * (polyOfFin q₁ - polyOfFin q₂) = 0 := by
    have hsub := add_left_cancel hpoly
    rw [mul_sub, sub_eq_zero]
    exact hsub
  have hq : polyOfFin q₁ = polyOfFin q₂ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (X_sub_C_ne_zero z))
  have hq' : q₁ = q₂ := by
    ext j
    have := congrArg (fun p : K[X] => p.coeff j.val) hq
    simpa [coeff_polyOfFin, j.isLt] using this
  rw [hq']

/-- **Exact OOD Quotient Split Equivalence:**
for `d ≥ 1` and any OOD point `z : K`, a uniform random polynomial `R` of degree `< d`
splits bijectively into independent uniform `(R(z), R_q)` with `R(X) = R(z) + (X - z) R_q(X)`. -/
noncomputable def oodQuotientSplitEquiv [Fintype K] (d : ℕ) (hd : 1 ≤ d) (z : K) :
    (Fin d → K) ≃ K × (Fin (d - 1) → K) :=
  (Equiv.ofBijective (oodQuotientCombine d hd z)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨oodQuotientCombine_injective d hd z, by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, ← pow_succ', Nat.sub_add_cancel hd]⟩)).symm

theorem oodQuotientSplitEquiv_spec [Fintype K] (d : ℕ) (hd : 1 ≤ d) (z : K) (r : Fin d → K) :
    (oodQuotientSplitEquiv d hd z r).1 = (polyOfFin r).eval z ∧
    polyOfFin r =
      C (oodQuotientSplitEquiv d hd z r).1 +
        (X - C z) * polyOfFin (oodQuotientSplitEquiv d hd z r).2 := by
  have hcomb : oodQuotientCombine d hd z (oodQuotientSplitEquiv d hd z r) = r :=
    (oodQuotientSplitEquiv d hd z).symm_apply_apply r
  have hpoly : polyOfFin r =
      C (oodQuotientSplitEquiv d hd z r).1 +
        (X - C z) * polyOfFin (oodQuotientSplitEquiv d hd z r).2 := by
    calc polyOfFin r
        = polyOfFin (oodQuotientCombine d hd z (oodQuotientSplitEquiv d hd z r)) := by
          rw [hcomb]
      _ = C (oodQuotientSplitEquiv d hd z r).1 +
            (X - C z) * polyOfFin (oodQuotientSplitEquiv d hd z r).2 :=
          polyOfFin_oodQuotientCombine d hd z _
  refine ⟨?_, hpoly⟩
  have hev := congrArg (Polynomial.eval z) hpoly
  simpa using hev.symm

/-- Decomposing coefficients of a degree-`< A * d` polynomial by residue modulo `A`. -/
def splitPolyMod (A d : ℕ) (r : Fin (A * d) → K) : Fin A → Fin d → K :=
  fun t j => r ⟨t.val + A * j.val, by
    have ht : t.val < A := t.isLt
    have hj : j.val + 1 ≤ d := j.isLt
    have hmul : A * (j.val + 1) ≤ A * d := Nat.mul_le_mul_left A hj
    linarith [Nat.mul_add A j.val 1]⟩

/-- Helper: `idx.val / A < d` for `idx : Fin (A * d)`. -/
private theorem fin_div_lt {A d : ℕ} (idx : Fin (A * d)) : idx.val / A < d :=
  Nat.div_lt_of_lt_mul (by have h := idx.isLt; linarith [mul_comm A d])

/-- Inverse recombination of `A` degree-`< d` residue slices into a degree-`< A * d` polynomial. -/
def mergePolyMod (A d : ℕ) (hA : 0 < A) (g : Fin A → Fin d → K) : Fin (A * d) → K :=
  fun idx => g ⟨idx.val % A, Nat.mod_lt _ hA⟩ ⟨idx.val / A, fin_div_lt idx⟩

/-- One `A`-ary FRI folding step with challenge `β : K`:
`foldPolyMod A d β r j = ∑_{t < A} β ^ t * r_{t + A * j}`. -/
def foldPolyMod (A d : ℕ) (β : K) (r : Fin (A * d) → K) : Fin d → K :=
  fun j => ∑ t : Fin A, β ^ t.val * splitPolyMod A d r t j

/-- One-round `A`-ary FRI decomposition of a polynomial `r` into its folded polynomial
`foldPolyMod A d β r` AND its `A - 1` sibling residue polynomials `(r_1, ..., r_{A-1})`. -/
def friStepDecomp (A d : ℕ) (β : K) (r : Fin (A * d) → K) :
    (Fin d → K) × (Fin (A - 1) → Fin d → K) :=
  (foldPolyMod A d β r, fun t => splitPolyMod A d r ⟨t.val + 1, by omega⟩)

/-- Inverse of `friStepDecomp`: uniquely reconstructs `r` from `(folded, siblings)`. -/
def friStepReconstruct (A d : ℕ) (hA : 1 ≤ A) (β : K)
    (p : (Fin d → K) × (Fin (A - 1) → Fin d → K)) : Fin (A * d) → K :=
  mergePolyMod A d (by omega) fun t j =>
    if h0 : t.val = 0 then
      p.1 j - ∑ s : Fin (A - 1), β ^ (s.val + 1) * p.2 s j
    else
      p.2 ⟨t.val - 1, by omega⟩ j

theorem friStepDecomp_left_inv (A d : ℕ) (hA : 1 ≤ A) (β : K) (r : Fin (A * d) → K) :
    friStepReconstruct A d hA β (friStepDecomp A d β r) = r := by
  ext idx
  unfold friStepReconstruct mergePolyMod friStepDecomp foldPolyMod splitPolyMod
  dsimp only
  split_ifs with h0
  · have hAeq : A = (A - 1) + 1 := by omega
    let eA : Fin ((A - 1) + 1) ≃ Fin A := finCongr hAeq.symm
    have hsum :
        ∑ t : Fin A, β ^ t.val * r ⟨t.val + A * (idx.val / A), by
          have ht : t.val < A := t.isLt
          have hj : idx.val / A + 1 ≤ d := fin_div_lt idx
          have hmul : A * (idx.val / A + 1) ≤ A * d := Nat.mul_le_mul_left A hj
          linarith [Nat.mul_add A (idx.val / A) 1]⟩ =
        r ⟨0 + A * (idx.val / A), by
          have hj : idx.val / A + 1 ≤ d := fin_div_lt idx
          have hmul : A * (idx.val / A + 1) ≤ A * d := Nat.mul_le_mul_left A hj
          linarith [Nat.mul_add A (idx.val / A) 1]⟩ +
        ∑ s : Fin (A - 1), β ^ (s.val + 1) * r ⟨s.val + 1 + A * (idx.val / A), by
          have hs : s.val + 1 < A := by omega
          have hj : idx.val / A + 1 ≤ d := fin_div_lt idx
          have hmul : A * (idx.val / A + 1) ≤ A * d := Nat.mul_le_mul_left A hj
          linarith [Nat.mul_add A (idx.val / A) 1]⟩ := by
      rw [← Equiv.sum_comp eA, Fin.sum_univ_succ]
      simp [eA]
    rw [hsum, add_sub_cancel_right]
    congr 1
    apply Fin.ext
    change 0 + A * (idx.val / A) = idx.val
    have hdiv := Nat.div_add_mod idx.val A
    omega
  · congr 1
    apply Fin.ext
    change idx.val % A - 1 + 1 + A * (idx.val / A) = idx.val
    have hdiv := Nat.div_add_mod idx.val A
    omega

theorem friStepDecomp_right_inv (A d : ℕ) (hA : 1 ≤ A) (β : K)
    (p : (Fin d → K) × (Fin (A - 1) → Fin d → K)) :
    friStepDecomp A d β (friStepReconstruct A d hA β p) = p := by
  have hmod : ∀ (t j : ℕ), t < A → (t + A * j) % A = t ∧ (t + A * j) / A = j := by
    intro t j ht
    constructor
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    · rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ht, zero_add]
  apply Prod.ext
  · ext j
    unfold friStepDecomp foldPolyMod splitPolyMod friStepReconstruct mergePolyMod
    dsimp only
    have hAeq : A = (A - 1) + 1 := by omega
    let eA : Fin ((A - 1) + 1) ≃ Fin A := finCongr hAeq.symm
    rw [← Equiv.sum_comp eA, Fin.sum_univ_succ]
    have h0mod := hmod 0 j.val (by omega)
    have h0val : (eA 0).val = 0 := rfl
    have h0term :
        β ^ (eA 0).val *
          (if h0 : ((eA 0).val + A * j.val) % A = 0 then
            p.1 ⟨((eA 0).val + A * j.val) / A, by
              have : ((eA 0).val + A * j.val) / A = j.val := by rw [h0val]; exact h0mod.2
              omega⟩ -
            ∑ s : Fin (A - 1), β ^ (s.val + 1) *
              p.2 s ⟨((eA 0).val + A * j.val) / A, by
                have : ((eA 0).val + A * j.val) / A = j.val := by rw [h0val]; exact h0mod.2
                omega⟩
          else p.2 ⟨((eA 0).val + A * j.val) % A - 1, by
              have : ((eA 0).val + A * j.val) % A = 0 := by rw [h0val]; exact h0mod.1
              omega⟩
            ⟨((eA 0).val + A * j.val) / A, by
              have : ((eA 0).val + A * j.val) / A = j.val := by rw [h0val]; exact h0mod.2
              omega⟩) =
        p.1 j - ∑ s : Fin (A - 1), β ^ (s.val + 1) * p.2 s j := by
      have hcond : ((eA 0).val + A * j.val) % A = 0 := by rw [h0val]; exact h0mod.1
      rw [dite_eq_left hcond]
      have hdiv : (⟨((eA 0).val + A * j.val) / A, by
          have : ((eA 0).val + A * j.val) / A = j.val := by rw [h0val]; exact h0mod.2
          omega⟩ : Fin d) = j := by
        apply Fin.ext; change ((eA 0).val + A * j.val) / A = j.val; rw [h0val]; exact h0mod.2
      rw [hdiv, h0val, pow_zero, one_mul]
    have htail :
        ∑ s : Fin (A - 1),
          β ^ (eA s.succ).val *
            (if h0 : ((eA s.succ).val + A * j.val) % A = 0 then
              p.1 ⟨((eA s.succ).val + A * j.val) / A, by
                have hm := hmod (s.val + 1) j.val (by omega)
                have : ((eA s.succ).val + A * j.val) / A = j.val := by simp [eA, hm.2]
                omega⟩ -
              ∑ s' : Fin (A - 1), β ^ (s'.val + 1) *
                p.2 s' ⟨((eA s.succ).val + A * j.val) / A, by
                  have hm := hmod (s.val + 1) j.val (by omega)
                  have : ((eA s.succ).val + A * j.val) / A = j.val := by simp [eA, hm.2]
                  omega⟩
            else p.2 ⟨((eA s.succ).val + A * j.val) % A - 1, by
                have hm := hmod (s.val + 1) j.val (by omega)
                have : ((eA s.succ).val + A * j.val) % A = s.val + 1 := by simp [eA, hm.1]
                omega⟩
              ⟨((eA s.succ).val + A * j.val) / A, by
                have hm := hmod (s.val + 1) j.val (by omega)
                have : ((eA s.succ).val + A * j.val) / A = j.val := by simp [eA, hm.2]
                omega⟩) =
        ∑ s : Fin (A - 1), β ^ (s.val + 1) * p.2 s j := by
      refine Finset.sum_congr rfl fun s _ => ?_
      have hval : (eA s.succ).val = s.val + 1 := rfl
      have hm := hmod (s.val + 1) j.val (by omega)
      have hne : ((eA s.succ).val + A * j.val) % A ≠ 0 := by rw [hval, hm.1]; omega
      rw [dite_eq_right hne]
      have hs1 : (⟨((eA s.succ).val + A * j.val) % A - 1, by
          have : ((eA s.succ).val + A * j.val) % A = s.val + 1 := by rw [hval]; exact hm.1
          omega⟩ : Fin (A - 1)) = s := by
        apply Fin.ext; change ((eA s.succ).val + A * j.val) % A - 1 = s.val; rw [hval, hm.1]; omega
      have hs2 : (⟨((eA s.succ).val + A * j.val) / A, by
          have : ((eA s.succ).val + A * j.val) / A = j.val := by rw [hval]; exact hm.2
          omega⟩ : Fin d) = j := by
        apply Fin.ext; change ((eA s.succ).val + A * j.val) / A = j.val; rw [hval]; exact hm.2
      rw [hs1, hs2, hval]
    rw [h0term, htail, sub_add_cancel]
  · ext t j
    unfold friStepDecomp splitPolyMod friStepReconstruct mergePolyMod
    dsimp only
    have ht : t.val + 1 < A := by have := t.isLt; omega
    have hm := hmod (t.val + 1) j.val ht
    have hne : (t.val + 1 + A * j.val) % A ≠ 0 := by omega
    rw [dite_eq_right hne]
    have ht1 : (⟨(t.val + 1 + A * j.val) % A - 1, by omega⟩ : Fin (A - 1)) = t := by
      apply Fin.ext; change (t.val + 1 + A * j.val) % A - 1 = t.val; omega
    have hj1 : (⟨(t.val + 1 + A * j.val) / A, by omega⟩ : Fin d) = j := by
      apply Fin.ext; change (t.val + 1 + A * j.val) / A = j.val; omega
    rw [ht1, hj1]

/-- **One-Round Multi-Arity FRI Folding Linear Equivalence:**
a uniform degree-`< A * d` polynomial decomposes bijectively into an independent uniform
folded polynomial `foldPolyMod A d β r` (`deg < d`) and `A - 1` independent uniform
sibling residue polynomials (`deg < d`). -/
def friStepEquiv (A d : ℕ) (hA : 1 ≤ A) (β : K) :
    (Fin (A * d) → K) ≃ (Fin d → K) × (Fin (A - 1) → Fin d → K) where
  toFun := friStepDecomp A d β
  invFun := friStepReconstruct A d hA β
  left_inv := friStepDecomp_left_inv A d hA β
  right_inv := friStepDecomp_right_inv A d hA β

theorem friStepDecomp_add (A d : ℕ) (β : K) (r₁ r₂ : Fin (A * d) → K) :
    friStepDecomp A d β (r₁ + r₂) =
      ((friStepDecomp A d β r₁).1 + (friStepDecomp A d β r₂).1,
       fun t => (friStepDecomp A d β r₁).2 t + (friStepDecomp A d β r₂).2 t) := by
  ext j
  · simp [friStepDecomp, foldPolyMod, splitPolyMod, mul_add, Finset.sum_add_distrib]
  · simp [friStepDecomp, splitPolyMod]

/-- Recursive type of multi-arity FRI sibling polynomials across all rounds of `arities`. -/
abbrev FriRoundSiblings (K : Type*) : List ℕ → ℕ → Type _
  | [], _ => PUnit
  | a :: rest, d_final =>
      (Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K) × FriRoundSiblings K rest d_final

/-- Recursive type of multi-arity FRI sibling evaluations at `q` queried cosets per round. -/
abbrev FriRoundSiblingEvals (K : Type*) : List ℕ → ℕ → Type _
  | [], _ => PUnit
  | a :: rest, q => (Fin (2 ^ a - 1) → Fin q → K) × FriRoundSiblingEvals K rest q

/-- Recursive type of per-round distinct folded query points (`q` points per round). -/
abbrev FriRoundQueryPoints (K : Type*) : List ℕ → ℕ → Type _
  | [], _ => PUnit
  | _ :: rest, q => (Fin q → K) × FriRoundQueryPoints K rest q

/-- Every round's `q` folded query points are distinct (injective). -/
def FriRoundQueryPointsInj {K : Type*} : ∀ (arities : List ℕ) (q : ℕ),
    FriRoundQueryPoints K arities q → Prop
  | [], _, _ => True
  | _ :: rest, q, (ys, rest_ys) => Function.Injective ys ∧ FriRoundQueryPointsInj rest q rest_ys

noncomputable instance instFintypeFriRoundSiblings [Fintype K] :
    ∀ (arities : List ℕ) (d_final : ℕ), Fintype (FriRoundSiblings K arities d_final)
  | [], _ => inferInstanceAs (Fintype PUnit)
  | a :: rest, d_final =>
      let _ := instFintypeFriRoundSiblings rest d_final
      inferInstanceAs (Fintype ((Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K) ×
        FriRoundSiblings K rest d_final))

instance instNonemptyFriRoundSiblings [Nonempty K] :
    ∀ (arities : List ℕ) (d_final : ℕ), Nonempty (FriRoundSiblings K arities d_final)
  | [], _ => ⟨PUnit.unit⟩
  | _ :: rest, d_final =>
      let _ := instNonemptyFriRoundSiblings rest d_final
      ⟨(fun _ _ => Classical.arbitrary K, Classical.arbitrary _)⟩

noncomputable instance instFintypeFriRoundSiblingEvals [Fintype K] :
    ∀ (arities : List ℕ) (q : ℕ), Fintype (FriRoundSiblingEvals K arities q)
  | [], _ => inferInstanceAs (Fintype PUnit)
  | a :: rest, q =>
      let _ := instFintypeFriRoundSiblingEvals rest q
      inferInstanceAs (Fintype ((Fin (2 ^ a - 1) → Fin q → K) × FriRoundSiblingEvals K rest q))

instance instNonemptyFriRoundSiblingEvals [Nonempty K] :
    ∀ (arities : List ℕ) (q : ℕ), Nonempty (FriRoundSiblingEvals K arities q)
  | [], _ => ⟨PUnit.unit⟩
  | _ :: rest, q =>
      let _ := instNonemptyFriRoundSiblingEvals rest q
      ⟨(fun _ _ => Classical.arbitrary K, Classical.arbitrary _)⟩

/-- Multi-round FRI decomposition of a degree-`< 2 ^ arities.sum * d_final` polynomial into
`(finalPoly, roundSiblings)` under folding challenges `betas : Fin arities.length → K`. -/
def friMultiDecomp : ∀ (arities : List ℕ) (d_final : ℕ),
    (Fin arities.length → K) → (Fin (2 ^ arities.sum * d_final) → K) →
      (Fin d_final → K) × FriRoundSiblings K arities d_final
  | [], d_final, _, r =>
      (fun j => r ⟨j.val, by simp⟩, PUnit.unit)
  | a :: rest, d_final, betas, r =>
      let r' : Fin (2 ^ a * (2 ^ rest.sum * d_final)) → K :=
        fun idx => r ⟨idx.val, by
          have heq : 2 ^ a * (2 ^ rest.sum * d_final) = 2 ^ (a :: rest).sum * d_final := by
            simp [List.sum_cons, pow_add, mul_assoc]
          omega⟩
      let (folded, sibs) := friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩) r'
      let (finalPoly, restSibs) :=
        friMultiDecomp rest d_final (fun i => betas ⟨i.val + 1, by simp⟩) folded
      (finalPoly, (sibs, restSibs))

/-- Evaluates every round's sibling polynomials at the corresponding queried coset points. -/
noncomputable def evalFriRoundSiblings : ∀ (arities : List ℕ) (d_final q : ℕ),
    FriRoundQueryPoints K arities q →
    FriRoundSiblings K arities d_final → FriRoundSiblingEvals K arities q
  | [], _, _, _, _ => PUnit.unit
  | _ :: rest, d_final, q, (ys, rest_ys), (sibs, restSibs) =>
      (fun t i => (polyOfFin (sibs t)).eval (ys i),
       evalFriRoundSiblings rest d_final q rest_ys restSibs)

/-- **Multi-Round FRI Decomposition Equivalence:**
`friMultiDecomp arities d_final betas` is a bijection from `Fin (2 ^ arities.sum * d_final) → K`
to `(Fin d_final → K) × FriRoundSiblings K arities d_final`. -/
def friMultiDecompEquiv : ∀ (arities : List ℕ) (d_final : ℕ) (_betas : Fin arities.length → K),
    (Fin (2 ^ arities.sum * d_final) → K) ≃
      (Fin d_final → K) × FriRoundSiblings K arities d_final
  | [], d_final, _ =>
      let castFin : Fin (2 ^ ([] : List ℕ).sum * d_final) ≃ Fin d_final :=
        finCongr (by simp)
      (Equiv.arrowCongr castFin (Equiv.refl K)).trans (Equiv.prodPUnit _).symm
  | a :: rest, d_final, betas =>
      let heq : 2 ^ (a :: rest).sum * d_final = 2 ^ a * (2 ^ rest.sum * d_final) := by
        simp [List.sum_cons, pow_add, mul_assoc]
      let eCast : (Fin (2 ^ (a :: rest).sum * d_final) → K) ≃
          (Fin (2 ^ a * (2 ^ rest.sum * d_final)) → K) :=
        Equiv.arrowCongr (finCongr heq) (Equiv.refl K)
      let eStep := friStepEquiv (K := K) (2 ^ a) (2 ^ rest.sum * d_final)
        (Nat.one_le_pow a 2 two_pos) (betas ⟨0, by simp⟩)
      let eRec := friMultiDecompEquiv rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
      let eReassoc :
          ((Fin d_final → K) × FriRoundSiblings K rest d_final) ×
            (Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K) ≃
          (Fin d_final → K) ×
            ((Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K) ×
              FriRoundSiblings K rest d_final) :=
        { toFun := fun ⟨⟨f, rs⟩, s⟩ => ⟨f, ⟨s, rs⟩⟩
          invFun := fun ⟨f, ⟨s, rs⟩⟩ => ⟨⟨f, rs⟩, s⟩
          left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
          right_inv := fun ⟨_, ⟨_, _⟩⟩ => rfl }
      eCast.trans (eStep.trans ((Equiv.prodCongr eRec (Equiv.refl _)).trans eReassoc))

theorem friMultiDecompEquiv_apply :
    ∀ (arities : List ℕ) (d_final : ℕ) (betas : Fin arities.length → K)
      (r : Fin (2 ^ arities.sum * d_final) → K),
      friMultiDecompEquiv arities d_final betas r = friMultiDecomp arities d_final betas r
  | [], _, _, _ => rfl
  | a :: rest, d_final, betas, r => by
      have ih := friMultiDecompEquiv_apply rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
        (friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
          (fun idx => r ⟨idx.val, by
            have heq : 2 ^ a * (2 ^ rest.sum * d_final) = 2 ^ (a :: rest).sum * d_final := by
              simp [List.sum_cons, pow_add, mul_assoc]
            omega⟩)).1
      change
        ((friMultiDecompEquiv rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
            (friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).1).1,
         ((friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).2,
          (friMultiDecompEquiv rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
            (friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).1).2)) =
        ((friMultiDecomp rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
            (friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).1).1,
         ((friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).2,
          (friMultiDecomp rest d_final (fun i => betas ⟨i.val + 1, by simp⟩)
            (friStepDecomp (2 ^ a) (2 ^ rest.sum * d_final) (betas ⟨0, by simp⟩)
              (fun idx => r ⟨idx.val, _⟩)).1).2))
      rw [ih]

/-- Evaluating uniformly random `FriRoundSiblings` at `q ≤ d_final` distinct folded query
points per round produces perfectly uniform `FriRoundSiblingEvals`. -/
theorem evalFriRoundSiblings_uniform [Fintype K] [DecidableEq K] :
    ∀ (arities : List ℕ) (d_final q : ℕ) (_hq : q ≤ d_final)
      (ys : FriRoundQueryPoints K arities q) (_hys : FriRoundQueryPointsInj arities q ys),
      IsUniformPushforward (evalFriRoundSiblings (K := K) arities d_final q ys)
  | [], _, _, _, _, _ => fun y => by
      cases y
      unfold unifMass
      simp
  | a :: rest, d_final, q, hq, (ys₀, rest_ys), ⟨hys₀, hrest_ys⟩ => by
      have hqd : q ≤ 2 ^ rest.sum * d_final :=
        hq.trans (Nat.le_mul_of_pos_left d_final (pow_pos two_pos _))
      have hhead : IsUniformPushforward
          (fun sibs : Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K =>
            fun t : Fin (2 ^ a - 1) => fun i : Fin q => (polyOfFin (sibs t)).eval (ys₀ i)) :=
        isUniformPushforward_pi
          (fun (_ : Fin (2 ^ a - 1)) (r : Fin (2 ^ rest.sum * d_final) → K) (i : Fin q) =>
            (polyOfFin r).eval (ys₀ i))
          (fun _ => by
            have h := isUniformPushforward_of_linear_surj
              (evalVecLin (b := 2 ^ rest.sum * d_final) ys₀) (evalVecLin_surjective hqd hys₀) 0
            simpa [evalVecLin] using h)
      exact isUniformPushforward_prod
        (fun sibs : Fin (2 ^ a - 1) → Fin (2 ^ rest.sum * d_final) → K =>
          fun t : Fin (2 ^ a - 1) => fun i : Fin q => (polyOfFin (sibs t)).eval (ys₀ i))
        (evalFriRoundSiblings (K := K) rest d_final q rest_ys)
        hhead
        (evalFriRoundSiblings_uniform rest d_final q hq rest_ys hrest_ys)

/-- **Multi-Arity FRI Randomizer Hiding (`fri_multi_round_randomizer_uniform`):**
for ANY multi-arity fold schedule `arities : List ℕ`, ANY deterministic batched witness
polynomial `W : Fin (2 ^ arities.sum * d_final) → K`, ANY folding challenges `betas`,
and ANY `q ≤ d_final` distinct folded coset query points per round, adding a uniform
randomizer `R : Fin (2 ^ arities.sum * d_final) → K` makes `(finalPoly, roundSiblingEvals)`
**perfectly uniform** and completely independent of `W`! -/
theorem fri_multi_round_randomizer_uniform [Fintype K] [DecidableEq K]
    (arities : List ℕ) (d_final q : ℕ) (hq : q ≤ d_final)
    (betas : Fin arities.length → K)
    (ys : FriRoundQueryPoints K arities q) (hys : FriRoundQueryPointsInj arities q ys)
    (W : Fin (2 ^ arities.sum * d_final) → K) :
    IsUniformPushforward
      (fun R : Fin (2 ^ arities.sum * d_final) → K =>
        let dec := friMultiDecomp arities d_final betas (W + R)
        (dec.1, evalFriRoundSiblings arities d_final q ys dec.2)) := by
  let eShift : (Fin (2 ^ arities.sum * d_final) → K) ≃ (Fin (2 ^ arities.sum * d_final) → K) :=
    Equiv.addLeft W
  let eFull := eShift.trans (friMultiDecompEquiv arities d_final betas)
  have hdecomp : IsUniformPushforward (fun R => friMultiDecomp arities d_final betas (W + R)) := by
    have heq : (fun R => friMultiDecomp arities d_final betas (W + R)) = eFull := by
      funext R
      simp [eFull, eShift, friMultiDecompEquiv_apply]
    rw [heq]
    exact isUniformPushforward_of_equiv eFull
  let hMap : (Fin d_final → K) × FriRoundSiblings K arities d_final →
      (Fin d_final → K) × FriRoundSiblingEvals K arities q :=
    fun p => (p.1, evalFriRoundSiblings arities d_final q ys p.2)
  have hMapUnif : IsUniformPushforward hMap :=
    isUniformPushforward_prod
      (id : (Fin d_final → K) → (Fin d_final → K))
      (evalFriRoundSiblings (K := K) arities d_final q ys)
      isUniformPushforward_id
      (evalFriRoundSiblings_uniform arities d_final q hq ys hys)
  intro z
  have hcomp :
      (fun R : Fin (2 ^ arities.sum * d_final) → K =>
        let dec := friMultiDecomp arities d_final betas (W + R)
        (dec.1, evalFriRoundSiblings arities d_final q ys dec.2)) =
      hMap ∘ (fun R => friMultiDecomp arities d_final betas (W + R)) := rfl
  rw [hcomp, unifMass_comp_eq_of_eq (F₂ := id)
    (fun y => (hdecomp y).trans (isUniformPushforward_id y).symm) hMap z]
  exact hMapUnif z

end FriRandomizerBlinding

end CertiFri.Zk
