import CertiFri.TensorBatching
import CertiFriProofs.Theory.ProximityGap.UniqueDecoding
import CertiFriProofs.Theory.ProximityGap.UniqueDecodingMCA
import CertiFriProofs.Theory.ProximityGap.JohnsonMCA

/-!
# Tensor FRI Batching Soundness (`TensorMCA` & `Tensor2DMCA`)

Formal soundness reduction for `FriBatching::Tensor` (`CertiFri/TensorBatching.lean`,
matching `multi-stark` `v6`'s `src/p3_adapter/fri_batching.rs`).

Given `2 ^ k` words `u : Fin (2 ^ k) → F → F` batched with `k` independent
extension-field challenges `r : Fin k → F` via the multilinear tensor basis
`tensorWeight r j = ∏ b : Fin k, if j.val.testBit b.val then r b else 1`,
this file proves:

1. **Multilinear tensor identities:**
   * `tensorWeight_succ_lo`, `tensorWeight_succ_hi`, `tensorCombine_succ`:
     one tensor challenge halves `2 ^ (k + 1)` words to `2 ^ k` pairwise lines
     `u₀ j + r_last * u₁ j`.
   * `tensorWeight_append`: 2D product `w_col[c] * w_open[o]` equals the 1D
     tensor weight of `Fin.append r_col r_open` at `c + 2 ^ kCol * o`.
   * `lt_two_pow_tensorNumChallenges`: `i < count → i < 2 ^ tensorNumChallenges count`.

2. **Unconditional batched-line MCA in the unique-decoding regime (`batchedLineMCA_ud`):**
   Using only the already-proved unconditional `curveCA_udThreshold` at `m = 2`
   and double-counting over `G × E_*`, simultaneous agreement of **any** number
   `M` of lines `u₀ j + β * u₁ j` on a common set `B ⊆ D` (`2 * e + d ≤ |D|`)
   holds outside at most `|D| + e` bad challenges `β` — **completely independent
   of `M`!**

3. **Unconditional `TensorMCA` and `Tensor2DMCA` in the unique-decoding regime:**
   * `tensorMCA_ud`: for `2 * δ + ρ ≤ 1`,
     `TensorMCA D d k (1 - δ) (k * ((1 + δ) * |D|) / |F|)`.
   * `tensor2DMCA_ud`: for `W` columns and `M` opening groups (`kCol = ⌈log₂ W⌉`,
     `kOpen = ⌈log₂ M⌉`),
     `Tensor2DMCA D d W M (1 - δ) ((kCol + kOpen) * ((1 + δ) * |D|) / |F|)`.
   This replaces the `W * M` Horner factor with `⌈log₂ W⌉ + ⌈log₂ M⌉` (exponential
   reduction in batching soundness loss for wide traces / many openings).

4. **Johnson-regime `TensorMCA` and `Tensor2DMCA` (`tensorMCA_johnson`, `tensor2DMCA_johnson`):**
   Conditional on `BatchedLineListCA F T` (correlated-agreement peeling for a
   batch of `M` lines `u₀ j + β * u₁ j`), gives the exact Johnson-regime tensor
   error `(kCol + kOpen) * (cT + L_J * (1 - θ) * |D|) / |F|`.
-/

namespace CertiFri

open Polynomial Finset

section MultilinearWeights

variable {F : Type*} [CommSemiring F]

/-- Multilinear tensor weight for index `j < 2 ^ k` and challenges `r : Fin k → F`:
`∏ b : Fin k, if j.val.testBit b.val then r b else 1`. -/
def tensorWeight {k : ℕ} (r : Fin k → F) (j : Fin (2 ^ k)) : F :=
  ∏ b : Fin k, if j.val.testBit b.val then r b else 1

/-- Tensor-batched linear combination of `2 ^ k` words on `F`. -/
def tensorCombine {k : ℕ} (r : Fin k → F) (u : Fin (2 ^ k) → F → F) (x : F) : F :=
  ∑ j : Fin (2 ^ k), tensorWeight r j * u j x

theorem tensorWeight_zero_dim (r : Fin 0 → F) (j : Fin (2 ^ 0)) :
    tensorWeight r j = 1 := by
  simp [tensorWeight]

theorem tensorCombine_zero_dim (r : Fin 0 → F) (u : Fin (2 ^ 0) → F → F) (x : F) :
    tensorCombine r u x = u ⟨0, by decide⟩ x := by
  unfold tensorCombine
  have huniv : (Finset.univ : Finset (Fin (2 ^ 0))) = {⟨0, by decide⟩} := by
    ext j; simp only [mem_univ, mem_singleton, true_iff, Fin.ext_iff]; omega
  rw [huniv, Finset.sum_singleton, tensorWeight_zero_dim, one_mul]

theorem tensorWeight_succ_lo {k : ℕ} (r : Fin (k + 1) → F) (j : Fin (2 ^ k)) :
    tensorWeight r ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos (Nat.le_succ k))⟩ =
      tensorWeight (r ∘ Fin.castSucc) j := by
  unfold tensorWeight
  rw [Fin.prod_univ_castSucc]
  have hbit : j.val.testBit k = false := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt j.isLt]
    rfl
  simp [hbit]

theorem tensorWeight_succ_hi {k : ℕ} (r : Fin (k + 1) → F) (j : Fin (2 ^ k)) :
    tensorWeight r ⟨j.val + 2 ^ k, by rw [pow_succ, mul_two]; exact Nat.add_lt_add_right j.isLt _⟩ =
      r (Fin.last k) * tensorWeight (r ∘ Fin.castSucc) j := by
  unfold tensorWeight
  rw [Fin.prod_univ_castSucc]
  have hlast : (j.val + 2 ^ k).testBit k = true := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.add_div_right _ (Nat.two_pow_pos k),
      Nat.div_eq_of_lt j.isLt]
    simp
  have hlo : ∀ b : Fin k, (j.val + 2 ^ k).testBit b.val = j.val.testBit b.val := by
    intro b
    have hpow : 2 ^ k = 2 ^ b.val * 2 ^ (k - b.val) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt b.isLt)]
    have hge1 : 1 ≤ k - b.val := Nat.sub_pos_of_lt b.isLt
    obtain ⟨t, ht⟩ : 2 ∣ 2 ^ (k - b.val) := dvd_pow_self 2 (by omega)
    have hdiv : ∀ m : ℕ, (m + 2 ^ k) / 2 ^ b.val = m / 2 ^ b.val + 2 * t := fun m => by
      rw [hpow, ht, mul_comm (2 ^ b.val), Nat.add_mul_div_right _ _ (Nat.two_pow_pos b.val)]
    have htest : ∀ m : ℕ, (m + 2 ^ k).testBit b.val = m.testBit b.val := fun m => by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv m, Nat.one_and_eq_mod_two,
        show (m / 2 ^ b.val + 2 * t) % 2 = (m / 2 ^ b.val) % 2 by omega]
    exact htest j.val
  dsimp only
  rw [Fin.val_last, hlast]
  simp only [↓reduceIte, mul_comm _ (r (Fin.last k))]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Fin.val_castSucc, hlo b]
  rfl

/-- Splitting `2 ^ (k + 1)` words along the highest bit factors out the last
challenge `r (Fin.last k)`. -/
theorem tensorCombine_succ {k : ℕ} (r : Fin (k + 1) → F) (u : Fin (2 ^ (k + 1)) → F → F) (x : F) :
    tensorCombine r u x =
      tensorCombine (r ∘ Fin.castSucc)
        (fun j y =>
          u ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos (Nat.le_succ k))⟩ y +
            r (Fin.last k) *
              u ⟨j.val + 2 ^ k, by rw [pow_succ, mul_two]; exact Nat.add_lt_add_right j.isLt _⟩ y)
        x := by
  unfold tensorCombine
  let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
    { toFun := fun s => match s with
        | .inl j => ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos (Nat.le_succ k))⟩
        | .inr j => ⟨j.val + 2 ^ k, by rw [pow_succ, mul_two]; exact Nat.add_lt_add_right j.isLt _⟩
      invFun := fun i =>
        if h : i.val < 2 ^ k then .inl ⟨i.val, h⟩
        else .inr ⟨i.val - 2 ^ k, by rw [pow_succ, mul_two] at i; omega⟩
      left_inv := fun s => by
        cases s with
        | inl j => simp [j.isLt]
        | inr j =>
          have hnot : ¬ (j.val + 2 ^ k < 2 ^ k) := by omega
          simp [hnot]
      right_inv := fun i => by
        by_cases h : i.val < 2 ^ k
        · simp [h]
        · simp only [dite_eq_right h]
          ext
          dsimp only
          omega }
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only [e, Equiv.coe_fn_mk]
  rw [tensorWeight_succ_lo, tensorWeight_succ_hi]
  ring

/-- 2D tensor factorisation: the product of column weight `w_col[j₁]` and opening
weight `w_open[j₂]` equals the 1D tensor weight of `Fin.append r₁ r₂` at
`j₁ + 2 ^ k₁ * j₂`. -/
theorem tensorWeight_append {k₁ k₂ : ℕ} (r₁ : Fin k₁ → F) (r₂ : Fin k₂ → F)
    (j₁ : Fin (2 ^ k₁)) (j₂ : Fin (2 ^ k₂)) :
    tensorWeight (Fin.append r₁ r₂)
        ⟨j₁.val + 2 ^ k₁ * j₂.val, by
          rw [pow_add]
          have h1 : j₁.val + 2 ^ k₁ * j₂.val < 2 ^ k₁ + 2 ^ k₁ * j₂.val :=
            Nat.add_lt_add_right j₁.isLt _
          have h2 : 2 ^ k₁ + 2 ^ k₁ * j₂.val = 2 ^ k₁ * (j₂.val + 1) := by ring
          have h3 : 2 ^ k₁ * (j₂.val + 1) ≤ 2 ^ k₁ * 2 ^ k₂ :=
            Nat.mul_le_mul_left _ j₂.isLt
          omega⟩ =
      tensorWeight r₁ j₁ * tensorWeight r₂ j₂ := by
  unfold tensorWeight
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun b _ => ?_
    have hbit : (j₁.val + 2 ^ k₁ * j₂.val).testBit b.val = j₁.val.testBit b.val := by
      have hpow : 2 ^ k₁ = 2 ^ b.val * 2 ^ (k₁ - b.val) := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt b.isLt)]
      have hge1 : 1 ≤ k₁ - b.val := Nat.sub_pos_of_lt b.isLt
      obtain ⟨t, ht⟩ : 2 ∣ 2 ^ (k₁ - b.val) := dvd_pow_self 2 (by omega)
      have hdiv : ∀ m₁ m₂ : ℕ, (m₁ + 2 ^ k₁ * m₂) / 2 ^ b.val = m₁ / 2 ^ b.val + 2 * t * m₂ :=
        fun m₁ m₂ => by
          rw [hpow, ht, mul_assoc, mul_comm (2 ^ b.val),
            Nat.add_mul_div_right _ _ (Nat.two_pow_pos b.val)]
      have htest : ∀ m₁ m₂ : ℕ, (m₁ + 2 ^ k₁ * m₂).testBit b.val = m₁.testBit b.val := fun m₁ m₂ => by
        have hmod : (m₁ / 2 ^ b.val + 2 * t * m₂) % 2 = (m₁ / 2 ^ b.val) % 2 := by
          rw [mul_assoc 2 t m₂]; omega
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv m₁ m₂, Nat.one_and_eq_mod_two, hmod]
      exact htest j₁.val j₂.val
    simp [Fin.append_left, hbit]
  · refine Finset.prod_congr rfl fun b _ => ?_
    have hbit : (j₁.val + 2 ^ k₁ * j₂.val).testBit (k₁ + b.val) = j₂.val.testBit b.val := by
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        pow_add, ← Nat.div_div_eq_div_mul, mul_comm (2 ^ k₁),
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos k₁), Nat.div_eq_of_lt j₁.isLt, Nat.zero_add]
    simp [Fin.append_right, hbit]

/-- `i < count → i < 2 ^ tensorNumChallenges count`. -/
theorem lt_two_pow_tensorNumChallenges {count i : ℕ} (hi : i < count) :
    i < 2 ^ Fri.tensorNumChallenges count := by
  unfold Fri.tensorNumChallenges
  split_ifs with hle
  · omega
  · have hlt : count - 1 < 2 ^ (Nat.log2 (count - 1) + 1) :=
      (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
    omega

end MultilinearWeights

/-! ## Definitions of `BatchedLineMCA`, `TensorMCA`, and `Tensor2DMCA` -/

section Defs

variable {F : Type*} [Field F] [Fintype F]

/-- Simultaneous mutual correlated agreement for `M` lines `u₀ j + β * u₁ j`
sharing a single challenge `β`: outside an `ε` fraction of `β`, whenever all
`M` lines agree with degree-`< d` polynomials on a common set `B ⊆ D` of
fraction `≥ θ`, all `2 * M` constituent words `u₀ j, u₁ j` agree with
degree-`< d` polynomials on that exact same `B`. -/
def BatchedLineMCA (D : Finset F) (d M : ℕ) (θ ε : ℝ) : Prop :=
  ∀ u₀ u₁ : Fin M → F → F,
    ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
      ∀ β ∉ bad, ∀ q : Fin M → F[X], (∀ j, (q j).degree < d) →
        ∀ B ⊆ D, θ * D.card ≤ B.card →
        (∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x) →
        ∃ v₀ v₁ : Fin M → F[X],
          (∀ j, (v₀ j).degree < d ∧ (v₁ j).degree < d) ∧
          ∀ j, ∀ x ∈ B, u₀ j x = (v₀ j).eval x ∧ u₁ j x = (v₁ j).eval x

/-- Mutual correlated agreement for `k`-challenge multilinear tensor batching of
`2 ^ k` words over Reed–Solomon codes. -/
def TensorMCA (D : Finset F) (d k : ℕ) (θ ε : ℝ) : Prop :=
  ∀ u : Fin (2 ^ k) → F → F,
    ∃ bad : Finset (Fin k → F), (bad.card : ℝ) ≤ ε * Fintype.card (Fin k → F) ∧
      ∀ r ∉ bad, ∀ p : F[X], p.degree < d → ∀ B ⊆ D, θ * D.card ≤ B.card →
        (∀ x ∈ B, tensorCombine r u x = p.eval x) →
        ∃ v : Fin (2 ^ k) → F[X], (∀ j, (v j).degree < d) ∧
          ∀ j, ∀ x ∈ B, u j x = (v j).eval x

/-- Mutual correlated agreement for 2D `col_weights ⊗ open_weights` tensor
batching (`W` columns × `M` opening groups, matching `FriBatching::Tensor` in
`multi-stark` `v6`). -/
def Tensor2DMCA (D : Finset F) (d W M : ℕ) (θ ε : ℝ) : Prop :=
  let kCol := Fri.tensorNumChallenges W
  let kOpen := Fri.tensorNumChallenges M
  ∀ u : Fin M → Fin W → F → F,
    ∃ bad : Finset ((Fin kCol → F) × (Fin kOpen → F)),
      (bad.card : ℝ) ≤ ε * Fintype.card ((Fin kCol → F) × (Fin kOpen → F)) ∧
      ∀ r ∉ bad, ∀ p : F[X], p.degree < d → ∀ B ⊆ D, θ * D.card ≤ B.card →
        (∀ x ∈ B,
          ∑ o : Fin M,
            tensorWeight r.2 ⟨o.val, lt_two_pow_tensorNumChallenges o.isLt⟩ *
              (∑ c : Fin W,
                tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩ * u o c x) =
            p.eval x) →
        ∃ v : Fin M → Fin W → F[X],
          (∀ o c, (v o c).degree < d) ∧ ∀ o c, ∀ x ∈ B, u o c x = (v o c).eval x

end Defs

/-! ## Generic induction: `BatchedLineMCA` → `TensorMCA` → `Tensor2DMCA` -/

section GenericInduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- Base case `k = 0`: a single word requires 0 challenges and has 0 batching error. -/
theorem tensorMCA_zero (D : Finset F) (d : ℕ) (θ : ℝ) :
    TensorMCA D d 0 θ 0 := by
  intro u
  refine ⟨∅, by simp, fun r _ p hp B _ _ hagree => ?_⟩
  refine ⟨fun _ => p, fun _ => hp, fun j x hx => ?_⟩
  have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
  subst hj
  have h := hagree x hx
  rwa [tensorCombine_zero_dim] at h

/-- **Inductive step (`k → k + 1`):** one tensor challenge halves `2 ^ (k + 1)`
words into `2 ^ k` lines, adding only ONE `BatchedLineMCA` error `ε₁`! -/
theorem tensorMCA_succ {D : Finset F} {d k : ℕ} {θ ε₁ ε_k : ℝ}
    (h1 : BatchedLineMCA D d (2 ^ k) θ ε₁)
    (hk : TensorMCA D d k θ ε_k) :
    TensorMCA D d (k + 1) θ (ε₁ + ε_k) := by
  classical
  intro u
  let u₀ : Fin (2 ^ k) → F → F := fun j =>
    u ⟨j.val, lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right two_pos (Nat.le_succ k))⟩
  let u₁ : Fin (2 ^ k) → F → F := fun j =>
    u ⟨j.val + 2 ^ k, by rw [pow_succ, mul_two]; exact Nat.add_lt_add_right j.isLt _⟩
  obtain ⟨bad₁, hbad₁_card, hbad₁⟩ := h1 u₀ u₁
  have hrest : ∀ β : F, ∃ badR : Finset (Fin k → F),
      (badR.card : ℝ) ≤ ε_k * Fintype.card (Fin k → F) ∧
      ∀ r' ∉ badR, ∀ p : F[X], p.degree < d → ∀ B ⊆ D, θ * D.card ≤ B.card →
        (∀ x ∈ B, tensorCombine r' (fun j y => u₀ j y + β * u₁ j y) x = p.eval x) →
        ∃ q : Fin (2 ^ k) → F[X], (∀ j, (q j).degree < d) ∧
          ∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x :=
    fun β => hk (fun j y => u₀ j y + β * u₁ j y)
  choose badR hbadR_card hbadR using hrest
  let e : (Fin (k + 1) → F) ≃ (Fin k → F) × F :=
    { toFun := fun r => (r ∘ Fin.castSucc, r (Fin.last k))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := fun r => by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc]
        · simp [Fin.snoc]
      right_inv := fun ⟨r', β⟩ => by
        ext i
        · simp [Fin.snoc]
        · simp [Fin.snoc] }
  let embR : (Σ _ : F, Fin k → F) ↪ ((Fin k → F) × F) :=
    ⟨fun p => (p.2, p.1), fun a b h => by
      rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
      simp only [Prod.mk.injEq] at h
      cases h.1; cases h.2; rfl⟩
  let badProd : Finset ((Fin k → F) × F) :=
    (univ ×ˢ bad₁) ∪ (univ.sigma badR).map embR
  refine ⟨badProd.map e.symm.toEmbedding, ?_, ?_⟩
  · have hcard_map : (badProd.map e.symm.toEmbedding).card = badProd.card := card_map _
    have hcard_union : (badProd.card : ℝ) ≤
        ((univ ×ˢ bad₁ : Finset ((Fin k → F) × F)).card : ℝ) +
          ((univ.sigma badR).card : ℝ) := by
      have hnat := card_union_le (univ ×ˢ bad₁ : Finset ((Fin k → F) × F)) ((univ.sigma badR).map embR)
      rw [card_map] at hnat
      exact_mod_cast hnat
    have h1_bound : ((univ ×ˢ bad₁ : Finset ((Fin k → F) × F)).card : ℝ) ≤
        ε₁ * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) := by
      rw [card_product, card_univ, Nat.cast_mul]
      calc (Fintype.card (Fin k → F) : ℝ) * (bad₁.card : ℝ)
          ≤ (Fintype.card (Fin k → F) : ℝ) * (ε₁ * Fintype.card F) :=
            mul_le_mul_of_nonneg_left hbad₁_card (Nat.cast_nonneg _)
        _ = ε₁ * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) := by ring
    have h2_bound : ((univ.sigma badR).card : ℝ) ≤
        ε_k * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) := by
      rw [card_sigma, Nat.cast_sum]
      calc (∑ β : F, ((badR β).card : ℝ))
          ≤ ∑ _β : F, (ε_k * Fintype.card (Fin k → F)) :=
            Finset.sum_le_sum fun β _ => hbadR_card β
        _ = (Fintype.card F : ℝ) * (ε_k * Fintype.card (Fin k → F)) := by simp
        _ = ε_k * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) := by ring
    have hcardF : (Fintype.card (Fin (k + 1) → F) : ℝ) =
        (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) := by
      rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
    rw [hcard_map, hcardF]
    calc (badProd.card : ℝ)
        ≤ ε₁ * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) +
            ε_k * (Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ) :=
          hcard_union.trans (add_le_add h1_bound h2_bound)
      _ = (ε₁ + ε_k) * ((Fintype.card (Fin k → F) : ℝ) * (Fintype.card F : ℝ)) := by ring
  · intro r hr p hp B hBD hB hagree
    have hr' : e r ∉ badProd := by
      intro hmem
      exact hr (mem_map.mpr ⟨e r, hmem, e.left_inv r⟩)
    have hnot1 : r (Fin.last k) ∉ bad₁ := by
      intro hmem
      exact hr' (mem_union_left _ (mem_product.mpr ⟨mem_univ _, hmem⟩))
    have hnotR : (r ∘ Fin.castSucc) ∉ badR (r (Fin.last k)) := by
      intro hmem
      refine hr' (mem_union_right _ (mem_map.mpr ⟨⟨r (Fin.last k), r ∘ Fin.castSucc⟩, ?_, rfl⟩))
      exact mem_sigma.mpr ⟨mem_univ _, hmem⟩
    have hagree' : ∀ x ∈ B,
        tensorCombine (r ∘ Fin.castSucc) (fun j y => u₀ j y + r (Fin.last k) * u₁ j y) x =
          p.eval x := by
      intro x hx
      rw [← tensorCombine_succ]
      exact hagree x hx
    obtain ⟨q, hq_deg, hq_ag⟩ := hbadR (r (Fin.last k)) (r ∘ Fin.castSucc) hnotR p hp B hBD hB hagree'
    obtain ⟨v₀, v₁, hv_deg, hv_ag⟩ := hbad₁ (r (Fin.last k)) hnot1 q hq_deg B hBD hB hq_ag
    refine ⟨fun i =>
        if h : i.val < 2 ^ k then v₀ ⟨i.val, h⟩
        else v₁ ⟨i.val - 2 ^ k, by rw [pow_succ, mul_two] at i; omega⟩, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs with h
      · exact (hv_deg ⟨i.val, h⟩).1
      · exact (hv_deg ⟨i.val - 2 ^ k, _⟩).2
    · intro i x hx
      dsimp only
      split_ifs with h
      · exact (hv_ag ⟨i.val, h⟩ x hx).1
      · have h2 := (hv_ag ⟨i.val - 2 ^ k, by
            have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
            have := i.isLt; omega⟩ x hx).2
        have hlt_add : i.val - 2 ^ k + 2 ^ k < 2 ^ (k + 1) := by
          have := i.isLt; omega
        have hi : (⟨i.val - 2 ^ k + 2 ^ k, hlt_add⟩ : Fin (2 ^ (k + 1))) = i := by
          ext; dsimp only; omega
        simpa only [u₁, hi] using h2

/-- **Linear-in-`k` `TensorMCA`** from uniform `BatchedLineMCA`: `k` challenges
on `2 ^ k` words incur error at most `k * ε₁`! -/
theorem tensorMCA_of_batchedLineMCA {D : Finset F} {d : ℕ} {θ ε₁ : ℝ} :
    ∀ k : ℕ, (∀ i < k, BatchedLineMCA D d (2 ^ i) θ ε₁) →
      TensorMCA D d k θ (k * ε₁)
  | 0, _ => by
    simpa using tensorMCA_zero (F := F) D d θ
  | k + 1, h => by
    have ih := tensorMCA_of_batchedLineMCA k (fun i hi => h i (Nat.lt_succ_of_lt hi))
    have hstep := tensorMCA_succ (h k (Nat.lt_succ_self k)) ih
    have heq : ε₁ + (k : ℝ) * ε₁ = ((k + 1 : ℕ) : ℝ) * ε₁ := by push_cast; ring
    rwa [heq] at hstep

omit [DecidableEq F] in
/-- **2D `col_weights ⊗ open_weights` reduction:** `TensorMCA` for `kCol + kOpen`
challenges directly yields `Tensor2DMCA` for `W` columns and `M` opening groups
with the EXACT same error `ε`! -/
theorem tensor2DMCA_of_tensorMCA {D : Finset F} {d W M : ℕ} {θ ε : ℝ}
    (ht : TensorMCA D d (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M) θ ε) :
    Tensor2DMCA D d W M θ ε := by
  classical
  let kCol := Fri.tensorNumChallenges W
  let kOpen := Fri.tensorNumChallenges M
  intro u
  let uPad : Fin (2 ^ (kCol + kOpen)) → F → F := fun idx x =>
    let c := idx.val % 2 ^ kCol
    let o := idx.val / 2 ^ kCol
    if hc : c < W then
      if ho : o < M then u ⟨o, ho⟩ ⟨c, hc⟩ x else 0
    else 0
  obtain ⟨bad, hbad_card, hbad⟩ := ht uPad
  let e : ((Fin kCol → F) × (Fin kOpen → F)) ≃ (Fin (kCol + kOpen) → F) :=
    { toFun := fun p => Fin.append p.1 p.2
      invFun := fun r => (fun i => r (Fin.castAdd kOpen i), fun j => r (Fin.natAdd kCol j))
      left_inv := fun ⟨r₁, r₂⟩ => by
        ext i
        · simp [Fin.append_left]
        · simp [Fin.append_right]
      right_inv := fun r => by
        funext i
        refine Fin.addCases (fun a => ?_) (fun b => ?_) i
        · simp [Fin.append_left]
        · simp [Fin.append_right] }
  refine ⟨bad.map e.symm.toEmbedding, ?_, ?_⟩
  · rw [card_map, Fintype.card_congr e]
    exact hbad_card
  · intro r hr p hp B hBD hB hagree
    have hnot : e r ∉ bad := fun hmem => hr (mem_map.mpr ⟨e r, hmem, e.left_inv r⟩)
    have hcomb : ∀ x,
        tensorCombine (e r) uPad x =
          ∑ o : Fin M,
            tensorWeight r.2 ⟨o.val, lt_two_pow_tensorNumChallenges o.isLt⟩ *
              (∑ c : Fin W,
                tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩ * u o c x) := by
      intro x
      unfold tensorCombine
      let idxEquiv : Fin (2 ^ kCol) × Fin (2 ^ kOpen) ≃ Fin (2 ^ (kCol + kOpen)) :=
        { toFun := fun p => ⟨p.1.val + 2 ^ kCol * p.2.val, by
            rw [pow_add]
            have h1 : p.1.val + 2 ^ kCol * p.2.val < 2 ^ kCol + 2 ^ kCol * p.2.val :=
              Nat.add_lt_add_right p.1.isLt _
            have h2 : 2 ^ kCol + 2 ^ kCol * p.2.val = 2 ^ kCol * (p.2.val + 1) := by ring
            have h3 : 2 ^ kCol * (p.2.val + 1) ≤ 2 ^ kCol * 2 ^ kOpen :=
              Nat.mul_le_mul_left _ p.2.isLt
            omega⟩
          invFun := fun idx =>
            (⟨idx.val % 2 ^ kCol, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
             ⟨idx.val / 2 ^ kCol, Nat.div_lt_of_lt_mul (lt_of_lt_of_eq idx.isLt (pow_add 2 kCol kOpen))⟩)
          left_inv := fun ⟨a, b⟩ => by
            ext
            · dsimp only
              rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
            · dsimp only
              rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos kCol), Nat.div_eq_of_lt a.isLt,
                Nat.zero_add]
          right_inv := fun idx => by
            ext; dsimp only
            rw [add_comm, Nat.div_add_mod] }
      rw [← Equiv.sum_comp idxEquiv, Fintype.sum_prod_type_right]
      have hinner : ∀ (b : Fin (2 ^ kOpen)),
          ∑ a : Fin (2 ^ kCol), tensorWeight (e r) (idxEquiv (a, b)) * uPad (idxEquiv (a, b)) x =
            if hb : b.val < M then
              tensorWeight r.2 b *
                ∑ c : Fin W, tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩ *
                  u ⟨b.val, hb⟩ c x
            else 0 := by
        intro b
        have hterm : ∀ a : Fin (2 ^ kCol),
            tensorWeight (e r) (idxEquiv (a, b)) * uPad (idxEquiv (a, b)) x =
              if ha : a.val < W then
                if hb : b.val < M then
                  tensorWeight r.2 b * (tensorWeight r.1 a * u ⟨b.val, hb⟩ ⟨a.val, ha⟩ x)
                else 0
              else 0 := by
          intro a
          have hwt : tensorWeight (e r) (idxEquiv (a, b)) = tensorWeight r.1 a * tensorWeight r.2 b :=
            tensorWeight_append r.1 r.2 a b
          have hmod : (idxEquiv (a, b)).val % 2 ^ kCol = a.val := by
            dsimp only [idxEquiv, Equiv.coe_fn_mk]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
          have hdiv : (idxEquiv (a, b)).val / 2 ^ kCol = b.val := by
            dsimp only [idxEquiv, Equiv.coe_fn_mk]
            rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos kCol), Nat.div_eq_of_lt a.isLt,
              Nat.zero_add]
          rw [hwt]
          dsimp only [uPad]
          rw [hmod, hdiv]
          split_ifs <;> ring
        simp_rw [hterm]
        by_cases hb : b.val < M
        · simp only [hb, ↓reduceDIte, Finset.mul_sum]
          have hW : W ≤ 2 ^ kCol := by
            cases W with
            | zero => exact Nat.zero_le _
            | succ w => exact lt_two_pow_tensorNumChallenges (Nat.lt_succ_self w)
          rw [← Finset.sum_subset (Finset.subset_univ (univ.filter fun a : Fin (2 ^ kCol) => a.val < W))
            (fun a _ ha => by
              simp only [mem_filter, mem_univ, true_and] at ha
              simp [ha])]
          refine Finset.sum_bij (fun a ha => ⟨a.val, (mem_filter.mp ha).2⟩)
            (fun _ _ => mem_univ _)
            (fun a₁ _ a₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
            (fun c _ => ⟨⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩,
              mem_filter.mpr ⟨mem_univ _, c.isLt⟩, rfl⟩)
            (fun a ha => by
              have hlt := (mem_filter.mp ha).2
              simp [hlt])
        · simp [hb]
      simp_rw [hinner]
      rw [← Finset.sum_subset (Finset.subset_univ (univ.filter fun b : Fin (2 ^ kOpen) => b.val < M))
        (fun b _ hb => by
          simp only [mem_filter, mem_univ, true_and] at hb
          simp [hb])]
      refine Finset.sum_bij (fun b hb => ⟨b.val, (mem_filter.mp hb).2⟩)
        (fun _ _ => mem_univ _)
        (fun b₁ _ b₂ _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun o _ => ⟨⟨o.val, lt_two_pow_tensorNumChallenges o.isLt⟩,
          mem_filter.mpr ⟨mem_univ _, o.isLt⟩, rfl⟩)
        (fun b hb => by
          have hlt := (mem_filter.mp hb).2
          simp [hlt])
    have hagree' : ∀ x ∈ B, tensorCombine (e r) uPad x = p.eval x := by
      intro x hx
      rw [hcomb x]
      exact hagree x hx
    obtain ⟨vPad, hv_deg, hv_ag⟩ := hbad (e r) hnot p hp B hBD hB hagree'
    let idxOf (o : Fin M) (c : Fin W) : Fin (2 ^ (kCol + kOpen)) :=
      ⟨c.val + 2 ^ kCol * o.val, by
        have hc : c.val < 2 ^ kCol := lt_two_pow_tensorNumChallenges c.isLt
        have ho : o.val < 2 ^ kOpen := lt_two_pow_tensorNumChallenges o.isLt
        rw [pow_add]
        have h1 : c.val + 2 ^ kCol * o.val < 2 ^ kCol + 2 ^ kCol * o.val :=
          Nat.add_lt_add_right hc _
        have h2 : 2 ^ kCol + 2 ^ kCol * o.val = 2 ^ kCol * (o.val + 1) := by ring
        have h3 : 2 ^ kCol * (o.val + 1) ≤ 2 ^ kCol * 2 ^ kOpen :=
          Nat.mul_le_mul_left _ ho
        omega⟩
    refine ⟨fun o c => vPad (idxOf o c), fun o c => hv_deg (idxOf o c), fun o c x hx => ?_⟩
    have hc : c.val < 2 ^ kCol := lt_two_pow_tensorNumChallenges c.isLt
    have hmod : (idxOf o c).val % 2 ^ kCol = c.val := by
      dsimp only [idxOf]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    have hdiv : (idxOf o c).val / 2 ^ kCol = o.val := by
      dsimp only [idxOf]
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos kCol), Nat.div_eq_of_lt hc, Nat.zero_add]
    have hpad : uPad (idxOf o c) x = u o c x := by
      dsimp only [uPad]
      rw [hmod, hdiv, dite_eq_left c.isLt, dite_eq_left o.isLt]
    rw [← hpad]
    exact hv_ag (idxOf o c) x hx

end GenericInduction

/-! ## Unconditional unique-decoding `BatchedLineMCA`, `TensorMCA`, and `Tensor2DMCA` -/

section UniqueDecodingTensor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Unconditional `BatchedLineMCA` in the unique-decoding regime (`2 * e + d ≤ |D|`),
with bad-set cardinality `≤ |D| + e` COMPLETELY INDEPENDENT of the batch size `M`!** -/
theorem batchedLineMCA_card_ud (D : Finset F) (d e M : ℕ) (he : 2 * e + d ≤ D.card)
    (u₀ u₁ : Fin M → F → F) :
    ∃ bad : Finset F, bad.card ≤ D.card + e ∧
      ∀ β ∉ bad, ∀ q : Fin M → F[X], (∀ j, (q j).degree < d) →
        ∀ B ⊆ D, D.card ≤ B.card + e →
        (∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x) →
        ∃ v₀ v₁ : Fin M → F[X],
          (∀ j, (v₀ j).degree < d ∧ (v₁ j).degree < d) ∧
          ∀ j, ∀ x ∈ B, u₀ j x = (v₀ j).eval x ∧ u₁ j x = (v₁ j).eval x := by
  classical
  let G : Finset F := univ.filter fun β =>
    ∃ (q : Fin M → F[X]) (B : Finset F),
      (∀ j, (q j).degree < d) ∧ B ⊆ D ∧ D.card ≤ B.card + e ∧
      ∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x
  by_cases hG : G.card ≤ D.card + e
  · exact ⟨G, hG, fun β hβ q hq B hBD hB hagree =>
      absurd (mem_filter.mpr ⟨mem_univ _, q, B, hq, hBD, hB, hagree⟩) hβ⟩
  · have hG_gt : D.card + e < G.card := not_le.mp hG
    -- Apply unconditional `curveCA_udThreshold` at `m = 2` to each index `j : Fin M`.
    have hpair : ∀ j : Fin M, ∃ v₀ v₁ : F[X],
        v₀.degree < d ∧ v₁.degree < d ∧
        (D.filter fun x => u₀ j x ≠ v₀.eval x ∨ u₁ j x ≠ v₁.eval x).card ≤ e := by
      intro j
      let uj : Fin 2 → F → F := ![u₀ j, u₁ j]
      have hthresh : udThreshold D.card e 2 < G.card := by
        simpa [udThreshold] using hG_gt
      have hclose : ∀ β ∈ G, ∃ p : F[X], p.degree < d ∧
          (D.filter fun x => ∑ k : Fin 2, β ^ (k : ℕ) * uj k x ≠ p.eval x).card ≤ e := by
        intro β hβ
        obtain ⟨q, B, hq, hBD, hB, hagree⟩ := (mem_filter.mp hβ).2
        refine ⟨q j, hq j, ?_⟩
        have hsub : (D.filter fun x => ∑ k : Fin 2, β ^ (k : ℕ) * uj k x ≠ (q j).eval x) ⊆ D \ B := by
          intro x hx
          rw [mem_sdiff]
          refine ⟨(mem_filter.mp hx).1, fun hxB => (mem_filter.mp hx).2 ?_⟩
          simpa [uj, Fin.sum_univ_two] using hagree j x hxB
        have hcard := card_le_card hsub
        have hsdiff := card_sdiff_add_card_eq_card hBD
        omega
      obtain ⟨v, hv_deg, hv_err⟩ := curveCA_udThreshold (F := F) D d e 2 he uj G hthresh hclose
      refine ⟨v 0, v 1, hv_deg 0, hv_deg 1, ?_⟩
      refine le_trans (card_le_card ?_) hv_err
      intro x hx
      rw [mem_filter] at hx ⊢
      refine ⟨hx.1, ?_⟩
      rcases hx.2 with h0 | h1
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
    choose v₀ v₁ hv₀_deg hv₁_deg hEj using hpair
    -- Union error set across all `M` pairs.
    let E : Finset F := D.filter fun x => ∃ j : Fin M, u₀ j x ≠ (v₀ j).eval x ∨ u₁ j x ≠ (v₁ j).eval x
    -- Unique decoding forces `q j = v₀ j + β • v₁ j` whenever `(q, B)` witnesses `β`.
    have huniq : ∀ (β : F) (q : Fin M → F[X]) (B : Finset F),
        (∀ j, (q j).degree < d) → B ⊆ D → D.card ≤ B.card + e →
        (∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x) →
        ∀ j, q j = v₀ j + β • v₁ j := by
      intro β q B hq hBD hB hagree j
      have hdeg_lin : (v₀ j + β • v₁ j).degree < d := by
        refine (degree_add_le _ _).trans_lt (max_lt (hv₀_deg j) ?_)
        exact (degree_smul_le β (v₁ j)).trans_lt (hv₁_deg j)
      let Ej := D.filter fun x => u₀ j x ≠ (v₀ j).eval x ∨ u₁ j x ≠ (v₁ j).eval x
      refine eq_of_agree_of_card (f := fun x => u₀ j x + β * u₁ j x) (hq j) hdeg_lin hBD
        (sdiff_subset : D \ Ej ⊆ D) ?_ (hagree j) fun x hx => ?_
      · have hsdiff := card_sdiff_add_card_eq_card (filter_subset _ D : Ej ⊆ D)
        have hEj_le : Ej.card ≤ e := hEj j
        dsimp only [Ej] at hsdiff hEj_le ⊢
        omega
      · rw [mem_sdiff, mem_filter] at hx
        have hnot : ¬ (u₀ j x ≠ (v₀ j).eval x ∨ u₁ j x ≠ (v₁ j).eval x) :=
          fun hc => hx.2 ⟨hx.1, hc⟩
        push Not at hnot
        simp [hnot.1, hnot.2]
    -- Double-count pairs `(β, x) ∈ G × E` to prove `E.card ≤ e`.
    have hE_le : E.card ≤ e := by
      by_cases hD0 : D.card = 0
      · have : E.card ≤ D.card := card_le_card (filter_subset _ D)
        omega
      · -- For each `β ∈ G`, pick witness `(q_β, B_β)`.
        have hG_wit : ∀ β ∈ G, ∃ (q : Fin M → F[X]) (B : Finset F),
            (∀ j, (q j).degree < d) ∧ B ⊆ D ∧ D.card ≤ B.card + e ∧
            ∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x :=
          fun β hβ => (mem_filter.mp hβ).2
        let Bwit : F → Finset F := fun β =>
          if h : β ∈ G then (Classical.choose (Classical.choose_spec (hG_wit β h))) else ∅
        have hBwit_sub : ∀ β ∈ G, Bwit β ⊆ D := by
          intro β hβ
          simp only [Bwit, dite_eq_left hβ]
          exact (Classical.choose_spec (Classical.choose_spec (hG_wit β hβ))).2.1
        have hBwit_card : ∀ β ∈ G, D.card ≤ (Bwit β).card + e := by
          intro β hβ
          simp only [Bwit, dite_eq_left hβ]
          exact (Classical.choose_spec (Classical.choose_spec (hG_wit β hβ))).2.2.1
        have hBwit_ag : ∀ β ∈ G, ∀ j, ∀ x ∈ Bwit β,
            u₀ j x + β * u₁ j x = (v₀ j + β • v₁ j).eval x := by
          intro β hβ j x hx
          simp only [Bwit, dite_eq_left hβ] at hx
          have hspec := Classical.choose_spec (Classical.choose_spec (hG_wit β hβ))
          rw [← huniq β _ _ hspec.1 hspec.2.1 hspec.2.2.1 hspec.2.2.2 j]
          exact hspec.2.2.2 j x hx
        -- For each `x ∈ E`, at most 1 `β ∈ G` can satisfy `x ∈ Bwit β`.
        have hx_hits : ∀ x ∈ E, (G.filter fun β => x ∈ Bwit β).card ≤ 1 := by
          intro x hx
          obtain ⟨j, hj⟩ := (mem_filter.mp hx).2
          refine card_le_one.mpr fun β₁ h₁ β₂ h₂ => ?_
          have h1 := hBwit_ag β₁ (mem_filter.mp h₁).1 j x (mem_filter.mp h₁).2
          have h2 := hBwit_ag β₂ (mem_filter.mp h₂).1 j x (mem_filter.mp h₂).2
          simp only [eval_add, eval_smul, smul_eq_mul] at h1 h2
          by_contra hne
          have hsub : (β₁ - β₂) * (u₁ j x - (v₁ j).eval x) = 0 := by linear_combination h1 - h2
          have h1eq : u₁ j x = (v₁ j).eval x :=
            sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne))
          have h0eq : u₀ j x = (v₀ j).eval x := by linear_combination h1 - β₁ * h1eq
          rcases hj with h0 | h1'
          · exact h0 h0eq
          · exact h1' h1eq
        -- Count non-membership pairs `(β, x) ∈ G × E` with `x ∉ Bwit β`.
        have hlower : E.card * (G.card - 1) ≤ ∑ x ∈ E, (G.filter fun β => x ∉ Bwit β).card := by
          calc E.card * (G.card - 1)
              = ∑ _x ∈ E, (G.card - 1) := by simp
            _ ≤ ∑ x ∈ E, (G.filter fun β => x ∉ Bwit β).card := by
                refine sum_le_sum fun x hx => ?_
                have hsplit := card_filter_add_card_filter_not (s := G) (fun β => x ∈ Bwit β)
                have hle1 := hx_hits x hx
                omega
        have hswap : ∑ x ∈ E, (G.filter fun β => x ∉ Bwit β).card =
            ∑ β ∈ G, (E.filter fun x => x ∉ Bwit β).card := by
          simp only [card_filter]
          exact Finset.sum_comm
        have hupper : ∑ β ∈ G, (E.filter fun x => x ∉ Bwit β).card ≤ G.card * e := by
          calc ∑ β ∈ G, (E.filter fun x => x ∉ Bwit β).card
              ≤ ∑ β ∈ G, (D \ Bwit β).card := by
                refine sum_le_sum fun β _ => card_le_card fun x hx => ?_
                rw [mem_sdiff]
                exact ⟨(mem_filter.mp (mem_filter.mp hx).1).1, (mem_filter.mp hx).2⟩
            _ ≤ ∑ _β ∈ G, e := by
                refine sum_le_sum fun β hβ => ?_
                have hsdiff := card_sdiff_add_card_eq_card (hBwit_sub β hβ)
                have hBc := hBwit_card β hβ
                omega
            _ = G.card * e := by simp
        have hineq : E.card * (G.card - 1) ≤ G.card * e :=
          hlower.trans (hswap ▸ hupper)
        by_contra hgt
        have hge : e + 1 ≤ E.card := by omega
        have hmul : (e + 1) * (G.card - 1) ≤ G.card * e :=
          (Nat.mul_le_mul_right _ hge).trans hineq
        have hGge1 : 1 ≤ G.card := by omega
        -- `(e + 1) * (G.card - 1) = e * G.card + G.card - e - 1 ≤ e * G.card` forces `G.card ≤ e + 1`,
        -- contradicting `D.card + e < G.card` with `1 ≤ D.card`!
        have hlin : (e + 1) * (G.card - 1) + (e + 1) = (e + 1) * G.card := by
          rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hGge1]
        have hle_G : G.card ≤ e + 1 := by
          have : (e + 1) * G.card ≤ G.card * e + (e + 1) := by omega
          have : G.card * e + G.card ≤ G.card * e + (e + 1) := by linarith
          omega
        omega
    -- Construct the bad set of size `≤ E.card ≤ e ≤ D.card + e` by picking one
    -- witnessing index `j_x` per error point `x ∈ E`.
    let jWit : ∀ x ∈ E, Fin M := fun x hx => Classical.choose (mem_filter.mp hx).2
    have hjWit : ∀ (x : F) (hx : x ∈ E),
        u₀ (jWit x hx) x ≠ (v₀ (jWit x hx)).eval x ∨ u₁ (jWit x hx) x ≠ (v₁ (jWit x hx)).eval x :=
      fun x hx => Classical.choose_spec (mem_filter.mp hx).2
    let bad : Finset F := E.attach.biUnion fun ⟨x, hx⟩ =>
      univ.filter fun β =>
        (u₀ (jWit x hx) x - (v₀ (jWit x hx)).eval x) +
          β * (u₁ (jWit x hx) x - (v₁ (jWit x hx)).eval x) = 0
    refine ⟨bad, ?_, ?_⟩
    · calc bad.card
          ≤ ∑ p ∈ E.attach, (univ.filter fun β =>
              (u₀ (jWit p.1 p.2) p.1 - (v₀ (jWit p.1 p.2)).eval p.1) +
                β * (u₁ (jWit p.1 p.2) p.1 - (v₁ (jWit p.1 p.2)).eval p.1) = 0).card :=
            card_biUnion_le
        _ ≤ ∑ _p ∈ E.attach, 1 := by
            refine sum_le_sum fun ⟨x, hx⟩ _ => card_le_one.mpr fun β₁ h₁ β₂ h₂ => ?_
            have h1 := (mem_filter.mp h₁).2
            have h2 := (mem_filter.mp h₂).2
            by_contra hne
            have hsub : (β₁ - β₂) * (u₁ (jWit x hx) x - (v₁ (jWit x hx)).eval x) = 0 := by
              linear_combination h1 - h2
            have h1eq : u₁ (jWit x hx) x = (v₁ (jWit x hx)).eval x :=
              sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne))
            have h0eq : u₀ (jWit x hx) x = (v₀ (jWit x hx)).eval x := by
              linear_combination h1 - β₁ * h1eq
            rcases hjWit x hx with h0 | h1'
            · exact h0 h0eq
            · exact h1' h1eq
        _ = E.card := by simp
        _ ≤ e := hE_le
        _ ≤ D.card + e := Nat.le_add_left _ _
    · intro β hβ q hq B hBD hB hagree
      have hq_eq := huniq β q B hq hBD hB hagree
      refine ⟨v₀, v₁, fun j => ⟨hv₀_deg j, hv₁_deg j⟩, fun j x hx => ?_⟩
      by_contra hne
      have hxE : x ∈ E := by
        rw [mem_filter]
        refine ⟨hBD hx, j, ?_⟩
        tauto
      refine hβ (mem_biUnion.mpr ⟨⟨x, hxE⟩, mem_attach _ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
      have hag := hagree (jWit x hxE) x hx
      rw [hq_eq (jWit x hxE), eval_add, eval_smul, smul_eq_mul] at hag
      linear_combination hag

/-- Relative-distance `BatchedLineMCA` in the unique-decoding regime (`2 * δ + ρ ≤ 1`),
with error `((1 + δ) * |D|) / |F|`, **independent of batch size `M`**. -/
theorem batchedLineMCA_ud (D : Finset F) (d M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * (δ * D.card) + d ≤ D.card) :
    BatchedLineMCA D d M (1 - δ) (((1 + δ) * D.card) / Fintype.card F) := by
  let e : ℕ := ⌊δ * D.card⌋₊
  have he_le : (e : ℝ) ≤ δ * D.card := Nat.floor_le (mul_nonneg hδ (Nat.cast_nonneg _))
  have he : 2 * e + d ≤ D.card := by
    have hreal : (2 * e + d : ℝ) ≤ D.card := by linarith
    exact_mod_cast hreal
  intro u₀ u₁
  obtain ⟨bad, hbad_card, hbad⟩ := batchedLineMCA_card_ud D d e M he u₀ u₁
  refine ⟨bad, ?_, fun β hβ q hq B hBD hB hagree => hbad β hβ q hq B hBD ?_ hagree⟩
  · have hpos : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [div_mul_cancel₀ _ hpos]
    have hreal : (bad.card : ℝ) ≤ (D.card : ℝ) + (e : ℝ) := by exact_mod_cast hbad_card
    linarith
  · have hsub : (D.card - B.card : ℝ) ≤ δ * D.card := by linarith
    have hfloor : D.card - B.card ≤ e := by
      have hcast : ((D.card - B.card : ℕ) : ℝ) ≤ δ * D.card := by
        by_cases hle : B.card ≤ D.card
        · rw [Nat.cast_sub hle]; exact hsub
        · have : D.card - B.card = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle)
          rw [this, Nat.cast_zero]
          exact mul_nonneg hδ (Nat.cast_nonneg _)
      exact Nat.le_floor hcast
    omega

/-- **Unconditional unique-decoding `TensorMCA`:** `k` tensor challenges on `2 ^ k`
words incur error `k * ((1 + δ) * |D|) / |F|` (linear in `k = log₂ N`, NOT `N`). -/
theorem tensorMCA_ud (D : Finset F) (d k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * (δ * D.card) + d ≤ D.card) :
    TensorMCA D d k (1 - δ) (k * (((1 + δ) * D.card) / Fintype.card F)) :=
  tensorMCA_of_batchedLineMCA k fun i _ => batchedLineMCA_ud D d (2 ^ i) hδ hrate

/-- **Unconditional unique-decoding `Tensor2DMCA` (`FriBatching::Tensor`):**
for `W` columns and `M` opening groups (`kCol = ⌈log₂ W⌉`, `kOpen = ⌈log₂ M⌉`),
the 2D tensor batching error is `(kCol + kOpen) * ((1 + δ) * |D|) / |F|`. -/
theorem tensor2DMCA_ud (D : Finset F) (d W M : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * (δ * D.card) + d ≤ D.card) :
    Tensor2DMCA D d W M (1 - δ)
      (((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        (((1 + δ) * D.card) / Fintype.card F)) :=
  tensor2DMCA_of_tensorMCA (tensorMCA_ud D d (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M) hδ hrate)

end UniqueDecodingTensor

/-! ## Johnson-regime `TensorMCA` and `Tensor2DMCA` (conditional on `BatchedLineListCA`) -/

section JohnsonTensor

/-- **List-decoding correlated agreement (peeling step) for a batch of `M` lines
in the Johnson regime.** Analogous to `CurveListCA F T` (`JohnsonMCA.lean`),
specialized to `M` parallel lines `u₀ j + β * u₁ j` sharing one challenge `β`. -/
def BatchedLineListCA (F : Type*) [Field F] [DecidableEq F]
    (T : ℕ → ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (D : Finset F) (d A M : ℕ), D.card * (d - 1) < A ^ 2 →
    ∀ (u₀ u₁ : Fin M → F → F) (L : Finset (Fin M → F[X] × F[X])) (G : Finset F),
      (∀ v ∈ L, (∀ j, (v j).1.degree < d ∧ (v j).2.degree < d) ∧
        A ≤ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x).card) →
      T D.card d A M < G.card →
      (∀ β ∈ G, ∃ (q : Fin M → F[X]) (B : Finset F),
        (∀ j, (q j).degree < d) ∧ B ⊆ D ∧ A ≤ B.card ∧
        (∀ v ∈ L, ∃ j, q j ≠ (v j).1 + β • (v j).2) ∧
        ∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x) →
      ∃ v : Fin M → F[X] × F[X], v ∉ L ∧
        (∀ j, (v j).1.degree < d ∧ (v j).2.degree < d) ∧
        A ≤ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x).card

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Convert a pair-tuple `Fin M → F[X] × F[X]` to a flat `Fin (2 * M) → F[X]`
tuple so the interleaved Johnson list-size bound (`card_correlatedTuples_le_johnson`)
applies directly. -/
private def flattenPairs {α : Type*} {M : ℕ} (f : Fin M → α × α) : Fin (2 * M) → α :=
  fun i =>
    if h : i.val < M then (f ⟨i.val, h⟩).1
    else (f ⟨i.val - M, by omega⟩).2

private theorem flattenPairs_injective {α : Type*} {M : ℕ} :
    Function.Injective (flattenPairs (α := α) (M := M)) := by
  intro f g h
  funext j
  ext
  · have h1 := congrFun h ⟨j.val, by omega⟩
    simpa [flattenPairs, j.isLt] using h1
  · have h2 := congrFun h ⟨j.val + M, by omega⟩
    have hnot : ¬ (j.val + M < M) := by omega
    simpa [flattenPairs, hnot] using h2

omit [Fintype F] in
private theorem pairAgreeSet_eq_tupleAgreeSet (D : Finset F) {M : ℕ}
    (u₀ u₁ : Fin M → F → F) (v : Fin M → F[X] × F[X]) :
    (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x) =
      tupleAgreeSet D (flattenPairs fun j => (u₀ j, u₁ j)) (flattenPairs v) := by
  ext x
  simp only [mem_filter, tupleAgreeSet]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i => ?_⟩
    dsimp only [flattenPairs]
    split_ifs with hi
    · exact (h ⟨i.val, hi⟩).1
    · exact (h ⟨i.val - M, by omega⟩).2
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun j => ⟨?_, ?_⟩⟩
    · have h1 := h ⟨j.val, by omega⟩
      simpa [flattenPairs, j.isLt] using h1
    · have h2 := h ⟨j.val + M, by omega⟩
      have hnot : ¬ (j.val + M < M) := by omega
      simpa [flattenPairs, hnot] using h2

omit [Fintype F] in
/-- Any family of correlated `M`-pairs agreeing on `≥ A` points above the Johnson
radius has size at most `johnsonListBound D.card d A` (independent of `M`!). -/
theorem card_correlatedPairs_le_johnson {D : Finset F} {d A M : ℕ}
    (hJ : D.card * (d - 1) < A ^ 2) {u₀ u₁ : Fin M → F → F}
    {L : Finset (Fin M → F[X] × F[X])}
    (hdeg : ∀ v ∈ L, ∀ j, (v j).1.degree < d ∧ (v j).2.degree < d)
    (hag : ∀ v ∈ L, A ≤ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x).card) :
    L.card ≤ johnsonListBound D.card d A := by
  let emb : (Fin M → F[X] × F[X]) ↪ (Fin (2 * M) → F[X]) :=
    ⟨flattenPairs, flattenPairs_injective⟩
  have hbound := card_correlatedTuples_le_johnson (D := D) (d := d) (A := A) (m := 2 * M)
    hJ (u := flattenPairs fun j => (u₀ j, u₁ j)) (L := L.map emb)
    (fun w hw => by
      obtain ⟨v, hvL, rfl⟩ := mem_map.mp hw
      intro i
      dsimp only [emb, Function.Embedding.coeFn_mk, flattenPairs]
      split_ifs with hi
      · exact (hdeg v hvL ⟨i.val, hi⟩).1
      · exact (hdeg v hvL ⟨i.val - M, by omega⟩).2)
    (fun w hw => by
      obtain ⟨v, hvL, rfl⟩ := mem_map.mp hw
      dsimp only [emb, Function.Embedding.coeFn_mk]
      rw [← pairAgreeSet_eq_tupleAgreeSet D u₀ u₁ v]
      exact hag v hvL)
  rwa [card_map] at hbound

/-- Peeling induction for `BatchedLineListCA`. -/
private noncomputable def uncoveredLineParams (D : Finset F) (d A M : ℕ)
    (u₀ u₁ : Fin M → F → F) (L : Finset (Fin M → F[X] × F[X])) : Finset F := by
  classical
  exact univ.filter fun β =>
    ∃ (q : Fin M → F[X]) (B : Finset F),
      (∀ j, (q j).degree < d) ∧ B ⊆ D ∧ A ≤ B.card ∧
      (∀ v ∈ L, ∃ j, q j ≠ (v j).1 + β • (v j).2) ∧
      ∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x

private theorem exists_peeled_line_list {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : BatchedLineListCA F T)
    (D : Finset F) (d A M : ℕ) (hJ : D.card * (d - 1) < A ^ 2) (u₀ u₁ : Fin M → F → F) :
    ∀ (k : ℕ) (L : Finset (Fin M → F[X] × F[X])),
      (∀ v ∈ L, (∀ j, (v j).1.degree < d ∧ (v j).2.degree < d) ∧
        A ≤ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x).card) →
      johnsonListBound D.card d A - L.card ≤ k →
      ∃ L' : Finset (Fin M → F[X] × F[X]),
        (∀ v ∈ L', (∀ j, (v j).1.degree < d ∧ (v j).2.degree < d) ∧
          A ≤ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x).card) ∧
        L'.card ≤ johnsonListBound D.card d A ∧
        (uncoveredLineParams D d A M u₀ u₁ L').card ≤ T D.card d A M := by
  classical
  intro k
  induction k with
  | zero =>
    intro L hL hrem
    have hLb := card_correlatedPairs_le_johnson hJ (fun v hv => (hL v hv).1) (fun v hv => (hL v hv).2)
    by_cases hG : (uncoveredLineParams D d A M u₀ u₁ L).card ≤ T D.card d A M
    · exact ⟨L, hL, hLb, hG⟩
    · obtain ⟨v, hv_not, hv_deg, hv_ag⟩ :=
        hca D d A M hJ u₀ u₁ L (uncoveredLineParams D d A M u₀ u₁ L) hL (not_le.mp hG) fun β hβ => by
          simpa [uncoveredLineParams] using hβ
      have hL1 : ∀ w ∈ insert v L, (∀ j, (w j).1.degree < d ∧ (w j).2.degree < d) ∧
          A ≤ (D.filter fun x => ∀ j, u₀ j x = (w j).1.eval x ∧ u₁ j x = (w j).2.eval x).card := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hwL
        · exact ⟨hv_deg, hv_ag⟩
        · exact hL w hwL
      have hL1b := card_correlatedPairs_le_johnson hJ (fun w hw => (hL1 w hw).1) (fun w hw => (hL1 w hw).2)
      rw [card_insert_of_notMem hv_not] at hL1b
      omega
  | succ k ih =>
    intro L hL hrem
    have hLb := card_correlatedPairs_le_johnson hJ (fun v hv => (hL v hv).1) (fun v hv => (hL v hv).2)
    by_cases hG : (uncoveredLineParams D d A M u₀ u₁ L).card ≤ T D.card d A M
    · exact ⟨L, hL, hLb, hG⟩
    · obtain ⟨v, hv_not, hv_deg, hv_ag⟩ :=
        hca D d A M hJ u₀ u₁ L (uncoveredLineParams D d A M u₀ u₁ L) hL (not_le.mp hG) fun β hβ => by
          simpa [uncoveredLineParams] using hβ
      have hL1 : ∀ w ∈ insert v L, (∀ j, (w j).1.degree < d ∧ (w j).2.degree < d) ∧
          A ≤ (D.filter fun x => ∀ j, u₀ j x = (w j).1.eval x ∧ u₁ j x = (w j).2.eval x).card := by
        intro w hw
        rcases mem_insert.mp hw with rfl | hwL
        · exact ⟨hv_deg, hv_ag⟩
        · exact hL w hwL
      have hcard1 : (insert v L).card = L.card + 1 := card_insert_of_notMem hv_not
      exact ih (insert v L) hL1 (by omega)

/-- **Johnson-regime `BatchedLineMCA`** from `BatchedLineListCA F T`:
the bad set has size at most `T |D| d A M + L_J * (|D| - A)`. -/
theorem batchedLineMCA_of_batchedLineListCA {T : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hca : BatchedLineListCA F T) (D : Finset F) (d A M : ℕ)
    (hJ : D.card * (d - 1) < A ^ 2) (u₀ u₁ : Fin M → F → F) :
    ∃ bad : Finset F, bad.card ≤ T D.card d A M + johnsonListBound D.card d A * (D.card - A) ∧
      ∀ β ∉ bad, ∀ q : Fin M → F[X], (∀ j, (q j).degree < d) →
        ∀ B ⊆ D, A ≤ B.card →
        (∀ j, ∀ x ∈ B, u₀ j x + β * u₁ j x = (q j).eval x) →
        ∃ v₀ v₁ : Fin M → F[X],
          (∀ j, (v₀ j).degree < d ∧ (v₁ j).degree < d) ∧
          ∀ j, ∀ x ∈ B, u₀ j x = (v₀ j).eval x ∧ u₁ j x = (v₁ j).eval x := by
  classical
  obtain ⟨L, hL, hLb, hG⟩ := exists_peeled_line_list hca D d A M hJ u₀ u₁
    (johnsonListBound D.card d A) ∅ (by simp) (by simp)
  -- For each `v ∈ L` and each disagreement point `x ∈ D \ agree(v)`, pick one
  -- witnessing `j` where `u₀ j x ≠ (v j).1 x ∨ u₁ j x ≠ (v j).2 x` (at most 1 root `β`!).
  let disSet (v : Fin M → F[X] × F[X]) : Finset F :=
    D.filter fun x => ∃ j : Fin M, u₀ j x ≠ (v j).1.eval x ∨ u₁ j x ≠ (v j).2.eval x
  let spur (v : Fin M → F[X] × F[X]) : Finset F :=
    (disSet v).attach.biUnion fun ⟨x, hx⟩ =>
      let j := Classical.choose (mem_filter.mp hx).2
      univ.filter fun β => (u₀ j x - (v j).1.eval x) + β * (u₁ j x - (v j).2.eval x) = 0
  let bad : Finset F := uncoveredLineParams D d A M u₀ u₁ L ∪ L.biUnion spur
  refine ⟨bad, ?_, ?_⟩
  · have hspur : ∀ v ∈ L, (spur v).card ≤ D.card - A := by
      intro v hv
      have hcard_dis : (disSet v).card ≤ D.card - A := by
        have hcomp : disSet v = D \ (D.filter fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x) := by
          ext x
          simp only [disSet, mem_filter, mem_sdiff, not_and, not_forall]
          constructor
          · rintro ⟨hx, j, hj⟩
            exact ⟨hx, fun _ => ⟨j, by tauto⟩⟩
          · rintro ⟨hx, h⟩
            obtain ⟨j, hj⟩ := h hx
            exact ⟨hx, j, by tauto⟩
        rw [hcomp]
        have hsdiff := card_sdiff_add_card_eq_card
          (filter_subset (fun x => ∀ j, u₀ j x = (v j).1.eval x ∧ u₁ j x = (v j).2.eval x) D)
        have hag := (hL v hv).2
        omega
      calc (spur v).card
          ≤ ∑ p ∈ (disSet v).attach, (univ.filter fun β =>
              let j := Classical.choose (mem_filter.mp p.2).2
              (u₀ j p.1 - (v j).1.eval p.1) + β * (u₁ j p.1 - (v j).2.eval p.1) = 0).card :=
            card_biUnion_le
        _ ≤ ∑ _p ∈ (disSet v).attach, 1 := by
            refine sum_le_sum fun ⟨x, hx⟩ _ => card_le_one.mpr fun β₁ h₁ β₂ h₂ => ?_
            let j := Classical.choose (mem_filter.mp hx).2
            have hj : u₀ j x ≠ (v j).1.eval x ∨ u₁ j x ≠ (v j).2.eval x :=
              Classical.choose_spec (mem_filter.mp hx).2
            have h1 := (mem_filter.mp h₁).2
            have h2 := (mem_filter.mp h₂).2
            by_contra hne
            have hsub : (β₁ - β₂) * (u₁ j x - (v j).2.eval x) = 0 := by linear_combination h1 - h2
            have h1eq : u₁ j x = (v j).2.eval x :=
              sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne))
            have h0eq : u₀ j x = (v j).1.eval x := by linear_combination h1 - β₁ * h1eq
            rcases hj with h0 | h1'
            · exact h0 h0eq
            · exact h1' h1eq
        _ = (disSet v).card := by simp
        _ ≤ D.card - A := hcard_dis
    calc bad.card
        ≤ (uncoveredLineParams D d A M u₀ u₁ L).card + (L.biUnion spur).card := card_union_le _ _
      _ ≤ T D.card d A M + ∑ v ∈ L, (spur v).card := Nat.add_le_add hG card_biUnion_le
      _ ≤ T D.card d A M + ∑ _v ∈ L, (D.card - A) := Nat.add_le_add_left (sum_le_sum hspur) _
      _ = T D.card d A M + L.card * (D.card - A) := by simp
      _ ≤ T D.card d A M + johnsonListBound D.card d A * (D.card - A) :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hLb) _
  · intro β hβ q hq B hBD hB hagree
    have hnot_uncov : β ∉ uncoveredLineParams D d A M u₀ u₁ L :=
      fun h => hβ (mem_union_left _ h)
    have hcov : ∃ v ∈ L, ∀ j, q j = (v j).1 + β • (v j).2 := by
      by_contra hnone
      push Not at hnone
      exact hnot_uncov (mem_filter.mpr ⟨mem_univ _, q, B, hq, hBD, hB, hnone, hagree⟩)
    obtain ⟨v, hvL, hqv⟩ := hcov
    refine ⟨fun j => (v j).1, fun j => (v j).2, (hL v hvL).1, fun j x hx => ?_⟩
    by_contra hne
    have hxdis : x ∈ disSet v := by
      rw [mem_filter]
      exact ⟨hBD hx, j, by tauto⟩
    refine hβ (mem_union_right _ (mem_biUnion.mpr ⟨v, hvL,
      mem_biUnion.mpr ⟨⟨x, hxdis⟩, mem_attach _ _, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩⟩))
    let jw := Classical.choose (mem_filter.mp hxdis).2
    have hag := hagree jw x hx
    rw [hqv jw, eval_add, eval_smul, smul_eq_mul] at hag
    linear_combination hag

/-- Relative-agreement Johnson `TensorMCA` under `BatchedLineListCA F T`:
for `ρ < θ ^ 2`, `0 < θ ≤ 1`, and `T |D| d ⌈θ |D|⌉₊ (2^i) ≤ cT`,
gives `TensorMCA D d k θ (k * (cT + ((θ - ρ) / (θ^2 - ρ)) * ((1 - θ) * |D|)) / |F|)`. -/
theorem tensorMCA_johnson {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : BatchedLineListCA F T)
    (D : Finset F) (hD : D.Nonempty) (d k : ℕ) {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (d : ℝ) / D.card < θ ^ 2)
    (hT : ∀ i < k, (T D.card d ⌈θ * D.card⌉₊ (2 ^ i) : ℝ) ≤ cT) :
    TensorMCA D d k θ
      ((k : ℝ) * ((cT + ((θ - (d : ℝ) / D.card) / (θ ^ 2 - (d : ℝ) / D.card)) *
          ((1 - θ) * D.card)) / Fintype.card F)) := by
  have hDpos : (0 : ℝ) < D.card := Nat.cast_pos.mpr hD.card_pos
  let A : ℕ := ⌈θ * D.card⌉₊
  have hA_ge : θ * D.card ≤ A := Nat.le_ceil _
  have hJ : D.card * (d - 1) < A ^ 2 := by
    have h1 : ((D.card * (d - 1) : ℕ) : ℝ) < ((A ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      have hdm : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
      have hgap' : (d : ℝ) * D.card < θ ^ 2 * (D.card : ℝ) ^ 2 := by
        have := (div_lt_iff₀ hDpos).mp hgap
        nlinarith
      have hsq : θ ^ 2 * (D.card : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (mul_nonneg hθ0.le hDpos.le) hA_ge 2
      have hdm' : (D.card : ℝ) * ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) * D.card := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hdm hDpos.le
      linarith
    exact_mod_cast h1
  have hLJ : (johnsonListBound D.card d A : ℝ) ≤
      (θ - (d : ℝ) / D.card) / (θ ^ 2 - (d : ℝ) / D.card) :=
    johnsonListBound_le_rel hD.card_pos hθ0 hθ1
      (by rw [div_mul_cancel₀ _ hDpos.ne']) hgap hA_ge
  refine tensorMCA_of_batchedLineMCA k fun i hi => ?_
  intro u₀ u₁
  obtain ⟨bad, hbad_card, hbad⟩ := batchedLineMCA_of_batchedLineListCA hca D d A (2 ^ i) hJ u₀ u₁
  refine ⟨bad, ?_, fun β hβ q hq B hBD hB hagree =>
    hbad β hβ q hq B hBD (by exact_mod_cast Nat.ceil_le.mpr hB) hagree⟩
  have hposF : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [div_mul_cancel₀ _ hposF]
  have hDA : ((D.card - A : ℕ) : ℝ) ≤ (1 - θ) * D.card := by
    by_cases hle : A ≤ D.card
    · rw [Nat.cast_sub hle]; linarith
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hle), Nat.cast_zero]
      exact mul_nonneg (by linarith) hDpos.le
  have hLJ_nn : 0 ≤ (θ - (d : ℝ) / D.card) / (θ ^ 2 - (d : ℝ) / D.card) := by
    have hnum : 0 ≤ θ - (d : ℝ) / D.card := by
      have hsq : θ ^ 2 ≤ θ := by nlinarith
      linarith
    have hden : 0 < θ ^ 2 - (d : ℝ) / D.card := by linarith
    exact div_nonneg hnum hden.le
  have hreal : (bad.card : ℝ) ≤
      (T D.card d A (2 ^ i) : ℝ) + (johnsonListBound D.card d A : ℝ) * ((D.card - A : ℕ) : ℝ) := by
    exact_mod_cast hbad_card
  have hmul : (johnsonListBound D.card d A : ℝ) * ((D.card - A : ℕ) : ℝ) ≤
      ((θ - (d : ℝ) / D.card) / (θ ^ 2 - (d : ℝ) / D.card)) * ((1 - θ) * D.card) :=
    mul_le_mul hLJ hDA (Nat.cast_nonneg _) hLJ_nn
  linarith [hT i hi]

/-- **Johnson-regime `Tensor2DMCA` (`FriBatching::Tensor`)** for `W` columns and `M`
opening groups under `BatchedLineListCA F T`. -/
theorem tensor2DMCA_johnson {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : BatchedLineListCA F T)
    (D : Finset F) (hD : D.Nonempty) (d W M : ℕ) {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (d : ℝ) / D.card < θ ^ 2)
    (hT : ∀ i < Fri.tensorNumChallenges W + Fri.tensorNumChallenges M,
      (T D.card d ⌈θ * D.card⌉₊ (2 ^ i) : ℝ) ≤ cT) :
    Tensor2DMCA D d W M θ
      (((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        ((cT + ((θ - (d : ℝ) / D.card) / (θ ^ 2 - (d : ℝ) / D.card)) *
          ((1 - θ) * D.card)) / Fintype.card F)) :=
  tensor2DMCA_of_tensorMCA (tensorMCA_johnson hca D hD d _ hθ0 hθ1 hgap hT)

end JohnsonTensor

end CertiFri
