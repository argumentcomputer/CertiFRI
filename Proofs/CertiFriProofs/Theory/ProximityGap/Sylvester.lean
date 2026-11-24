import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Basic

/-!
# Explicit Sylvester Matrix & Resultant Toolkit (`Sylvester`)

Self-contained Sylvester matrix, Bézout identity, non-vanishing under
coprimality, specialization, and coefficient degree bounds over an arbitrary
commutative ring `R`:

* `sylvesterMatrix m n f g`: the `(m + n) × (m + n)` Sylvester matrix whose
  columns encode `f, X f, …, X^(n-1) f, g, X g, …, X^(m-1) g`.
* `sylvesterDet m n f g`: determinant of `sylvesterMatrix m n f g`.
* `sylvester_bezout`: explicit Bézout polynomials `U, V : R[X]` with
  `U.natDegree < n`, `V.natDegree < m`, and `U * f + V * g = C (sylvesterDet m n f g)`,
  constructed directly from the `0`-th column of `Matrix.adjugate`.
* `sylvesterDet_ne_zero_of_isCoprime`: over a field `K`, if `f.natDegree = m ≥ 1`,
  `g.natDegree ≤ n` (`n ≥ 1`), and `IsCoprime f g`, then `sylvesterDet m n f g ≠ 0`.
* `map_sylvesterDet`: ring-homomorphism functoriality of `sylvesterDet`.
* `sylvesterDet_eq_zero_of_common_root`: if `f.eval y = 0` and `g.eval y = 0`,
  then `sylvesterDet m n f g = 0`.
* `natDegree_sylvesterDet_le` and `sylvester_bezout_deg_le`: exact degree bounds
  over a polynomial ring `S[Z]` when coefficients of `f` have degree `≤ B_f` and
  coefficients of `g` have degree `≤ B_g`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

namespace CertiFri

namespace Sylvester

open Polynomial Finset Matrix

section Defs

variable {R : Type*} [CommRing R]

/-- The `(m + n) × (m + n)` Sylvester matrix of `f, g : R[X]`:
* column `j < n` holds the coefficients of `X^j * f`;
* column `n ≤ j` holds the coefficients of `X^(j - n) * g`. -/
noncomputable def sylvesterMatrix (m n : ℕ) (f g : R[X]) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.of fun i j =>
    if j.val < n then
      if j.val ≤ i.val then f.coeff (i.val - j.val) else 0
    else
      if j.val - n ≤ i.val then g.coeff (i.val - (j.val - n)) else 0

/-- The Sylvester resultant determinant `det (sylvesterMatrix m n f g) : R`. -/
noncomputable def sylvesterDet (m n : ℕ) (f g : R[X]) : R :=
  (sylvesterMatrix m n f g).det

/-- Polynomial `U` of degree `< n` extracted from the first `n` entries of `w`. -/
noncomputable def vecToU (m n : ℕ) (w : Fin (m + n) → R) : R[X] :=
  ∑ k : Fin n, C (w ⟨k.val, by omega⟩) * X ^ k.val

/-- Polynomial `V` of degree `< m` extracted from the last `m` entries of `w`. -/
noncomputable def vecToV (m n : ℕ) (w : Fin (m + n) → R) : R[X] :=
  ∑ k : Fin m, C (w ⟨n + k.val, by omega⟩) * X ^ k.val

theorem coeff_vecToU (m n : ℕ) (w : Fin (m + n) → R) (k : ℕ) :
    (vecToU m n w).coeff k = if h : k < n then w ⟨k, by omega⟩ else 0 := by
  unfold vecToU
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : k < n
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hne
      have : k ≠ b.val := fun heq => hne (Fin.ext heq.symm)
      simp [this]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro b _
    have : k ≠ b.val := by omega
    simp [this]

theorem coeff_vecToV (m n : ℕ) (w : Fin (m + n) → R) (k : ℕ) :
    (vecToV m n w).coeff k = if h : k < m then w ⟨n + k, by omega⟩ else 0 := by
  unfold vecToV
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  by_cases h : k < m
  · rw [dite_eq_left h, Finset.sum_eq_single ⟨k, h⟩]
    · simp
    · intro b _ hne
      have : k ≠ b.val := fun heq => hne (Fin.ext heq.symm)
      simp [this]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [dite_eq_right h, Finset.sum_eq_zero]
    intro b _
    have : k ≠ b.val := by omega
    simp [this]

theorem natDegree_vecToU_lt {m n : ℕ} (hn : 1 ≤ n) (w : Fin (m + n) → R) :
    (vecToU m n w).natDegree < n := by
  have hle : (vecToU m n w).natDegree ≤ n - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_X_pow_le k.val).trans (by omega))
  omega

theorem natDegree_vecToV_lt {m n : ℕ} (hm : 1 ≤ m) (w : Fin (m + n) → R) :
    (vecToV m n w).natDegree < m := by
  have hle : (vecToV m n w).natDegree ≤ m - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      ((Polynomial.natDegree_X_pow_le k.val).trans (by omega))
  omega

/-- Matrix-vector multiplication by `sylvesterMatrix m n f g` computes the
coefficients `0 .. m + n - 1` of `vecToU m n w * f + vecToV m n w * g`. -/
theorem sylvesterMatrix_mulVec (m n : ℕ) (f g : R[X]) (w : Fin (m + n) → R) (i : Fin (m + n)) :
    (sylvesterMatrix m n f g).mulVec w i =
      (vecToU m n w * f + vecToV m n w * g).coeff i.val := by
  rw [Polynomial.coeff_add]
  have hU : (vecToU m n w * f).coeff i.val =
      ∑ k : Fin n, (if k.val ≤ i.val then f.coeff (i.val - k.val) else 0) *
        w ⟨k.val, by omega⟩ := by
    unfold vecToU
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    split_ifs <;> ring
  have hV : (vecToV m n w * g).coeff i.val =
      ∑ k : Fin m, (if k.val ≤ i.val then g.coeff (i.val - k.val) else 0) *
        w ⟨n + k.val, by omega⟩ := by
    unfold vecToV
    rw [Finset.sum_mul, Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    split_ifs <;> ring
  rw [hU, hV]
  unfold Matrix.mulVec dotProduct sylvesterMatrix
  simp only [Matrix.of_apply]
  have hsplit : ∀ (F : Fin (m + n) → R),
      ∑ j : Fin (m + n), F j =
        (∑ k : Fin n, F ⟨k.val, by omega⟩) + ∑ k : Fin m, F ⟨n + k.val, by omega⟩ := by
    intro F
    let e : Fin (n + m) ≃ Fin (m + n) := finCongr (Nat.add_comm n m)
    rw [← Equiv.sum_comp e F, Fin.sum_univ_add]
    rfl
  rw [hsplit]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [k.isLt]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hnot : ¬ (n + k.val < n) := by omega
    simp [hnot]

/-- When `f.natDegree ≤ m`, `g.natDegree ≤ n`, `1 ≤ m`, `1 ≤ n`, every linear
combination `vecToU m n w * f + vecToV m n w * g` has degree `< m + n`. -/
theorem coeff_vecToUV_eq_zero_of_ge {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {f g : R[X]} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (w : Fin (m + n) → R) {i : ℕ} (hi : m + n ≤ i) :
    (vecToU m n w * f + vecToV m n w * g).coeff i = 0 := by
  rw [Polynomial.coeff_add]
  have h1 : (vecToU m n w * f).coeff i = 0 := by
    by_cases hU0 : vecToU m n w = 0
    · simp [hU0]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have hU := natDegree_vecToU_lt hn w
      exact lt_of_le_of_lt Polynomial.natDegree_mul_le (by omega)
  have h2 : (vecToV m n w * g).coeff i = 0 := by
    by_cases hV0 : vecToV m n w = 0
    · simp [hV0]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have hV := natDegree_vecToV_lt hm w
      exact lt_of_le_of_lt Polynomial.natDegree_mul_le (by omega)
  rw [h1, h2, add_zero]

/-- **Explicit Sylvester Bézout identity via `Matrix.adjugate`:**
for `1 ≤ m`, `1 ≤ n`, `f.natDegree ≤ m`, `g.natDegree ≤ n`, letting
`w j = (sylvesterMatrix m n f g).adjugate j 0`, we have
`vecToU m n w * f + vecToV m n w * g = C (sylvesterDet m n f g)`. -/
theorem sylvester_bezout_explicit {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {f g : R[X]} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    let w : Fin (m + n) → R :=
      fun j => (sylvesterMatrix m n f g).adjugate j ⟨0, by omega⟩
    vecToU m n w * f + vecToV m n w * g = C (sylvesterDet m n f g) := by
  intro w
  ext i
  by_cases hi : i < m + n
  · have hmv := sylvesterMatrix_mulVec m n f g w ⟨i, hi⟩
    rw [← hmv]
    have hmul : (sylvesterMatrix m n f g).mulVec w ⟨i, hi⟩ =
        ((sylvesterMatrix m n f g) * (sylvesterMatrix m n f g).adjugate) ⟨i, hi⟩ ⟨0, by omega⟩ :=
      rfl
    rw [hmul, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hi0 : i = 0
    · subst hi0; simp [sylvesterDet]
    · have hne : (⟨i, hi⟩ : Fin (m + n)) ≠ ⟨0, by omega⟩ := fun h => hi0 (congrArg Fin.val h)
      simp [hne, Polynomial.coeff_C, hi0]
  · have hge : m + n ≤ i := Nat.le_of_not_lt hi
    rw [coeff_vecToUV_eq_zero_of_ge hm hn hf hg w hge, Polynomial.coeff_C]
    have hne : i ≠ 0 := by omega
    simp [hne]

/-- Ring-homomorphism functoriality of `sylvesterMatrix`. -/
theorem map_sylvesterMatrix {S : Type*} [CommRing S] (φ : R →+* S) (m n : ℕ) (f g : R[X]) :
    (sylvesterMatrix m n f g).map φ = sylvesterMatrix m n (f.map φ) (g.map φ) := by
  ext i j
  simp only [Matrix.map_apply, sylvesterMatrix, Matrix.of_apply]
  split_ifs <;> simp [Polynomial.coeff_map]

/-- Ring-homomorphism functoriality of `sylvesterDet`. -/
theorem map_sylvesterDet {S : Type*} [CommRing S] (φ : R →+* S) (m n : ℕ) (f g : R[X]) :
    φ (sylvesterDet m n f g) = sylvesterDet m n (f.map φ) (g.map φ) := by
  unfold sylvesterDet
  rw [RingHom.map_det]
  exact congrArg Matrix.det (map_sylvesterMatrix φ m n f g)

/-- If `f` and `g` share a root `y : R`, then `sylvesterDet m n f g = 0`. -/
theorem sylvesterDet_eq_zero_of_common_root {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {f g : R[X]} (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    {y : R} (hfy : f.eval y = 0) (hgy : g.eval y = 0) :
    sylvesterDet m n f g = 0 := by
  have hbez := sylvester_bezout_explicit hm hn hf hg
  have hev := congrArg (Polynomial.eval y) hbez
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hfy, hgy,
    mul_zero, add_zero] at hev
  exact hev.symm

end Defs

section FieldNonVanishing

variable {K : Type*} [Field K]

/-- **Non-vanishing of `sylvesterDet` under coprimality over a field `K`:**
if `f.natDegree = m ≥ 1`, `g.natDegree ≤ n` (`n ≥ 1`), and `IsCoprime f g`, then
`sylvesterDet m n f g ≠ 0`. -/
theorem sylvesterDet_ne_zero_of_isCoprime {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {f g : K[X]} (hf : f.natDegree = m) (hg : g.natDegree ≤ n) (hcop : IsCoprime f g) :
    sylvesterDet m n f g ≠ 0 := by
  unfold sylvesterDet
  set M := sylvesterMatrix m n f g
  have hinj : Function.Injective (Matrix.toLin' M) := by
    rw [injective_iff_map_eq_zero]
    intro w hmw
    have hpoly : vecToU m n w * f + vecToV m n w * g = 0 := by
      ext i
      by_cases hi : i < m + n
      · have hmv : M.mulVec w ⟨i, hi⟩ = 0 := by
          simpa [Matrix.toLin'_apply] using congrFun hmw ⟨i, hi⟩
        rw [← sylvesterMatrix_mulVec m n f g w ⟨i, hi⟩]
        exact hmv
      · exact coeff_vecToUV_eq_zero_of_ge hm hn hf.le hg w (Nat.le_of_not_lt hi)
    have hf_ne : f ≠ 0 := by
      intro hf0; rw [hf0, natDegree_zero] at hf; omega
    have hfdvd : f ∣ vecToV m n w * g := by
      refine ⟨-vecToU m n w, ?_⟩
      have h1 : vecToV m n w * g = -(vecToU m n w * f) := eq_neg_of_add_eq_zero_right hpoly
      rw [h1]; ring
    have hfdvdV : f ∣ vecToV m n w := hcop.dvd_of_dvd_mul_right hfdvd
    have hV0 : vecToV m n w = 0 := by
      by_contra hVne
      have hle := Polynomial.natDegree_le_of_dvd hfdvdV hVne
      have hlt := natDegree_vecToV_lt hm w
      omega
    have hU0 : vecToU m n w = 0 := by
      rw [hV0, zero_mul, add_zero] at hpoly
      exact (mul_eq_zero.mp hpoly).resolve_right hf_ne
    funext j
    by_cases hj : j.val < n
    · have := congrArg (fun p : K[X] => p.coeff j.val) hU0
      rw [coeff_vecToU, dite_eq_left hj, coeff_zero] at this
      exact this
    · have hsub : j.val - n < m := by omega
      have := congrArg (fun p : K[X] => p.coeff (j.val - n)) hV0
      rw [coeff_vecToV, dite_eq_left hsub, coeff_zero] at this
      have heq : (⟨n + (j.val - n), by omega⟩ : Fin (m + n)) = j := by
        ext; dsimp only; omega
      rwa [heq] at this
  have hbij : Function.Bijective (Matrix.toLin' M) :=
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  let e : (Fin (m + n) → K) ≃ₗ[K] (Fin (m + n) → K) := LinearEquiv.ofBijective _ hbij
  have hunit : IsUnit M := by
    refine ⟨⟨M, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
    · apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
      exact LinearMap.ext fun v => e.apply_symm_apply v
    · apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix']
      exact LinearMap.ext fun v => e.symm_apply_apply v
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hunit).ne_zero

end FieldNonVanishing

section DegreeBounds

variable {S : Type*} [CommRing S]

/-- Maximum coefficient `Z`-degree of a bivariate polynomial `p : (S[Z])[Y]`. -/
noncomputable def maxCoeffDeg (p : (S[X])[X]) : ℕ :=
  p.support.sup fun j => (p.coeff j).natDegree

theorem coeff_natDegree_le_maxCoeffDeg (p : (S[X])[X]) (j : ℕ) :
    (p.coeff j).natDegree ≤ maxCoeffDeg p := by
  by_cases hj : j ∈ p.support
  · exact Finset.le_sup (f := fun j' => (p.coeff j').natDegree) hj
  · have h0 : p.coeff j = 0 := by simpa [Polynomial.mem_support_iff] using hj
    rw [h0, natDegree_zero]
    exact Nat.zero_le _

/-- General determinant degree bound: if every entry in column `j` of a matrix
`M : Matrix ι ι S[Z]` has `natDegree ≤ colDeg j`, then `M.det.natDegree ≤ ∑ j, colDeg j`. -/
theorem natDegree_det_le_sum_col {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι S[X]) (colDeg : ι → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ colDeg j) :
    M.det.natDegree ≤ ∑ j : ι, colDeg j := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hsign : ((Equiv.Perm.sign σ : ℤ) • ∏ i : ι, M (σ i) i).natDegree ≤
      (∏ i : ι, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hneg
    · rw [h1, Units.val_one, one_zsmul]
    · rw [hneg, Units.val_neg, Units.val_one, neg_one_zsmul, natDegree_neg]
  refine hsign.trans ?_
  exact (Polynomial.natDegree_prod_le _ _).trans
    (Finset.sum_le_sum fun i _ => hM (σ i) i)

/-- Column-wise degree bound for `sylvesterMatrix m n f g` over `S[Z]`. -/
private theorem sylvesterMatrix_entry_natDegree_le {m n B_f B_g : ℕ}
    {f g : (S[X])[X]} (hf : ∀ k, (f.coeff k).natDegree ≤ B_f)
    (hg : ∀ k, (g.coeff k).natDegree ≤ B_g) (i j : Fin (m + n)) :
    (sylvesterMatrix m n f g i j).natDegree ≤ if j.val < n then B_f else B_g := by
  unfold sylvesterMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact hf _
  · simp
  · exact hg _
  · simp

/-- Exact degree bound on `sylvesterDet m n f g : S[Z]`:
`(sylvesterDet m n f g).natDegree ≤ n * B_f + m * B_g`. -/
theorem natDegree_sylvesterDet_le {m n B_f B_g : ℕ}
    {f g : (S[X])[X]} (hf : ∀ k, (f.coeff k).natDegree ≤ B_f)
    (hg : ∀ k, (g.coeff k).natDegree ≤ B_g) :
    (sylvesterDet m n f g).natDegree ≤ n * B_f + m * B_g := by
  unfold sylvesterDet
  have h := natDegree_det_le_sum_col (sylvesterMatrix m n f g)
    (fun j => if j.val < n then B_f else B_g)
    (sylvesterMatrix_entry_natDegree_le hf hg)
  refine h.trans_eq ?_
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < n then B_f else B_g) (m + n),
    Nat.add_comm m n, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range n, (if x < n then B_f else B_g) = n * B_f := by
    have : ∀ x ∈ Finset.range n, (if x < n then B_f else B_g) = B_f := fun x hx =>
      ite_eq_left (Finset.mem_range.mp hx)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : ∑ x ∈ Finset.range m, (if n + x < n then B_f else B_g) = m * B_g := by
    have : ∀ x ∈ Finset.range m, (if n + x < n then B_f else B_g) = B_g := fun x _ =>
      ite_eq_right (by omega)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [h1, h2]

/-- Exact degree bound on every entry of the adjugate of `sylvesterMatrix m n f g` over `S[Z]`:
each entry `adjugate j i` has `natDegree ≤ n * B_f + m * B_g`. -/
theorem natDegree_sylvesterAdjugate_le {m n B_f B_g : ℕ}
    {f g : (S[X])[X]} (hf : ∀ k, (f.coeff k).natDegree ≤ B_f)
    (hg : ∀ k, (g.coeff k).natDegree ≤ B_g) (j i : Fin (m + n)) :
    ((sylvesterMatrix m n f g).adjugate j i).natDegree ≤ n * B_f + m * B_g := by
  rw [Matrix.adjugate_apply]
  have h := natDegree_det_le_sum_col
    ((sylvesterMatrix m n f g).updateRow i (Pi.single j 1))
    (fun c => if c.val < n then B_f else B_g)
    (fun r c => by
      by_cases hr : r = i
      · subst hr
        rw [Matrix.updateRow_self]
        by_cases hcj : c = j
        · subst hcj; simp
        · simp [Pi.single_eq_of_ne hcj]
      · rw [Matrix.updateRow_ne hr]
        exact sylvesterMatrix_entry_natDegree_le hf hg r c)
  refine h.trans_eq ?_
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < n then B_f else B_g) (m + n),
    Nat.add_comm m n, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range n, (if x < n then B_f else B_g) = n * B_f := by
    have : ∀ x ∈ Finset.range n, (if x < n then B_f else B_g) = B_f := fun x hx =>
      ite_eq_left (Finset.mem_range.mp hx)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : ∑ x ∈ Finset.range m, (if n + x < n then B_f else B_g) = m * B_g := by
    have : ∀ x ∈ Finset.range m, (if n + x < n then B_f else B_g) = B_g := fun x _ =>
      ite_eq_right (by omega)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [h1, h2]

/-- Combined Sylvester Bézout + exact degree bounds over `S[Z]`. -/
theorem sylvester_bezout_deg_le {m n B_f B_g : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    {f g : (S[X])[X]} (hf_deg : f.natDegree ≤ m) (hg_deg : g.natDegree ≤ n)
    (hf : ∀ k, (f.coeff k).natDegree ≤ B_f) (hg : ∀ k, (g.coeff k).natDegree ≤ B_g) :
    ∃ U V : (S[X])[X],
      U.natDegree < n ∧ V.natDegree < m ∧
      (∀ k, (U.coeff k).natDegree ≤ n * B_f + m * B_g) ∧
      (∀ k, (V.coeff k).natDegree ≤ n * B_f + m * B_g) ∧
      (sylvesterDet m n f g).natDegree ≤ n * B_f + m * B_g ∧
      U * f + V * g = C (sylvesterDet m n f g) := by
  let w : Fin (m + n) → S[X] :=
    fun j => (sylvesterMatrix m n f g).adjugate j ⟨0, by omega⟩
  refine ⟨vecToU m n w, vecToV m n w,
    natDegree_vecToU_lt hn w, natDegree_vecToV_lt hm w,
    ?_, ?_, natDegree_sylvesterDet_le hf hg, sylvester_bezout_explicit hm hn hf_deg hg_deg⟩
  · intro k
    rw [coeff_vecToU]
    split_ifs
    · exact natDegree_sylvesterAdjugate_le hf hg _ _
    · simp
  · intro k
    rw [coeff_vecToV]
    split_ifs
    · exact natDegree_sylvesterAdjugate_le hf hg _ _
    · simp

end DegreeBounds

end Sylvester

end CertiFri
