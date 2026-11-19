import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# A proximity gap for linear codes, below a fraction of the minimum distance

Let `L` be a linear code of length `n` over a finite field `F` in which every
nonzero codeword has weight at least `dist`, let `u 0, …, u (m - 1)` be words,
and write `u(β) = ∑ k, β ^ k • u k` for the curve through them. Fix a number of
errors `e` with `(m + 1) * e < dist`.

* `correlated_agreement_of_minDist`: if `u(β)` is within Hamming distance `e`
  of `L` for more than `(m - 1) * (e + 1)` values of `β`, then there are
  codewords `v k` such that all the `u k` agree with the `v k` outside one
  common set of at most `e` positions.
* `curve_mca_of_minDist`: for all `β` outside a set of at most
  `(m - 1) * (e + 1)` values, every set `B` of at least `n - e` positions on
  which `u(β)` agrees with a codeword is a set on which every `u k` agrees with
  a codeword. This is mutual correlated agreement: the agreement set of the
  combination is itself an agreement set of each term.

Both hold for every linear code and are proved here in full, with no
hypothesis beyond the minimum distance. The price is the radius: `e` stays
below `dist / (m + 1)`, well inside the unique-decoding radius `dist / 2`. For
Reed–Solomon codes the unique-decoding radius is reached in
`ProximityGap/UniqueDecoding.lean`; larger radii (up to the Johnson bound) are
not covered.

The proof is elementary. From `m` close points of the curve, with close
codewords `c i` at parameters `b i`, interpolation (the Vandermonde matrix of
the `b i` is invertible) gives codewords `v k` whose curve passes through the
`c i`. The `u k` and `v k` differ in at most `m * e` positions, which with the
minimum distance forces the codeword close to any `u(β)` to be `v(β)`. A double
count over pairs of a close parameter and a position then brings the number of
differing positions down to `e`. The exceptional `β` are the roots of the
nonzero polynomials `∑ k, (u k j - v k j) X ^ k` at the differing positions `j`.
-/

namespace CertiFri

namespace ProximityGap

open Finset

variable {F ι : Type*} [Field F] {m : ℕ}

/-- The point with parameter `β` of the curve with coefficients `u`: the word
`∑ k, β ^ k • u k`. -/
def curve (u : Fin m → ι → F) (β : F) : ι → F :=
  fun j => ∑ k : Fin m, β ^ (k : ℕ) * u k j

/-- A curve with coefficients in a linear code stays in the code. -/
theorem curve_mem {L : Submodule F (ι → F)} {v : Fin m → ι → F} (hv : ∀ k, v k ∈ L) (β : F) :
    curve v β ∈ L := by
  have h : curve v β = ∑ k : Fin m, β ^ (k : ℕ) • v k := by
    funext j
    simp [curve, Finset.sum_apply]
  rw [h]
  exact L.sum_mem fun k _ => L.smul_mem _ (hv k)

/-- The difference of two curves at one position is a polynomial expression in
the parameter, with the differences of the coefficients as coefficients. -/
theorem curve_sub_curve (u v : Fin m → ι → F) (β : F) (j : ι) :
    curve u β j - curve v β j = ∑ k : Fin m, β ^ (k : ℕ) * (u k j - v k j) := by
  simp [curve, mul_sub, Finset.sum_sub_distrib]

/-- A finite set with at least `m` elements contains `m` distinct ones. -/
theorem exists_injective_of_le_card {α : Type*} {s : Finset α} (h : m ≤ s.card) :
    ∃ b : Fin m → α, Function.Injective b ∧ ∀ i, b i ∈ s := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := s) (by simpa using h)
  exact ⟨fun i => (f i : α), Subtype.val_injective.comp f.injective, fun i => (f i).2⟩

/-- A nonzero polynomial expression with `m` coefficients has fewer than `m`
roots. -/
theorem card_roots_lt [DecidableEq F] {a : Fin m → F} (ha : a ≠ 0) (s : Finset F) :
    (s.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * a k = 0).card < m := by
  by_contra h
  obtain ⟨b, hb, hmem⟩ := exists_injective_of_le_card (not_lt.mp h)
  exact ha (Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hb
    fun i => (mem_filter.mp (hmem i)).2)

/-- Interpolation: through `m` codewords placed at `m` distinct parameters
passes a curve with `m` coefficients, all of them codewords. -/
theorem exists_interpolant {L : Submodule F (ι → F)} {b : Fin m → F}
    (hb : Function.Injective b) {c : Fin m → ι → F} (hc : ∀ i, c i ∈ L) :
    ∃ v : Fin m → ι → F, (∀ k, v k ∈ L) ∧ ∀ i, curve v (b i) = c i := by
  have hVV : Matrix.vandermonde b * (Matrix.vandermonde b)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (Matrix.det_vandermonde_ne_zero_iff.mpr hb).isUnit
  refine ⟨fun k => ∑ i, (Matrix.vandermonde b)⁻¹ k i • c i,
    fun k => L.sum_mem fun i _ => L.smul_mem _ (hc i), fun i => funext fun j => ?_⟩
  calc curve (fun k => ∑ i, (Matrix.vandermonde b)⁻¹ k i • c i) (b i) j
      = ∑ k, ∑ i', Matrix.vandermonde b i k * (Matrix.vandermonde b)⁻¹ k i' * c i' j := by
        simp [curve, Finset.sum_apply, Finset.mul_sum, mul_assoc, Matrix.vandermonde_apply]
    _ = ∑ i', (Matrix.vandermonde b * (Matrix.vandermonde b)⁻¹) i i' * c i' j := by
        rw [Finset.sum_comm]
        simp [Matrix.mul_apply, Finset.sum_mul]
    _ = c i j := by
        rw [hVV]
        simp [Matrix.one_apply]

variable [Fintype ι] [DecidableEq F]

/-- The positions at which some `u k` differs from `v k`. -/
def diffSet (u v : Fin m → ι → F) : Finset ι :=
  univ.filter fun j => ∃ k, u k j ≠ v k j

/-- Two curves differ only at positions where their coefficients differ. -/
theorem hammingDist_curve_le (u v : Fin m → ι → F) (β : F) :
    hammingDist (curve u β) (curve v β) ≤ (diffSet u v).card := by
  refine card_le_card fun j hj => ?_
  rw [mem_filter] at hj
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  by_contra hn
  exact hj.2 (by simp [curve, fun k => not_not.mp (not_exists.mp hn k)])

/-- If two curves are within distance `e` of each other at `m` distinct
parameters, their coefficients differ in at most `m * e` positions. -/
theorem card_diffSet_le_mul {u v : Fin m → ι → F} {b : Fin m → F} (hb : Function.Injective b)
    {e : ℕ} (h : ∀ i, hammingDist (curve u (b i)) (curve v (b i)) ≤ e) :
    (diffSet u v).card ≤ m * e := by
  classical
  have hsub : diffSet u v ⊆
      univ.biUnion fun i => univ.filter fun j => curve u (b i) j ≠ curve v (b i) j := by
    intro j hj
    by_contra hn
    simp only [mem_biUnion, mem_univ, true_and, mem_filter, not_exists, not_not] at hn
    have h0 : (fun k => u k j - v k j) = 0 :=
      Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hb fun i => by
        rw [← curve_sub_curve, hn i, sub_self]
    obtain ⟨k, hk⟩ := (mem_filter.mp hj).2
    exact hk (sub_eq_zero.mp (congrFun h0 k))
  calc (diffSet u v).card
      ≤ (univ.biUnion fun i => univ.filter fun j => curve u (b i) j ≠ curve v (b i) j).card :=
        card_le_card hsub
    _ ≤ ∑ i : Fin m, (univ.filter fun j => curve u (b i) j ≠ curve v (b i) j).card :=
        card_biUnion_le
    _ ≤ ∑ _i : Fin m, e := sum_le_sum fun i _ => h i
    _ = m * e := by simp

/-- Unique decoding along a curve: if the coefficients of `u` differ from the
codewords `v` in few positions, the only codeword within distance `e` of a point
of the curve of `u` is the corresponding point of the curve of `v`. -/
theorem eq_curve_of_close {L : Submodule F (ι → F)} {dist : ℕ}
    (hdist : ∀ c ∈ L, c ≠ 0 → dist ≤ hammingNorm c) {u v : Fin m → ι → F}
    (hv : ∀ k, v k ∈ L) {e : ℕ} (hE : (diffSet u v).card + e < dist) {β : F} {c : ι → F}
    (hc : c ∈ L) (hclose : hammingDist (curve u β) c ≤ e) : c = curve v β := by
  by_contra hne
  have hmem : -c + curve v β ∈ L := L.add_mem (L.neg_mem hc) (curve_mem hv β)
  have h1 := hdist _ hmem (by rwa [Ne, neg_add_eq_zero])
  rw [← hammingDist_eq_hammingNorm] at h1
  have h2 := hammingDist_triangle c (curve u β) (curve v β)
  have h3 := hammingDist_curve_le u v β
  have h4 := hammingDist_comm c (curve u β)
  omega

/-- The double count: if the curves of `u` and `v` are within distance `e` at
more than `(m - 1) * (e + 1)` parameters, the coefficients differ in at most `e`
positions. -/
theorem card_diffSet_le {u v : Fin m → ι → F} {e : ℕ} {G : Finset F}
    (hG : (m - 1) * (e + 1) < G.card)
    (h : ∀ β ∈ G, hammingDist (curve u β) (curve v β) ≤ e) : (diffSet u v).card ≤ e := by
  classical
  have key : (diffSet u v).card * (G.card - (m - 1)) ≤ G.card * e := by
    refine card_mul_le_card_mul (fun j β => curve u β j ≠ curve v β j) (fun j hj => ?_)
      fun β hβ => ?_
    · have ha : (fun k => u k j - v k j) ≠ 0 := by
        obtain ⟨k, hk⟩ := (mem_filter.mp hj).2
        exact fun h0 => hk (sub_eq_zero.mp (congrFun h0 k))
      have hroots := card_roots_lt ha G
      have hsplit := card_filter_add_card_filter_not (s := G)
        fun β => curve u β j ≠ curve v β j
      have heq : (G.filter fun β => ¬curve u β j ≠ curve v β j) =
          G.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k j - v k j) = 0 :=
        filter_congr fun β _ => by rw [← curve_sub_curve, sub_eq_zero, not_not]
      rw [heq] at hsplit
      simp only [bipartiteAbove]
      omega
    · exact (card_le_card fun j hj =>
        mem_filter.mpr ⟨mem_univ _, (mem_bipartiteBelow _).mp hj |>.2⟩).trans (h β hβ)
  by_contra hlt
  have h1 : (e + 1) * (G.card - (m - 1)) ≤ G.card * e :=
    (Nat.mul_le_mul_right _ (not_le.mp hlt)).trans key
  have h2 : m - 1 ≤ (m - 1) * (e + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos e)
  obtain ⟨t, ht⟩ : ∃ t, G.card = t + (m - 1) := ⟨G.card - (m - 1), by omega⟩
  rw [ht, Nat.add_sub_cancel] at h1
  rw [ht] at hG
  nlinarith

/-- Correlated agreement with uniqueness: if more than `(m - 1) * (e + 1)`
points of the curve of `u` are within distance `e` of the code, there are
codewords `v k` such that the `u k` differ from the `v k` in at most `e`
positions overall, and the codeword within distance `e` of any point of the
curve of `u` is the corresponding point of the curve of `v`. -/
theorem exists_close_curve {L : Submodule F (ι → F)} {dist : ℕ}
    (hdist : ∀ c ∈ L, c ≠ 0 → dist ≤ hammingNorm c) {e : ℕ} (he : (m + 1) * e < dist)
    (u : Fin m → ι → F) {G : Finset F} (hG : (m - 1) * (e + 1) < G.card)
    (hgood : ∀ β ∈ G, ∃ c ∈ L, hammingDist (curve u β) c ≤ e) :
    ∃ v : Fin m → ι → F, (∀ k, v k ∈ L) ∧ (diffSet u v).card ≤ e ∧
      ∀ β, ∀ c ∈ L, hammingDist (curve u β) c ≤ e → c = curve v β := by
  have hm : m ≤ G.card := by
    have : m - 1 ≤ (m - 1) * (e + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos e)
    omega
  obtain ⟨b, hb, hbG⟩ := exists_injective_of_le_card hm
  choose c hcL hc using fun i => hgood (b i) (hbG i)
  obtain ⟨v, hv, hvc⟩ := exists_interpolant hb hcL
  have hE : (diffSet u v).card ≤ m * e :=
    card_diffSet_le_mul hb fun i => by rw [hvc i]; exact hc i
  have hE' : (diffSet u v).card + e < dist := by
    have : (m + 1) * e = m * e + e := by ring
    omega
  have huniq : ∀ β, ∀ c ∈ L, hammingDist (curve u β) c ≤ e → c = curve v β :=
    fun β c hc hclose => eq_curve_of_close hdist hv hE' hc hclose
  refine ⟨v, hv, card_diffSet_le hG fun β hβ => ?_, huniq⟩
  obtain ⟨c, hc, hclose⟩ := hgood β hβ
  rw [← huniq β c hc hclose]
  exact hclose

end ProximityGap

open ProximityGap Finset

/-- **Correlated agreement for curves, for any linear code.**

`L` is a linear code in which every nonzero codeword has weight at least
`dist`, and `(m + 1) * e < dist`. If the combination `∑ k, β ^ k • u k` is
within Hamming distance `e` of `L` for more than `(m - 1) * (e + 1)` values of
`β`, then there are codewords `v k` such that every `u k` agrees with `v k`
outside one common set of at most `e` positions. -/
theorem correlated_agreement_of_minDist {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (L : Submodule F (ι → F)) (dist : ℕ)
    (hdist : ∀ c ∈ L, c ≠ 0 → dist ≤ (Finset.univ.filter fun j => c j ≠ 0).card)
    (m e : ℕ) (he : (m + 1) * e < dist) (u : Fin m → ι → F)
    (G : Finset F) (hG : (m - 1) * (e + 1) < G.card)
    (hgood : ∀ β ∈ G, ∃ c ∈ L,
      (Finset.univ.filter fun j => ∑ k : Fin m, β ^ (k : ℕ) * u k j ≠ c j).card ≤ e) :
    ∃ v : Fin m → ι → F, (∀ k, v k ∈ L) ∧
      (Finset.univ.filter fun j => ∃ k, u k j ≠ v k j).card ≤ e := by
  obtain ⟨v, hv, hE, -⟩ := exists_close_curve hdist he u hG hgood
  exact ⟨v, hv, hE⟩

/-- **Mutual correlated agreement for curves, for any linear code.**

`L` is a linear code of length `Fintype.card ι` in which every nonzero codeword
has weight at least `dist`, and `(m + 1) * e < dist`. For every choice of words
`u k` there is a set `bad` of at most `(m - 1) * (e + 1)` values of `β` outside
which the following holds: whenever the combination `∑ k, β ^ k • u k` agrees
with a codeword on a set `B` that misses at most `e` positions, every `u k`
agrees with a codeword on that same `B`. -/
theorem curve_mca_of_minDist {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype ι]
    (L : Submodule F (ι → F)) (dist : ℕ)
    (hdist : ∀ c ∈ L, c ≠ 0 → dist ≤ (Finset.univ.filter fun j => c j ≠ 0).card)
    (m e : ℕ) (he : (m + 1) * e < dist) (u : Fin m → ι → F) :
    ∃ bad : Finset F, bad.card ≤ (m - 1) * (e + 1) ∧
      ∀ β ∉ bad, ∀ c ∈ L, ∀ B : Finset ι, Fintype.card ι ≤ B.card + e →
        (∀ j ∈ B, ∑ k : Fin m, β ^ (k : ℕ) * u k j = c j) →
        ∃ v : Fin m → ι → F, (∀ k, v k ∈ L) ∧ ∀ k, ∀ j ∈ B, u k j = v k j := by
  classical
  -- Agreement on a set missing at most `e` positions is distance at most `e`.
  have hclose : ∀ (β : F) (c : ι → F) (B : Finset ι), Fintype.card ι ≤ B.card + e →
      (∀ j ∈ B, curve u β j = c j) → hammingDist (curve u β) c ≤ e := by
    intro β c B hB hagree
    have hsub : (univ.filter fun j => curve u β j ≠ c j) ⊆ Bᶜ := fun j hj =>
      mem_compl.mpr fun hjB => (mem_filter.mp hj).2 (hagree j hjB)
    have hcard := card_le_card hsub
    rw [card_compl] at hcard
    unfold hammingDist
    omega
  -- The parameters at which the curve is close to the code.
  let G : Finset F := univ.filter fun β => ∃ c ∈ L, hammingDist (curve u β) c ≤ e
  by_cases hG : G.card ≤ (m - 1) * (e + 1)
  · -- Few close parameters: they are the exceptional set.
    exact ⟨G, hG, fun β hβ c hc B hB hagree =>
      absurd (mem_filter.mpr ⟨mem_univ _, c, hc, hclose β c B hB hagree⟩) hβ⟩
  · -- Many close parameters: the `u k` are close to codewords `v k`, and the
    -- exceptional set is where the curve of `u - v` vanishes at a position
    -- where `u` and `v` differ.
    obtain ⟨v, hv, hE, huniq⟩ :=
      exists_close_curve hdist he u (not_le.mp hG) fun β hβ => (mem_filter.mp hβ).2
    refine ⟨(diffSet u v).biUnion fun j =>
      univ.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k j - v k j) = 0, ?_, ?_⟩
    · calc ((diffSet u v).biUnion fun j =>
            univ.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k j - v k j) = 0).card
          ≤ ∑ j ∈ diffSet u v,
            (univ.filter fun β => ∑ k : Fin m, β ^ (k : ℕ) * (u k j - v k j) = 0).card :=
            card_biUnion_le
        _ ≤ ∑ _j ∈ diffSet u v, (m - 1) := sum_le_sum fun j hj => by
            have ha : (fun k => u k j - v k j) ≠ 0 := by
              obtain ⟨k, hk⟩ := (mem_filter.mp hj).2
              exact fun h0 => hk (sub_eq_zero.mp (congrFun h0 k))
            have := card_roots_lt ha univ
            omega
        _ = (diffSet u v).card * (m - 1) := by simp
        _ ≤ e * (m - 1) := Nat.mul_le_mul_right _ hE
        _ ≤ (m - 1) * (e + 1) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left _ (Nat.le_succ e)
    · intro β hβ c hc B hB hagree
      have hcv := huniq β c hc (hclose β c B hB hagree)
      refine ⟨v, hv, fun k j hj => ?_⟩
      by_contra hne
      have hjE : j ∈ diffSet u v := mem_filter.mpr ⟨mem_univ _, k, hne⟩
      refine hβ (mem_biUnion.mpr ⟨j, hjE, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩)
      rw [← curve_sub_curve, ← hcv]
      exact sub_eq_zero.mpr (hagree j hj)

end CertiFri
