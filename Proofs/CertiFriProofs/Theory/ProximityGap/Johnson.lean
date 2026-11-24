import Mathlib.Analysis.Real.Sqrt
import CertiFriProofs.Theory.ProximityGap

/-!
# The interleaved Johnson list-decoding bound for Reed–Solomon codes

This file proves the Johnson list-decoding bound unconditionally for interleaved
Reed–Solomon codes (any number `m` of words simultaneously) over an arbitrary
field `F`:

* `johnsonListBound n d A`: the sharp integer Johnson bound
  `⌊n * (A - (d - 1)) / (A ^ 2 - n * (d - 1))⌋`.
* `card_correlatedTuples_le_johnson`: if `D.card * (d - 1) < A ^ 2`, then at
  most `johnsonListBound D.card d A` distinct `m`-tuples `v : Fin m → F[X]` of
  polynomials of degree below `d` can simultaneously agree with `u : Fin m → F → F`
  on at least `A` points of `D`.
* `card_close_le_johnson`: specialization to a single Reed–Solomon word
  (`m = 1`).
* `johnsonListBound_le_rel`: in relative terms, for rate `ρ` (`d ≤ ρ * |D|`)
  and agreement `θ` (`ρ < θ ^ 2`, `θ ≤ 1`, `θ * |D| ≤ A`),
  `johnsonListBound |D| d A ≤ (θ - ρ) / (θ ^ 2 - ρ)`.
* `johnsonListBound_le_sqrt_gap`: for `θ = √ρ + η` (`0 < ρ`, `0 < η`,
  `√ρ + η ≤ 1`), `johnsonListBound |D| d A ≤ 1 / (2 * η * √ρ)`.

## Proof

For each tuple `v ∈ L`, let `S v := {x ∈ D | ∀ k, u k x = (v k).eval x}`. Any
two distinct tuples `v₁ ≠ v₂ ∈ L` differ in some coordinate `k`, so
`|S v₁ ∩ S v₂| ≤ d - 1` by the distance of the Reed–Solomon code. Double
counting incidences `c x := |{v ∈ L | x ∈ S v}|` and ordered off-diagonal pairs
`(v₁, v₂) ∈ L.offDiag` gives:
`T := ∑ x ∈ D, c x ≥ |L| * A` and
`∑ x ∈ D, c x ^ 2 ≤ |L| * (|L| - 1) * (d - 1) + T`.
Applying Cauchy–Schwarz `T ^ 2 ≤ |D| * ∑ x ∈ D, c x ^ 2` yields
`|L| * (A ^ 2 - |D| * (d - 1)) ≤ |D| * (A - (d - 1))`.
-/

namespace CertiFri

open Polynomial Finset

section JohnsonBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- Cauchy–Schwarz on a finite set: `(∑ x ∈ s, f x) ^ 2 ≤ s.card * ∑ x ∈ s, (f x) ^ 2`. -/
private theorem sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 := by
  have hnn : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  have hexpand : ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
      2 * ((s.card : ℝ) * ∑ x ∈ s, (f x) ^ 2 - (∑ x ∈ s, f x) ^ 2) := by
    have hsub : ∀ x y : α, (f x - f y) ^ 2 = (f x) ^ 2 - 2 * (f x * f y) + (f y) ^ 2 := by
      intro x y; ring
    simp_rw [hsub, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul,
      ← mul_sum, ← sum_mul]
    ring
  linarith

/-- The exact integer Johnson list-decoding bound for domain size `n`, degree
bound `d` (so distinct codewords overlap in at most `d - 1` points), and
agreement count `A` satisfying `n * (d - 1) < A ^ 2`. -/
def johnsonListBound (n d A : ℕ) : ℕ :=
  (n * (A - (d - 1))) / (A ^ 2 - n * (d - 1))

/-- The set of domain points where every coordinate of `u` agrees with `v`. -/
def tupleAgreeSet (D : Finset F) {m : ℕ} (u : Fin m → F → F) (v : Fin m → F[X]) : Finset F :=
  D.filter fun x => ∀ k : Fin m, u k x = (v k).eval x

/-- Two distinct `m`-tuples of polynomials of degree below `d` can agree with
`u` simultaneously on at most `d - 1` points of `D`. -/
theorem card_inter_tupleAgreeSet_le {D : Finset F} {d m : ℕ} {u : Fin m → F → F}
    {v₁ v₂ : Fin m → F[X]} (hv₁ : ∀ k, (v₁ k).degree < d) (hv₂ : ∀ k, (v₂ k).degree < d)
    (hne : v₁ ≠ v₂) :
    (tupleAgreeSet D u v₁ ∩ tupleAgreeSet D u v₂).card ≤ d - 1 := by
  have hk : ∃ k : Fin m, v₁ k ≠ v₂ k := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  obtain ⟨k, hvk⟩ := hk
  by_contra hgt
  have hge : d ≤ (tupleAgreeSet D u v₁ ∩ tupleAgreeSet D u v₂).card := by
    cases d with
    | zero => exact Nat.zero_le _
    | succ d' => simp only [Nat.add_sub_cancel] at hgt; omega
  exact hvk (eq_of_degree_lt_of_agree (hv₁ k) (hv₂ k) hge fun x hx => by
    rw [mem_inter] at hx
    have h1 := (mem_filter.mp hx.1).2 k
    have h2 := (mem_filter.mp hx.2).2 k
    exact h1.symm.trans h2)

/-- **Double-counting incidence identity.** Summing the multiplicity of each
point `x ∈ D` across `L` equals summing the agreement set sizes over `L`. -/
private theorem sum_incidence_eq {D : Finset F} {m : ℕ} {u : Fin m → F → F}
    (L : Finset (Fin m → F[X])) :
    ∑ x ∈ D, (L.filter fun v => x ∈ tupleAgreeSet D u v).card =
      ∑ v ∈ L, (tupleAgreeSet D u v).card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun v _ => ?_
  rw [← sum_filter, filter_mem_eq_inter,
    inter_eq_right.mpr (show tupleAgreeSet D u v ⊆ D from filter_subset _ _)]

/-- **Double-counting pair identity.** Summing `c(x) * (c(x) - 1)` over `x ∈ D`
equals summing `|S v₁ ∩ S v₂|` over all ordered distinct pairs `(v₁, v₂) ∈ L.offDiag`. -/
private theorem sum_pair_incidences_eq {D : Finset F} {m : ℕ} {u : Fin m → F → F}
    (L : Finset (Fin m → F[X])) :
    ∑ x ∈ D, ((L.filter fun v => x ∈ tupleAgreeSet D u v).card *
        ((L.filter fun v => x ∈ tupleAgreeSet D u v).card - 1)) =
      ∑ p ∈ L.offDiag, (tupleAgreeSet D u p.1 ∩ tupleAgreeSet D u p.2).card := by
  have hcard : ∀ x ∈ D,
      (L.filter fun v => x ∈ tupleAgreeSet D u v).card *
        ((L.filter fun v => x ∈ tupleAgreeSet D u v).card - 1) =
      (L.offDiag.filter fun p => x ∈ tupleAgreeSet D u p.1 ∩ tupleAgreeSet D u p.2).card := by
    intro x _
    have hset : (L.filter fun v => x ∈ tupleAgreeSet D u v).offDiag =
        L.offDiag.filter fun p => x ∈ tupleAgreeSet D u p.1 ∩ tupleAgreeSet D u p.2 := by
      ext ⟨v₁, v₂⟩
      simp only [mem_offDiag, mem_filter, mem_inter]
      tauto
    rw [← hset, offDiag_card, Nat.mul_sub_one]
  rw [sum_congr rfl hcard]
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  have hsub : tupleAgreeSet D u p.1 ∩ tupleAgreeSet D u p.2 ⊆ D :=
    inter_subset_left.trans (filter_subset _ _)
  rw [← sum_filter, filter_mem_eq_inter, inter_eq_right.mpr hsub]

/-- **Interleaved Johnson bound (real multiplicative form).** For any finite set
`L` of `m`-tuples of polynomials of degree below `d`, each agreeing with `u` on
at least `A` points of `D`, if `L` is nonempty then
`L.card * (A ^ 2 - D.card * (d - 1)) ≤ D.card * (A - (d - 1))`. -/
theorem johnson_mul_le {D : Finset F} {d A m : ℕ} {u : Fin m → F → F}
    {L : Finset (Fin m → F[X])}
    (hdeg : ∀ v ∈ L, ∀ k, (v k).degree < d)
    (hagree : ∀ v ∈ L, A ≤ (tupleAgreeSet D u v).card)
    (hne : L.Nonempty) :
    (L.card : ℝ) * ((A : ℝ) ^ 2 - (D.card : ℝ) * ((d - 1 : ℕ) : ℝ)) ≤
      (D.card : ℝ) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) := by
  let c : F → ℕ := fun x => (L.filter fun v => x ∈ tupleAgreeSet D u v).card
  let T : ℕ := ∑ x ∈ D, c x
  have hT_ge : L.card * A ≤ T := by
    change L.card * A ≤ ∑ x ∈ D, c x
    rw [sum_incidence_eq]
    calc L.card * A = ∑ _v ∈ L, A := by simp
      _ ≤ ∑ v ∈ L, (tupleAgreeSet D u v).card := sum_le_sum hagree
  have hpairs : ∑ x ∈ D, c x * (c x - 1) ≤ L.card * (L.card - 1) * (d - 1) := by
    calc ∑ x ∈ D, c x * (c x - 1)
        = ∑ p ∈ L.offDiag, (tupleAgreeSet D u p.1 ∩ tupleAgreeSet D u p.2).card :=
          sum_pair_incidences_eq L
      _ ≤ ∑ _p ∈ L.offDiag, (d - 1) := sum_le_sum fun p hp => by
          rw [mem_offDiag] at hp
          exact card_inter_tupleAgreeSet_le (hdeg p.1 hp.1) (hdeg p.2 hp.2.1) hp.2.2
      _ = L.offDiag.card * (d - 1) := by simp
      _ = L.card * (L.card - 1) * (d - 1) := by rw [offDiag_card, ← Nat.mul_sub_one]
  have hsq_sum : (∑ x ∈ D, (c x : ℝ) ^ 2) ≤
      (L.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ) + (T : ℝ) := by
    have hsplit : ∀ x ∈ D, (c x : ℝ) ^ 2 = ((c x * (c x - 1) : ℕ) : ℝ) + (c x : ℝ) := by
      intro x _
      rcases Nat.eq_zero_or_pos (c x) with h0 | hpos
      · simp [h0]
      · have h1 : 1 ≤ c x := hpos
        rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
        ring
    rw [sum_congr rfl hsplit, sum_add_distrib]
    have hpairsR : (∑ x ∈ D, ((c x * (c x - 1) : ℕ) : ℝ)) ≤
        (L.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℕ) ≤ L.card := hne.card_pos
      have hcast : ((L.card * (L.card - 1) * (d - 1) : ℕ) : ℝ) =
          (L.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_one]
      rw [← hcast, ← Nat.cast_sum]
      exact Nat.cast_le.mpr hpairs
    have hTR : (∑ x ∈ D, (c x : ℝ)) = (T : ℝ) := by simp [T]
    linarith
  have hcs : ((T : ℝ)) ^ 2 ≤ (D.card : ℝ) * ∑ x ∈ D, (c x : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq D (fun x => (c x : ℝ))
    simpa [T] using h
  have hmain : (T : ℝ) ^ 2 - (D.card : ℝ) * (T : ℝ) ≤
      (D.card : ℝ) * ((L.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ)) := by
    have h1 : (T : ℝ) ^ 2 ≤
        (D.card : ℝ) * ((L.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ) + (T : ℝ)) :=
      hcs.trans (mul_le_mul_of_nonneg_left hsq_sum (Nat.cast_nonneg _))
    linarith
  have hMpos : (0 : ℝ) < (L.card : ℝ) := Nat.cast_pos.mpr hne.card_pos
  have hMA_le_T : (L.card : ℝ) * (A : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT_ge
  have hMsub : (0 : ℝ) ≤ (L.card : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (L.card : ℝ) := by exact_mod_cast hne.card_pos
    linarith
  by_cases hle : (L.card : ℝ) * (A : ℝ) ≤ (D.card : ℝ)
  · have h1 : (L.card : ℝ) * (A : ℝ) ^ 2 ≤ (D.card : ℝ) * (A : ℝ) := by
      have hA : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
      nlinarith
    have h2 : (0 : ℝ) ≤ (D.card : ℝ) * ((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ) := by positivity
    linarith
  · push Not at hle
    have hprod : (L.card : ℝ) * (A : ℝ) * ((L.card : ℝ) * (A : ℝ) - (D.card : ℝ)) ≤
        (T : ℝ) * ((T : ℝ) - (D.card : ℝ)) := by
      have h0 : (0 : ℝ) ≤ (L.card : ℝ) * (A : ℝ) := by positivity
      nlinarith
    have hTfact : (T : ℝ) * ((T : ℝ) - (D.card : ℝ)) = (T : ℝ) ^ 2 - (D.card : ℝ) * (T : ℝ) := by
      ring
    have hMmul : (L.card : ℝ) * ((A : ℝ) * ((L.card : ℝ) * (A : ℝ) - (D.card : ℝ))) ≤
        (L.card : ℝ) * ((D.card : ℝ) * (((L.card : ℝ) - 1) * ((d - 1 : ℕ) : ℝ))) := by
      linarith
    have hcancel := le_of_mul_le_mul_left hMmul hMpos
    linarith

/-- **Interleaved Johnson list-decoding bound for Reed–Solomon codes.**

If `D.card * (d - 1) < A ^ 2`, then at most `johnsonListBound D.card d A`
distinct `m`-tuples of polynomials of degree below `d` can agree with `u` on
at least `A` points of `D`. -/
theorem card_correlatedTuples_le_johnson {D : Finset F} {d A m : ℕ}
    (hJ : D.card * (d - 1) < A ^ 2) {u : Fin m → F → F}
    {L : Finset (Fin m → F[X])}
    (hdeg : ∀ v ∈ L, ∀ k, (v k).degree < d)
    (hagree : ∀ v ∈ L, A ≤ (tupleAgreeSet D u v).card) :
    L.card ≤ johnsonListBound D.card d A := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  · have ⟨v₀, hv₀⟩ := hne
    have hAD : A ≤ D.card := (hagree v₀ hv₀).trans (card_le_card (filter_subset _ _))
    have hdA : d - 1 ≤ A := by
      have h1 : D.card * (d - 1) < D.card * A := by
        calc D.card * (d - 1) < A ^ 2 := hJ
          _ = A * A := sq A
          _ ≤ D.card * A := Nat.mul_le_mul_right A hAD
      by_cases hD0 : D.card = 0
      · simp [hD0] at h1
      · exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left h1)
    have hmulR := johnson_mul_le hdeg hagree hne
    have hmulN : L.card * (A ^ 2 - D.card * (d - 1)) ≤ D.card * (A - (d - 1)) := by
      have hcast : ((L.card * (A ^ 2 - D.card * (d - 1)) : ℕ) : ℝ) ≤
          ((D.card * (A - (d - 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub (Nat.le_of_lt hJ), Nat.cast_pow, Nat.cast_mul,
          Nat.cast_mul, Nat.cast_sub hdA]
        exact hmulR
      exact Nat.cast_le.mp hcast
    exact (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hJ)).mpr hmulN

/-- **Single-word Johnson list-decoding bound for Reed–Solomon codes.**

If `D.card * (d - 1) < A ^ 2`, then at most `johnsonListBound D.card d A`
polynomials of degree below `d` agree with `f : F → F` on at least `A` points
of `D`. -/
theorem card_close_le_johnson {D : Finset F} {d A : ℕ}
    (hJ : D.card * (d - 1) < A ^ 2) {f : F → F} {L : Finset F[X]}
    (hdeg : ∀ p ∈ L, p.degree < d)
    (hagree : ∀ p ∈ L, A ≤ (D.filter fun x => f x = p.eval x).card) :
    L.card ≤ johnsonListBound D.card d A := by
  let emb : F[X] ↪ (Fin 1 → F[X]) :=
    ⟨fun p _ => p, fun p q h => congrFun h 0⟩
  have hcard : L.card = (L.map emb).card := (card_map emb).symm
  rw [hcard]
  refine card_correlatedTuples_le_johnson (u := fun (_ : Fin 1) => f) hJ ?_ ?_
  · intro v hv k
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hv
    exact hdeg p hp
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_map.mp hv
    have heq : tupleAgreeSet D (fun (_ : Fin 1) => f) (emb p) =
        D.filter fun x => f x = p.eval x := by
      ext x
      simp only [tupleAgreeSet, mem_filter, Fin.forall_fin_one]
      rfl
    rw [heq]
    exact hagree p hp

/-! ## Relative-rate upper bounds on `johnsonListBound` -/

/-- The exact integer Johnson bound is at most `(θ - ρ) / (θ ^ 2 - ρ)` whenever
`d ≤ ρ * n`, `θ * n ≤ A`, `0 < θ ≤ 1`, and `ρ < θ ^ 2`. -/
theorem johnsonListBound_le_rel {n d A : ℕ} {ρ θ : ℝ}
    (hn : 0 < n) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hd : (d : ℝ) ≤ ρ * n) (hgap : ρ < θ ^ 2) (hA : θ * n ≤ A) :
    (johnsonListBound n d A : ℝ) ≤ (θ - ρ) / (θ ^ 2 - ρ) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnsq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hden_pos : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
  have hk_le_ρn : ((d - 1 : ℕ) : ℝ) ≤ ρ * n := by
    have : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr (Nat.sub_le d 1)
    linarith
  have hρ_lt_θ : ρ < θ := by nlinarith
  have hk_le_θn : ((d - 1 : ℕ) : ℝ) ≤ θ * n := by nlinarith
  have hk_le_A : ((d - 1 : ℕ) : ℝ) ≤ (A : ℝ) := hk_le_θn.trans hA
  have hk_le_n : ((d - 1 : ℕ) : ℝ) ≤ n := by nlinarith
  have hρ_lt_θsq : ρ * (n : ℝ) ^ 2 < θ ^ 2 * (n : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hgap hnsq
  have hJA : (n : ℝ) * ((d - 1 : ℕ) : ℝ) < (A : ℝ) ^ 2 := by
    have h1 : (n : ℝ) * ((d - 1 : ℕ) : ℝ) ≤ ρ * (n : ℝ) ^ 2 := by nlinarith
    have h3 : θ ^ 2 * (n : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by nlinarith
    linarith
  have hJN : n * (d - 1) < A ^ 2 := by exact_mod_cast hJA
  have hdiv_le : (johnsonListBound n d A : ℝ) ≤
      (n : ℝ) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) /
        ((A : ℝ) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) := by
    rw [johnsonListBound]
    have hsubpos : (0 : ℝ) < (A : ℝ) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ) := sub_pos.mpr hJA
    rw [le_div_iff₀ hsubpos]
    have hmul : (n * (A - (d - 1))) / (A ^ 2 - n * (d - 1)) * (A ^ 2 - n * (d - 1)) ≤
        n * (A - (d - 1)) := Nat.div_mul_le_self _ _
    have hmulR : (((n * (A - (d - 1))) / (A ^ 2 - n * (d - 1)) : ℕ) : ℝ) *
        (((A ^ 2 - n * (d - 1) : ℕ) : ℝ)) ≤ ((n * (A - (d - 1)) : ℕ) : ℝ) := by
      exact_mod_cast hmul
    have hdA : d - 1 ≤ A := by exact_mod_cast hk_le_A
    rw [Nat.cast_sub (Nat.le_of_lt hJN), Nat.cast_pow, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_sub hdA] at hmulR
    exact hmulR
  refine hdiv_le.trans ?_
  -- Step 1: monotonicity in `A` (`θ * n ≤ A` lowers the ratio).
  have hdenA : 0 < (A : ℝ) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ) := sub_pos.mpr hJA
  have hdenθ : 0 < (θ * n) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ) := by
    have h1 : (n : ℝ) * ((d - 1 : ℕ) : ℝ) ≤ ρ * (n : ℝ) ^ 2 := by nlinarith
    have h2 : (θ * n) ^ 2 = θ ^ 2 * (n : ℝ) ^ 2 := mul_pow θ (n : ℝ) 2
    linarith
  have hstep1 : (n : ℝ) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) /
        ((A : ℝ) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) ≤
      (n : ℝ) * (θ * n - ((d - 1 : ℕ) : ℝ)) /
        ((θ * n) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ hdenA hdenθ]
    have hdiff :
        (n : ℝ) * (θ * n - ((d - 1 : ℕ) : ℝ)) * ((A : ℝ) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) -
        (n : ℝ) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) * ((θ * n) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) =
        (n : ℝ) * ((A : ℝ) - θ * n) *
          ((θ * n - ((d - 1 : ℕ) : ℝ)) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) +
            ((d - 1 : ℕ) : ℝ) * ((n : ℝ) - ((d - 1 : ℕ) : ℝ))) := by ring
    have hnn : 0 ≤ (n : ℝ) * ((A : ℝ) - θ * n) *
        ((θ * n - ((d - 1 : ℕ) : ℝ)) * ((A : ℝ) - ((d - 1 : ℕ) : ℝ)) +
          ((d - 1 : ℕ) : ℝ) * ((n : ℝ) - ((d - 1 : ℕ) : ℝ))) := by
      have h0 : 0 ≤ (A : ℝ) - θ * n := sub_nonneg.mpr hA
      have h1 : 0 ≤ θ * n - ((d - 1 : ℕ) : ℝ) := sub_nonneg.mpr hk_le_θn
      have h2 : 0 ≤ (A : ℝ) - ((d - 1 : ℕ) : ℝ) := sub_nonneg.mpr hk_le_A
      have h3 : 0 ≤ (n : ℝ) - ((d - 1 : ℕ) : ℝ) := sub_nonneg.mpr hk_le_n
      have h4 : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity
    linarith
  refine hstep1.trans ?_
  -- Step 2: monotonicity in `k = d - 1 ≤ ρ * n`.
  rw [div_le_div_iff₀ hdenθ hden_pos]
  have hdiff2 :
      (θ - ρ) * ((θ * n) ^ 2 - (n : ℝ) * ((d - 1 : ℕ) : ℝ)) -
      (n : ℝ) * (θ * n - ((d - 1 : ℕ) : ℝ)) * (θ ^ 2 - ρ) =
      (n : ℝ) * θ * (1 - θ) * (ρ * n - ((d - 1 : ℕ) : ℝ)) := by ring
  have hnn2 : 0 ≤ (n : ℝ) * θ * (1 - θ) * (ρ * n - ((d - 1 : ℕ) : ℝ)) := by
    have h1 : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    have h2 : 0 ≤ ρ * n - ((d - 1 : ℕ) : ℝ) := sub_nonneg.mpr hk_le_ρn
    positivity
  linarith

/-- Convenient coarser bound `(θ - ρ) / (θ ^ 2 - ρ) ≤ θ / (θ ^ 2 - ρ)`. -/
theorem johnsonListBound_le_div {n d A : ℕ} {ρ θ : ℝ}
    (hn : 0 < n) (hρ0 : 0 ≤ ρ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hd : (d : ℝ) ≤ ρ * n) (hgap : ρ < θ ^ 2) (hA : θ * n ≤ A) :
    (johnsonListBound n d A : ℝ) ≤ θ / (θ ^ 2 - ρ) := by
  refine (johnsonListBound_le_rel hn hθ0 hθ1 hd hgap hA).trans ?_
  have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- **Gap-to-Johnson bound.** At agreement `θ = √ρ + η` (`0 < ρ`, `0 < η`,
`√ρ + η ≤ 1`), the Johnson list size is at most `1 / (2 * η * √ρ)`. -/
theorem johnsonListBound_le_sqrt_gap {n d A : ℕ} {ρ η : ℝ}
    (hn : 0 < n) (hρ0 : 0 < ρ) (hη0 : 0 < η) (hθ1 : Real.sqrt ρ + η ≤ 1)
    (hd : (d : ℝ) ≤ ρ * n) (hA : (Real.sqrt ρ + η) * n ≤ A) :
    (johnsonListBound n d A : ℝ) ≤ 1 / (2 * η * Real.sqrt ρ) := by
  have hsqrt : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ0
  have hθ0 : 0 < Real.sqrt ρ + η := by linarith
  have hsq : (Real.sqrt ρ + η) ^ 2 - ρ = 2 * η * Real.sqrt ρ + η ^ 2 := by
    have h := Real.sq_sqrt hρ0.le
    nlinarith
  have hgap : ρ < (Real.sqrt ρ + η) ^ 2 := by
    have : 0 < 2 * η * Real.sqrt ρ + η ^ 2 := by positivity
    linarith
  refine (johnsonListBound_le_div hn hρ0.le hθ0 hθ1 hd hgap hA).trans ?_
  rw [hsq]
  have hden1 : 0 < 2 * η * Real.sqrt ρ + η ^ 2 := by positivity
  have hden2 : 0 < 2 * η * Real.sqrt ρ := by positivity
  calc (Real.sqrt ρ + η) / (2 * η * Real.sqrt ρ + η ^ 2)
      ≤ 1 / (2 * η * Real.sqrt ρ + η ^ 2) := div_le_div_of_nonneg_right hθ1 hden1.le
    _ ≤ 1 / (2 * η * Real.sqrt ρ) :=
        one_div_le_one_div_of_le hden2 (by nlinarith)

/-- **Relative-rate interleaved Johnson bound.** If `d ≤ ρ * D.card`, `0 < θ ≤ 1`,
and `ρ < θ ^ 2`, then any finite set `L` of `m`-tuples of `< d`-degree
polynomials agreeing with `u` on at least a `θ`-fraction of `D` has size at
most `(θ - ρ) / (θ ^ 2 - ρ)`. -/
theorem card_correlatedTuples_le_rel {D : Finset F} {d m : ℕ} {ρ θ : ℝ}
    (hD : D.Nonempty) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hd : (d : ℝ) ≤ ρ * D.card) (hgap : ρ < θ ^ 2)
    {u : Fin m → F → F} {L : Finset (Fin m → F[X])}
    (hdeg : ∀ v ∈ L, ∀ k, (v k).degree < d)
    (hagree : ∀ v ∈ L, θ * D.card ≤ (tupleAgreeSet D u v).card) :
    (L.card : ℝ) ≤ (θ - ρ) / (θ ^ 2 - ρ) := by
  let A : ℕ := Nat.ceil (θ * D.card)
  have hA : θ * D.card ≤ (A : ℝ) := Nat.le_ceil _
  have hDpos : 0 < D.card := hD.card_pos
  have hJ : D.card * (d - 1) < A ^ 2 := by
    have hDposR : (0 : ℝ) < D.card := Nat.cast_pos.mpr hDpos
    have hDsq : (0 : ℝ) < (D.card : ℝ) ^ 2 := sq_pos_of_pos hDposR
    have hk : ((d - 1 : ℕ) : ℝ) ≤ ρ * D.card := by
      have : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr (Nat.sub_le d 1)
      linarith
    have h1 : (D.card : ℝ) * ((d - 1 : ℕ) : ℝ) ≤ ρ * (D.card : ℝ) ^ 2 := by nlinarith
    have h2 : ρ * (D.card : ℝ) ^ 2 < θ ^ 2 * (D.card : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hgap hDsq
    have h3 : θ ^ 2 * (D.card : ℝ) ^ 2 ≤ (A : ℝ) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hA 2
    have h4 : (D.card : ℝ) * ((d - 1 : ℕ) : ℝ) < (A : ℝ) ^ 2 := by linarith
    exact_mod_cast h4
  have hcard : L.card ≤ johnsonListBound D.card d A :=
    card_correlatedTuples_le_johnson hJ hdeg fun v hv => Nat.ceil_le.mpr (hagree v hv)
  exact (Nat.cast_le.mpr hcard).trans (johnsonListBound_le_rel hDpos hθ0 hθ1 hd hgap hA)

end JohnsonBound

end CertiFri
