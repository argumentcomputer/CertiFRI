import Mathlib
import CertiFriProofs.Theory.Oracle.BadEvent

/-!
# Lookup sums and balanced lists of messages

A lookup argument proves that a list of messages, each sent with a
multiplicity, is *balanced*: for every message, the multiplicities with which
it is sent add up to zero. The verifier checks this at two random challenges:
with the fingerprint `f(γ) = ∑_i γ^i * arg_i` of a message, it checks

    ∑ multiplicity / (β + f(γ)) = 0.

This file proves that, for a list that is not balanced, few challenges make
the sum zero or a denominator zero.

## Contents

* `fpPoly args`: the fingerprint of a message as a polynomial in `γ`. Two
  messages have the same fingerprint polynomial exactly when they agree up to
  trailing zeros; the verifier does not tell such messages apart.
* `Balanced items`: for every fingerprint polynomial, the multiplicities of the
  items with that fingerprint add up to zero.
* `lookupSum β γ items`: the sum the verifier's check is about.
* `balPoly items`: a polynomial in `β` over the polynomials in `γ` that is not
  zero when the list is not balanced (`balPoly_ne_zero`), and such that, where
  it does not vanish, no denominator is zero and the lookup sum is not zero
  (`of_eval_balPoly_ne_zero`).
* `fractionLE_balPoly_beta`, `fractionLE_balPoly_gamma`: at most a fraction
  `2 * n / |K|` of the values of `β` make `balPoly` vanish identically in `γ`,
  and for any other `β` at most a fraction `2 * n * L / |K|` of the values of
  `γ` make it vanish, where `n` is the number of items and `L` bounds the
  length of a message.
* `fractionLE_eval_eq_zero`, `fractionLE_eval_C_eq_zero`: the counting facts
  behind these, for the roots of a nonzero polynomial.

The multiplicities are elements of the field: "add up to zero" is in the
field, so a multiplicity that is a multiple of the characteristic counts as
zero.
-/

namespace CertiFri.Stark.Model

open Polynomial CertiFri.Oracle

variable {K : Type} [Field K]

/-! ## Roots of a nonzero polynomial -/

/-- A nonzero polynomial of degree `n` vanishes on at most a fraction
`n / |K|` of the field. -/
theorem fractionLE_eval_eq_zero [Fintype K] {p : K[X]} (hp : p ≠ 0) :
    FractionLE (fun x : K => p.eval x = 0) (p.natDegree / Fintype.card K) := by
  classical
  have hcard : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨p.roots.toFinset, ?_, fun x hx => ?_⟩
  · rw [div_mul_cancel₀ _ hcard, Nat.cast_le]
    exact (Multiset.toFinset_card_le _).trans (card_roots' p)
  · rw [Multiset.mem_toFinset, mem_roots hp]
    exact hx

/-- A nonzero polynomial in one variable over the polynomials in another, of
degree `n` in the first, vanishes identically in the second variable for at
most a fraction `n / |K|` of the values of the first. -/
theorem fractionLE_eval_C_eq_zero [Fintype K] {P : K[X][X]} (hP : P ≠ 0) :
    FractionLE (fun b : K => P.eval (C b) = 0) (P.natDegree / Fintype.card K) := by
  classical
  have hcard : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨Finset.univ.filter fun b : K => P.eval (C b) = 0, ?_,
    fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩⟩
  rw [div_mul_cancel₀ _ hcard, Nat.cast_le]
  refine le_trans (Finset.card_le_card_of_injOn (t := P.roots.toFinset) C ?_ C_injective.injOn)
    ((Multiset.toFinset_card_le _).trans (card_roots' P))
  intro b hb
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP]
  exact (Finset.mem_filter.mp hb).2

/-! ## Fingerprints -/

/-- The fingerprint of a message as a polynomial: `∑_i arg_i * X^i`. -/
noncomputable def fpPoly (args : List K) : K[X] :=
  args.foldr (fun a acc => acc * X + C a) 0

/-- The fingerprint polynomial of the empty message is zero. -/
private theorem fpPoly_nil : fpPoly ([] : List K) = 0 := rfl

/-- The fingerprint polynomial of a message, by its first argument (Horner). -/
private theorem fpPoly_cons (a : K) (args : List K) :
    fpPoly (a :: args) = fpPoly args * X + C a := rfl

/-- The fingerprint at `γ`, as the verifier computes it. -/
theorem eval_fpPoly (γ : K) (args : List K) :
    (fpPoly args).eval γ = args.foldr (fun a acc => acc * γ + a) 0 := by
  induction args with
  | nil => rw [fpPoly_nil, eval_zero, List.foldr_nil]
  | cons a l ih =>
    rw [fpPoly_cons, List.foldr_cons, ← ih, eval_add, eval_mul, eval_X, eval_C]

/-- The fingerprint at `γ` is `∑_i γ^i * arg_i`. -/
theorem eval_fpPoly_eq_sum (γ : K) (args : List K) :
    (fpPoly args).eval γ = ∑ i ∈ Finset.range args.length, γ ^ i * args.getD i 0 := by
  induction args with
  | nil => rw [fpPoly_nil, eval_zero, List.length_nil, Finset.sum_range_zero]
  | cons a l ih =>
    rw [fpPoly_cons, eval_add, eval_mul, eval_X, eval_C, ih, List.length_cons,
      Finset.sum_range_succ', Finset.sum_mul, List.getD_cons_zero, pow_zero, one_mul]
    refine congrArg (· + a) (Finset.sum_congr rfl fun i _ => ?_)
    rw [List.getD_cons_succ, pow_succ]
    ring

/-- The fingerprint polynomial of a message of length at most `L` has degree
below `L`. -/
theorem natDegree_fpPoly_le (args : List K) : (fpPoly args).natDegree ≤ args.length - 1 := by
  induction args with
  | nil => rw [fpPoly_nil, natDegree_zero]; exact Nat.zero_le _
  | cons a l ih =>
    rw [fpPoly_cons]
    cases l with
    | nil => rw [fpPoly_nil, zero_mul, zero_add, natDegree_C]; exact Nat.zero_le _
    | cons a' l' =>
      refine (natDegree_add_le _ _).trans ?_
      rw [natDegree_C, max_eq_left (Nat.zero_le _)]
      refine natDegree_mul_le.trans ?_
      rw [natDegree_X]
      simp only [List.length_cons] at ih ⊢
      omega

/-! ## Balanced lists -/

open Classical in
/-- The list of messages with multiplicities is balanced: for every
fingerprint, the multiplicities of the items with that fingerprint add up to
zero. An item is a multiplicity and the arguments of a message. -/
def Balanced (items : List (K × List K)) : Prop :=
  ∀ p : K[X], ((items.filter fun it => fpPoly it.2 = p).map Prod.fst).sum = 0

/-- The lookup sum of a list at the challenges `β` and `γ`:
`∑ multiplicity / (β + fingerprint(γ))`. -/
noncomputable def lookupSum (β γ : K) (items : List (K × List K)) : K :=
  (items.map fun it => it.1 / (β + (fpPoly it.2).eval γ)).sum

/-- The lookup sum of a concatenation. -/
theorem lookupSum_append (β γ : K) (l₁ l₂ : List (K × List K)) :
    lookupSum β γ (l₁ ++ l₂) = lookupSum β γ l₁ + lookupSum β γ l₂ := by
  rw [lookupSum, List.map_append, List.sum_append, lookupSum, lookupSum]

/-- The polynomial of a list of items, in `β` over the polynomials in `γ`: with
`f` ranging over the distinct fingerprints of the list and `c_f` the sum of the
multiplicities of the items with fingerprint `f`,

    (∑_f c_f * ∏_{f' ≠ f} (β + f')) * ∏_f (β + f).

It is not zero when the list is not balanced. Where it does not vanish, no
denominator of the lookup sum is zero and the lookup sum is not zero. -/
noncomputable def balPoly (items : List (K × List K)) : K[X][X] := by
  classical
  exact
    let fps : Finset K[X] := (items.map fun it => fpPoly it.2).toFinset
    let net : K[X] → K := fun p => ((items.filter fun it => fpPoly it.2 = p).map Prod.fst).sum
    (∑ f ∈ fps, C (C (net f)) * ∏ f' ∈ fps.erase f, (X + C f')) * ∏ f ∈ fps, (X + C f)

/-- `balPoly` unfolded, for any way of deciding the equality of polynomials. -/
private theorem balPoly_eq [DecidableEq K[X]] (items : List (K × List K)) :
    balPoly items
      = (∑ f ∈ (items.map fun it => fpPoly it.2).toFinset,
          C (C ((items.filter fun it => fpPoly it.2 = f).map Prod.fst).sum)
            * ∏ f' ∈ ((items.map fun it => fpPoly it.2).toFinset).erase f, (X + C f'))
        * ∏ f ∈ (items.map fun it => fpPoly it.2).toFinset, (X + C f) := by
  unfold balPoly
  congr!

/-- The sum of a function over a list, with the members of the list grouped by
a key: any finite set that holds the keys of the list will do. -/
private theorem sum_map_eq_sum_filter {α β M : Type*} [DecidableEq β] [AddCommMonoid M]
    (l : List α) (key : α → β) (g : α → M) (s : Finset β) (hs : ∀ a ∈ l, key a ∈ s) :
    (l.map g).sum = ∑ k ∈ s, ((l.filter fun a => key a = k).map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : key a ∈ s := hs a List.mem_cons_self
    have hcons : ∀ k, (((a :: l).filter fun a => key a = k).map g).sum
        = (if key a = k then g a else 0) + ((l.filter fun a => key a = k).map g).sum := by
      intro k
      by_cases hk : key a = k <;> simp [hk]
    rw [List.map_cons, List.sum_cons, ih fun a' ha' => hs a' (List.mem_cons_of_mem a ha')]
    simp only [hcons, Finset.sum_add_distrib, Finset.sum_ite_eq, ha, ite_true]

/-- The shape of `balPoly`: with a coefficient that is not zero at a member `p`
of the set, the polynomial is not zero. Its first factor does not vanish at
`-p`, and its second is a product of polynomials of degree one. -/
private theorem sum_mul_prod_erase_mul_prod_ne_zero [DecidableEq K[X]] (s : Finset K[X])
    (c : K[X] → K) {p : K[X]} (hp : p ∈ s) (hc : c p ≠ 0) :
    (∑ f ∈ s, C (C (c f)) * ∏ f' ∈ s.erase f, (X + C f')) * ∏ f ∈ s, (X + C f) ≠ 0 := by
  refine mul_ne_zero (fun h0 => ?_) (Finset.prod_ne_zero_iff.mpr fun f _ => X_add_C_ne_zero f)
  have h := congrArg (eval (-p)) h0
  rw [eval_finsetSum, Finset.sum_eq_single p, eval_zero] at h
  · simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X] at h
    rcases mul_eq_zero.mp h with h | h
    · exact hc (C_eq_zero.mp h)
    · obtain ⟨f, hf, hf0⟩ := Finset.prod_eq_zero_iff.mp h
      rw [neg_add_eq_zero] at hf0
      exact (Finset.mem_erase.mp hf).1 hf0.symm
  · intro f _ hfp
    rw [eval_mul, eval_prod, Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hfp, hp⟩),
      mul_zero]
    rw [eval_add, eval_X, eval_C, neg_add_cancel]
  · intro h
    exact absurd hp h

/-- The degree of a polynomial of the shape of `balPoly`, with `n` factors of
degree at most `d`, is at most `2 * n * d`. -/
private theorem natDegree_sum_mul_prod_erase_mul_prod_le {ι R : Type*} [DecidableEq ι]
    [CommSemiring R] (s : Finset ι) (c : ι → R) (x : ι → R[X]) (d : ℕ)
    (hx : ∀ i ∈ s, (x i).natDegree ≤ d) :
    ((∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, x j) * ∏ i ∈ s, x i).natDegree ≤ 2 * s.card * d := by
  have hprod : ∀ t ⊆ s, (∏ i ∈ t, x i).natDegree ≤ s.card * d := by
    intro t ht
    refine (natDegree_prod_le t x).trans ?_
    refine (Finset.sum_le_card_nsmul t _ d fun i hi => hx i (ht hi)).trans ?_
    rw [smul_eq_mul]
    exact Nat.mul_le_mul_right d (Finset.card_le_card ht)
  have hsum : (∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, x j).natDegree ≤ s.card * d := by
    refine natDegree_sum_le_of_forall_le s _ fun i _ => ?_
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C, zero_add]
    exact hprod _ (Finset.erase_subset i s)
  calc ((∑ i ∈ s, C (c i) * ∏ j ∈ s.erase i, x j) * ∏ i ∈ s, x i).natDegree
      ≤ s.card * d + s.card * d := natDegree_mul_le.trans (add_le_add hsum (hprod s subset_rfl))
    _ = 2 * s.card * d := by ring

/-- The shape of a value of `balPoly` in a field: where it is not zero, no
factor is zero and the sum of the fractions is not zero. -/
private theorem of_sum_mul_prod_erase_mul_prod_ne_zero {ι F : Type*} [DecidableEq ι] [Field F]
    (s : Finset ι) (c x : ι → F)
    (h : (∑ i ∈ s, c i * ∏ j ∈ s.erase i, x j) * ∏ i ∈ s, x i ≠ 0) :
    (∀ i ∈ s, x i ≠ 0) ∧ ∑ i ∈ s, c i / x i ≠ 0 := by
  have hx : ∀ i ∈ s, x i ≠ 0 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
  refine ⟨hx, fun h0 => left_ne_zero_of_mul h ?_⟩
  have hsum : ∑ i ∈ s, c i * ∏ j ∈ s.erase i, x j = (∑ i ∈ s, c i / x i) * ∏ i ∈ s, x i := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.mul_prod_erase s x hi, ← mul_assoc, div_mul_cancel₀ _ (hx i hi)]
  rw [hsum, h0, zero_mul]

/-- The fingerprint of an item of the list is among the fingerprints of the list. -/
private theorem fpPoly_mem_toFinset [DecidableEq K[X]] {items : List (K × List K)}
    {it : K × List K} (hit : it ∈ items) :
    fpPoly it.2 ∈ (items.map fun it => fpPoly it.2).toFinset :=
  List.mem_toFinset.mpr (List.mem_map.mpr ⟨it, hit, rfl⟩)

/-- A list has at most as many distinct fingerprints as items. -/
private theorem card_toFinset_fpPoly_le [DecidableEq K[X]] (items : List (K × List K)) :
    (items.map fun it => fpPoly it.2).toFinset.card ≤ items.length :=
  (List.toFinset_card_le _).trans (List.length_map _).le

/-- The polynomial of a list that is not balanced is not zero. -/
theorem balPoly_ne_zero {items : List (K × List K)} (h : ¬ Balanced items) :
    balPoly items ≠ 0 := by
  classical
  rw [Balanced, not_forall] at h
  obtain ⟨p, hp⟩ := h
  have hmem : p ∈ (items.map fun it => fpPoly it.2).toFinset := by
    by_contra hmem
    refine hp ?_
    rw [List.filter_eq_nil_iff.mpr, List.map_nil, List.sum_nil]
    intro it hit hfp
    rw [decide_eq_true_eq] at hfp
    exact hmem (hfp ▸ fpPoly_mem_toFinset hit)
  rw [balPoly_eq]
  exact sum_mul_prod_erase_mul_prod_ne_zero _ _ hmem hp

/-- The degree of `balPoly` in `β` is at most twice the number of items. -/
theorem natDegree_balPoly_le (items : List (K × List K)) :
    (balPoly items).natDegree ≤ 2 * items.length := by
  classical
  rw [balPoly_eq]
  refine (natDegree_sum_mul_prod_erase_mul_prod_le _ _ (fun f : K[X] => X + C f) 1
    fun f _ => (natDegree_X_add_C f).le).trans ?_
  rw [mul_one]
  exact Nat.mul_le_mul_left 2 (card_toFinset_fpPoly_le items)

/-- The value of `balPoly` at a fixed `β`, as a polynomial in `γ`. -/
private theorem eval_C_balPoly [DecidableEq K[X]] (items : List (K × List K)) (b : K) :
    (balPoly items).eval (C b)
      = (∑ f ∈ (items.map fun it => fpPoly it.2).toFinset,
          C ((items.filter fun it => fpPoly it.2 = f).map Prod.fst).sum
            * ∏ f' ∈ ((items.map fun it => fpPoly it.2).toFinset).erase f, (C b + f'))
        * ∏ f ∈ (items.map fun it => fpPoly it.2).toFinset, (C b + f) := by
  rw [balPoly_eq]
  simp only [eval_mul, eval_finsetSum, eval_prod, eval_add, eval_X, eval_C]

/-- For a fixed `β`, the degree of `balPoly` in `γ` is at most `2 * n * L`,
for `n` items whose messages have length at most `L`. -/
theorem natDegree_eval_balPoly_le (items : List (K × List K)) (b : K) {L : ℕ}
    (hL : ∀ it ∈ items, it.2.length ≤ L) :
    ((balPoly items).eval (C b)).natDegree ≤ 2 * items.length * L := by
  classical
  rw [eval_C_balPoly]
  refine (natDegree_sum_mul_prod_erase_mul_prod_le _ _ (fun f : K[X] => C b + f) L
    fun f hf => ?_).trans ?_
  · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hf)
    refine (natDegree_add_le _ _).trans ?_
    rw [natDegree_C, max_eq_right (Nat.zero_le _)]
    exact (natDegree_fpPoly_le it.2).trans ((Nat.sub_le _ _).trans (hL it hit))
  · exact Nat.mul_le_mul_right L (Nat.mul_le_mul_left 2 (card_toFinset_fpPoly_le items))

/-- Where `balPoly` does not vanish, no denominator of the lookup sum is zero
and the lookup sum is not zero. -/
theorem of_eval_balPoly_ne_zero {items : List (K × List K)} {b c : K}
    (h : ((balPoly items).eval (C b)).eval c ≠ 0) :
    (∀ it ∈ items, b + (fpPoly it.2).eval c ≠ 0) ∧ lookupSum b c items ≠ 0 := by
  classical
  rw [eval_C_balPoly] at h
  simp only [eval_mul, eval_finsetSum, eval_prod, eval_add, eval_C] at h
  obtain ⟨hx, hsum⟩ := of_sum_mul_prod_erase_mul_prod_ne_zero _ _
    (fun f : K[X] => b + f.eval c) h
  refine ⟨fun it hit => hx _ (fpPoly_mem_toFinset hit), fun h0 => hsum ?_⟩
  rw [← h0, lookupSum, sum_map_eq_sum_filter items (fun it => fpPoly it.2) _ _
    fun it hit => fpPoly_mem_toFinset hit]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [div_eq_mul_inv, ← List.sum_map_mul_right]
  refine congrArg List.sum (List.map_congr_left fun it hit => ?_)
  have hf : fpPoly it.2 = f := of_decide_eq_true (List.mem_filter.mp hit).2
  rw [hf, div_eq_mul_inv]

/-! ## The two challenges -/

/-- **The first lookup challenge.** For a list that is not balanced, at most a
fraction `2 * n / |K|` of the values of `β` make `balPoly` vanish for every
`γ`. -/
theorem fractionLE_balPoly_beta [Fintype K] {items : List (K × List K)} (h : ¬ Balanced items) :
    FractionLE (fun b : K => (balPoly items).eval (C b) = 0)
      ((2 * items.length : ℕ) / Fintype.card K) := by
  refine (fractionLE_eval_C_eq_zero (balPoly_ne_zero h)).mono_right ?_
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (natDegree_balPoly_le items))
    (Nat.cast_nonneg _)

/-- **The second lookup challenge.** For a `β` at which `balPoly` does not
vanish for every `γ`, at most a fraction `2 * n * L / |K|` of the values of `γ`
make it vanish. -/
theorem fractionLE_balPoly_gamma [Fintype K] {items : List (K × List K)} {b : K} {L : ℕ}
    (hL : ∀ it ∈ items, it.2.length ≤ L) (hb : (balPoly items).eval (C b) ≠ 0) :
    FractionLE (fun c : K => ((balPoly items).eval (C b)).eval c = 0)
      ((2 * items.length * L : ℕ) / Fintype.card K) := by
  refine (fractionLE_eval_eq_zero hb).mono_right ?_
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (natDegree_eval_balPoly_le items b hL))
    (Nat.cast_nonneg _)

end CertiFri.Stark.Model
