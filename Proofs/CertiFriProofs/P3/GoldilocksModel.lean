import Mathlib
import CertiFriP3.GoldilocksExt
import CertiFriProofs.P3.Primes
import CertiFriProofs.P3.GoldilocksWord
import CertiFriProofs.P3.Model

/-!
# Goldilocks and its quadratic extension are a model of the verifier's fields

The code of `CertiFriP3/Goldilocks.lean` and `CertiFriP3/GoldilocksExt.lean`
implements the field `Goldilocks.K = (ZMod p)[X] / (X^2 - 7)` of `p ^ 2`
elements, with `p = 2^64 - 2^32 + 1`, as the theorems about the verifiers
require (`StarkModel`, and through it `FieldModel` and `WellFormed`).

## Contents

* `Goldilocks.primeRep`: the base field implements the integers modulo `p`.
* `Goldilocks.twoAdicRep`: Plonky3's table of generators is compatible, so the
  generator of order `2 ^ k` is a primitive root of that order for `k ≤ 32`.
  The 32 squarings are checked by evaluating the code on machine words.
* `Goldilocks.K`, with `Goldilocks.card_K`.
* `GoldilocksExt.toZMod_nonResidue`: the constant `W` of the code is `7`.
* `GoldilocksExt.binomialRep`: the extension implements `Goldilocks.K`, with
  `c0 + c1 * X` the value of an element. The inverse of the code divides the
  conjugate `c0 - c1 * X` by the norm `c0^2 - 7 * c1^2`, which is not zero for
  an element other than zero because the model is a field.
* `Goldilocks.starkModel`: the model of the two fields.
* `Goldilocks.natCast_inj`: natural numbers below `p` are different in
  `Goldilocks.K`.

## Assumptions

None: the order is prime (`P3/Primes.lean`) and the machine arithmetic is
proved (`P3/GoldilocksWord.lean`).
-/

open Polynomial

namespace CertiFri.P3

open CertiFri.Exec.Stark

namespace Goldilocks

/-- The Goldilocks field implements the integers modulo its order. -/
def primeRep : PrimeRep Goldilocks order where
  toNat := toNat
  lt := toNat_lt_order
  injective := toNat_injective
  surj := fun _ h => exists_toNat_eq h
  zero := toNat_zero
  one := toNat_one
  add := toNat_add
  sub := toNat_sub
  mul := toNat_mul
  neg := toNat_neg
  inv_zero := toNat_inv_zero
  inv := toNat_inv order_prime
  beq := beq_iff

/-- The order is more than two. -/
theorem two_lt_order : 2 < order := by
  decide

/-- Plonky3's generators of the two-adic subgroups are compatible, and the
coset shift is not zero. -/
theorem twoAdicRep : TwoAdicRep primeRep where
  gen_zero := by decide +kernel
  gen_one := by decide +kernel
  gen_sq := by decide +kernel
  shift := by decide +kernel

/-- `X^2 - 7` is irreducible over the Goldilocks field: `7` is not a square. -/
instance irreducible_fact : Fact (Irreducible (X ^ 2 - C 7 : (ZMod order)[X])) :=
  ⟨Binomial.irreducible_two seven_not_isSquare⟩

/-- The field of `p ^ 2` elements that models the extension of Goldilocks:
`(ZMod p)[X] / (X^2 - 7)`. -/
abbrev K : Type := Binomial (ZMod order) 2 7

/-- The model field has `p ^ 2` elements. -/
theorem card_K : Fintype.card K = order ^ 2 := by
  rw [Binomial.card, ZMod.card]

/-- Natural numbers below the order are different in the model field. -/
theorem natCast_inj {a b : ℕ} (ha : a < order) (hb : b < order) (h : (a : K) = b) : a = b := by
  exact Binomial.natCast_injOn order ha hb h

end Goldilocks

namespace GoldilocksExt

open Binomial (of root ofCoords)

/-- The coordinates of an element; zero from the second on. -/
def coord (x : GoldilocksExt) (i : ℕ) : Goldilocks :=
  match i with
  | 0 => x.c0
  | 1 => x.c1
  | _ => 0

/-- The value of the constant `W` of the code is `7`. -/
theorem toZMod_nonResidue : Goldilocks.primeRep.toZMod nonResidue = 7 := by
  have h : Goldilocks.primeRep.toNat nonResidue = 7 := by decide +kernel
  rw [PrimeRep.toZMod, h, Nat.cast_ofNat]

/-- The value of an element of the base field in `ZMod p`, as the abstraction
map of the refinement. -/
local notation "φ" => Refines.toModel (PrimeRep.refines Goldilocks.primeRep)

/-- A combination of the powers of `X` is `c 0 + c 1 * X`. -/
private theorem ofCoords_eq (c : ℕ → ZMod Goldilocks.order) :
    (ofCoords c : Goldilocks.K) = of (c 0) + of (c 1) * root := by
  rw [ofCoords, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, mul_one, pow_one]

/-- The value of an element is `c0 + c1 * X`. -/
private theorem value_eq (x : GoldilocksExt) :
    (ofCoords (fun i => Goldilocks.primeRep.toZMod (coord x i)) : Goldilocks.K) =
      of (φ x.c0) + of (φ x.c1) * root :=
  ofCoords_eq _

/-- The coordinates of `a + b * X` are unique. -/
private theorem add_mul_root_eq_iff (a b a' b' : ZMod Goldilocks.order) :
    (of a + of b * root : Goldilocks.K) = of a' + of b' * root ↔ a = a' ∧ b = b' := by
  have h := Binomial.ofCoords_eq_iff (d := 2) (w := (7 : ZMod Goldilocks.order))
    (fun i => if i = 0 then a else b) (fun i => if i = 0 then a' else b')
  rw [ofCoords_eq, ofCoords_eq] at h
  refine h.trans ⟨fun h => ⟨h 0 (by decide), h 1 (by decide)⟩, fun h i hi => ?_⟩
  interval_cases i
  exacts [h.1, h.2]

/-- `a + b * X` is zero only when `a` and `b` are. -/
private theorem add_mul_root_eq_zero {a b : ZMod Goldilocks.order}
    (h : (of a + of b * root : Goldilocks.K) = 0) : a = 0 ∧ b = 0 := by
  apply (add_mul_root_eq_iff a b 0 0).mp
  rw [h, map_zero, zero_mul, add_zero]

/-- The inverse of `a + b * X` is the conjugate `a - b * X` divided by the norm
`n = a^2 - 7 * b^2`. The norm is the product of the element and its conjugate,
so it is zero only for zero, whose inverse is zero on both sides. -/
private theorem inv_eq (a b n : ZMod Goldilocks.order) (hn : n = a * a - 7 * (b * b)) :
    (of (a * n⁻¹) + of (-(b * n⁻¹)) * root : Goldilocks.K) = (of a + of b * root)⁻¹ := by
  have hroot : (root : Goldilocks.K) ^ 2 = of 7 := Binomial.root_pow
  have hnorm : (of a + of b * root) * (of a - of b * root) = (of n : Goldilocks.K) := by
    rw [hn]
    simp only [map_sub, map_mul]
    linear_combination (-(of b * of b)) * hroot
  by_cases h0 : n = 0
  · have hz : a = 0 ∧ b = 0 := by
      rw [h0, map_zero] at hnorm
      rcases mul_eq_zero.mp hnorm with h | h
      · exact add_mul_root_eq_zero h
      · have h' := add_mul_root_eq_zero (a := a) (b := -b)
          (by rw [map_neg, neg_mul, ← sub_eq_add_neg]; exact h)
        exact ⟨h'.1, neg_eq_zero.mp h'.2⟩
    rw [hz.1, hz.2, zero_mul, neg_zero, map_zero, zero_mul, add_zero, inv_zero]
  · apply eq_inv_of_mul_eq_one_right
    have h1 : (of n * of n⁻¹ : Goldilocks.K) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ h0, map_one]
    simp only [map_mul, map_neg]
    linear_combination (of n⁻¹) * hnorm + h1

/-- **The quadratic extension of Goldilocks implements `Goldilocks.K`.** -/
noncomputable def binomialRep :
    BinomialRep Goldilocks GoldilocksExt Goldilocks.primeRep 2 7 where
  coord := coord
  ext :=
    { toModel := fun x => Binomial.ofCoords fun i => Goldilocks.primeRep.toZMod (coord x i)
      map_zero := by
        rw [value_eq]
        show of (φ 0) + of (φ 0) * root = _
        rw [Refines.map_zero, map_zero, zero_mul, add_zero]
      map_one := by
        rw [value_eq]
        show of (φ 1) + of (φ 0) * root = _
        rw [Refines.map_zero, Refines.map_one, map_zero, map_one, zero_mul, add_zero]
      map_add := by
        intro a b
        rw [value_eq, value_eq a, value_eq b]
        show of (φ (a.c0 + b.c0)) + of (φ (a.c1 + b.c1)) * root = _
        rw [Refines.map_add, Refines.map_add, map_add, map_add]
        ring
      map_sub := by
        intro a b
        rw [value_eq, value_eq a, value_eq b]
        show of (φ (a.c0 - b.c0)) + of (φ (a.c1 - b.c1)) * root = _
        rw [Refines.map_sub, Refines.map_sub, map_sub, map_sub]
        ring
      map_mul := by
        intro a b
        rw [value_eq, value_eq a, value_eq b]
        show of (φ (a.c0 * b.c0 + nonResidue * (a.c1 * b.c1))) +
          of (φ (a.c0 * b.c1 + a.c1 * b.c0)) * root = _
        have hroot : (root : Goldilocks.K) ^ 2 = of 7 := Binomial.root_pow
        have hw : φ nonResidue = 7 := toZMod_nonResidue
        simp only [Refines.map_add, Refines.map_mul, map_add, map_mul, hw]
        linear_combination (-(of (φ a.c1) * of (φ b.c1))) * hroot
      map_neg := by
        intro a
        rw [value_eq, value_eq a]
        show of (φ (-a.c0)) + of (φ (-a.c1)) * root = _
        rw [Refines.map_neg, Refines.map_neg, map_neg, map_neg]
        ring
      map_inv := by
        intro a
        rw [value_eq, value_eq a]
        show of (φ (a.c0 * (a.c0 * a.c0 - nonResidue * (a.c1 * a.c1))⁻¹)) +
          of (φ (-(a.c1 * (a.c0 * a.c0 - nonResidue * (a.c1 * a.c1))⁻¹))) * root = _
        have hw : φ nonResidue = 7 := toZMod_nonResidue
        rw [Refines.map_mul, Refines.map_neg, Refines.map_mul, Refines.map_inv]
        exact inv_eq _ _ _ (by simp only [Refines.map_sub, Refines.map_mul, hw])
      beq_iff := by
        intro a b
        rw [show (a == b) = decide (a = b) from rfl, decide_eq_true_iff,
          Binomial.ofCoords_eq_iff]
        constructor
        · rintro rfl i _
          rfl
        · intro h
          have h0 : a.c0 = b.c0 := Goldilocks.primeRep.toZMod_injective (h 0 (by decide))
          have h1 : a.c1 = b.c1 := Goldilocks.primeRep.toZMod_injective (h 1 (by decide))
          cases a
          cases b
          cases h0
          cases h1
          rfl }
  toModel_eq := fun _ => rfl
  surj := by
    intro c
    exact ⟨⟨c 0, c 1⟩, fun i hi => by interval_cases i <;> rfl⟩
  degree_eq := rfl
  embed := by
    intro a i hi
    interval_cases i <;> rfl
  toBasis_size := by
    intro x
    rfl
  toBasis := by
    intro x i hi
    interval_cases i <;> rfl
  ofBasis := by
    intro a _ i hi
    rw [Array.getD_eq_getD_getElem?]
    interval_cases i <;> rfl

end GoldilocksExt

/-- **The model of Goldilocks and its quadratic extension.** -/
noncomputable def Goldilocks.starkModel : StarkModel Goldilocks GoldilocksExt Goldilocks.K :=
  P3.starkModel Goldilocks.twoAdicRep Goldilocks.two_lt_order GoldilocksExt.binomialRep

end CertiFri.P3
