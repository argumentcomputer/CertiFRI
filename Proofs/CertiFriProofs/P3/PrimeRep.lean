import Mathlib
import CertiFriProofs.Refines

/-!
# Implementations of a prime field

`PrimeRep F p` says that the executable type `F` implements the integers
modulo `p` with canonical representatives: every element has a representative
below `p`, different elements have different representatives, and each
operation is the operation on representatives, reduced modulo `p`. The
statements are about natural numbers only, so they can be proved of machine
arithmetic without any algebra. For a prime `p`, such an implementation
refines the field `ZMod p`.

## Contents

* `PrimeRep`: the specification.
* `PrimeRep.toZMod`: the element of `ZMod p` an executable value stands for.
  It is a bijection (`toZMod_injective`, `toZMod_surjective`).
* `PrimeRep.refines`: the refinement of `ZMod p`, for a prime `p`.
* `Refines.map`: a refinement followed by an embedding of fields.
* `isPrimitiveRoot_two_pow_of_chain`: if each element of a sequence is the
  square of the next, the first is one and the second is minus one, then
  element `k` is a primitive root of unity of order `2 ^ k`.

## Assumptions

None beyond the hypotheses of each statement.
-/

namespace CertiFri

variable {F k K : Type} [FieldOps F] [Field k] [Field K]

/-- A refinement of a field, followed by an embedding of that field in a
larger one. -/
def Refines.map (r : Refines F k) (f : k →+* K) : Refines F K where
  toModel := fun a => f (r.toModel a)
  map_zero := by rw [r.map_zero, _root_.map_zero]
  map_one := by rw [r.map_one, _root_.map_one]
  map_add := fun a b => by rw [r.map_add, _root_.map_add]
  map_sub := fun a b => by rw [r.map_sub, _root_.map_sub]
  map_mul := fun a b => by rw [r.map_mul, _root_.map_mul]
  map_neg := fun a => by rw [r.map_neg, _root_.map_neg]
  map_inv := fun a => by rw [r.map_inv, map_inv₀]
  beq_iff := fun a b => by rw [r.beq_iff, f.injective.eq_iff]

/-- The value of an element under `Refines.map`. -/
@[simp] theorem Refines.map_toModel (r : Refines F k) (f : k →+* K) (a : F) :
    (r.map f).toModel a = f (r.toModel a) := rfl

/-- If each element of a sequence is the square of the next, the first is one
and the second is minus one, then element `k` is a primitive root of unity of
order `2 ^ k`. -/
theorem isPrimitiveRoot_two_pow_of_chain (h2 : (2 : K) ≠ 0) (g : ℕ → K) (t : ℕ)
    (h0 : g 0 = 1) (h1 : g 1 = -1) (hsq : ∀ k < t, g (k + 1) ^ 2 = g k) :
    ∀ k ≤ t, IsPrimitiveRoot (g k) (2 ^ k) := by
  have hneg : ∀ k, k + 1 ≤ t → g (k + 1) ^ 2 ^ k = -1 := by
    intro k
    induction k with
    | zero => intro _; rw [pow_zero, pow_one, h1]
    | succ k ih =>
      intro hk
      rw [pow_succ', pow_mul, hsq (k + 1) (by omega), ih (by omega)]
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  intro k hk
  cases k with
  | zero => rw [h0, pow_zero]; exact IsPrimitiveRoot.one
  | succ k =>
    have h : orderOf (g (k + 1)) = 2 ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [hneg k hk]; exact hne)
        (by rw [pow_succ, pow_mul, hneg k hk, neg_one_sq])
    rw [← h]
    exact IsPrimitiveRoot.orderOf _

namespace P3

/-- `F` implements the integers modulo `p` with canonical representatives. -/
structure PrimeRep (F : Type) [FieldOps F] (p : ℕ) where
  /-- The representative of an element. -/
  toNat : F → ℕ
  /-- The representative is below `p`. -/
  lt : ∀ a, toNat a < p
  /-- Different elements have different representatives. -/
  injective : Function.Injective toNat
  /-- Every number below `p` is a representative. -/
  surj : ∀ n < p, ∃ a, toNat a = n
  /-- The representative of zero. -/
  zero : toNat 0 = 0
  /-- The representative of one. -/
  one : toNat 1 = 1
  /-- The sum. -/
  add : ∀ a b, toNat (a + b) = (toNat a + toNat b) % p
  /-- The difference. -/
  sub : ∀ a b, toNat (a - b) = (toNat a + (p - toNat b)) % p
  /-- The product. -/
  mul : ∀ a b, toNat (a * b) = (toNat a * toNat b) % p
  /-- The opposite. -/
  neg : ∀ a, toNat (-a) = (p - toNat a) % p
  /-- The inverse of zero is zero. -/
  inv_zero : toNat (0 : F)⁻¹ = 0
  /-- The inverse of an element other than zero. -/
  inv : ∀ a, toNat a ≠ 0 → toNat a⁻¹ * toNat a % p = 1
  /-- The equality test decides equality. -/
  beq : ∀ a b : F, (a == b) = true ↔ a = b

namespace PrimeRep

variable {p : ℕ} (R : PrimeRep F p)

/-- The element of `ZMod p` an executable value stands for. -/
def toZMod (a : F) : ZMod p := (R.toNat a : ZMod p)

/-- Different elements stand for different values. -/
theorem toZMod_injective : Function.Injective R.toZMod := by
  intro a b h
  have h' := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h
  rw [Nat.mod_eq_of_lt (R.lt a), Nat.mod_eq_of_lt (R.lt b)] at h'
  exact R.injective h'

/-- Every element of `ZMod p` is the value of an element. -/
theorem toZMod_surjective [NeZero p] : Function.Surjective R.toZMod := by
  intro x
  obtain ⟨a, ha⟩ := R.surj x.val (ZMod.val_lt x)
  exact ⟨a, by rw [toZMod, ha, ZMod.natCast_zmod_val]⟩

/-- The representative is the value, read as a natural number. -/
theorem val_toZMod (a : F) : (R.toZMod a).val = R.toNat a := by
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt (R.lt a)]

/-- For a prime `p`, the implementation refines the field `ZMod p`. -/
def refines [Fact p.Prime] : Refines F (ZMod p) where
  toModel := R.toZMod
  map_zero := by rw [toZMod, R.zero, Nat.cast_zero]
  map_one := by rw [toZMod, R.one, Nat.cast_one]
  map_add := fun a b => by
    rw [toZMod, R.add, ZMod.natCast_mod, Nat.cast_add]; rfl
  map_sub := fun a b => by
    rw [toZMod, R.sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (R.lt b).le,
      ZMod.natCast_self, zero_sub, ← sub_eq_add_neg]; rfl
  map_mul := fun a b => by
    rw [toZMod, R.mul, ZMod.natCast_mod, Nat.cast_mul]; rfl
  map_neg := fun a => by
    rw [toZMod, R.neg, ZMod.natCast_mod, Nat.cast_sub (R.lt a).le, ZMod.natCast_self,
      zero_sub]; rfl
  map_inv := fun a => by
    by_cases h : R.toNat a = 0
    · have ha : a = 0 := R.injective (h.trans R.zero.symm)
      rw [ha, toZMod, R.inv_zero, toZMod, R.zero, Nat.cast_zero, _root_.inv_zero]
    · have h1 : R.toZMod a⁻¹ * R.toZMod a = 1 := by
        rw [toZMod, toZMod, ← Nat.cast_mul, ← ZMod.natCast_mod, R.inv a h, Nat.cast_one]
      exact eq_inv_of_mul_eq_one_left h1
  beq_iff := fun a b => by rw [R.beq, R.toZMod_injective.eq_iff]

/-- The abstraction map of `refines`. -/
@[simp] theorem refines_toModel [Fact p.Prime] (a : F) : R.refines.toModel a = R.toZMod a :=
  rfl

end PrimeRep

end P3

end CertiFri
