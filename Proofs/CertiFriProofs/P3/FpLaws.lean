import Mathlib
import CertiFriP3.PrimeField
import CertiFriProofs.P3.PrimeRep

/-!
# The prime fields on natural numbers are fields

`Fp p` (`CertiFriP3/PrimeField.lean`) stores an element as its representative
below `p` and computes with the natural numbers. For a prime `p` it implements
the integers modulo `p` in the sense of `PrimeRep`, and so refines `ZMod p`.

## Contents

* `Fp.val_powBits`: the square-and-multiply loop computes the power modulo
  `p`.
* `Fp.primeRep`: `Fp p` is a `PrimeRep` for a prime `p`.

## Assumptions

`p` is prime, as a hypothesis. The inverse is the power `p - 2`, which is the
inverse by Fermat's little theorem.
-/

namespace CertiFri.P3.Fp

variable {p : ℕ}

/-- The square-and-multiply loop computes the power modulo `p`, for an exponent
below `2 ^ bits`, when `one` represents one. -/
theorem val_powBits (one x : Fp p) (hone : one.val = 1 % p) (bits : ℕ) :
    ∀ n, n < 2 ^ bits → (powBits one x bits n).val = x.val ^ n % p := by
  induction bits with
  | zero =>
    intro n h
    obtain rfl : n = 0 := by simpa using h
    rw [powBits, hone, pow_zero]
  | succ bits ih =>
    intro n h
    have hhalf : n / 2 < 2 ^ bits := by
      rw [pow_succ] at h
      omega
    have e := ih (n / 2) hhalf
    simp only [powBits]
    split
    · show (_ * _) % p = _
      rw [e, ← Nat.mul_mod, ← pow_add]
      congr 2
      omega
    · show ((_ * _) % p * x.val) % p = _
      rw [e, ← Nat.mul_mod, Nat.mod_mul_mod, ← pow_add, ← pow_succ]
      congr 2
      omega

/-- For a prime `p`, the field `Fp p` implements the integers modulo `p`. -/
def primeRep [NeZero p] (hp : p.Prime) : PrimeRep (Fp p) p where
  toNat := Fp.val
  lt := fun a => a.lt
  injective := fun _ _ h => Fp.ext h
  surj := fun n hn => ⟨⟨n, hn⟩, rfl⟩
  zero := Nat.zero_mod p
  one := Nat.mod_eq_of_lt hp.one_lt
  add := fun _ _ => rfl
  sub := fun _ _ => rfl
  mul := fun _ _ => rfl
  neg := fun _ => rfl
  inv_zero := by
    show (Fp.inv (ofNat 0)).val = 0
    have h : (ofNat 0 : Fp p).val = 0 := Nat.zero_mod p
    rw [Fp.inv, ite_eq_left h, h]
  inv := by
    intro a ha
    show (Fp.inv a).val * a.val % p = 1
    have hlt : p - 2 < 2 ^ (Nat.log2 p + 1) :=
      lt_of_le_of_lt (Nat.sub_le p 2) Nat.lt_log2_self
    have hcop : Nat.Coprime a.val p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero ha) a.lt))
    have hfermat := Nat.ModEq.pow_totient hcop
    have h2 : p - 2 + 1 = p - 1 := by have := hp.two_le; omega
    rw [Nat.totient_prime hp, Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] at hfermat
    rw [Fp.inv, ite_eq_right ha, val_powBits _ _ rfl _ _ hlt, Nat.mod_mul_mod, ← pow_succ, h2,
      hfermat]
  beq := fun _ _ => decide_eq_true_iff

/-- The representative of `primeRep` is the stored one. -/
@[simp] theorem primeRep_toNat [NeZero p] (hp : p.Prime) (a : Fp p) :
    (primeRep hp).toNat a = a.val :=
  rfl

end CertiFri.P3.Fp
