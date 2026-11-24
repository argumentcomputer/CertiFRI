import Mathlib
import CertiFriP3.Goldilocks

/-!
# The arithmetic of Goldilocks on machine words

The operations of `CertiFriP3/Goldilocks.lean` work on 64-bit words: sums and
differences with one conditional correction, the product through a 128-bit
value reduced with `2^64 = 2^32 - 1` and `2^96 = -1` modulo the order, and the
inverse by the extended Euclidean algorithm. This file proves what each
computes, as a statement about the representatives in the natural numbers.

## Contents

* `toNat_injective`, `exists_toNat_eq`: the representatives are exactly the
  numbers below the order.
* `toNat_ofUInt64`: the element of a word is the word reduced modulo the
  order.
* `toNat_zero`, `toNat_one`, `toNat_add`, `toNat_sub`, `toNat_neg`,
  `toNat_mul`: each operation is the operation on representatives, reduced
  modulo the order.
* `toNat_mulHigh`, `toNat_mulHigh_mul`: `mulHigh` and the wrapping product are
  the high and low words of the 128-bit product of two words.
* `toNat_reduce128`: `reduce128` reduces a 128-bit value, given by its two
  words, modulo the order.
* `toNat_inv_zero`, `toNat_inv`: the inverse of zero is zero, and the inverse
  of another element times that element is one modulo the order.
* `beq_iff`: the equality test decides equality.

## Assumptions

`toNat_inv` assumes that the order is prime, as a hypothesis; it is proved in
`P3/Primes.lean`. Nothing else.
-/

namespace CertiFri.P3.Goldilocks

/-- The order, as a numeral. -/
private theorem order_eq : order = 18446744069414584321 := rfl

/-- The word of the order, as a number. -/
private theorem toNat_p64 :
    (0xFFFFFFFF00000001 : UInt64).toNat = 18446744069414584321 := rfl

/-- The word `2^32 - 1`, as a number. -/
private theorem toNat_eps : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl

/-- The word one, as a number. -/
private theorem toNat_one_word : (1 : UInt64).toNat = 1 := rfl

/-- Different elements have different representatives. -/
theorem toNat_injective : Function.Injective toNat :=
  fun _ _ h => ext (UInt64.toNat_inj.mp h)

/-- Every number below the order is a representative. -/
theorem exists_toNat_eq {n : ℕ} (h : n < order) : ∃ a : Goldilocks, a.toNat = n := by
  rw [order_eq] at h
  have hn : n < UInt64.size := by rw [UInt64.size]; omega
  refine ⟨⟨UInt64.ofNatLT n hn, ?_⟩, UInt64.toNat_ofNatLT⟩
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNatLT, toNat_p64]
  exact h

/-- The representative of the element of a word is the word reduced modulo the order. A word
is below twice the order, so the reduction is at most one subtraction. -/
theorem toNat_ofUInt64 (x : UInt64) : (ofUInt64 x).toNat = x.toNat % order := by
  have hx := x.toNat_lt
  rw [order_eq]
  unfold ofUInt64
  split
  · rename_i h
    have h' := UInt64.lt_iff_toNat_lt.mp h
    rw [toNat_p64] at h'
    show x.toNat = _
    omega
  · rename_i h
    have hle : (0xFFFFFFFF00000001 : UInt64) ≤ x := UInt64.not_lt.mp h
    have h' := UInt64.le_iff_toNat_le.mp hle
    rw [toNat_p64] at h'
    show (x - 0xFFFFFFFF00000001).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ hle, toNat_p64]
    omega

/-- The representative of zero. -/
theorem toNat_zero : (0 : Goldilocks).toNat = 0 := rfl

/-- The representative of one. -/
theorem toNat_one : (1 : Goldilocks).toNat = 1 := rfl

/-- The word `p - b` of an element `b` does not wrap. -/
private theorem toNat_p64_sub (b : Goldilocks) :
    ((0xFFFFFFFF00000001 : UInt64) - b.val).toNat = 18446744069414584321 - b.val.toNat := by
  have hb : b.val.toNat < 18446744069414584321 := b.toNat_lt_order
  have hle : b.val ≤ (0xFFFFFFFF00000001 : UInt64) := by
    rw [UInt64.le_iff_toNat_le, toNat_p64]; omega
  rw [UInt64.toNat_sub_of_le _ _ hle, toNat_p64]

/-- The sum, on representatives. -/
theorem toNat_add (a b : Goldilocks) : (a + b).toNat = (a.toNat + b.toNat) % order := by
  have ha : a.val.toNat < 18446744069414584321 := a.toNat_lt_order
  have hb : b.val.toNat < 18446744069414584321 := b.toNat_lt_order
  have hnb := toNat_p64_sub b
  show (Goldilocks.add a b).toNat = (a.val.toNat + b.val.toNat) % 18446744069414584321
  unfold Goldilocks.add
  by_cases h : (0xFFFFFFFF00000001 : UInt64) - b.val ≤ a.val
  · have h' := UInt64.le_iff_toNat_le.mp h
    simp only [h, ↓reduceIte]
    rw [toNat_ofUInt64, UInt64.toNat_sub_of_le _ _ h, hnb, order_eq]
    omega
  · have h' := mt UInt64.le_iff_toNat_le.mpr h
    simp only [h, ↓reduceIte]
    rw [toNat_ofUInt64, UInt64.toNat_add, order_eq]
    omega

/-- The difference, on representatives. -/
theorem toNat_sub (a b : Goldilocks) :
    (a - b).toNat = (a.toNat + (order - b.toNat)) % order := by
  have ha : a.val.toNat < 18446744069414584321 := a.toNat_lt_order
  have hb : b.val.toNat < 18446744069414584321 := b.toNat_lt_order
  have hnb := toNat_p64_sub b
  show (Goldilocks.sub a b).toNat =
    (a.val.toNat + (18446744069414584321 - b.val.toNat)) % 18446744069414584321
  unfold Goldilocks.sub
  by_cases h : b.val ≤ a.val
  · have h' := UInt64.le_iff_toNat_le.mp h
    simp only [h, ↓reduceIte]
    rw [toNat_ofUInt64, UInt64.toNat_sub_of_le _ _ h, order_eq]
    omega
  · have h' := mt UInt64.le_iff_toNat_le.mpr h
    simp only [h, ↓reduceIte]
    rw [toNat_ofUInt64, UInt64.toNat_add, hnb, order_eq]
    omega

/-- The opposite, on representatives. -/
theorem toNat_neg (a : Goldilocks) : (-a).toNat = (order - a.toNat) % order := by
  show (Goldilocks.neg a).toNat = (order - a.val.toNat) % order
  unfold Goldilocks.neg
  rw [toNat_ofUInt64, toNat_p64_sub, order_eq]

/-- Masking a word with `2^32 - 1` keeps its low half. -/
private theorem toNat_and_eps (x : UInt64) :
    (x &&& 0xFFFFFFFF).toNat = x.toNat % 4294967296 := by
  rw [UInt64.toNat_and, toNat_eps]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

/-- Shifting a word right by 32 keeps its high half. -/
private theorem toNat_shiftRight_32 (x : UInt64) :
    (x >>> 32).toNat = x.toNat / 4294967296 := by
  rw [UInt64.toNat_shiftRight]
  exact Nat.shiftRight_eq_div_pow x.toNat 32

/-- A product of two numbers below `2^32` is at most `(2^32 - 1)^2`. -/
private theorem mul_half_le {x y : ℕ} (hx : x < 4294967296) (hy : y < 4294967296) :
    x * y ≤ 18446744065119617025 :=
  Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)

/-- `mulHigh` is the high word of the 128-bit product of two words. With the operands split
in halves of 32 bits, the four partial products are atoms for `omega`, which checks that no
partial sum wraps and that the carries add up. -/
theorem toNat_mulHigh (a b : UInt64) : (mulHigh a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have ha0 : a.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
  have hb0 : b.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by omega)
  have ha1 : a.toNat / 4294967296 < 4294967296 := by omega
  have hb1 : b.toNat / 4294967296 < 4294967296 := by omega
  have h00 := mul_half_le ha0 hb0
  have h01 := mul_half_le ha0 hb1
  have h10 := mul_half_le ha1 hb0
  have h11 := mul_half_le ha1 hb1
  have hab : a.toNat * b.toNat =
      a.toNat / 4294967296 * (b.toNat / 4294967296) * 18446744073709551616 +
      (a.toNat / 4294967296 * (b.toNat % 4294967296) +
        a.toNat % 4294967296 * (b.toNat / 4294967296)) * 4294967296 +
      a.toNat % 4294967296 * (b.toNat % 4294967296) := by
    conv_lhs => rw [← Nat.div_add_mod a.toNat 4294967296, ← Nat.div_add_mod b.toNat 4294967296]
    ring
  rw [hab]
  unfold mulHigh
  simp only [UInt64.toNat_add, UInt64.toNat_mul, toNat_and_eps, toNat_shiftRight_32]
  omega

/-- `mulHigh` and the wrapping product are the high and low words of the 128-bit product of
two words. -/
theorem toNat_mulHigh_mul (a b : UInt64) :
    (mulHigh a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  rw [toNat_mulHigh, UInt64.toNat_mul]
  exact Nat.div_add_mod' _ _

/-- `reduce128` reduces the 128-bit value `hi * 2^64 + lo` modulo the order, for all words
`hi` and `lo`.

With `hi = hh * 2^32 + hl`, the value is `lo - hh + hl * (2^32 - 1)` plus
`(hh * (2^32 + 1) + hl) * p`. The word `t0` is `lo - hh`, or `lo - hh + p` after a borrow;
the sum `t0 + t1` loses `2^64` when it wraps, and adding `2^32 - 1` makes the loss `p`. -/
theorem toNat_reduce128 (hi lo : UInt64) :
    (reduce128 hi lo).toNat = (hi.toNat * 2 ^ 64 + lo.toNat) % order := by
  have hhi := hi.toNat_lt
  have hlo := lo.toNat_lt
  have hhh := toNat_shiftRight_32 hi
  have hhl := toNat_and_eps hi
  unfold reduce128
  rw [toNat_ofUInt64, order_eq]
  generalize hi >>> 32 = hh at hhh ⊢
  generalize hi &&& 0xFFFFFFFF = hl at hhl ⊢
  have ht1 : (hl * 0xFFFFFFFF).toNat = hl.toNat * 4294967295 := by
    rw [UInt64.toNat_mul, toNat_eps]; omega
  generalize hl * 0xFFFFFFFF = t1 at ht1 ⊢
  have ht0 : ∃ K, hi.toNat * 2 ^ 64 + lo.toNat =
      (if lo < hh then lo - hh - 0xFFFFFFFF else lo - hh).toNat + t1.toNat +
        K * 18446744069414584321 := by
    by_cases h : lo < hh
    · have h' := UInt64.lt_iff_toNat_lt.mp h
      simp only [h, ↓reduceIte]
      rw [UInt64.toNat_sub, UInt64.toNat_sub, toNat_eps]
      exact ⟨hh.toNat * 4294967297 + hl.toNat - 1, by omega⟩
    · have h' := UInt64.not_lt.mp h
      have h'' := UInt64.le_iff_toNat_le.mp h'
      simp only [h, ↓reduceIte]
      rw [UInt64.toNat_sub_of_le _ _ h']
      exact ⟨hh.toNat * 4294967297 + hl.toNat, by omega⟩
  generalize (if lo < hh then lo - hh - 0xFFFFFFFF else lo - hh) = t0 at ht0 ⊢
  obtain ⟨K, hK⟩ := ht0
  rw [hK, Nat.add_mul_mod_self_right]
  have ht0 := t0.toNat_lt
  have ht2 := UInt64.toNat_add t0 t1
  generalize t0 + t1 = t2 at ht2 ⊢
  by_cases h : t2 < t1
  · have h' := UInt64.lt_iff_toNat_lt.mp h
    have hwrap : t0.toNat + t1.toNat = t2.toNat + 18446744073709551616 := by omega
    have hfit : (t2.toNat + 4294967295) % 2 ^ 64 = t2.toNat + 4294967295 := by omega
    simp only [h, ↓reduceIte]
    rw [UInt64.toNat_add, toNat_eps, hfit, hwrap]
    omega
  · have h' := mt UInt64.lt_iff_toNat_lt.mpr h
    have hfit : t0.toNat + t1.toNat = t2.toNat := by omega
    simp only [h, ↓reduceIte]
    rw [hfit]

/-- The product, on representatives. -/
theorem toNat_mul (a b : Goldilocks) : (a * b).toNat = (a.toNat * b.toNat) % order := by
  show (Goldilocks.mul a b).toNat = (a.val.toNat * b.val.toNat) % order
  unfold Goldilocks.mul
  rw [toNat_reduce128, toNat_mulHigh_mul]

/-- The inverse of zero is zero. -/
theorem toNat_inv_zero : ((0 : Goldilocks)⁻¹).toNat = 0 := by
  show (invLoop 0xFFFFFFFF00000001 0 0 1 false).toNat = 0
  rw [invLoop]
  rfl

/-- The extended Euclidean algorithm returns the inverse of `A`, from any state that
satisfies its invariant: the remainders satisfy `0 < r1 < r0` and are coprime, the cofactors
satisfy `t1 * r0 + t0 * r1 = p` over the natural numbers, and modulo `p` the remainders are
`r1 = s * t1 * A` and `r0 = -s * t0 * A`, where the sign `s` is `-1` when `odd` and `1`
otherwise.

The equation on the cofactors bounds them by `p`, so the words that hold them do not wrap.
Coprimality and `0 < r1` exclude a remainder of zero, so the loop stops at `r1 = 1`. -/
private theorem invLoop_spec (A : ℕ) (r0 r1 t0 t1 : UInt64) (odd : Bool)
    (hpos : 0 < r1.toNat) (hlt : r1.toNat < r0.toNat)
    (hgcd : Nat.gcd r0.toNat r1.toNat = 1)
    (hsum : t1.toNat * r0.toNat + t0.toNat * r1.toNat = order)
    (h1 : (r1.toNat : ZMod order) = (if odd then -1 else 1) * t1.toNat * A)
    (h0 : (r0.toNat : ZMod order) = -(if odd then -1 else 1) * t0.toNat * A) :
    ((invLoop r0 r1 t0 t1 odd).toNat : ZMod order) * A = 1 := by
  fun_induction invLoop r0 r1 t0 t1 odd with
  | case1 r0 t0 t1 _ =>
    rw [toNat_one_word] at hlt hsum h1
    have ht1 : t1.toNat ≤ 18446744069414584321 := by
      have := Nat.le_mul_of_pos_right t1.toNat (Nat.zero_lt_of_lt hlt)
      rw [order_eq] at hsum
      omega
    have hle : t1 ≤ (0xFFFFFFFF00000001 : UInt64) := by
      rw [UInt64.le_iff_toNat_le, toNat_p64]; exact ht1
    rw [toNat_ofUInt64, ZMod.natCast_mod, UInt64.toNat_sub_of_le _ _ hle, toNat_p64, ← order_eq,
      Nat.cast_sub (by rw [order_eq]; exact ht1), ZMod.natCast_self]
    simp only [↓reduceIte, Nat.cast_one] at h1
    linear_combination (-1 : ZMod order) * h1
  | case2 r0 t0 t1 odd hodd _ =>
    rw [toNat_one_word] at h1
    rw [toNat_ofUInt64, ZMod.natCast_mod]
    simp only [hodd, Bool.false_eq_true, ↓reduceIte, Nat.cast_one] at h1
    linear_combination (-1 : ZMod order) * h1
  | case3 r0 r1 t0 t1 odd hle hne =>
    have hle' := UInt64.le_iff_toNat_le.mp hle
    have hne' := mt UInt64.toNat_inj.mp hne
    rw [toNat_one_word] at hle' hne'
    omega
  | case4 r0 r1 t0 t1 odd hgt hmod ih =>
    have hgt' := mt UInt64.le_iff_toNat_le.mpr hgt
    rw [toNat_one_word] at hgt'
    obtain ⟨q, m, hq, hm, hdiv⟩ : ∃ q m, r0.toNat / r1.toNat = q ∧ r0.toNat % r1.toNat = m ∧
        r0.toNat = r1.toNat * q + m := ⟨_, _, rfl, rfl, (Nat.div_add_mod _ _).symm⟩
    have hsum' : (t0.toNat + q * t1.toNat) * r1.toNat + t1.toNat * m = order := by
      rw [← hsum, hdiv]; ring
    have hfit : (t0 + r0 / r1 * t1).toNat = t0.toNat + q * t1.toNat := by
      have := Nat.le_mul_of_pos_right (t0.toNat + q * t1.toNat) hpos
      rw [order_eq] at hsum'
      rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_div, hq]
      omega
    have hr0 : (r0.toNat : ZMod order) = r1.toNat * q + m := by
      rw [hdiv]; push_cast; ring
    have hs : (if (!odd) = true then (-1 : ZMod order) else 1) =
        -(if odd = true then -1 else 1) := by
      cases odd <;> simp
    apply ih
    · rw [UInt64.toNat_mod, hm]
      refine Nat.pos_of_ne_zero fun h => ?_
      have hdvd : r1.toNat ∣ Nat.gcd r0.toNat r1.toNat :=
        Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (hm.trans h)) (dvd_refl _)
      rw [hgcd, Nat.dvd_one] at hdvd
      omega
    · exact hmod
    · rw [UInt64.toNat_mod, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
      exact hgcd
    · rw [hfit, UInt64.toNat_mod, hm]
      exact hsum'
    · rw [hfit, UInt64.toNat_mod, hm, hs]
      push_cast
      linear_combination h0 - hr0 - (q : ZMod order) * h1
    · rw [hs]
      linear_combination h1

/-- The inverse of an element other than zero, times the element, is one. -/
theorem toNat_inv (hp : order.Prime) (a : Goldilocks) (ha : a.toNat ≠ 0) :
    a⁻¹.toNat * a.toNat % order = 1 := by
  have hlt : a.toNat < order := a.toNat_lt_order
  have hpos : 0 < a.toNat := Nat.pos_of_ne_zero ha
  have hgcd : Nat.gcd (0xFFFFFFFF00000001 : UInt64).toNat a.val.toNat = 1 := by
    rw [toNat_p64, ← order_eq]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_of_pos_of_lt hpos hlt)
  have hsum : (1 : UInt64).toNat * (0xFFFFFFFF00000001 : UInt64).toNat +
      (0 : UInt64).toNat * a.val.toNat = order := by
    rw [toNat_p64, toNat_one_word, order_eq, UInt64.toNat_zero]
    omega
  have h := invLoop_spec a.toNat 0xFFFFFFFF00000001 a.val 0 1 false hpos
    (by rw [toNat_p64, ← order_eq]; exact hlt) hgcd hsum
    (by rw [toNat_one_word]; simp [toNat])
    (by rw [toNat_p64, ← order_eq, ZMod.natCast_self, UInt64.toNat_zero]; simp)
  have hone : 1 % order = 1 := rfl
  exact ((ZMod.natCast_eq_natCast_iff' _ _ _).mp (by push_cast; exact h)).trans hone

/-- The equality test decides equality. -/
theorem beq_iff (a b : Goldilocks) : (a == b) = true ↔ a = b := by
  show decide (a = b) = true ↔ a = b
  exact decide_eq_true_iff

end CertiFri.P3.Goldilocks
