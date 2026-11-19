import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import CertiFri.Bits

/-!
# Bit reversal

Facts about `reverseBitsLen`, the executable bit reversal that turns a query
index into the exponent of its domain point.

`reverseBitsLen x b` reverses the low `b` bits of `x` and ignores the others.
The file gives its two recursions (`reverseBitsLen_succ` peels the lowest bit of
`x`, `reverseBitsLen_succ'` adds a bit to `b`), its bits
(`testBit_reverseBitsLen`), the bound `reverseBitsLen x b < 2 ^ b`, and the fact
that reversing twice gives back the low `b` bits.

There are no assumptions. Machine words are not covered: Plonky3's
`reverse_bits_len` works on a `usize`, and these lemmas are about the function
on unbounded naturals.
-/

namespace CertiFri

namespace Domain

/-- The accumulator of the bit-reversal loop ends up above the reversed bits. -/
theorem reverseBitsLen_go (bits x acc : ℕ) :
    reverseBitsLen.go bits x acc = acc * 2 ^ bits + reverseBitsLen.go bits x 0 := by
  induction bits generalizing x acc with
  | zero => simp [reverseBitsLen.go]
  | succ b ih =>
    rw [reverseBitsLen.go, ih, reverseBitsLen.go, ih (x / 2) (2 * 0 + x % 2)]
    ring

/-- Reversing no bits gives zero. -/
@[simp]
theorem reverseBitsLen_zero (x : ℕ) : reverseBitsLen x 0 = 0 := rfl

/-- The lowest bit of `x` becomes the highest bit of its reversal. -/
theorem reverseBitsLen_succ (x b : ℕ) :
    reverseBitsLen x (b + 1) = x % 2 * 2 ^ b + reverseBitsLen (x / 2) b := by
  unfold reverseBitsLen
  rw [reverseBitsLen.go, reverseBitsLen_go]
  simp

/-- Reversing one more bit of `x` appends bit `b` of `x` below the reversal. -/
theorem reverseBitsLen_succ' (x b : ℕ) :
    reverseBitsLen x (b + 1) = 2 * reverseBitsLen x b + x / 2 ^ b % 2 := by
  induction b generalizing x with
  | zero => simp [reverseBitsLen_succ]
  | succ b ih =>
    rw [reverseBitsLen_succ, ih, reverseBitsLen_succ x b, Nat.div_div_eq_div_mul, ← pow_succ']
    ring

/-- The reversal of `b` bits is below `2 ^ b`. -/
theorem reverseBitsLen_lt (x b : ℕ) : reverseBitsLen x b < 2 ^ b := by
  induction b generalizing x with
  | zero => simp
  | succ b ih =>
    have h1 := ih (x / 2)
    have h2 := Nat.mod_lt x two_pos
    rw [reverseBitsLen_succ, pow_succ]
    nlinarith

/-- Bit `i` of the reversal of `b` bits of `x` is bit `b - 1 - i` of `x`. -/
theorem testBit_reverseBitsLen (x b i : ℕ) :
    (reverseBitsLen x b).testBit i = (decide (i < b) && x.testBit (b - 1 - i)) := by
  induction b generalizing x i with
  | zero => simp
  | succ b ih =>
    rw [reverseBitsLen_succ']
    cases i with
    | zero =>
      simp [Nat.testBit_eq_decide_div_mod_eq]
    | succ i =>
      have h1 : (2 * reverseBitsLen x b + x / 2 ^ b % 2) / 2 = reverseBitsLen x b := by omega
      have h2 : b + 1 - 1 - (i + 1) = b - 1 - i := by omega
      rw [Nat.testBit_add_one, h1, h2, ih]
      simp

/-- Reversing twice keeps the low `b` bits. -/
theorem reverseBitsLen_reverseBitsLen (x b : ℕ) :
    reverseBitsLen (reverseBitsLen x b) b = x % 2 ^ b := by
  induction b generalizing x with
  | zero => simp [Nat.mod_one]
  | succ b ih =>
    rw [reverseBitsLen_succ, reverseBitsLen_succ' x b, Nat.mul_add_mod, Nat.mod_mod,
      Nat.mul_add_div two_pos, Nat.div_eq_of_lt (Nat.mod_lt _ two_pos), add_zero, ih,
      Nat.mod_pow_succ]
    ring

/-- The reversal reads only the low `b` bits. -/
theorem reverseBitsLen_mod (x b : ℕ) : reverseBitsLen (x % 2 ^ b) b = reverseBitsLen x b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [testBit_reverseBitsLen, Nat.testBit_mod_two_pow]
  by_cases hi : i < b
  · have : b - 1 - i < b := by omega
    simp [hi, this]
  · simp [hi]

/-- An index below `2 ^ b` is determined by its reversal. -/
theorem reverseBitsLen_inj {b x y : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b)
    (h : reverseBitsLen x b = reverseBitsLen y b) : x = y := by
  have := congrArg (reverseBitsLen · b) h
  simpa only [reverseBitsLen_reverseBitsLen, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using this

/-- Reversing extra high bits of an index below `2 ^ b` shifts the reversal up. -/
theorem reverseBitsLen_add_of_lt {b x : ℕ} (hx : x < 2 ^ b) (k : ℕ) :
    reverseBitsLen x (b + k) = 2 ^ k * reverseBitsLen x b := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : x / 2 ^ (b + k) = 0 :=
      Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right two_pos (Nat.le_add_right b k)))
    rw [← add_assoc, reverseBitsLen_succ', ih, this, pow_succ]
    ring

/-- The reversal of an even index: the left child of `x`. -/
theorem reverseBitsLen_two_mul (x b : ℕ) :
    reverseBitsLen (2 * x) (b + 1) = reverseBitsLen x b := by
  simp [reverseBitsLen_succ]

/-- The reversal of an odd index: the right child of `x`. -/
theorem reverseBitsLen_two_mul_add_one (x b : ℕ) :
    reverseBitsLen (2 * x + 1) (b + 1) = 2 ^ b + reverseBitsLen x b := by
  rw [reverseBitsLen_succ]
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  rw [h1, h2, one_mul]

end Domain

end CertiFri
