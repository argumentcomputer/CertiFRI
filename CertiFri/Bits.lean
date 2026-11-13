/-!
# Bit reversal

Committed codewords are stored in bit-reversed order, so that the points folded
together in one round sit next to each other. A query index therefore names the
domain point whose exponent is the bit reversal of the index.
-/

namespace CertiFri

/-- Reverse the low `bits` bits of `x` (port of `p3_util::reverse_bits_len`). -/
def reverseBitsLen (x bits : Nat) : Nat :=
  go bits x 0
where
  /-- Move the low bit of `x` onto the end of `acc`, `bits` times. -/
  go : (bits x acc : Nat) → Nat
    | 0, _, acc => acc
    | bits + 1, x, acc => go bits (x / 2) (2 * acc + x % 2)

example : reverseBitsLen 0b1011 4 = 0b1101 := by decide
example : reverseBitsLen 0b001 3 = 0b100 := by decide
example : reverseBitsLen 5 0 = 0 := by decide

end CertiFri
