import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import CertiFriP3.Digest

/-!
# Cardinality of 32-byte (`Digest`) and 48-byte (`Digest48`) BLAKE3 outputs

This module equips `CertiFri.P3.Digest` (8 `UInt32` words = 256 bits) and
`CertiFri.P3.Digest48` (12 `UInt32` words = 384 bits) with `Fintype` instances
and proves their exact cardinalities in Lean's kernel:

* `card_digest : Fintype.card Digest = 2 ^ 256`
* `card_digest48 : Fintype.card Digest48 = 2 ^ 384`

It also proves exact classical BCS collision bounds (`c = 3 / 2`) and exact BHT
quantum collision resistance for 48-byte BLAKE3 XOF
(`Q ^ 3 / 2 ^ 384 = (Q / 2 ^ 128) ^ 3`, giving 128.0-bit BHT quantum collision
resistance vs 85.3-bit for 32-byte outputs).
-/

namespace CertiFri.P3

/-- Equivalence between `UInt32` and `Fin (2 ^ 32)`. -/
def uint32EquivFin : UInt32 ≃ Fin (2 ^ 32) where
  toFun u := ⟨u.toNat, u.toNat_lt⟩
  invFun n := UInt32.ofNat n.val
  left_inv u := by
    apply UInt32.toNat_inj.mp
    simp
  right_inv n := by
    apply Fin.ext
    simp

noncomputable instance : Fintype UInt32 :=
  Fintype.ofEquiv (Fin (2 ^ 32)) uint32EquivFin.symm

theorem card_uint32 : Fintype.card UInt32 = 2 ^ 32 := by
  rw [Fintype.card_congr uint32EquivFin, Fintype.card_fin]

/-- Equivalence between `Digest` and `Fin 8 → UInt32`. -/
def digestEquivFun : Digest ≃ (Fin 8 → UInt32) where
  toFun d i :=
    match i.val with
    | 0 => d.w0
    | 1 => d.w1
    | 2 => d.w2
    | 3 => d.w3
    | 4 => d.w4
    | 5 => d.w5
    | 6 => d.w6
    | _ => d.w7
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩
  left_inv d := by cases d; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

noncomputable instance : Fintype Digest :=
  Fintype.ofEquiv (Fin 8 → UInt32) digestEquivFun.symm

instance : Nonempty Digest := ⟨default⟩

/-- Exact cardinality of 32-byte BLAKE3 digests: `2 ^ 256`. -/
theorem card_digest : Fintype.card Digest = 2 ^ 256 := by
  rw [Fintype.card_congr digestEquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-- Equivalence between `Digest48` and `Fin 12 → UInt32`. -/
def digest48EquivFun : Digest48 ≃ (Fin 12 → UInt32) where
  toFun d i :=
    match i.val with
    | 0 => d.w0
    | 1 => d.w1
    | 2 => d.w2
    | 3 => d.w3
    | 4 => d.w4
    | 5 => d.w5
    | 6 => d.w6
    | 7 => d.w7
    | 8 => d.w8
    | 9 => d.w9
    | 10 => d.w10
    | _ => d.w11
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11⟩
  left_inv d := by cases d; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

noncomputable instance : Fintype Digest48 :=
  Fintype.ofEquiv (Fin 12 → UInt32) digest48EquivFun.symm

instance : Nonempty Digest48 := ⟨default⟩

/-- Exact cardinality of 48-byte BLAKE3 XOF digests: `2 ^ 384`. -/
theorem card_digest48 : Fintype.card Digest48 = 2 ^ 384 := by
  rw [Fintype.card_congr digest48EquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-! ## Concrete classical BCS & BHT quantum collision bounds -/

/-- For 32-byte BLAKE3 under incremental sponge chaining (`c = 3 / 2`),
at `N ≤ 2 ^ 127` queries the collision bound is at most `3 / 8 < 1`
(asymptotic threshold `2 ^ 127.71`). -/
theorem digest_sponge_collision_at_127 {N : ℕ} (hN : N ≤ 2 ^ 127) :
    3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest) ≤ 3 / 8 := by
  rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ 127 := by exact_mod_cast hN
  have hsq : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 127) ^ 2 := by nlinarith
  have h256 : (2 : ℝ) ^ 256 = 4 * ((2 : ℝ) ^ 127) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 127) ^ 2 := by positivity
  calc 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256)
      ≤ 3 * ((2 : ℝ) ^ 127) ^ 2 / (2 * (2 : ℝ) ^ 256) := by gcongr
    _ = 3 * ((2 : ℝ) ^ 127) ^ 2 / (8 * ((2 : ℝ) ^ 127) ^ 2) := by rw [h256]; ring
    _ = 3 / 8 := by field_simp

/-- Negative control: for 32-byte BLAKE3 at `N = 2 ^ 128` queries, even the
optimal incremental-sponge collision term `3 * N ^ 2 / (2 * 2 ^ 256) = 3 / 2`
exceeds `1` (`= N / 2 ^ 128`). -/
theorem digest_sponge_collision_exceeds_one_at_128 :
    (1 : ℝ) < 3 * ((2 ^ 128 : ℕ) : ℝ) ^ 2 / (2 * Fintype.card Digest) := by
  rw [card_digest, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
  have h256 : (2 : ℝ) ^ 256 = ((2 : ℝ) ^ 128) ^ 2 := by rw [← pow_mul]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 128) ^ 2 := by positivity
  rw [h256]
  have hval : 3 * ((2 : ℝ) ^ 128) ^ 2 / (2 * ((2 : ℝ) ^ 128) ^ 2) = 3 / 2 := by field_simp
  rw [hval]
  norm_num

/-- For 48-byte BLAKE3 XOF under incremental sponge chaining (`c = 3 / 2`),
the classical collision bound stays strictly below `1` even at `N ≤ 2 ^ 191`
(clearing `190.5`-bit classical collision security, exact threshold `191.71` bits). -/
theorem digest48_sponge_collision_at_191 {N : ℕ} (hN : N ≤ 2 ^ 191) :
    3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest48) ≤ 3 / 8 := by
  rw [card_digest48, Nat.cast_pow, Nat.cast_ofNat]
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ 191 := by exact_mod_cast hN
  have hsq : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 191) ^ 2 := by nlinarith
  have h384 : (2 : ℝ) ^ 384 = 4 * ((2 : ℝ) ^ 191) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 191) ^ 2 := by positivity
  calc 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 384)
      ≤ 3 * ((2 : ℝ) ^ 191) ^ 2 / (2 * (2 : ℝ) ^ 384) := by gcongr
    _ = 3 * ((2 : ℝ) ^ 191) ^ 2 / (8 * ((2 : ℝ) ^ 191) ^ 2) := by rw [h384]; ring
    _ = 3 / 8 := by field_simp

/-- For 48-byte BLAKE3 XOF at ANY `N ≤ 2 ^ 128` queries, the per-query
classical collision rate is at most `(1 / 4) / 2 ^ 128` (in fact `≤ 3 / 2 ^ 257`),
leaving full headroom for literal `≤ N / 2 ^ 128` total classical soundness. -/
theorem digest48_sponge_collision_le_quarter_128 {N : ℕ} (hN : N ≤ 2 ^ 128) :
    3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest48) ≤ (N : ℝ) / (4 * 2 ^ 128) := by
  rw [card_digest48, Nat.cast_pow, Nat.cast_ofNat]
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ 128 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h384 : (2 : ℝ) ^ 384 = ((2 : ℝ) ^ 128) ^ 2 * (2 : ℝ) ^ 128 := by
    rw [← pow_mul, ← pow_add]
  have hden0 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ 384 :=
    mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 384)
  have hstep : 3 * (2 : ℝ) ^ 128 / (2 * (2 : ℝ) ^ 384) ≤ 1 / (4 * (2 : ℝ) ^ 128) := by
    rw [h384]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow : (6 : ℝ) ≤ (2 : ℝ) ^ 128 := by
      have : (6 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) (by decide : 3 ≤ 128))
    nlinarith [sq_pos_of_pos hpos]
  calc 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 384)
      = (N : ℝ) * (3 * (N : ℝ) / (2 * (2 : ℝ) ^ 384)) := by
          rw [mul_div_assoc', sq, mul_left_comm]
    _ ≤ (N : ℝ) * (3 * (2 : ℝ) ^ 128 / (2 * (2 : ℝ) ^ 384)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hden0) hN0
    _ ≤ (N : ℝ) * (1 / (4 * (2 : ℝ) ^ 128)) := mul_le_mul_of_nonneg_left hstep hN0
    _ = (N : ℝ) / (4 * (2 : ℝ) ^ 128) := by ring

/-- Exact BHT / Zhandry QROM collision bound for 48-byte (384-bit) BLAKE3 XOF:
`Q ^ 3 / |Digest48| = (Q / 2 ^ 128) ^ 3`, giving exact **128.0-bit** BHT quantum
collision resistance (`2 ^ (384 / 3) = 2 ^ 128`). -/
theorem digest48_bht_quantum_collision (Q : ℕ) :
    (Q : ℝ) ^ 3 / Fintype.card Digest48 = ((Q : ℝ) / 2 ^ 128) ^ 3 := by
  rw [card_digest48, Nat.cast_pow, Nat.cast_ofNat]
  have h384 : (2 : ℝ) ^ 384 = ((2 : ℝ) ^ 128) ^ 3 := by rw [← pow_mul]
  rw [h384, div_pow]

/-- 48-byte BLAKE3 XOF BHT quantum collision bound stays `≤ 1` for all `Q ≤ 2 ^ 128`. -/
theorem digest48_bht_quantum_collision_le_one {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    (Q : ℝ) ^ 3 / Fintype.card Digest48 ≤ 1 := by
  rw [digest48_bht_quantum_collision]
  have hQr : (Q : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) / 2 ^ 128 := by positivity
  calc ((Q : ℝ) / 2 ^ 128) ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hQ0 hQr 3
    _ = 1 := one_pow 3

/-- Negative control: 32-byte BLAKE3 fails BHT quantum collision resistance well
below 128 bits (`Q = 2 ^ 86` already gives `Q ^ 3 / 2 ^ 256 = 4 > 1`, i.e., `85.3` bits). -/
theorem digest_bht_quantum_collision_fails_at_86 :
    (1 : ℝ) < ((2 ^ 86 : ℕ) : ℝ) ^ 3 / Fintype.card Digest := by
  rw [card_digest, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have h258 : (2 : ℝ) ^ (86 * 3) = 4 * (2 : ℝ) ^ 256 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 256 := by positivity
  rw [h258, mul_div_cancel_right₀ _ hpos.ne']
  norm_num

end CertiFri.P3
