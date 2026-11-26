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
# Cardinality of 32-byte (`Digest`, `BLAKE3-256`) and 64-byte (`Digest64`, `BLAKE2b-512`) outputs

This module equips `CertiFri.P3.Digest` (`8 × UInt32` = 256 bits, production
128-bit **classical** `BLAKE3-256`), `CertiFri.P3.Digest64` (`8 × UInt64` = 512
bits, 64-byte RFC 7693 `BLAKE2b-512`), and legacy `CertiFri.P3.Digest48` with
`Fintype` instances and proves their exact cardinalities in Lean's kernel:

* `card_digest : Fintype.card Digest = 2 ^ 256`
* `card_digest64 : Fintype.card Digest64 = 2 ^ 512`
* `card_digest48 : Fintype.card Digest48 = 2 ^ 384` *(ROM-only legacy; retired
  because `BLAKE3-XOF48`/`BLAKE3-XOF64` retain a 256-bit internal chaining
  value `cv`.)*

**Scope note:** A 64-byte (`2 ^ 512`) digest gives classical BCS
collision resistance (`3 * N ^ 2 / (2 * 2 ^ 512)`) in the classical ROM, **not**
certified 128-bit post-quantum soundness for the STARK/FRI protocol (Grover
search against FRI queries/PoW and QROM Fiat–Shamir are not formalized here).

For `Digest64` (`|Digest64| = 2 ^ 512`), this module proves the following
arithmetic cardinality inequalities:
* Classical BCS collision term (`c = 3 / 2`): `≤ 3 / 8` up to `N ≤ 2 ^ 255`
  (`255.71b` threshold) and `≤ N / (4 * 2 ^ 128)` for all `N ≤ 2 ^ 128`;
* Arithmetic ratio `Q ^ 3 / 2 ^ 512` (the generic BHT collision formula):
  `≤ 1 / 2 ^ 128` at `Q ≤ 2 ^ 128` and `≤ 1 / 4` at `Q ≤ 2 ^ 170`;
* Arithmetic ratio `Q ^ 5 / (2 ^ 512) ^ 2` (the generic CNS collision formula):
  `≤ 1 / 16` at `Q ≤ 2 ^ 204`;
* Arithmetic identity `Q ^ 2 / 2 ^ 512 = (Q / 2 ^ 256) ^ 2` (generic Grover
  preimage formula on a 512-bit output space, not a protocol-level QROM bound).
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

/-- Equivalence between `UInt64` and `Fin (2 ^ 64)`. -/
def uint64EquivFin : UInt64 ≃ Fin (2 ^ 64) where
  toFun u := ⟨u.toNat, u.toNat_lt⟩
  invFun n := UInt64.ofNat n.val
  left_inv u := by
    apply UInt64.toNat_inj.mp
    simp
  right_inv n := by
    apply Fin.ext
    simp

noncomputable instance : Fintype UInt64 :=
  Fintype.ofEquiv (Fin (2 ^ 64)) uint64EquivFin.symm

theorem card_uint64 : Fintype.card UInt64 = 2 ^ 64 := by
  rw [Fintype.card_congr uint64EquivFin, Fintype.card_fin]

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

/-- Exact cardinality of 32-byte `BLAKE3-256` digests: `2 ^ 256` (production
128-bit classical instantiation). -/
theorem card_digest : Fintype.card Digest = 2 ^ 256 := by
  rw [Fintype.card_congr digestEquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-- Equivalence between `Digest64` and `Fin 8 → UInt64`. -/
def digest64EquivFun : Digest64 ≃ (Fin 8 → UInt64) where
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

noncomputable instance : Fintype Digest64 :=
  Fintype.ofEquiv (Fin 8 → UInt64) digest64EquivFun.symm

instance : Nonempty Digest64 := ⟨default⟩

/-- Exact cardinality of 64-byte RFC 7693 `BLAKE2b-512` digests: `2 ^ 512`
(512-bit digest space for classical BCS collision bounds; does not by itself
certify 128-bit post-quantum protocol soundness). -/
theorem card_digest64 : Fintype.card Digest64 = 2 ^ 512 := by
  rw [Fintype.card_congr digest64EquivFun, Fintype.card_fun, Fintype.card_fin, card_uint64,
    ← pow_mul]

/-- Equivalence between legacy `Digest48` and `Fin 12 → UInt32`.
**Retired for concrete 128-bit PQ:** `BLAKE3-XOF48` retains a 256-bit internal
`cv` capping concrete BHT collision resistance at `85.3` bits. -/
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

/-- ROM-only cardinality of legacy `Digest48`: `2 ^ 384`.
**Not concrete 128-bit PQ** (`BLAKE3-XOF48` has a 256-bit internal `cv` capping
concrete BHT collision resistance at `85.3` bits). Use `card_digest64` (`BLAKE2b-512`). -/
theorem card_digest48 : Fintype.card Digest48 = 2 ^ 384 := by
  rw [Fintype.card_congr digest48EquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-! ## Production 128-bit classical (`Digest`, `BLAKE3-256`) bounds & negative controls -/

/-- For 32-byte `BLAKE3-256` under incremental sponge chaining (`c = 3 / 2`),
at `N ≤ 2 ^ 127` queries the collision bound is at most `3 / 8 < 1`
(asymptotic threshold `2 ^ 127.71` — production 128-bit classical instantiation). -/
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

/-- Negative control: for 32-byte `BLAKE3-256` at `N = 2 ^ 128` queries, even the
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

/-- Negative control: 32-byte `BLAKE3-256` (and any hash with a 256-bit internal
chaining value, including `BLAKE3-XOF48` and `BLAKE3-XOF64`) fails BHT quantum
collision resistance well below 128 bits (`Q = 2 ^ 86` already gives
`Q ^ 3 / 2 ^ 256 = 4 > 1`, i.e., `85.3` bits). -/
theorem digest_bht_quantum_collision_fails_at_86 :
    (1 : ℝ) < ((2 ^ 86 : ℕ) : ℝ) ^ 3 / Fintype.card Digest := by
  rw [card_digest, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  have h258 : (2 : ℝ) ^ (86 * 3) = 4 * (2 : ℝ) ^ 256 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ 256 := by positivity
  rw [h258, mul_div_cancel_right₀ _ hpos.ne']
  norm_num

/-! ## 64-byte digest (`Digest64`, RFC 7693 `BLAKE2b-512`) classical collision and cardinality-ratio bounds -/

/-- For 64-byte RFC 7693 `BLAKE2b-512` (`Digest64`, true 512-bit internal state)
under incremental sponge chaining (`c = 3 / 2`), the classical collision bound
stays `≤ 3 / 8 < 1` up to `N ≤ 2 ^ 255` (asymptotic threshold **`255.71` bits**!). -/
theorem digest64_sponge_collision_at_255 {N : ℕ} (hN : N ≤ 2 ^ 255) :
    3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest64) ≤ 3 / 8 := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ 255 := by exact_mod_cast hN
  have hsq : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ 255) ^ 2 := by nlinarith
  have h512 : (2 : ℝ) ^ 512 = 4 * ((2 : ℝ) ^ 255) ^ 2 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 255) ^ 2 := by positivity
  calc 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ 3 * ((2 : ℝ) ^ 255) ^ 2 / (2 * (2 : ℝ) ^ 512) := by gcongr
    _ = 3 * ((2 : ℝ) ^ 255) ^ 2 / (8 * ((2 : ℝ) ^ 255) ^ 2) := by rw [h512]; ring
    _ = 3 / 8 := by field_simp

/-- For 64-byte `BLAKE2b-512` at ANY `N ≤ 2 ^ 128` queries, the incremental-sponge
classical collision term is at most `N / (4 * 2 ^ 128)` (in fact `≤ 3 * N / 2 ^ 385`),
leaving full headroom for literal `≤ N / 2 ^ 128` total soundness. -/
theorem digest64_sponge_collision_le_quarter_128 {N : ℕ} (hN : N ≤ 2 ^ 128) :
    3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest64) ≤ (N : ℝ) / (4 * 2 ^ 128) := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have hNr : (N : ℝ) ≤ (2 : ℝ) ^ 128 := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h512 : (2 : ℝ) ^ 512 = (2 : ℝ) ^ 256 * ((2 : ℝ) ^ 128 * (2 : ℝ) ^ 128) := by
    rw [← pow_add, ← pow_add]
  have hden0 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ 512 :=
    mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 512)
  have hstep : 3 * (2 : ℝ) ^ 128 / (2 * (2 : ℝ) ^ 512) ≤ 1 / (4 * (2 : ℝ) ^ 128) := by
    rw [h512]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 128 := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow : (6 : ℝ) ≤ (2 : ℝ) ^ 256 := by
      have : (6 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      exact this.trans (pow_le_pow_right₀ (by norm_num) (by decide : 3 ≤ 256))
    nlinarith [mul_pos hpos hpos]
  calc 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      = (N : ℝ) * (3 * (N : ℝ) / (2 * (2 : ℝ) ^ 512)) := by
          rw [mul_div_assoc', sq, mul_left_comm]
    _ ≤ (N : ℝ) * (3 * (2 : ℝ) ^ 128 / (2 * (2 : ℝ) ^ 512)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith) hden0) hN0
    _ ≤ (N : ℝ) * (1 / (4 * (2 : ℝ) ^ 128)) := mul_le_mul_of_nonneg_left hstep hN0
    _ = (N : ℝ) / (4 * (2 : ℝ) ^ 128) := by ring

/-- Arithmetic inequality on the generic BHT collision-ratio expression for a
512-bit digest space (`|Digest64| = 2 ^ 512`): `Q ^ 3 / 2 ^ 512 ≤ 1 / 2 ^ 128`
when `Q ≤ 2 ^ 128`. This is a pure cardinality-ratio inequality, **not** a QROM
security proof and **not** a 128-bit post-quantum protocol certificate (Grover
search against FRI queries/PoW is unaffected by digest width). -/
theorem digest64_bht_quantum_collision_at_128 {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    (Q : ℝ) ^ 3 / Fintype.card Digest64 ≤ 1 / (2 : ℝ) ^ 128 := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have hQr : (Q : ℝ) ≤ (2 : ℝ) ^ 128 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hcube : (Q : ℝ) ^ 3 ≤ ((2 : ℝ) ^ 128) ^ 3 := pow_le_pow_left₀ hQ0 hQr 3
  have h512 : (2 : ℝ) ^ 512 = ((2 : ℝ) ^ 128) ^ 3 * (2 : ℝ) ^ 128 := by
    rw [← pow_mul, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 128) ^ 3 := by positivity
  calc (Q : ℝ) ^ 3 / (2 : ℝ) ^ 512
      ≤ ((2 : ℝ) ^ 128) ^ 3 / (2 : ℝ) ^ 512 := by gcongr
    _ = ((2 : ℝ) ^ 128) ^ 3 / (((2 : ℝ) ^ 128) ^ 3 * (2 : ℝ) ^ 128) := by rw [h512]
    _ = 1 / (2 : ℝ) ^ 128 := by field_simp

/-- Arithmetic inequality on the generic BHT collision-ratio expression for
`|Digest64| = 2 ^ 512`: for all `Q ≤ 2 ^ 170`, `Q ^ 3 / 2 ^ 512 ≤ 1 / 4 < 1`
(a pure arithmetic ratio bound, not a QROM proof). -/
theorem digest64_bht_quantum_collision_at_170 {Q : ℕ} (hQ : Q ≤ 2 ^ 170) :
    (Q : ℝ) ^ 3 / Fintype.card Digest64 ≤ 1 / 4 := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have hQr : (Q : ℝ) ≤ (2 : ℝ) ^ 170 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hcube : (Q : ℝ) ^ 3 ≤ ((2 : ℝ) ^ 170) ^ 3 := pow_le_pow_left₀ hQ0 hQr 3
  have h512 : (2 : ℝ) ^ 512 = 4 * ((2 : ℝ) ^ 170) ^ 3 := by
    rw [← pow_mul, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 170) ^ 3 := by positivity
  calc (Q : ℝ) ^ 3 / (2 : ℝ) ^ 512
      ≤ ((2 : ℝ) ^ 170) ^ 3 / (2 : ℝ) ^ 512 := by gcongr
    _ = ((2 : ℝ) ^ 170) ^ 3 / (4 * ((2 : ℝ) ^ 170) ^ 3) := by rw [h512]
    _ = 1 / 4 := by field_simp

/-- Arithmetic inequality on the generic CNS (non-qRAM) collision-ratio
expression for `|Digest64| = 2 ^ 512`: for all `Q ≤ 2 ^ 204`,
`Q ^ 5 / (2 ^ 512) ^ 2 ≤ 1 / 16 < 1` (pure arithmetic, not a QROM proof). -/
theorem digest64_cns_quantum_collision_at_204 {Q : ℕ} (hQ : Q ≤ 2 ^ 204) :
    (Q : ℝ) ^ 5 / (Fintype.card Digest64 : ℝ) ^ 2 ≤ 1 / 16 := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have hQr : (Q : ℝ) ≤ (2 : ℝ) ^ 204 := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hpow5 : (Q : ℝ) ^ 5 ≤ ((2 : ℝ) ^ 204) ^ 5 := pow_le_pow_left₀ hQ0 hQr 5
  have h1024 : ((2 : ℝ) ^ 512) ^ 2 = 16 * ((2 : ℝ) ^ 204) ^ 5 := by
    rw [← pow_mul, ← pow_mul, show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, ← pow_add]
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ 204) ^ 5 := by positivity
  calc (Q : ℝ) ^ 5 / ((2 : ℝ) ^ 512) ^ 2
      ≤ ((2 : ℝ) ^ 204) ^ 5 / ((2 : ℝ) ^ 512) ^ 2 := by gcongr
    _ = ((2 : ℝ) ^ 204) ^ 5 / (16 * ((2 : ℝ) ^ 204) ^ 5) := by rw [h1024]
    _ = 1 / 16 := by field_simp

/-- Arithmetic identity for the generic Grover preimage ratio on a 512-bit
digest space: `Q ^ 2 / |Digest64| = (Q / 2 ^ 256) ^ 2` (pure arithmetic on
hash output cardinality; does not bound Grover attacks on FRI queries/PoW). -/
theorem digest64_grover_preimage (Q : ℕ) :
    (Q : ℝ) ^ 2 / Fintype.card Digest64 = ((Q : ℝ) / 2 ^ 256) ^ 2 := by
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  have h512 : (2 : ℝ) ^ 512 = ((2 : ℝ) ^ 256) ^ 2 := by rw [← pow_mul]
  rw [h512, div_pow]

/-- Arithmetic corollary: `Q ^ 2 / |Digest64| ≤ 1` for all `Q ≤ 2 ^ 256`. -/
theorem digest64_grover_preimage_le_one {Q : ℕ} (hQ : Q ≤ 2 ^ 256) :
    (Q : ℝ) ^ 2 / Fintype.card Digest64 ≤ 1 := by
  rw [digest64_grover_preimage]
  have hQr : (Q : ℝ) / 2 ^ 256 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hQ
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) / 2 ^ 256 := by positivity
  calc ((Q : ℝ) / 2 ^ 256) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hQ0 hQr 2
    _ = 1 := one_pow 2

end CertiFri.P3
