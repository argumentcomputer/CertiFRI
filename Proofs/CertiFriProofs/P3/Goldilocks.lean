import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Prime
import CertiFriP3.Goldilocks
import CertiFriProofs.Refines

/-!
# Formal verification of the Goldilocks field `CertiFriP3/Goldilocks.lean`

This file proves, strictly in Lean's kernel without `sorry`, `axiom`,
`native_decide`, or `bv_decide`, that `CertiFri.P3.Goldilocks` faithfully
implements the prime field `ZMod Goldilocks.order` (`p = 2^64 - 2^32 + 1`):

* `goldilocks_prime`: `Nat.Prime Goldilocks.order`, via Lucas's primality
  certificate with primitive root `7` and the Fermat-prime factorization
  `p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`.
* `goldilocks_refines`: `Refines Goldilocks (ZMod Goldilocks.order)`, verifying
  every executable `UInt64` operation (`add`, `sub`, `neg`, 128-bit `mulHigh`
  + `reduce128`, extended-Euclidean `invLoop`/`inv`, and `==`).
* `goldilocks_twoAdicGenerator_isPrimitiveRoot`: for every `n ≤ 32`,
  `Goldilocks.twoAdicGenerator n` represents a primitive `2^n`-th root of unity
  in `ZMod Goldilocks.order`.
* `goldilocks_cosetShift_ne_zero`: `Goldilocks.generator` (`7`) is nonzero in
  `ZMod Goldilocks.order`.
-/

namespace CertiFri.P3

/-! ## Primality of `p = 2^64 - 2^32 + 1` via Lucas's test -/

/-- Verify that `tbl` is the table of repeated squarings `[cur, cur^2 % m, cur^4 % m, ...]`
starting from `cur`. Each step multiplies `Nat` literals, so the kernel checks
64 steps without recursion-depth or call-by-name blowup. -/
def checkSqTable (m : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | cur, x :: rest => (cur == x) && checkSqTable m ((x * x) % m) rest

/-- Multiply `acc` by the entries of `tbl` selected by the binary digits of `e`,
modulo `m`. Linear in `tbl.length` in the Lean kernel. -/
def mulByBits (m : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | _, [], acc => acc
  | e, sq :: rest, acc =>
    let acc' := if e % 2 = 1 then (acc * sq) % m else acc
    mulByBits m (e / 2) rest acc'

theorem mulByBits_spec (m : ℕ) :
    ∀ (tbl : List ℕ) (cur e acc : ℕ),
      checkSqTable m cur tbl = true →
      e < 2 ^ tbl.length →
      (mulByBits m e tbl acc : ZMod m) = (acc : ZMod m) * (cur : ZMod m) ^ e
  | [], _, e, acc, _, he => by
    have h0 : e = 0 := by simp at he; exact he
    subst h0
    simp [mulByBits]
  | x :: rest, cur, e, acc, hchk, he => by
    simp only [checkSqTable, Bool.and_eq_true, beq_iff_eq] at hchk
    obtain ⟨hcur, hrest⟩ := hchk
    subst hcur
    have hhalf_lt : e / 2 < 2 ^ rest.length := by
      simp only [List.length_cons, pow_succ] at he
      omega
    simp only [mulByBits]
    rw [mulByBits_spec m rest ((cur * cur) % m) (e / 2) _ hrest hhalf_lt]
    rw [ZMod.natCast_mod, Nat.cast_mul, ← sq, ← pow_mul]
    split_ifs with hodd
    · rw [ZMod.natCast_mod, Nat.cast_mul, mul_assoc, ← pow_succ']
      congr 2
      omega
    · congr 2
      omega

theorem mulByBits_lt (m : ℕ) (hm : 0 < m) :
    ∀ (tbl : List ℕ) (e acc : ℕ), acc < m → mulByBits m e tbl acc < m
  | [], _, _, hacc => hacc
  | _ :: rest, e, acc, hacc => by
    simp only [mulByBits]
    refine mulByBits_lt m hm rest (e / 2) _ ?_
    split_ifs
    · exact Nat.mod_lt _ hm
    · exact hacc

private theorem goldilocks_order_pos : 0 < Goldilocks.order := by
  unfold Goldilocks.order
  decide

private theorem goldilocks_order_sub_one_eq :
    Goldilocks.order - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 := by
  unfold Goldilocks.order
  decide

private theorem zmod_cast_ne_one_of_lt {m x : ℕ} (hx : x < m) (h1 : x ≠ 1) (hm : 1 < m) :
    (x : ZMod m) ≠ 1 := by
  have : NeZero m := ⟨by omega⟩
  intro heq
  have hval := congrArg ZMod.val heq
  rw [ZMod.val_natCast_of_lt hx, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hm] at hval
  exact h1 hval

/-- Squaring table `7^(2^k) mod p` for `k = 0, …, 63`, certified by `sqTable7_ok`. -/
private def sqTable7 : List ℕ :=
  [7, 49, 2401, 5764801, 33232930569601, 3732854072722565977, 11250886851934520606,
   12159723539389677939, 1536671775522476176, 18371408314118145657, 2431605942540367610,
   6358221588783459004, 10083885515493449909, 15094611910849701842, 18060412910171584788,
   10529651373896570371, 11156834669773791359, 11840798296997857860, 1447330804268045396,
   15265864706138236984, 12990112920302977158, 16491641580159807679, 17642952523097762870,
   4419967652436713981, 7206579306846404579, 17869454728573311546, 4919185416341570378,
   14445320067108370181, 17666966662873528270, 5473358340599679662, 4120449531758749877,
   17380019310548783236, 12275445934081160404, 4756475762779100925, 8312008622371998338,
   3688660304411827445, 6534114114080170934, 12241777603010464820, 6822456961749002749,
   14740284407083446365, 14198376421529404772, 16372603252271478917, 6094962593300533783,
   12855798221536971597, 4570035464479216815, 13312966101283008305, 17717521521350689785,
   2579852125121816621, 5647278486080789199, 10087368686013698258, 13705325519725492466,
   16094056529116650251, 839801632116640137, 809314592928515922, 17285123329644556226,
   13607546115301327129, 8495382904317313497, 7711545778172399998, 14653638268244293248,
   4449853170003902284, 16684733269283358279, 10831206780798498119, 8050641074587903850,
   1066724758865801085]

private theorem sqTable7_ok : checkSqTable Goldilocks.order 7 sqTable7 = true := rfl
private theorem sqTable7_len : sqTable7.length = 64 := rfl

private theorem goldilocks_pow7_spec (e : ℕ) (he : e < 2 ^ 64) :
    (mulByBits Goldilocks.order e sqTable7 1 : ZMod Goldilocks.order) =
      ((7 : ℕ) : ZMod Goldilocks.order) ^ e := by
  simpa using mulByBits_spec Goldilocks.order sqTable7 7 e 1 sqTable7_ok (sqTable7_len ▸ he)

private theorem goldilocks_powMod_full :
    mulByBits Goldilocks.order (Goldilocks.order - 1) sqTable7 1 = 1 := rfl

private theorem goldilocks_powMod_div2 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 2) sqTable7 1 ≠ 1 := by decide

private theorem goldilocks_powMod_div3 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 3) sqTable7 1 ≠ 1 := by decide

private theorem goldilocks_powMod_div5 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 5) sqTable7 1 ≠ 1 := by decide

private theorem goldilocks_powMod_div17 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 17) sqTable7 1 ≠ 1 := by decide

private theorem goldilocks_powMod_div257 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 257) sqTable7 1 ≠ 1 := by decide

private theorem goldilocks_powMod_div65537 :
    mulByBits Goldilocks.order ((Goldilocks.order - 1) / 65537) sqTable7 1 ≠ 1 := by decide

private theorem prime_65537 : Nat.Prime 65537 := by norm_num
private theorem prime_257 : Nat.Prime 257 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num

private theorem prime_dvd_goldilocks_sub_one {q : ℕ} (hq : Nat.Prime q)
    (hdvd : q ∣ Goldilocks.order - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  rw [goldilocks_order_sub_one_eq] at hdvd
  rcases hq.dvd_mul.mp hdvd with h1 | h65537
  · rcases hq.dvd_mul.mp h1 with h2 | h257
    · rcases hq.dvd_mul.mp h2 with h3 | h17
      · rcases hq.dvd_mul.mp h3 with h4 | h5
        · rcases hq.dvd_mul.mp h4 with h2pow | h3'
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2pow))
          · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h3'))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).mp h5)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq prime_17).mp h17))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq prime_257).mp h257)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hq prime_65537).mp h65537)))))

/-- **Primality of the Goldilocks modulus `p = 2^64 - 2^32 + 1`.** Proved in the
Lean kernel via Lucas's primality test with witness `7`. -/
theorem goldilocks_prime : Nat.Prime Goldilocks.order := by
  refine lucas_primality Goldilocks.order ((7 : ℕ) : ZMod Goldilocks.order) ?_ ?_
  · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide), goldilocks_powMod_full]
    rfl
  · intro q hq hdvd
    have hm1 : 1 < Goldilocks.order := by unfold Goldilocks.order; decide
    rcases prime_dvd_goldilocks_sub_one hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div2 hm1
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div3 hm1
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div5 hm1
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div17 hm1
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div257 hm1
    · rw [← goldilocks_pow7_spec _ (by unfold Goldilocks.order; decide)]
      exact zmod_cast_ne_one_of_lt (mulByBits_lt _ goldilocks_order_pos _ _ _ hm1)
        goldilocks_powMod_div65537 hm1

instance : Fact (Nat.Prime Goldilocks.order) := ⟨goldilocks_prime⟩

/-! ## Refinement `Refines Goldilocks (ZMod Goldilocks.order)` -/

namespace Goldilocks

/-- The abstraction map from canonical `Goldilocks` words to `ZMod Goldilocks.order`. -/
def toZMod (a : Goldilocks) : ZMod Goldilocks.order :=
  (a.val.toNat : ZMod Goldilocks.order)

private theorem p64_toNat : (0xFFFFFFFF00000001 : UInt64).toNat = Goldilocks.order := rfl
private theorem eps_toNat : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl

theorem toZMod_ofUInt64 (x : UInt64) : toZMod (ofUInt64 x) = (x.toNat : ZMod Goldilocks.order) := by
  unfold toZMod ofUInt64
  split_ifs with h
  · rfl
  · have hle : (0xFFFFFFFF00000001 : UInt64) ≤ x := UInt64.not_lt.mp h
    have hleN : Goldilocks.order ≤ x.toNat := by
      simpa only [UInt64.le_iff_toNat_le, p64_toNat] using hle
    rw [UInt64.toNat_sub_of_le _ _ hle, p64_toNat, Nat.cast_sub hleN, ZMod.natCast_self, sub_zero]

theorem toZMod_zero : toZMod (0 : Goldilocks) = 0 := by
  show toZMod Goldilocks.zero = 0
  unfold Goldilocks.zero
  rw [toZMod_ofUInt64]
  rfl

theorem toZMod_one : toZMod (1 : Goldilocks) = 1 := by
  show toZMod Goldilocks.one = 1
  unfold Goldilocks.one
  rw [toZMod_ofUInt64]
  rfl

theorem toZMod_add (a b : Goldilocks) : toZMod (a + b) = toZMod a + toZMod b := by
  show toZMod (Goldilocks.add a b) = toZMod a + toZMod b
  unfold Goldilocks.add
  dsimp only
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hb : b.val.toNat < Goldilocks.order := b.toNat_lt_order
  have hble : b.val ≤ (0xFFFFFFFF00000001 : UInt64) :=
    UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
  have hnb : ((0xFFFFFFFF00000001 : UInt64) - b.val).toNat = Goldilocks.order - b.val.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hble, p64_toNat]
  split_ifs with h
  · rw [toZMod_ofUInt64, UInt64.toNat_sub_of_le _ _ h, hnb]
    have hle : Goldilocks.order - b.val.toNat ≤ a.val.toNat := by
      rw [← hnb]; exact UInt64.le_iff_toNat_le.mp h
    have heq : a.val.toNat - (Goldilocks.order - b.val.toNat) + Goldilocks.order =
        a.val.toNat + b.val.toNat := by omega
    have hcast : (((a.val.toNat - (Goldilocks.order - b.val.toNat) + Goldilocks.order : ℕ) :
        ZMod Goldilocks.order)) = ((a.val.toNat + b.val.toNat : ℕ) : ZMod Goldilocks.order) :=
      congrArg Nat.cast heq
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero] at hcast
    exact hcast
  · rw [toZMod_ofUInt64, UInt64.toNat_add]
    have hlt : a.val.toNat < Goldilocks.order - b.val.toNat := by
      have := UInt64.not_le.mp h
      rw [UInt64.lt_iff_toNat_lt, hnb] at this
      exact this
    have hsum : a.val.toNat + b.val.toNat < 2 ^ 64 := by
      unfold Goldilocks.order at hlt; omega
    rw [Nat.mod_eq_of_lt hsum, Nat.cast_add]
    rfl

theorem toZMod_sub (a b : Goldilocks) : toZMod (a - b) = toZMod a - toZMod b := by
  show toZMod (Goldilocks.sub a b) = toZMod a - toZMod b
  unfold Goldilocks.sub
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hb : b.val.toNat < Goldilocks.order := b.toNat_lt_order
  split_ifs with h
  · rw [toZMod_ofUInt64, UInt64.toNat_sub_of_le _ _ h, Nat.cast_sub (UInt64.le_iff_toNat_le.mp h)]
    rfl
  · have hble : b.val ≤ (0xFFFFFFFF00000001 : UInt64) :=
      UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
    have hnb : ((0xFFFFFFFF00000001 : UInt64) - b.val).toNat = Goldilocks.order - b.val.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ hble, p64_toNat]
    have hlt : a.val.toNat < b.val.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h)
    rw [toZMod_ofUInt64, UInt64.toNat_add, hnb]
    have hsum : a.val.toNat + (Goldilocks.order - b.val.toNat) < 2 ^ 64 := by
      unfold Goldilocks.order at *; omega
    rw [Nat.mod_eq_of_lt hsum, Nat.cast_add, Nat.cast_sub hb.le, ZMod.natCast_self]
    unfold toZMod
    ring

theorem toZMod_neg (a : Goldilocks) : toZMod (-a) = -toZMod a := by
  show toZMod (Goldilocks.neg a) = -toZMod a
  unfold Goldilocks.neg
  have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
  have hale : a.val ≤ (0xFFFFFFFF00000001 : UInt64) :=
    UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; omega)
  rw [toZMod_ofUInt64, UInt64.toNat_sub_of_le _ _ hale, p64_toNat, Nat.cast_sub ha.le,
    ZMod.natCast_self, zero_sub]
  rfl

private theorem uint64_and_eps (x : UInt64) : (x &&& (0xFFFFFFFF : UInt64)).toNat = x.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and, eps_toNat]
  exact Nat.and_two_pow_sub_one_eq_mod x.toNat 32

private theorem uint64_shift32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  have h32 : (32 : UInt64).toNat = 32 := rfl
  rw [UInt64.toNat_shiftRight, h32, Nat.mod_eq_of_lt (by decide : 32 < 64),
    Nat.shiftRight_eq_div_pow]

private theorem mulHigh_arith (A0 A1 B0 B1 M M2 : ℕ)
    (hM : M = A0 * B1 + A0 * B0 / 2 ^ 32)
    (hM2 : M2 = A1 * B0 + M % 2 ^ 32) :
    (A1 * 2 ^ 32 + A0) * (B1 * 2 ^ 32 + B0) =
      (A1 * B1 + M / 2 ^ 32 + M2 / 2 ^ 32) * 2 ^ 64 +
      (M2 % 2 ^ 32 * 2 ^ 32 + A0 * B0 % 2 ^ 32) := by
  have h1 : M = M / 2 ^ 32 * 2 ^ 32 + M % 2 ^ 32 := (Nat.div_add_mod' M (2 ^ 32)).symm
  have h2 : M2 = M2 / 2 ^ 32 * 2 ^ 32 + M2 % 2 ^ 32 := (Nat.div_add_mod' M2 (2 ^ 32)).symm
  have h3 : A0 * B0 = A0 * B0 / 2 ^ 32 * 2 ^ 32 + A0 * B0 % 2 ^ 32 :=
    (Nat.div_add_mod' (A0 * B0) (2 ^ 32)).symm
  zify at hM hM2 h1 h2 h3 ⊢
  linear_combination (2 ^ 32 : ℤ) * (h2 - hM2) + (2 ^ 32 : ℤ) * (h1 - hM) + h3

private theorem zmod_cast_eq_of_add_order {x y : ℕ} (h : x + Goldilocks.order = y) :
    (x : ZMod Goldilocks.order) = (y : ZMod Goldilocks.order) := by
  rw [← h, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- Exact 128-bit multiplication identity for `Goldilocks.mulHigh`. -/
theorem mulHigh_spec (a b : UInt64) :
    (mulHigh a b).toNat * 2 ^ 64 + (a * b).toNat = a.toNat * b.toNat := by
  unfold mulHigh
  dsimp only
  set a0 := a &&& (0xFFFFFFFF : UInt64)
  set a1 := a >>> 32
  set b0 := b &&& (0xFFFFFFFF : UInt64)
  set b1 := b >>> 32
  have ha0 : a0.toNat = a.toNat % 2 ^ 32 := uint64_and_eps a
  have ha1 : a1.toNat = a.toNat / 2 ^ 32 := uint64_shift32 a
  have hb0 : b0.toNat = b.toNat % 2 ^ 32 := uint64_and_eps b
  have hb1 : b1.toNat = b.toNat / 2 ^ 32 := uint64_shift32 b
  have ha_lt : a.toNat < 2 ^ 64 := a.toNat_lt
  have hb_lt : b.toNat < 2 ^ 64 := b.toNat_lt
  have ha0_lt : a0.toNat < 2 ^ 32 := ha0 ▸ Nat.mod_lt _ (by decide)
  have ha1_lt : a1.toNat < 2 ^ 32 := by omega
  have hb0_lt : b0.toNat < 2 ^ 32 := hb0 ▸ Nat.mod_lt _ (by decide)
  have hb1_lt : b1.toNat < 2 ^ 32 := by omega
  have hmul_no_ov : ∀ x y : UInt64, x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 →
      (x * y).toNat = x.toNat * y.toNat := fun x y hx hy => by
    rw [UInt64.toNat_mul]
    exact Nat.mod_eq_of_lt (by nlinarith)
  have ha0b0 : (a0 * b0).toNat = a0.toNat * b0.toNat := hmul_no_ov a0 b0 ha0_lt hb0_lt
  have ha0b1 : (a0 * b1).toNat = a0.toNat * b1.toNat := hmul_no_ov a0 b1 ha0_lt hb1_lt
  have ha1b0 : (a1 * b0).toNat = a1.toNat * b0.toNat := hmul_no_ov a1 b0 ha1_lt hb0_lt
  have ha1b1 : (a1 * b1).toNat = a1.toNat * b1.toNat := hmul_no_ov a1 b1 ha1_lt hb1_lt
  set mid := a0 * b1 + ((a0 * b0) >>> 32)
  have hmid_val : mid.toNat = a0.toNat * b1.toNat + (a0.toNat * b0.toNat) / 2 ^ 32 := by
    rw [UInt64.toNat_add, ha0b1, uint64_shift32 (a0 * b0), ha0b0]
    have hdiv_lt : a0.toNat * b0.toNat / 2 ^ 32 < 2 ^ 32 := by
      have : a0.toNat * b0.toNat < 2 ^ 32 * 2 ^ 32 := by nlinarith
      omega
    have hlt : a0.toNat * b1.toNat + a0.toNat * b0.toNat / 2 ^ 32 < 2 ^ 64 := by nlinarith
    exact Nat.mod_eq_of_lt hlt
  have hmid_div_lt : mid.toNat / 2 ^ 32 < 2 ^ 32 := by
    have : mid.toNat < 2 ^ 32 * 2 ^ 32 := by
      rw [hmid_val]
      have : a0.toNat * b0.toNat / 2 ^ 32 < 2 ^ 32 := by
        have : a0.toNat * b0.toNat < 2 ^ 32 * 2 ^ 32 := by nlinarith
        omega
      nlinarith
    omega
  set mid2 := a1 * b0 + (mid &&& (0xFFFFFFFF : UInt64))
  have hmid2_val : mid2.toNat = a1.toNat * b0.toNat + mid.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_add, ha1b0, uint64_and_eps mid]
    have hrem : mid.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have hlt : a1.toNat * b0.toNat + mid.toNat % 2 ^ 32 < 2 ^ 64 := by nlinarith
    exact Nat.mod_eq_of_lt hlt
  have hmid2_div_lt : mid2.toNat / 2 ^ 32 < 2 ^ 32 := by
    have : mid2.toNat < 2 ^ 32 * 2 ^ 32 := by
      rw [hmid2_val]
      have : mid.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
      nlinarith
    omega
  have hhi_val : (a1 * b1 + (mid >>> 32) + (mid2 >>> 32)).toNat =
      a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 + mid2.toNat / 2 ^ 32 := by
    have ha1b1_le : a1.toNat * b1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h1 : (a1 * b1 + (mid >>> 32)).toNat = a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 := by
      rw [UInt64.toNat_add, ha1b1, uint64_shift32 mid]
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, h1, uint64_shift32 mid2]
    exact Nat.mod_eq_of_lt (by omega)
  have ha_eq : a.toNat = a1.toNat * 2 ^ 32 + a0.toNat := by omega
  have hb_eq : b.toNat = b1.toNat * 2 ^ 32 + b0.toNat := by omega
  have hprod : a.toNat * b.toNat =
      (a1.toNat * b1.toNat + mid.toNat / 2 ^ 32 + mid2.toNat / 2 ^ 32) * 2 ^ 64 +
      (mid2.toNat % 2 ^ 32 * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32) := by
    rw [ha_eq, hb_eq]
    exact mulHigh_arith a0.toNat a1.toNat b0.toNat b1.toNat mid.toNat mid2.toNat hmid_val hmid2_val
  have hlo_lt : mid2.toNat % 2 ^ 32 * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32 < 2 ^ 64 := by
    have h1 : mid2.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h2 : (a0.toNat * b0.toNat) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    omega
  have hlo_eq : (a * b).toNat =
      mid2.toNat % 2 ^ 32 * 2 ^ 32 + (a0.toNat * b0.toNat) % 2 ^ 32 := by
    rw [UInt64.toNat_mul, hprod, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlo_lt]
  rw [hhi_val, hlo_eq, hprod]

/-- Modular identities `2^64 = 2^32 - 1` and `2^96 = -1` in `ZMod Goldilocks.order`. -/
private theorem two_pow_64_zmod :
    ((2 ^ 64 : ℕ) : ZMod Goldilocks.order) = ((2 ^ 32 - 1 : ℕ) : ZMod Goldilocks.order) := by
  have h : 2 ^ 64 = Goldilocks.order + (2 ^ 32 - 1) := by unfold Goldilocks.order; decide
  have hc := congrArg (Nat.cast (R := ZMod Goldilocks.order)) h
  simpa [ZMod.natCast_self] using hc

private theorem two_pow_96_zmod :
    ((2 ^ 96 : ℕ) : ZMod Goldilocks.order) = -1 := by
  have h : 2 ^ 96 + 1 = Goldilocks.order * (2 ^ 32 + 1) := by unfold Goldilocks.order; decide
  have hc := congrArg (Nat.cast (R := ZMod Goldilocks.order)) h
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, ZMod.natCast_self, zero_mul] at hc
  exact eq_neg_of_add_eq_zero_left hc

/-- Reduction of a 128-bit integer `hi * 2^64 + lo` modulo `Goldilocks.order`. -/
theorem reduce128_spec (hi lo : UInt64) :
    toZMod (reduce128 hi lo) =
      (hi.toNat : ZMod Goldilocks.order) * ((2 ^ 64 : ℕ) : ZMod Goldilocks.order) +
        (lo.toNat : ZMod Goldilocks.order) := by
  unfold reduce128
  dsimp only
  set hh := hi >>> 32
  set hl := hi &&& (0xFFFFFFFF : UInt64)
  have hhh : hh.toNat = hi.toNat / 2 ^ 32 := uint64_shift32 hi
  have hhl : hl.toNat = hi.toNat % 2 ^ 32 := uint64_and_eps hi
  have hhh_lt : hh.toNat < 2 ^ 32 := by have := hi.toNat_lt; omega
  have hhl_lt : hl.toNat < 2 ^ 32 := hhl ▸ Nat.mod_lt _ (by decide)
  set t0 := if lo < hh then lo - hh - (0xFFFFFFFF : UInt64) else lo - hh
  have ht0 : (t0.toNat : ZMod Goldilocks.order) =
      (lo.toNat : ZMod Goldilocks.order) - (hh.toNat : ZMod Goldilocks.order) := by
    dsimp only [t0]
    split_ifs with hlt
    · have hltN : lo.toNat < hh.toNat := UInt64.lt_iff_toNat_lt.mp hlt
      have hsub1 : (lo - hh).toNat = 2 ^ 64 + lo.toNat - hh.toNat := by
        rw [UInt64.toNat_sub]
        have hlo : lo.toNat < 2 ^ 64 := lo.toNat_lt
        have hhh' : hh.toNat < 2 ^ 64 := by omega
        omega
      have hge_eps : (0xFFFFFFFF : UInt64) ≤ lo - hh := by
        rw [UInt64.le_iff_toNat_le, eps_toNat, hsub1]
        omega
      rw [UInt64.toNat_sub_of_le _ _ hge_eps, hsub1, eps_toNat]
      have heq : (2 ^ 64 + lo.toNat - hh.toNat - (2 ^ 32 - 1)) + hh.toNat =
          lo.toNat + Goldilocks.order := by
        unfold Goldilocks.order; omega
      have hc : (((2 ^ 64 + lo.toNat - hh.toNat - (2 ^ 32 - 1) : ℕ) : ZMod Goldilocks.order) +
          (hh.toNat : ZMod Goldilocks.order)) = (lo.toNat : ZMod Goldilocks.order) := by
        rw [← Nat.cast_add]
        exact (zmod_cast_eq_of_add_order heq.symm).symm
      exact eq_sub_of_add_eq hc
    · have hle : hh ≤ lo := UInt64.not_lt.mp hlt
      rw [UInt64.toNat_sub_of_le _ _ hle, Nat.cast_sub (UInt64.le_iff_toNat_le.mp hle)]
  set t1 := hl * (0xFFFFFFFF : UInt64)
  have ht1_le_sq : hl.toNat * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have ht1_lt : hl.toNat * (2 ^ 32 - 1) < 2 ^ 64 := lt_of_le_of_lt ht1_le_sq (by decide)
  have ht1_nat : t1.toNat = hl.toNat * (2 ^ 32 - 1) := by
    rw [UInt64.toNat_mul, eps_toNat, Nat.mod_eq_of_lt ht1_lt]
  have ht1 : (t1.toNat : ZMod Goldilocks.order) =
      (hl.toNat : ZMod Goldilocks.order) * ((2 ^ 32 - 1 : ℕ) : ZMod Goldilocks.order) := by
    rw [ht1_nat, Nat.cast_mul]
  set t2 := t0 + t1
  rw [toZMod_ofUInt64]
  have ht2_zmod : ((if t2 < t1 then t2 + (0xFFFFFFFF : UInt64) else t2).toNat :
      ZMod Goldilocks.order) =
      (t0.toNat : ZMod Goldilocks.order) + (t1.toNat : ZMod Goldilocks.order) := by
    have h0_lt : t0.toNat < 2 ^ 64 := t0.toNat_lt
    have h1_lt : t1.toNat < 2 ^ 64 := t1.toNat_lt
    split_ifs with hcarry
    · have hltN : t2.toNat < t1.toNat := UInt64.lt_iff_toNat_lt.mp hcarry
      have hov : 2 ^ 64 ≤ t0.toNat + t1.toNat := by
        by_contra hlt2
        push Not at hlt2
        have : t2.toNat = t0.toNat + t1.toNat := by
          rw [UInt64.toNat_add, Nat.mod_eq_of_lt hlt2]
        omega
      have ht2_val : t2.toNat = t0.toNat + t1.toNat - 2 ^ 64 := by
        rw [UInt64.toNat_add]
        have hlt2 : t0.toNat + t1.toNat - 2 ^ 64 < 2 ^ 64 := by omega
        have : (t0.toNat + t1.toNat) % 2 ^ 64 = (t0.toNat + t1.toNat - 2 ^ 64) % 2 ^ 64 := by
          conv_lhs => rw [show t0.toNat + t1.toNat = (t0.toNat + t1.toNat - 2 ^ 64) + 2 ^ 64 by omega]
          rw [Nat.add_mod_right]
        rw [this, Nat.mod_eq_of_lt hlt2]
      have ht1_le : t1.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
        rw [ht1_nat]; exact ht1_le_sq
      have hno_ov2 : t2.toNat + (2 ^ 32 - 1) < 2 ^ 64 := by omega
      rw [UInt64.toNat_add, eps_toNat, Nat.mod_eq_of_lt hno_ov2]
      have heq : (t2.toNat + (2 ^ 32 - 1)) + Goldilocks.order = t0.toNat + t1.toNat := by
        unfold Goldilocks.order; omega
      rw [← Nat.cast_add]
      exact zmod_cast_eq_of_add_order heq
    · have hgeN : t1.toNat ≤ t2.toNat := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hcarry)
      have hno_ov : t0.toNat + t1.toNat < 2 ^ 64 := by
        by_contra hov
        push Not at hov
        have ht2_val : t2.toNat = t0.toNat + t1.toNat - 2 ^ 64 := by
          rw [UInt64.toNat_add]
          have hlt2 : t0.toNat + t1.toNat - 2 ^ 64 < 2 ^ 64 := by omega
          have : (t0.toNat + t1.toNat) % 2 ^ 64 = (t0.toNat + t1.toNat - 2 ^ 64) % 2 ^ 64 := by
            conv_lhs => rw [show t0.toNat + t1.toNat = (t0.toNat + t1.toNat - 2 ^ 64) + 2 ^ 64 by omega]
            rw [Nat.add_mod_right]
          rw [this, Nat.mod_eq_of_lt hlt2]
        omega
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt hno_ov, Nat.cast_add]
  rw [ht2_zmod, ht0, ht1]
  have hhi_split : hi.toNat = hh.toNat * 2 ^ 32 + hl.toNat := by omega
  have hhi_cast : (hi.toNat : ZMod Goldilocks.order) * ((2 ^ 64 : ℕ) : ZMod Goldilocks.order) =
      (hh.toNat : ZMod Goldilocks.order) * ((2 ^ 96 : ℕ) : ZMod Goldilocks.order) +
      (hl.toNat : ZMod Goldilocks.order) * ((2 ^ 64 : ℕ) : ZMod Goldilocks.order) := by
    rw [hhi_split, Nat.cast_add, Nat.cast_mul, add_mul, mul_assoc]
    have hpow : ((2 ^ 32 : ℕ) : ZMod Goldilocks.order) * ((2 ^ 64 : ℕ) : ZMod Goldilocks.order) =
        ((2 ^ 96 : ℕ) : ZMod Goldilocks.order) := by
      rw [← Nat.cast_mul]
      norm_num
    rw [hpow]
  rw [hhi_cast, two_pow_96_zmod, two_pow_64_zmod]
  ring

theorem toZMod_mul (a b : Goldilocks) : toZMod (a * b) = toZMod a * toZMod b := by
  show toZMod (Goldilocks.mul a b) = toZMod a * toZMod b
  unfold Goldilocks.mul
  rw [reduce128_spec]
  have h := congrArg (Nat.cast (R := ZMod Goldilocks.order)) (mulHigh_spec a.val b.val)
  simp only [Nat.cast_add, Nat.cast_mul] at h
  exact h

/-- Loop invariant for `Goldilocks.invLoop`, proved by strong induction on `r1.toNat`. -/
private theorem toZMod_invLoop (a : Goldilocks) :
    ∀ (n : ℕ) (r0 r1 t0 t1 : UInt64) (odd : Bool),
      r1.toNat = n →
      0 < r0.toNat →
      r0.toNat ≤ Goldilocks.order →
      r1.toNat ≤ Goldilocks.order →
      t1.toNat * r0.toNat + t0.toNat * r1.toNat = Goldilocks.order →
      (r0.toNat : ZMod Goldilocks.order) =
        (if odd then (t0.toNat : ZMod Goldilocks.order)
         else -(t0.toNat : ZMod Goldilocks.order)) * toZMod a →
      (r1.toNat : ZMod Goldilocks.order) =
        (if odd then -(t1.toNat : ZMod Goldilocks.order)
         else (t1.toNat : ZMod Goldilocks.order)) * toZMod a →
      (a.val = 0 ∨ Nat.gcd r0.toNat r1.toNat = 1) →
      (r1.toNat = 0 → a.val = 0) →
      toZMod (invLoop r0 r1 t0 t1 odd) = (toZMod a)⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro r0 r1 t0 t1 odd hr1 hr0_pos hr0 hr1_le hbez hcong0 hcong1 hgcd hzero
    unfold invLoop
    by_cases hle : r1 ≤ 1
    · rw [dite_eq_left hle]
      by_cases h1 : r1 = 1
      · rw [ite_eq_left h1]
        subst h1
        have ht1_le : t1.toNat ≤ Goldilocks.order := by nlinarith
        have hmul1 : (if odd then -(t1.toNat : ZMod Goldilocks.order)
            else (t1.toNat : ZMod Goldilocks.order)) * toZMod a = 1 := by
          have h1N : (1 : UInt64).toNat = 1 := rfl
          rw [← hcong1, h1N, Nat.cast_one]
        have hres : toZMod (if odd then ofUInt64 ((0xFFFFFFFF00000001 : UInt64) - t1)
            else ofUInt64 t1) =
            (if odd then -(t1.toNat : ZMod Goldilocks.order)
             else (t1.toNat : ZMod Goldilocks.order)) := by
          cases odd
          · simp [toZMod_ofUInt64]
          · simp only [↓reduceIte]
            have ht1_u : t1 ≤ (0xFFFFFFFF00000001 : UInt64) :=
              UInt64.le_iff_toNat_le.mpr (by rw [p64_toNat]; exact ht1_le)
            rw [toZMod_ofUInt64, UInt64.toNat_sub_of_le _ _ ht1_u, p64_toNat,
              Nat.cast_sub ht1_le, ZMod.natCast_self, zero_sub]
        rw [hres]
        exact eq_inv_of_mul_eq_one_left hmul1
      · rw [ite_eq_right h1]
        have hr1_0 : r1.toNat = 0 := by
          have hleN : r1.toNat ≤ 1 := UInt64.le_iff_toNat_le.mp hle
          have hne1 : r1.toNat ≠ 1 := fun he => h1 (UInt64.toNat_inj.mp he)
          omega
        have ha0 : a.val = 0 := hzero hr1_0
        have haz : toZMod a = 0 := by
          unfold toZMod; rw [ha0]; rfl
        rw [haz, inv_zero]
        exact toZMod_zero
    · rw [dite_eq_right hle]
      dsimp only
      have hr1_gt1 : 1 < r1.toNat := by
        have := UInt64.not_le.mp hle
        exact UInt64.lt_iff_toNat_lt.mp this
      have hr2_lt : (r0 % r1).toNat < n := by
        rw [UInt64.toNat_mod, ← hr1]
        exact Nat.mod_lt _ (by omega)
      set q := r0 / r1
      set r2 := r0 % r1
      set t2 := t0 + q * t1
      have hqN : q.toNat = r0.toNat / r1.toNat := UInt64.toNat_div r0 r1
      have hr2N : r2.toNat = r0.toNat % r1.toNat := UInt64.toNat_mod r0 r1
      have hdiv : q.toNat * r1.toNat + r2.toNat = r0.toNat := by
        rw [hqN, hr2N, Nat.mul_comm]; exact Nat.div_add_mod r0.toNat r1.toNat
      have hbezN : (t0.toNat + q.toNat * t1.toNat) * r1.toNat + t1.toNat * r2.toNat =
          Goldilocks.order := by
        have : (t0.toNat + q.toNat * t1.toNat) * r1.toNat + t1.toNat * r2.toNat =
            t1.toNat * (q.toNat * r1.toNat + r2.toNat) + t0.toNat * r1.toNat := by ring
        rw [this, hdiv, hbez]
      have ht2_bound : t0.toNat + q.toNat * t1.toNat < 2 ^ 64 := by
        have hp_lt : Goldilocks.order < 2 ^ 64 := by unfold Goldilocks.order; decide
        have : (t0.toNat + q.toNat * t1.toNat) * r1.toNat ≤ Goldilocks.order := by omega
        nlinarith
      have hqt1_bound : q.toNat * t1.toNat < 2 ^ 64 := by omega
      have hqt1 : (q * t1).toNat = q.toNat * t1.toNat := by
        rw [UInt64.toNat_mul, Nat.mod_eq_of_lt hqt1_bound]
      have ht2N : t2.toNat = t0.toNat + q.toNat * t1.toNat := by
        rw [UInt64.toNat_add, hqt1, Nat.mod_eq_of_lt ht2_bound]
      have hbez' : t2.toNat * r1.toNat + t1.toNat * r2.toNat = Goldilocks.order := by
        rw [ht2N]; exact hbezN
      have hr2_le : r2.toNat ≤ Goldilocks.order := by omega
      refine ih r2.toNat hr2_lt r1 r2 t1 t2 (!odd) rfl (by omega) hr1_le hr2_le hbez' ?_ ?_ ?_ ?_
      · cases odd <;> simpa using hcong1
      · have hr2_zmod : (r2.toNat : ZMod Goldilocks.order) =
            (r0.toNat : ZMod Goldilocks.order) -
              (q.toNat : ZMod Goldilocks.order) * (r1.toNat : ZMod Goldilocks.order) := by
          have hc := congrArg (Nat.cast (R := ZMod Goldilocks.order)) hdiv
          simp only [Nat.cast_add, Nat.cast_mul] at hc
          exact eq_sub_of_add_eq' hc
        rw [hr2_zmod, hcong0, hcong1, ht2N, Nat.cast_add, Nat.cast_mul]
        cases odd <;> simp <;> ring
      · rcases hgcd with ha0 | hg
        · exact Or.inl ha0
        · refine Or.inr ?_
          rw [hr2N]
          have : Nat.gcd r1.toNat (r0.toNat % r1.toNat) = Nat.gcd r0.toNat r1.toNat := by
            rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
          rw [this, hg]
      · intro hr2_0
        rcases hgcd with ha0 | hg
        · exact ha0
        · exfalso
          rw [hr2N] at hr2_0
          have hdvd : r1.toNat ∣ r0.toNat := Nat.dvd_of_mod_eq_zero hr2_0
          have hg' : Nat.gcd r0.toNat r1.toNat = r1.toNat := Nat.gcd_eq_right hdvd
          omega

theorem toZMod_inv (a : Goldilocks) : toZMod a⁻¹ = (toZMod a)⁻¹ := by
  show toZMod (Goldilocks.inv a) = (toZMod a)⁻¹
  unfold Goldilocks.inv
  refine toZMod_invLoop a a.val.toNat (0xFFFFFFFF00000001 : UInt64) a.val 0 1 false rfl
    (by rw [p64_toNat]; exact goldilocks_order_pos)
    (by rw [p64_toNat]) a.toNat_lt_order.le ?_ ?_ ?_ ?_ ?_
  · rw [p64_toNat]
    change 1 * Goldilocks.order + 0 * a.val.toNat = Goldilocks.order
    ring
  · rw [p64_toNat, ZMod.natCast_self]
    simp
  · simp [toZMod]
  · by_cases ha0 : a.val = 0
    · exact Or.inl ha0
    · refine Or.inr ?_
      rw [p64_toNat]
      have hpos : 0 < a.val.toNat := by
        by_contra h
        push Not at h
        have hz : (0 : UInt64).toNat = 0 := rfl
        exact ha0 (UInt64.toNat_inj.mp (by omega))
      have hlt : a.val.toNat < Goldilocks.order := a.toNat_lt_order
      have hndvd : ¬ Goldilocks.order ∣ a.val.toNat := Nat.not_dvd_of_pos_of_lt hpos hlt
      exact (goldilocks_prime.coprime_iff_not_dvd.mpr hndvd).gcd_eq_one
  · intro h0
    exact UInt64.toNat_inj.mp h0

theorem beq_iff_toZMod (a b : Goldilocks) : (a == b) = true ↔ toZMod a = toZMod b := by
  change decide (a = b) = true ↔ toZMod a = toZMod b
  rw [decide_eq_true_eq]
  constructor
  · intro h; rw [h]
  · intro h
    have hval := congrArg ZMod.val h
    unfold toZMod at hval
    have ha : a.val.toNat < Goldilocks.order := a.toNat_lt_order
    have hb : b.val.toNat < Goldilocks.order := b.toNat_lt_order
    rw [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hval
    exact Goldilocks.ext (UInt64.toNat_inj.mp hval)

end Goldilocks

/-- **Refinement of executable `Goldilocks` arithmetic to `ZMod Goldilocks.order`.** -/
def goldilocks_refines : Refines Goldilocks (ZMod Goldilocks.order) where
  toModel := Goldilocks.toZMod
  map_zero := Goldilocks.toZMod_zero
  map_one := Goldilocks.toZMod_one
  map_add := Goldilocks.toZMod_add
  map_sub := Goldilocks.toZMod_sub
  map_mul := Goldilocks.toZMod_mul
  map_neg := Goldilocks.toZMod_neg
  map_inv := Goldilocks.toZMod_inv
  beq_iff := Goldilocks.beq_iff_toZMod

/-! ## Two-adic primitive roots of unity and coset shift -/

private theorem twoAdicGen_step_check :
    (List.range 32).all (fun k =>
      let cur := (Goldilocks.twoAdicGenerators[k]?.getD 0).toNat
      let nxt := (Goldilocks.twoAdicGenerators[k + 1]?.getD 0).toNat
      (nxt * nxt) % Goldilocks.order == cur) = true := by
  decide

private theorem twoAdicGen_step (k : ℕ) (hk : k < 32) :
    Goldilocks.toZMod (Goldilocks.twoAdicGenerator k) =
      (Goldilocks.toZMod (Goldilocks.twoAdicGenerator (k + 1))) ^ 2 := by
  have hall := List.all_eq_true.mp twoAdicGen_step_check k (List.mem_range.mpr hk)
  rw [beq_iff_eq] at hall
  have hlt1 : k < Goldilocks.twoAdicGenerators.size := by
    have : Goldilocks.twoAdicGenerators.size = 33 := rfl
    omega
  have hlt2 : k + 1 < Goldilocks.twoAdicGenerators.size := by
    have : Goldilocks.twoAdicGenerators.size = 33 := rfl
    omega
  have hcur : Goldilocks.toZMod (Goldilocks.twoAdicGenerator k) =
      ((Goldilocks.twoAdicGenerators[k]?.getD 0).toNat : ZMod Goldilocks.order) := by
    unfold Goldilocks.twoAdicGenerator
    cases h : Goldilocks.twoAdicGenerators[k]? with
    | none => exact absurd h (by simp [hlt1])
    | some w => simp [Goldilocks.toZMod_ofUInt64]
  have hnxt : Goldilocks.toZMod (Goldilocks.twoAdicGenerator (k + 1)) =
      ((Goldilocks.twoAdicGenerators[k + 1]?.getD 0).toNat : ZMod Goldilocks.order) := by
    unfold Goldilocks.twoAdicGenerator
    cases h : Goldilocks.twoAdicGenerators[k + 1]? with
    | none => exact absurd h (by simp [hlt2])
    | some w => simp [Goldilocks.toZMod_ofUInt64]
  rw [hcur, hnxt, ← hall, ZMod.natCast_mod, Nat.cast_mul, sq]

private theorem twoAdicGen_eq_pow (n : ℕ) (hn : n ≤ 32) :
    Goldilocks.toZMod (Goldilocks.twoAdicGenerator n) =
      (Goldilocks.toZMod (Goldilocks.twoAdicGenerator 32)) ^ (2 ^ (32 - n)) := by
  induction hd : 32 - n generalizing n with
  | zero =>
    have hn32 : n = 32 := by omega
    subst hn32
    simp
  | succ d ih =>
    have hlt : n < 32 := by omega
    rw [twoAdicGen_step n hlt, ih (n + 1) (by omega) (by omega), ← pow_mul]
    rfl

private theorem twoAdicGen32_isPrimitiveRoot :
    IsPrimitiveRoot (Goldilocks.toZMod (Goldilocks.twoAdicGenerator 32)) (2 ^ 32) := by
  set g := Goldilocks.toZMod (Goldilocks.twoAdicGenerator 32)
  have hhalf : g ^ (2 ^ 31) = -1 := by
    have h1 := (twoAdicGen_eq_pow 1 (by decide)).symm
    rw [show 32 - 1 = 31 by decide] at h1
    rw [h1]
    have hgen1 : Goldilocks.toZMod (Goldilocks.twoAdicGenerator 1) =
        ((Goldilocks.order - 1 : ℕ) : ZMod Goldilocks.order) := by
      unfold Goldilocks.twoAdicGenerator
      change Goldilocks.toZMod (Goldilocks.ofUInt64 0xffffffff00000000) = _
      rw [Goldilocks.toZMod_ofUInt64]
      rfl
    rw [hgen1]
    have hle1 : 1 ≤ Goldilocks.order := by unfold Goldilocks.order; decide
    rw [Nat.cast_sub hle1, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hfull : g ^ (2 ^ 32) = 1 := by
    have : (2 ^ 32 : ℕ) = 2 ^ 31 + 2 ^ 31 := by decide
    rw [this, pow_add, hhalf]
    ring
  have hne1 : g ^ (2 ^ 31) ≠ 1 := by
    rw [hhalf]
    intro heq
    have h2 : ((2 : ℕ) : ZMod Goldilocks.order) = 0 := by
      push_cast
      linear_combination -heq
    have hdvd : Goldilocks.order ∣ 2 := (ZMod.natCast_eq_zero_iff 2 Goldilocks.order).mp h2
    have hle : Goldilocks.order ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    unfold Goldilocks.order at hle
    omega
  rw [IsPrimitiveRoot.iff_def]
  refine ⟨hfull, fun l hl => ?_⟩
  have hord_dvd : orderOf g ∣ 2 ^ 32 := orderOf_dvd_of_pow_eq_one hfull
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord_dvd
  have hj32 : j = 32 := by
    by_contra hne
    have hjle31 : j ≤ 31 := by omega
    have hdvd31 : orderOf g ∣ 2 ^ 31 := hj ▸ Nat.pow_dvd_pow 2 hjle31
    exact hne1 (orderOf_dvd_iff_pow_eq_one.mp hdvd31)
  have hord : orderOf g = 2 ^ 32 := by rw [hj, hj32]
  exact hord ▸ orderOf_dvd_of_pow_eq_one hl

/-- **Every Goldilocks two-adic generator (`n ≤ 32`) is a primitive `2^n`-th root
of unity in `ZMod Goldilocks.order`.** -/
theorem goldilocks_twoAdicGenerator_isPrimitiveRoot (n : ℕ) (hn : n ≤ 32) :
    IsPrimitiveRoot (Goldilocks.toZMod (Goldilocks.twoAdicGenerator n)) (2 ^ n) := by
  rw [twoAdicGen_eq_pow n hn]
  have hpow : 2 ^ 32 = 2 ^ (32 - n) * 2 ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hn]
  rw [IsPrimitiveRoot.iff_def]
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← pow_mul, ← hpow]
    exact twoAdicGen32_isPrimitiveRoot.pow_eq_one
  · rw [← pow_mul] at hl
    have hdvd : 2 ^ 32 ∣ 2 ^ (32 - n) * l := twoAdicGen32_isPrimitiveRoot.dvd_of_pow_eq_one _ hl
    rw [hpow] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (pow_pos two_pos _)).mp hdvd

/-- **The Goldilocks two-adic generators are compatible: squaring the
`2^(k + 1)`-th generator gives the `2^k`-th generator for every `k < 32`.** -/
theorem goldilocks_twoAdicGenerator_sq (k : ℕ) (hk : k < 32) :
    Goldilocks.toZMod (Goldilocks.twoAdicGenerator (k + 1)) ^ 2 =
      Goldilocks.toZMod (Goldilocks.twoAdicGenerator k) :=
  (twoAdicGen_step k hk).symm

/-- **The Goldilocks coset shift (`7`) is nonzero in `ZMod Goldilocks.order`.** -/
theorem goldilocks_cosetShift_ne_zero :
    Goldilocks.toZMod Goldilocks.generator ≠ 0 := by
  intro h
  have h7 : Goldilocks.toZMod Goldilocks.generator = ((7 : ℕ) : ZMod Goldilocks.order) := by
    unfold Goldilocks.generator
    rw [Goldilocks.toZMod_ofUInt64]
    rfl
  rw [h7] at h
  have hdvd : Goldilocks.order ∣ 7 := (ZMod.natCast_eq_zero_iff 7 Goldilocks.order).mp h
  have hle : Goldilocks.order ≤ 7 := Nat.le_of_dvd (by decide) hdvd
  unfold Goldilocks.order at hle
  omega

end CertiFri.P3
