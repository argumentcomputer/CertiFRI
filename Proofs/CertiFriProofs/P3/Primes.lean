import Mathlib
import CertiFriP3.Goldilocks
import CertiFriP3.BabyBear
import CertiFriP3.Bn254

/-!
# The orders of the fields are prime

The orders of the three prime fields of `CertiFriP3` are prime, and the
constants of their extensions are not squares.

## Contents

* `Goldilocks.order_prime`, `BabyBear.order_prime`, `Bn254.order_prime`, with
  the corresponding `Fact` instances.
* `Goldilocks.seven_not_isSquare`: `7` is not a square modulo the order of
  Goldilocks, so `X^2 - 7` is irreducible.
* `BabyBear.eleven_not_isSquare`, `BabyBear.neg_eleven_not_isSquare`: neither
  `11` nor `-11` is a square modulo the order of BabyBear, so `X^4 - 11` is
  irreducible.

## Proofs

Each order `p` is proved prime by the Lucas test (`lucas_primality`): a number
`a` with `a ^ (p - 1) = 1` and `a ^ ((p - 1) / q) ≠ 1` modulo `p` for every
prime factor `q` of `p - 1`. The prime factors of `p - 1` that are too large
for trial division are proved prime the same way, which makes a Pratt
certificate. That a constant is not a square is Euler's criterion
(`ZMod.euler_criterion`). In both cases what is left is a closed statement
about powers modulo `p`, which the kernel evaluates by repeated squaring
(`decide +kernel` on the private `powMod`).

## Assumptions

None.
-/

namespace CertiFri.P3

/-- A number congruent to `acc * b ^ e` modulo `m`, by repeated squaring. The recursion is on
`fuel`, which has to be at least `e`; it stops as soon as `e` is zero, so the number of steps is
the number of bits of `e`. -/
private def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e = 0 then acc
    else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

/-- `powModAux` is congruent to `acc * b ^ e` modulo `m` when `fuel` is at least `e`. -/
private theorem powModAux_modEq (m : ℕ) : ∀ fuel b e acc : ℕ, e ≤ fuel →
    powModAux m fuel b e acc ≡ acc * b ^ e [MOD m]
  | 0, b, e, acc, h => by
    obtain rfl : e = 0 := by omega
    simp [powModAux, Nat.ModEq]
  | fuel + 1, b, e, acc, h => by
    rw [powModAux]
    split_ifs with he hodd
    · subst he
      simp [Nat.ModEq]
    · refine (powModAux_modEq m fuel _ _ _ (by omega)).trans ?_
      have hpow : acc * b * (b * b) ^ (e / 2) = acc * b ^ e := by
        rw [mul_assoc, ← pow_two, ← pow_mul, ← pow_succ']
        congr 2
        omega
      exact hpow ▸ (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
    · refine (powModAux_modEq m fuel _ _ _ (by omega)).trans ?_
      have hpow : acc * (b * b) ^ (e / 2) = acc * b ^ e := by
        rw [← pow_two, ← pow_mul]
        congr 2
        omega
      exact hpow ▸ (Nat.ModEq.refl acc).mul ((Nat.mod_modEq _ _).pow _)

/-- `a ^ n % m`, computed by repeated squaring, so that the kernel can evaluate it for a large
exponent `n`. -/
private def powMod (a n m : ℕ) : ℕ := powModAux m n a n 1 % m

/-- `powMod a n m` is `a ^ n % m`. -/
private theorem powMod_eq (a n m : ℕ) : powMod a n m = a ^ n % m := by
  have h := powModAux_modEq m n a n 1 le_rfl
  rwa [one_mul] at h

/-- For a modulus `p` other than `1`, a power of a natural number is `1` in `ZMod p` exactly when
`powMod` computes `1`. -/
private theorem natCast_pow_eq_one_iff {p : ℕ} (hp : p ≠ 1) (a n : ℕ) :
    (a : ZMod p) ^ n = 1 ↔ powMod a n p = 1 := by
  rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff',
    Nat.one_mod_eq_one.mpr hp]

/-- The Lucas test as a closed computation. `fs` lists the prime factors of `p - 1` with their
exponents, and `a` is the witness: `p` is prime when the factors are prime, their powers multiply
to `p - 1`, `a ^ (p - 1) = 1` modulo `p`, and `a ^ ((p - 1) / q) ≠ 1` modulo `p` for each factor
`q`. The hypothesis `h` is decidable, and is meant to be proved by `decide +kernel`. -/
private theorem prime_of_lucas {p : ℕ} (a : ℕ) (fs : List (ℕ × ℕ))
    (hfs : fs.Forall fun f => f.1.Prime)
    (h : (fs.map fun f => f.1 ^ f.2).prod = p - 1 ∧ powMod a (p - 1) p = 1 ∧
      ∀ f ∈ fs, powMod a ((p - 1) / f.1) p ≠ 1) : p.Prime := by
  obtain ⟨hprod, ha, hd⟩ := h
  have hp : p ≠ 1 := by
    rintro rfl
    simp [powMod_eq] at ha
  refine lucas_primality p a ((natCast_pow_eq_one_iff hp a _).mpr ha) fun q hq hqd => ?_
  rw [← hprod, hq.prime.dvd_prod_iff] at hqd
  obtain ⟨_, hmem, hdvd⟩ := hqd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hmem
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (List.forall_iff_forall_mem.mp hfs f hf)).mp
    (hq.dvd_of_dvd_pow hdvd)
  exact (natCast_pow_eq_one_iff hp a _).not.mpr (hd f hf)

/-- Euler's criterion as a closed computation: a natural number `a` that is not a multiple of the
prime `p`, and with `a ^ (p / 2) ≠ 1` modulo `p`, is not a square in `ZMod p`. The hypothesis `h`
is decidable, and is meant to be proved by `decide +kernel`. -/
private theorem not_isSquare_natCast {p : ℕ} [Fact p.Prime] (a : ℕ)
    (h : a % p ≠ 0 ∧ powMod a (p / 2) p ≠ 1) : ¬ IsSquare (a : ZMod p) := by
  have ha : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    exact h.1
  rw [ZMod.euler_criterion p ha, natCast_pow_eq_one_iff (Fact.out : p.Prime).ne_one]
  exact h.2

/-- The order of the Goldilocks field is prime: `p - 1 = 2^32 * 3 * 5 * 17 * 257 * 65537`, and
`7` generates the multiplicative group. -/
theorem Goldilocks.order_prime : Nat.Prime Goldilocks.order :=
  prime_of_lucas 7 [(2, 32), (3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)]
    (by norm_num [List.Forall]) (by decide +kernel)

/-- The order of the BabyBear field is prime: `p - 1 = 2^27 * 3 * 5`, and `31` generates the
multiplicative group. -/
theorem BabyBear.order_prime : Nat.Prime BabyBear.order :=
  prime_of_lucas 31 [(2, 27), (3, 1), (5, 1)] (by norm_num [List.Forall]) (by decide +kernel)

/-- `405928799`, a factor of `Bn254.order - 1`, is prime. -/
private theorem Bn254.prime_405928799 : Nat.Prime 405928799 :=
  prime_of_lucas 22 [(2, 1), (11, 1), (3691, 1), (4999, 1)]
    (by norm_num [List.Forall]) (by decide +kernel)

/-- `12048837557`, a factor of `5156902474397 - 1`, is prime. -/
private theorem Bn254.prime_12048837557 : Nat.Prime 12048837557 :=
  prime_of_lucas 2 [(2, 2), (7, 2), (661, 1), (93001, 1)]
    (by norm_num [List.Forall]) (by decide +kernel)

/-- `5156902474397`, a factor of `1670836401704629 - 1`, is prime. -/
private theorem Bn254.prime_5156902474397 : Nat.Prime 5156902474397 :=
  prime_of_lucas 2 [(2, 2), (107, 1), (12048837557, 1)]
    ⟨by norm_num, by norm_num, prime_12048837557⟩ (by decide +kernel)

/-- `1670836401704629`, a factor of `Bn254.order - 1`, is prime. -/
private theorem Bn254.prime_1670836401704629 : Nat.Prime 1670836401704629 :=
  prime_of_lucas 2 [(2, 2), (3, 4), (5156902474397, 1)]
    ⟨by norm_num, by norm_num, prime_5156902474397⟩ (by decide +kernel)

/-- `639533339`, a factor of `65865678001877903 - 1`, is prime. -/
private theorem Bn254.prime_639533339 : Nat.Prime 639533339 :=
  prime_of_lucas 2 [(2, 1), (229, 1), (853, 1), (1637, 1)]
    (by norm_num [List.Forall]) (by decide +kernel)

/-- `65865678001877903`, a factor of `13818364434197438864469338081 - 1`, is prime. -/
private theorem Bn254.prime_65865678001877903 : Nat.Prime 65865678001877903 :=
  prime_of_lucas 5 [(2, 1), (83, 1), (379, 1), (1637, 1), (639533339, 1)]
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_639533339⟩ (by decide +kernel)

/-- `13818364434197438864469338081`, a factor of `Bn254.order - 1`, is prime. -/
private theorem Bn254.prime_13818364434197438864469338081 :
    Nat.Prime 13818364434197438864469338081 :=
  prime_of_lucas 3 [(2, 5), (5, 1), (823, 1), (1593227, 1), (65865678001877903, 1)]
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, prime_65865678001877903⟩
    (by decide +kernel)

/-- The order of the scalar field of BN254 is prime:
`r - 1 = 2^28 * 3^2 * 13 * 29 * 983 * 11003 * 237073 * 405928799 * 1670836401704629 *
13818364434197438864469338081`, and `5` generates the multiplicative group. -/
theorem Bn254.order_prime : Nat.Prime Bn254.order :=
  prime_of_lucas 5
    [(2, 28), (3, 2), (13, 1), (29, 1), (983, 1), (11003, 1), (237073, 1), (405928799, 1),
      (1670836401704629, 1), (13818364434197438864469338081, 1)]
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
      prime_405928799, prime_1670836401704629, prime_13818364434197438864469338081⟩
    (by decide +kernel)

/-- The order of Goldilocks is prime, for instance resolution. -/
instance Goldilocks.order_fact : Fact (Nat.Prime Goldilocks.order) := ⟨Goldilocks.order_prime⟩

/-- The order of BabyBear is prime, for instance resolution. -/
instance BabyBear.order_fact : Fact (Nat.Prime BabyBear.order) := ⟨BabyBear.order_prime⟩

/-- The order of the scalar field of BN254 is prime, for instance resolution. -/
instance Bn254.order_fact : Fact (Nat.Prime Bn254.order) := ⟨Bn254.order_prime⟩

/-- `7` is not a square in the Goldilocks field. -/
theorem Goldilocks.seven_not_isSquare : ¬ IsSquare (7 : ZMod Goldilocks.order) :=
  mod_cast not_isSquare_natCast (p := Goldilocks.order) 7 (by decide +kernel)

/-- `11` is not a square in the BabyBear field. -/
theorem BabyBear.eleven_not_isSquare : ¬ IsSquare (11 : ZMod BabyBear.order) :=
  mod_cast not_isSquare_natCast (p := BabyBear.order) 11 (by decide +kernel)

/-- `-11` is not a square in the BabyBear field. -/
theorem BabyBear.neg_eleven_not_isSquare : ¬ IsSquare (-11 : ZMod BabyBear.order) := by
  have h := not_isSquare_natCast (p := BabyBear.order) (BabyBear.order - 11) (by decide +kernel)
  rwa [Nat.cast_sub (by decide), ZMod.natCast_self, zero_sub] at h

end CertiFri.P3
