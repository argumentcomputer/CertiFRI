import CertiFriProofs.Theory.Zk.PolyBlinding
import CertiFriProofs.Theory.Zk.SaltedMerkle
import CertiFriProofs.Exec.SoundnessZk
import CertiFriProofs.P3.GoldilocksExt3MultiAritySoundness
import CertiFriProofs.P3.DigestCard

/-!
# Formal Honest-Verifier Zero-Knowledge (HVZK) for Protocol `v6-zk`

This module combines the algebraic blinding stack (`Theory/Zk/PolyBlinding.lean`) and
the ROM salted-Merkle hiding theorem (`Theory/Zk/SaltedMerkle.lean`) to prove full
Honest-Verifier Zero-Knowledge (HVZK) for Protocol `v6-zk`, and instantiates it
concretely over `GoldilocksExt3` (`Fp3Model`), 16-byte (`DomainSep.Salt16`) and
32-byte (`Salt32`) leaf salts, 32-byte `BLAKE3-256` (`Digest`) and 64-byte
`BLAKE2b-512` (`Digest64`), and the compact 8-ary FRI profiles including
`FriParams.ultraCompact400KBZk` and `FriParams.compact400KBBalanced`.

## Architecture

1. **Concrete Salt Spaces & Goldilocks Coset Disjointness (`ConcretePrimitives`):**
   * `Fintype DomainSep.Salt16` with `card_salt16 : Fintype.card DomainSep.Salt16 = 2 ^ 128`
     (current shipped `v6-zk` 16-byte classical salt).
   * `Salt32` with `card_salt32 : Fintype.card Salt32 = 2 ^ 256` (32-byte post-quantum-margin salt).
   * `goldilocks_coset_disjoint_from_trace` and `fp3_coset_disjoint_from_trace`:
     kernel-checked proof that `(7 : GoldilocksField) ^ (2 ^ 32) ≠ 1`, certifying that
     the entire `v6-zk` LDE coset `7 * H_{2^h}` is strictly disjoint from every trace
     subgroup `H_{2^logN}` (`logN, h ≤ 32`).

2. **Full `v6-zk` Algebraic Transcript View & Witness-Free Simulator (`AlgebraicV6Zk`):**
   * `V6ZkParams`, `V6ZkPublic`, `V6ZkChallenges`, `V6ZkWitness`, `V6ZkAlgView`.
   * `v6ZkRealAlgProver`: models the real `v6-zk` prover with:
     - vanishing-blinded main trace columns `f_main(X) + (X^N - 1) r_main(X)`,
     - vanishing-blinded LogUp running-sum columns `f_logup(X) + (X^N - 1) r_logup(X)`,
     - cross-circuit masked intermediate LogUp accumulators `A'_p = S_p + μ_p` with
       blinded mask polynomials `U_p(X) = U₀(p, μ_p)(X) + (X^N - 1) r_mask(X)`,
     - half-stride telescoping quotient slices `c'_k(X) = c_k(X) - ρ_{k-1}(X) + X^N ρ_k(X)`
       satisfying the exact verifier OOD and coset quotient recombination equations,
     - randomizer polynomial `R(X)` split via `oodQuotientSplitEquiv` into `(R(z), R_q)`
       and folded through any multi-arity FRI schedule `arities` down to `finalPoly`.
   * `v6ZkAlgSimulator`: explicit zero-knowledge simulator taking **zero witness** inputs.
   * `v6ZkAlgSimulator_ood_check`: every simulated transcript satisfies the exact verifier
     OOD composition-quotient equation `∑_k z^{kN} c'_k(z) = evalComposition(...) / (z^N - 1)`.
   * `v6Zk_alg_perfect_hvzk`: **exact zero total-variation distance (`tvDist = 0`)**
     between `v6ZkRealAlgProver` and `v6ZkAlgSimulator` in the idealized algebraic layer.

3. **Full ROM `v6-zk` HVZK Theorem (`FullRomHvzk`):**
   * `V6ZkView`: full verifier view pairing `V6ZkAlgView` with `SaltedMerkleView`
     (commitments, opened rows/salts, Merkle cap and sibling authentication paths).
   * `v6ZkRealGame` vs witness-free `v6ZkSimulator`.
   * `v6Zk_hvzk`: for ANY adaptive `N_RO`-query ROM distinguisher `D`,
     `|v6ZkRealGame - v6ZkSimulator| ≤ N_RO * L_unopened / |Salt|`
     (and `v6Zk_hvzk_unindexed`: `≤ (N_RO * L_unopened + L_unopened * (L - 1)) / |Salt|`
     for unindexed `RO(row || salt)` leaves).

4. **Concrete `GoldilocksExt3` & `ultraCompact400KBZk` HVZK Instantiations (`ConcreteGoldilocksExt3`):**
   * `goldilocksExt3_v6Zk_hvzk`: concrete `Fp3Model` + `DomainSep.Salt16` (`128`-bit salt)
     + `Digest` (`BLAKE3-256`) / `Digest64` (`BLAKE2b-512`).
   * `goldilocksExt3_v6Zk_hvzk_salt32`: concrete `Fp3Model` + `Salt32` (`256`-bit salt).
   * `goldilocksExt3_ultraCompact400KBZk_hvzk` & `_salt32`: concrete HVZK for
     `FriParams.ultraCompact400KBZk` (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8,
     numQueries = 55, queryPowBits = 30`) with explicit `55 ≤ 256` and
     `55 * 8 + 2 = 442 ≤ 2 ^ logTraceHeight` (`logTraceHeight ≥ 9`) discharge!
   * `goldilocksExt3_v6Zk_hvzk_with_tensor4_span`: combines `v6Zk_hvzk` with
     `fp3_tensor4_span_failure_prob_le` (`≤ 2 / Goldilocks.order ^ 2 < 1 / 2 ^ 126`)
     for `W_R = 4` base-field tensor randomizer columns.
-/

namespace CertiFri.P3.Exec

open Polynomial CertiFri CertiFri.P3 CertiFri.Zk CertiFri.Oracle CertiFri.Oracle.OracleComp
open scoped BigOperators

/-! ## Section 1: Concrete `Salt16` / `Salt32` Cardinalities & Goldilocks Coset Disjointness -/

section ConcretePrimitives

/-- Equivalence between `DomainSep.Salt16` (`4 × UInt32`) and `Fin 4 → UInt32`. -/
def salt16EquivFun : DomainSep.Salt16 ≃ (Fin 4 → UInt32) where
  toFun s i :=
    match i.val with
    | 0 => s.w0
    | 1 => s.w1
    | 2 => s.w2
    | _ => s.w3
  invFun f := ⟨f 0, f 1, f 2, f 3⟩
  left_inv s := by cases s; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

noncomputable instance : Fintype DomainSep.Salt16 :=
  Fintype.ofEquiv (Fin 4 → UInt32) salt16EquivFun.symm

instance : Nonempty DomainSep.Salt16 := ⟨default⟩

/-- Exact cardinality of 16-byte `v6-zk` leaf salts (`DomainSep.Salt16`): `2 ^ 128`. -/
theorem card_salt16 : Fintype.card DomainSep.Salt16 = 2 ^ 128 := by
  rw [Fintype.card_congr salt16EquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-- 32-byte (`256`-bit) post-quantum-margin per-leaf salt (`8 × UInt32`). -/
structure Salt32 where
  w0 : UInt32
  w1 : UInt32
  w2 : UInt32
  w3 : UInt32
  w4 : UInt32
  w5 : UInt32
  w6 : UInt32
  w7 : UInt32
  deriving DecidableEq, Repr, Inhabited

/-- Equivalence between `Salt32` and `Fin 8 → UInt32`. -/
def salt32EquivFun : Salt32 ≃ (Fin 8 → UInt32) where
  toFun s i :=
    match i.val with
    | 0 => s.w0
    | 1 => s.w1
    | 2 => s.w2
    | 3 => s.w3
    | 4 => s.w4
    | 5 => s.w5
    | 6 => s.w6
    | _ => s.w7
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7⟩
  left_inv s := by cases s; rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

noncomputable instance : Fintype Salt32 :=
  Fintype.ofEquiv (Fin 8 → UInt32) salt32EquivFun.symm

instance : Nonempty Salt32 := ⟨default⟩

/-- Exact cardinality of 32-byte post-quantum-margin leaf salts (`Salt32`): `2 ^ 256`. -/
theorem card_salt32 : Fintype.card Salt32 = 2 ^ 256 := by
  rw [Fintype.card_congr salt32EquivFun, Fintype.card_fun, Fintype.card_fin, card_uint32,
    ← pow_mul]

/-- Iterated squaring `a ↦ a ^ (2 ^ k)` for fast kernel evaluation in `GoldilocksField`. -/
private def iterSq {R : Type*} [Mul R] : ℕ → R → R
  | 0, a => a
  | k + 1, a => iterSq k (a * a)

private theorem iterSq_eq_pow {R : Type*} [CommMonoid R] :
    ∀ (k : ℕ) (a : R), iterSq k a = a ^ (2 ^ k)
  | 0, a => by simp [iterSq]
  | k + 1, a => by
    rw [iterSq, iterSq_eq_pow k (a * a), ← sq, ← pow_mul, mul_comm 2, ← pow_succ]

/-- The Goldilocks coset shift `s = 7` (`Val::GENERATOR`) satisfies `7 ^ (2 ^ 32) ≠ 1`. -/
theorem goldilocks_gen_pow_two_pow_32_ne_one :
    ((7 : GoldilocksField) ^ (2 ^ 32)) ≠ 1 := by
  rw [← iterSq_eq_pow]
  decide

/-- **Goldilocks Coset Disjointness Theorem (`goldilocks_coset_disjoint_from_trace`):**
for ANY trace log-height `logN ≤ 32` and ANY element `d` of a Goldilocks two-adic
subgroup (`d ^ (2 ^ 32) = 1`), the coset point `7 * d` lies strictly outside the trace
domain `H_{2^logN}` (`(7 * d) ^ (2 ^ logN) ≠ 1`). -/
theorem goldilocks_coset_disjoint_from_trace {logN : ℕ} (hlogN : logN ≤ 32)
    {d : GoldilocksField} (hd : d ^ (2 ^ 32) = 1) :
    ((7 : GoldilocksField) * d) ^ (2 ^ logN) ≠ 1 :=
  coset_pow_ne_one_of_shift goldilocks_gen_pow_two_pow_32_ne_one hd
    (Nat.pow_dvd_pow 2 hlogN)

/-- **Cubic Extension (`Fp3Model`) Coset Disjointness Theorem:**
embedding the Goldilocks LDE coset `7 * D` into `Fp3Model` preserves strict disjointness
from every trace subgroup `H_{2^logN}` (`logN ≤ 32`). -/
theorem fp3_coset_disjoint_from_trace {logN : ℕ} (hlogN : logN ≤ 32)
    {d : GoldilocksField} (hd : d ^ (2 ^ 32) = 1) :
    (Fp3Model.embed 7 * Fp3Model.embed d) ^ (2 ^ logN) ≠ 1 := by
  intro h1
  have hem : Fp3Model.embed (((7 : GoldilocksField) * d) ^ (2 ^ logN)) = 1 := by
    have hmul : ∀ a b : GoldilocksField, Fp3Model.embed (a * b) = Fp3Model.embed a * Fp3Model.embed b :=
      fun a b => by ext <;> simp [Fp3Model.embed]
    have hpow : ∀ (k : ℕ) (a : GoldilocksField),
        Fp3Model.embed (a ^ k) = (Fp3Model.embed a) ^ k := by
      intro k a
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ, pow_succ, hmul, ih]
    rw [hpow, hmul]
    exact h1
  have hbase : ((7 : GoldilocksField) * d) ^ (2 ^ logN) = 1 :=
    congrArg Fp3Model.c0 hem
  exact goldilocks_coset_disjoint_from_trace hlogN hd hbase

end ConcretePrimitives

/-! ## Section 2: `v6-zk` Algebraic Transcript View, Real Prover, Simulator & Perfect HVZK -/

section AlgebraicV6Zk

/-- Public structural parameters for a `v6-zk` proving instance. -/
structure V6ZkParams where
  logTraceHeight : ℕ
  blindingBudget : ℕ
  logBlowup : ℕ
  numQueries : ℕ
  maxLogArity : ℕ
  arities : List ℕ
  logFinalPolyLen : ℕ
  numMainCols : ℕ
  numLogupCols : ℕ
  numCircuits : ℕ
  halfQuotientSlices : ℕ
  randomizerWidth : ℕ
  deriving DecidableEq, Repr

namespace V6ZkParams

/-- Unblinded trace domain size `N = 2 ^ logTraceHeight`. -/
def traceHeight (P : V6ZkParams) : ℕ := 2 ^ P.logTraceHeight

/-- Maximum FRI fold factor `2 ^ maxLogArity`. -/
def maxArity (P : V6ZkParams) : ℕ := 2 ^ P.maxLogArity

/-- FRI final polynomial length `2 ^ logFinalPolyLen`. -/
def finalPolyLen (P : V6ZkParams) : ℕ := 2 ^ P.logFinalPolyLen

/-- Number of telescoping quotient slices `2 * halfQuotientSlices`. -/
def numQuotientSlices (P : V6ZkParams) : ℕ := 2 * P.halfQuotientSlices

/-- Degree of the FRI randomizer polynomial before OOD quotient splitting:
`2 ^ arities.sum * finalPolyLen + 1`. -/
abbrev friRandomizerDeg (P : V6ZkParams) : ℕ := 2 ^ P.arities.sum * P.finalPolyLen + 1

/-- Blinding-budget soundness condition for `v6-zk` HVZK:
1. At least one pair of telescoping quotient slices (`1 ≤ halfQuotientSlices`).
2. `numQueries ≤ finalPolyLen` (so every multi-arity FRI round has enough sibling degree).
3. `traceEvalCard ≤ blindingBudget` and `quotEvalCard ≤ blindingBudget` (discharged
   immediately from `numQueries * maxArity + 2 ≤ blindingBudget` or exact opening count). -/
def BlindingOk (P : V6ZkParams) (traceEvalCard quotEvalCard : ℕ) : Prop :=
  1 ≤ P.halfQuotientSlices ∧
  P.numQueries ≤ P.finalPolyLen ∧
  traceEvalCard ≤ P.blindingBudget ∧
  quotEvalCard ≤ P.blindingBudget

end V6ZkParams

/-- Public statement and verifying-key evaluator for `v6-zk` (takes ZERO secret witness). -/
structure V6ZkPublic (K : Type) (P : V6ZkParams) where
  /-- Public final global LogUp balance (e.g. `0` for standalone proofs). -/
  finalAcc : K
  /-- Deterministic AIR + LogUp constraint-folding evaluator at point `x`, given
  `(mainCur, mainNext, logupCur, logupNext, maskedInterAccs, maskVal)`. -/
  evalComposition :
    K →
    (Fin P.numMainCols → K) → (Fin P.numMainCols → K) →
    (Fin P.numLogupCols → K) → (Fin P.numLogupCols → K) →
    (Fin (P.numCircuits - 1) → K) → (Fin (P.numCircuits - 1) → K) →
    K

/-- Honest-verifier challenges for a `v6-zk` execution. -/
structure V6ZkChallenges (K : Type) [DecidableEq K] (P : V6ZkParams) where
  /-- Trace subgroup generator `g` (`g ^ N = 1`, `g ≠ 1`). -/
  g : K
  /-- Out-of-domain evaluation challenge `z` (`z ≠ 0`, `z ^ N ≠ 1`). -/
  z : K
  /-- Exact number of distinct coset query points opened by FRI (`≤ numQueries * maxArity`). -/
  numOpenings : ℕ
  /-- Distinct coset LDE points opened by FRI queries. -/
  queryPoints : Fin numOpenings → K
  /-- Per-round multi-arity FRI folding challenges. -/
  friBetas : Fin P.arities.length → K
  /-- Per-round folded coset query points (`numQueries` distinct points per round). -/
  friRoundPoints : FriRoundQueryPoints K P.arities P.numQueries

namespace V6ZkChallenges

variable {K : Type} [Field K] [DecidableEq K] {P : V6ZkParams}

/-- Deduplicated finite set of all evaluation points where quotient and mask polynomials
are opened: `{z} ∪ {queryPoints i}`. -/
def quotEvalSet (ch : V6ZkChallenges K P) : Finset K :=
  insert ch.z (Finset.univ.image ch.queryPoints)

/-- Deduplicated finite set of all evaluation points where main and LogUp trace polynomials
are evaluated (directly via OOD / FRI openings or indirectly via `g * x` in the quotient):
`{z, g * z} ∪ {queryPoints i} ∪ {g * queryPoints i}`. -/
def traceEvalSet (ch : V6ZkChallenges K P) : Finset K :=
  insert ch.z (insert (ch.g * ch.z)
    (Finset.univ.image ch.queryPoints ∪ Finset.univ.image (fun i => ch.g * ch.queryPoints i)))

omit [Field K] in
theorem mem_quotEvalSet_z (ch : V6ZkChallenges K P) : ch.z ∈ ch.quotEvalSet :=
  Finset.mem_insert_self _ _

omit [Field K] in
theorem mem_quotEvalSet_query (ch : V6ZkChallenges K P) (i : Fin ch.numOpenings) :
    ch.queryPoints i ∈ ch.quotEvalSet :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem mem_traceEvalSet_z (ch : V6ZkChallenges K P) : ch.z ∈ ch.traceEvalSet :=
  Finset.mem_insert_self _ _

theorem mem_traceEvalSet_gz (ch : V6ZkChallenges K P) : ch.g * ch.z ∈ ch.traceEvalSet :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem mem_traceEvalSet_query (ch : V6ZkChallenges K P) (i : Fin ch.numOpenings) :
    ch.queryPoints i ∈ ch.traceEvalSet :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))

theorem mem_traceEvalSet_gquery (ch : V6ZkChallenges K P) (i : Fin ch.numOpenings) :
    ch.g * ch.queryPoints i ∈ ch.traceEvalSet :=
  Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))))

omit [Field K] in
/-- Exact cardinality bound on `quotEvalSet`: `≤ numOpenings + 1`. -/
theorem card_quotEvalSet_le (ch : V6ZkChallenges K P) :
    ch.quotEvalSet.card ≤ ch.numOpenings + 1 := by
  unfold quotEvalSet
  calc (insert ch.z (Finset.univ.image ch.queryPoints)).card
      ≤ (Finset.univ.image ch.queryPoints).card + 1 := Finset.card_insert_le _ _
    _ ≤ (Finset.univ : Finset (Fin ch.numOpenings)).card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ = ch.numOpenings + 1 := by simp

/-- Exact cardinality bound on `traceEvalSet`: `≤ 2 * numOpenings + 2` in full generality. -/
theorem card_traceEvalSet_le (ch : V6ZkChallenges K P) :
    ch.traceEvalSet.card ≤ 2 * ch.numOpenings + 2 := by
  unfold traceEvalSet
  have h1 := Finset.card_insert_le ch.z
    (insert (ch.g * ch.z) (Finset.univ.image ch.queryPoints ∪
      Finset.univ.image (fun i => ch.g * ch.queryPoints i)))
  have h2 := Finset.card_insert_le (ch.g * ch.z)
    (Finset.univ.image ch.queryPoints ∪ Finset.univ.image (fun i => ch.g * ch.queryPoints i))
  have h3 := Finset.card_union_le
    (Finset.univ.image ch.queryPoints)
    (Finset.univ.image (fun i => ch.g * ch.queryPoints i))
  have h4 : (Finset.univ.image ch.queryPoints).card ≤ ch.numOpenings :=
    Finset.card_image_le.trans (by simp)
  have h5 : (Finset.univ.image (fun i => ch.g * ch.queryPoints i)).card ≤ ch.numOpenings :=
    Finset.card_image_le.trans (by simp)
  omega

/-- When `queryPoints` is closed under trace rotation `x ↦ g * x` (or has `traceEvalSet.card ≤
numOpenings + 2`), `traceEvalSet.card ≤ numOpenings + 2`. -/
theorem card_traceEvalSet_le_of_closed (ch : V6ZkChallenges K P)
    (hclosed : ∀ i : Fin ch.numOpenings, ∃ j : Fin ch.numOpenings, ch.g * ch.queryPoints i = ch.queryPoints j) :
    ch.traceEvalSet.card ≤ ch.numOpenings + 2 := by
  have hunion :
      Finset.univ.image ch.queryPoints ∪ Finset.univ.image (fun i => ch.g * ch.queryPoints i) =
        Finset.univ.image ch.queryPoints := by
    ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨i, rfl⟩)
      · exact h
      · obtain ⟨j, hj⟩ := hclosed i
        exact ⟨j, hj.symm⟩
    · exact Or.inl
  unfold traceEvalSet
  rw [hunion]
  have h1 := Finset.card_insert_le ch.z (insert (ch.g * ch.z) (Finset.univ.image ch.queryPoints))
  have h2 := Finset.card_insert_le (ch.g * ch.z) (Finset.univ.image ch.queryPoints)
  have h3 : (Finset.univ.image ch.queryPoints).card ≤ ch.numOpenings :=
    Finset.card_image_le.trans (by simp)
  omega

/-- Honest-verifier challenge admissibility predicate. -/
def Ok (ch : V6ZkChallenges K P) : Prop :=
  ch.g ^ P.traceHeight = 1 ∧
  ch.z ^ P.traceHeight ≠ 1 ∧
  (∀ i : Fin ch.numOpenings, (ch.queryPoints i) ^ P.traceHeight ≠ 1) ∧
  FriRoundQueryPointsInj P.arities P.numQueries ch.friRoundPoints

theorem traceEvalSet_disjoint_of_ok {ch : V6ZkChallenges K P} (hok : ch.Ok) :
    ∀ x ∈ ch.traceEvalSet, x ^ P.traceHeight ≠ 1 := by
  obtain ⟨hg, hz, hq, _⟩ := hok
  intro x hx
  unfold traceEvalSet at hx
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hz
  · rw [mul_pow, hg, one_mul]; exact hz
  · exact hq i
  · rw [mul_pow, hg, one_mul]; exact hq i

theorem quotEvalSet_disjoint_of_ok {ch : V6ZkChallenges K P} (hok : ch.Ok) :
    ∀ x ∈ ch.quotEvalSet, x ^ P.traceHeight ≠ 1 := by
  obtain ⟨_, hz, hq, _⟩ := hok
  intro x hx
  unfold quotEvalSet at hx
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with rfl | ⟨i, rfl⟩
  · exact hz
  · exact hq i

end V6ZkChallenges

/-- **Full Algebraic Transcript View of Protocol `v6-zk` (`V6ZkAlgView`):**
captures every algebraic field opening observed by the honest verifier:
OOD evaluations at `(z, g * z)`, coset FRI query openings for main trace, masked LogUp,
cross-circuit boundary mask, and telescoping quotient slices, masked intermediate
accumulators, randomizer OOD opening, multi-arity FRI sibling openings, and `finalPoly`. -/
structure V6ZkAlgView (K : Type) [DecidableEq K] (P : V6ZkParams) (ch : V6ZkChallenges K P) where
  mainOodCur : Fin P.numMainCols → K
  mainOodNext : Fin P.numMainCols → K
  mainFriOpenings : Fin P.numMainCols → Fin ch.numOpenings → K
  logupOodCur : Fin P.numLogupCols → K
  logupOodNext : Fin P.numLogupCols → K
  logupFriOpenings : Fin P.numLogupCols → Fin ch.numOpenings → K
  maskedInterAccs : Fin (P.numCircuits - 1) → K
  maskPolyOod : Fin (P.numCircuits - 1) → K
  maskPolyFri : Fin (P.numCircuits - 1) → Fin ch.numOpenings → K
  quotientOodSlices : Fin (2 * P.halfQuotientSlices) → K
  quotientFriSlices : Fin (2 * P.halfQuotientSlices) → Fin ch.numOpenings → K
  randomizerOod : K
  friSiblingOpenings : FriRoundSiblingEvals K P.arities P.numQueries
  finalPoly : Fin P.finalPolyLen → K

/-- Prover's fresh algebraic blinding randomness for one `v6-zk` proof. -/
abbrev V6ZkProverRand (K : Type) (P : V6ZkParams) : Type :=
  (Fin P.numMainCols → Fin P.blindingBudget → K) ×
  (Fin P.numLogupCols → Fin P.blindingBudget → K) ×
  ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) ×
  (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
  (Fin P.friRandomizerDeg → K)

/-- Secret witness held solely by the real `v6-zk` prover (never passed to the simulator). -/
structure V6ZkWitness (K : Type) [Field K] [DecidableEq K] (P : V6ZkParams)
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) where
  /-- Secret main trace polynomials (degree `< N`). -/
  mainPolys : Fin P.numMainCols → K[X]
  /-- Secret LogUp running-sum polynomials (degree `< N`). -/
  logupPolys : Fin P.numLogupCols → K[X]
  /-- Secret per-circuit intermediate LogUp sums `S_0, ..., S_{M-2}`. -/
  interAccs : Fin (P.numCircuits - 1) → K
  /-- Base mask polynomial `U₀(p, μ_p)` satisfying `U₀(p, μ_p)(1) = μ_p`. -/
  maskBasePolys : Fin (P.numCircuits - 1) → K → K[X]
  /-- Unblinded quotient slices `c_0, ..., c_{2q-1}` induced by the blinded trace/LogUp/mask
  polynomials. -/
  quotientSlices :
    (Fin P.numMainCols → Fin P.blindingBudget → K) →
    (Fin P.numLogupCols → Fin P.blindingBudget → K) →
    (Fin (P.numCircuits - 1) → K) →
    (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K) →
    Fin (2 * P.halfQuotientSlices) → K[X]
  /-- Batched witness polynomial entering multi-arity FRI (determined by the blinded trace,
  LogUp, mask, and quotient slices, before adding the FRI randomizer quotient `R_q`). -/
  friWitnessBatch :
    (Fin P.numMainCols → Fin P.blindingBudget → K) →
    (Fin P.numLogupCols → Fin P.blindingBudget → K) →
    (Fin (P.numCircuits - 1) → K) →
    (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K) →
    (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) →
    Fin (2 ^ P.arities.sum * P.finalPolyLen) → K
  /-- Soundness/completeness relation of the honest witness: at every point `x ∈ ch.quotEvalSet`,
  the recombined quotient equals `evalComposition(x, ...) / (x ^ N - 1)`. -/
  quotient_valid :
    ∀ (rMain : Fin P.numMainCols → Fin P.blindingBudget → K)
      (rLogup : Fin P.numLogupCols → Fin P.blindingBudget → K)
      (μ : Fin (P.numCircuits - 1) → K)
      (rMask : Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)
      (x : K), x ∈ ch.quotEvalSet →
      (∑ k : Fin (2 * P.halfQuotientSlices),
        X ^ (k.val * P.traceHeight) * quotientSlices rMain rLogup μ rMask k).eval x =
      pub.evalComposition x
        (fun w => (blindPoly P.traceHeight (mainPolys w) (rMain w)).eval x)
        (fun w => (blindPoly P.traceHeight (mainPolys w) (rMain w)).eval (ch.g * x))
        (fun w => (blindPoly P.traceHeight (logupPolys w) (rLogup w)).eval x)
        (fun w => (blindPoly P.traceHeight (logupPolys w) (rLogup w)).eval (ch.g * x))
        (fun p => interAccs p + μ p)
        (fun p => (blindPoly P.traceHeight (maskBasePolys p (μ p)) (rMask p)).eval x) *
      (x ^ P.traceHeight - 1)⁻¹

/-- Canonical uniform core sample space of the witness-free `v6-zk` algebraic simulator. -/
abbrev V6ZkCoreSample (K : Type) [Field K] [DecidableEq K] (P : V6ZkParams)
    (ch : V6ZkChallenges K P) : Type :=
  (Fin P.numMainCols → {x : K // x ∈ ch.traceEvalSet} → K) ×
  (Fin P.numLogupCols → {x : K // x ∈ ch.traceEvalSet} → K) ×
  ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) ×
  (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
  (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals K P.arities P.numQueries))

/-- Canonical zero inhabitant of `FriRoundSiblingEvals`. -/
private def zeroFriRoundSiblingEvals {K : Type} [Zero K] :
    (arities : List ℕ) → (q : ℕ) → FriRoundSiblingEvals.{0, 0} K arities q
  | [], _ => PUnit.unit
  | _ :: rest, q => (fun _ _ => 0, zeroFriRoundSiblingEvals rest q)

private theorem nonempty_v6ZkProverRand {K : Type} [Zero K] (P : V6ZkParams) :
    Nonempty (V6ZkProverRand K P) :=
  ⟨(fun _ _ => 0, fun _ _ => 0, (fun _ => 0, fun _ _ => 0), fun _ _ => 0, fun _ => 0)⟩

private theorem nonempty_v6ZkCoreSample {K : Type} [Field K] [DecidableEq K] (P : V6ZkParams)
    (ch : V6ZkChallenges K P) : Nonempty (V6ZkCoreSample K P ch) :=
  ⟨(fun _ _ => 0, fun _ _ => 0, (fun _ => 0, fun _ _ => 0), fun _ _ => 0,
    (0, (fun _ => 0, zeroFriRoundSiblingEvals P.arities P.numQueries)))⟩

/-- **Deterministic Transcript Assembly (`v6ZkAlgSimulator`):**
takes ONLY public parameters `P`, public claims/VK `pub`, honest-verifier challenges `ch`,
and a uniform random sample `s : V6ZkCoreSample K P ch` — **ZERO secret witness** — and
assembles a complete, verifier-consistent `V6ZkAlgView`! -/
noncomputable def v6ZkAlgSimulator {K : Type} [Field K] [DecidableEq K] {P : V6ZkParams}
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hq : 1 ≤ P.halfQuotientSlices)
    (s : V6ZkCoreSample K P ch) : V6ZkAlgView K P ch :=
  let mainEval := s.1
  let logupEval := s.2.1
  let maskedAccs := s.2.2.1.1
  let maskEval := s.2.2.1.2
  let quotTail := s.2.2.2.1
  let randOod := s.2.2.2.2.1
  let finalPoly := s.2.2.2.2.2.1
  let friSibs := s.2.2.2.2.2.2
  let quotAt (x : K) (hxQ : x ∈ ch.quotEvalSet)
      (hxT : x ∈ ch.traceEvalSet) (hgxT : ch.g * x ∈ ch.traceEvalSet) :
      Fin (2 * P.halfQuotientSlices) → K :=
    let totalQ : K :=
      pub.evalComposition x
        (fun w => mainEval w ⟨x, hxT⟩)
        (fun w => mainEval w ⟨ch.g * x, hgxT⟩)
        (fun w => logupEval w ⟨x, hxT⟩)
        (fun w => logupEval w ⟨ch.g * x, hgxT⟩)
        maskedAccs
        (fun p => maskEval p ⟨x, hxQ⟩) *
      (x ^ P.traceHeight - 1)⁻¹
    fun k =>
      if h0 : k.val = 0 then
        totalQ - ∑ j : Fin (2 * P.halfQuotientSlices - 1),
          x ^ ((j.val + 1) * P.traceHeight) * quotTail j ⟨x, hxQ⟩
      else
        quotTail ⟨k.val - 1, by omega⟩ ⟨x, hxQ⟩
  { mainOodCur := fun w => mainEval w ⟨ch.z, ch.mem_traceEvalSet_z⟩
    mainOodNext := fun w => mainEval w ⟨ch.g * ch.z, ch.mem_traceEvalSet_gz⟩
    mainFriOpenings := fun w i => mainEval w ⟨ch.queryPoints i, ch.mem_traceEvalSet_query i⟩
    logupOodCur := fun w => logupEval w ⟨ch.z, ch.mem_traceEvalSet_z⟩
    logupOodNext := fun w => logupEval w ⟨ch.g * ch.z, ch.mem_traceEvalSet_gz⟩
    logupFriOpenings := fun w i => logupEval w ⟨ch.queryPoints i, ch.mem_traceEvalSet_query i⟩
    maskedInterAccs := maskedAccs
    maskPolyOod := fun p => maskEval p ⟨ch.z, ch.mem_quotEvalSet_z⟩
    maskPolyFri := fun p i => maskEval p ⟨ch.queryPoints i, ch.mem_quotEvalSet_query i⟩
    quotientOodSlices := quotAt ch.z ch.mem_quotEvalSet_z ch.mem_traceEvalSet_z ch.mem_traceEvalSet_gz
    quotientFriSlices := fun k i =>
      quotAt (ch.queryPoints i) (ch.mem_quotEvalSet_query i)
        (ch.mem_traceEvalSet_query i) (ch.mem_traceEvalSet_gquery i) k
    randomizerOod := randOod
    friSiblingOpenings := friSibs
    finalPoly := finalPoly }

/-- **Verifier OOD Algebraic Check Consistency of `v6ZkAlgSimulator`:**
every transcript produced by the witness-free simulator satisfies the exact verifier OOD
recombination equation
`∑_{k < 2q} z^{k N} c'_k(z) = evalComposition(z, ...) / (z^N - 1)`. -/
theorem v6ZkAlgSimulator_ood_check {K : Type} [Field K] [DecidableEq K] {P : V6ZkParams}
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hq : 1 ≤ P.halfQuotientSlices)
    (s : V6ZkCoreSample K P ch) :
    let v := v6ZkAlgSimulator pub ch hq s
    ∑ k : Fin (2 * P.halfQuotientSlices), ch.z ^ (k.val * P.traceHeight) * v.quotientOodSlices k =
      pub.evalComposition ch.z v.mainOodCur v.mainOodNext v.logupOodCur v.logupOodNext
        v.maskedInterAccs v.maskPolyOod * (ch.z ^ P.traceHeight - 1)⁻¹ := by
  intro v
  have h2q : 2 * P.halfQuotientSlices = (2 * P.halfQuotientSlices - 1) + 1 := by omega
  let e : Fin ((2 * P.halfQuotientSlices - 1) + 1) ≃ Fin (2 * P.halfQuotientSlices) :=
    finCongr h2q.symm
  rw [← Equiv.sum_comp e, Fin.sum_univ_succ]
  have h0 : ch.z ^ ((e 0).val * P.traceHeight) * v.quotientOodSlices (e 0) =
      pub.evalComposition ch.z v.mainOodCur v.mainOodNext v.logupOodCur v.logupOodNext
        v.maskedInterAccs v.maskPolyOod * (ch.z ^ P.traceHeight - 1)⁻¹ -
      ∑ j : Fin (2 * P.halfQuotientSlices - 1),
        ch.z ^ ((j.val + 1) * P.traceHeight) * s.2.2.2.1 j ⟨ch.z, ch.mem_quotEvalSet_z⟩ := by
    simp [v, v6ZkAlgSimulator, e]
  have htail :
      ∑ j : Fin (2 * P.halfQuotientSlices - 1),
        ch.z ^ ((e j.succ).val * P.traceHeight) * v.quotientOodSlices (e j.succ) =
      ∑ j : Fin (2 * P.halfQuotientSlices - 1),
        ch.z ^ ((j.val + 1) * P.traceHeight) * s.2.2.2.1 j ⟨ch.z, ch.mem_quotEvalSet_z⟩ := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [v, v6ZkAlgSimulator, e]
  rw [h0, htail, sub_add_cancel]

/-- OOD split of a `v6-zk` FRI randomizer polynomial (`deg < 2 ^ arities.sum * finalPolyLen + 1`)
into `(R(z), R_q)` with `R_q : Fin (2 ^ arities.sum * finalPolyLen) → K`. -/
noncomputable def v6ZkFriRandSplit {K : Type} [Field K] [Fintype K] (P : V6ZkParams) (z : K) :
    (Fin P.friRandomizerDeg → K) ≃ K × (Fin (2 ^ P.arities.sum * P.finalPolyLen) → K) :=
  oodQuotientSplitEquiv (2 ^ P.arities.sum * P.finalPolyLen + 1) (Nat.succ_pos _) z

/-- **Real `v6-zk` Algebraic Prover (`v6ZkRealAlgProver`):**
runs the real `v6-zk` blinding, telescoping quotient slicing, and multi-arity FRI randomizer
folding on the secret witness `w` using fresh prover randomness `rand`. -/
noncomputable def v6ZkRealAlgProver {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (w : V6ZkWitness K P pub ch) (rand : V6ZkProverRand K P) : V6ZkAlgView K P ch :=
  let rMain := rand.1
  let rLogup := rand.2.1
  let μ := rand.2.2.1.1
  let rMask := rand.2.2.1.2
  let ρ := rand.2.2.2.1
  let rFri := rand.2.2.2.2
  let qSlices := w.quotientSlices rMain rLogup μ rMask
  let friSplit := v6ZkFriRandSplit P ch.z rFri
  let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
  let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
    friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
  { mainOodCur := fun c => (blindPoly P.traceHeight (w.mainPolys c) (rMain c)).eval ch.z
    mainOodNext := fun c => (blindPoly P.traceHeight (w.mainPolys c) (rMain c)).eval (ch.g * ch.z)
    mainFriOpenings := fun c i =>
      (blindPoly P.traceHeight (w.mainPolys c) (rMain c)).eval (ch.queryPoints i)
    logupOodCur := fun c => (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval ch.z
    logupOodNext := fun c => (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval (ch.g * ch.z)
    logupFriOpenings := fun c i =>
      (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval (ch.queryPoints i)
    maskedInterAccs := fun p => w.interAccs p + μ p
    maskPolyOod := fun p => (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval ch.z
    maskPolyFri := fun p i =>
      (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval (ch.queryPoints i)
    quotientOodSlices := fun k =>
      (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget qSlices ρ k).eval ch.z
    quotientFriSlices := fun k i =>
      (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget qSlices ρ k).eval
        (ch.queryPoints i)
    randomizerOod := friSplit.1
    friSiblingOpenings := evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries
      ch.friRoundPoints friDec.2
    finalPoly := friDec.1 }

/-- Extraction of the uniform core sample from a real prover execution. -/
private noncomputable def v6ZkRealToCore {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (w : V6ZkWitness K P pub ch) (rand : V6ZkProverRand K P) : V6ZkCoreSample K P ch :=
  let rMain := rand.1
  let rLogup := rand.2.1
  let μ := rand.2.2.1.1
  let rMask := rand.2.2.1.2
  let ρ := rand.2.2.2.1
  let rFri := rand.2.2.2.2
  let qSlices := w.quotientSlices rMain rLogup μ rMask
  let friSplit := v6ZkFriRandSplit P ch.z rFri
  let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
  let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
    friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
  (fun c x => (blindPoly P.traceHeight (w.mainPolys c) (rMain c)).eval x.1,
   fun c x => (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval x.1,
   (fun p => w.interAccs p + μ p,
    fun p x => (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval x.1),
   fun j x => (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
     qSlices ρ ⟨j.val + 1, by omega⟩).eval x.1,
   (friSplit.1,
    (friDec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints friDec.2)))

/-- Factorization identity: `v6ZkRealAlgProver` equals `v6ZkAlgSimulator ∘ v6ZkRealToCore`. -/
private theorem v6ZkRealAlgProver_eq_sim_comp {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hq : 1 ≤ P.halfQuotientSlices) (w : V6ZkWitness K P pub ch) (rand : V6ZkProverRand K P) :
    v6ZkRealAlgProver pub ch w rand =
      v6ZkAlgSimulator pub ch hq (v6ZkRealToCore pub ch w rand) := by
  have hqSlice : ∀ (x : K) (hxQ : x ∈ ch.quotEvalSet) (k : Fin (2 * P.halfQuotientSlices)),
      (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
        (w.quotientSlices rand.1 rand.2.1 rand.2.2.1.1 rand.2.2.1.2) rand.2.2.2.1 k).eval x =
      if h0 : k.val = 0 then
        pub.evalComposition x
          (fun c => (blindPoly P.traceHeight (w.mainPolys c) (rand.1 c)).eval x)
          (fun c => (blindPoly P.traceHeight (w.mainPolys c) (rand.1 c)).eval (ch.g * x))
          (fun c => (blindPoly P.traceHeight (w.logupPolys c) (rand.2.1 c)).eval x)
          (fun c => (blindPoly P.traceHeight (w.logupPolys c) (rand.2.1 c)).eval (ch.g * x))
          (fun p => w.interAccs p + rand.2.2.1.1 p)
          (fun p => (blindPoly P.traceHeight (w.maskBasePolys p (rand.2.2.1.1 p))
            (rand.2.2.1.2 p)).eval x) * (x ^ P.traceHeight - 1)⁻¹ -
          ∑ j : Fin (2 * P.halfQuotientSlices - 1),
            x ^ ((j.val + 1) * P.traceHeight) *
              (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
                (w.quotientSlices rand.1 rand.2.1 rand.2.2.1.1 rand.2.2.1.2) rand.2.2.2.1
                ⟨j.val + 1, by omega⟩).eval x
      else
        (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
          (w.quotientSlices rand.1 rand.2.1 rand.2.2.1.1 rand.2.2.1.2) rand.2.2.2.1
          ⟨k.val - 1 + 1, by omega⟩).eval x := by
    intro x hxQ k
    split_ifs with h0
    · have hk0 : k = ⟨0, by omega⟩ := Fin.ext h0
      rw [hk0, eval_blindedQuotientSlice_zero _ _ _ hq,
        w.quotient_valid rand.1 rand.2.1 rand.2.2.1.1 rand.2.2.1.2 x hxQ]
    · have hk : k = ⟨k.val - 1 + 1, by omega⟩ := by ext; dsimp only; omega
      conv_lhs => rw [hk]
  unfold v6ZkRealAlgProver v6ZkAlgSimulator v6ZkRealToCore
  dsimp only
  congr 1
  · funext k
    exact hqSlice ch.z ch.mem_quotEvalSet_z k
  · funext k i
    exact hqSlice (ch.queryPoints i) (ch.mem_quotEvalSet_query i) k

/-- Helper: finite-set indexing equivalence `Fin s.card ≃ {x // x ∈ s}`. -/
private theorem eval_matrix_uniform_finset {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (n W b : ℕ) (fs : Fin W → K[X]) (S : Finset K) (hSb : S.card ≤ b)
    (hdisj : ∀ x ∈ S, x ^ n ≠ 1) :
    IsUniformPushforward
      (fun rs : Fin W → Fin b → K =>
        fun w : Fin W => fun x : {x : K // x ∈ S} => (blindPoly n (fs w) (rs w)).eval x.1) := by
  let eFin : Fin S.card ≃ {x : K // x ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let xs : Fin S.card → K := fun i => (eFin i).1
  have hxs_inj : Function.Injective xs := fun i j hij => eFin.injective (Subtype.ext hij)
  have hxs_disj : ∀ i : Fin S.card, (xs i) ^ n ≠ 1 := fun i => hdisj (eFin i).1 (eFin i).2
  have hmat := eval_matrix_uniform_of_blinding n W fs hSb hxs_inj hxs_disj
  let eOut : (Fin W → Fin S.card → K) ≃ (Fin W → {x : K // x ∈ S} → K) :=
    Equiv.arrowCongr (Equiv.refl (Fin W)) (Equiv.arrowCongr eFin (Equiv.refl K))
  have hcomp :
      (fun rs : Fin W → Fin b → K =>
        fun w : Fin W => fun x : {x : K // x ∈ S} => (blindPoly n (fs w) (rs w)).eval x.1) =
      eOut ∘ (fun rs : Fin W → Fin b → K =>
        fun w : Fin W => fun i : Fin S.card => (blindPoly n (fs w) (rs w)).eval (xs i)) := by
    funext rs w x
    simp [eOut, xs]
  rw [hcomp]
  exact isUniformPushforward_comp_equiv hmat eOut

/-- Helper: telescoping quotient tail uniformity over any finite point set `S` (`S.card ≤ b`). -/
private theorem quotient_slices_uniform_finset {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (n q b : ℕ) (hq : 1 ≤ q) (c : Fin (2 * q) → K[X]) (S : Finset K) (hSb : S.card ≤ b) :
    IsUniformPushforward
      (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        fun j : Fin (2 * q - 1) => fun x : {x : K // x ∈ S} =>
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval x.1) := by
  let eFin : Fin S.card ≃ {x : K // x ∈ S} := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  let xs : Fin S.card → K := fun i => (eFin i).1
  have hxs_inj : Function.Injective xs := fun i j hij => eFin.injective (Subtype.ext hij)
  have hquot := quotient_slices_uniform_of_telescoping n q hq c hSb hxs_inj
  let eOut : (Fin (2 * q - 1) → Fin S.card → K) ≃
      (Fin (2 * q - 1) → {x : K // x ∈ S} → K) :=
    Equiv.arrowCongr (Equiv.refl _) (Equiv.arrowCongr eFin (Equiv.refl K))
  have hcomp :
      (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        fun j : Fin (2 * q - 1) => fun x : {x : K // x ∈ S} =>
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval x.1) =
      eOut ∘ (fun ρ : Fin (2 * q - 1) → Fin b → K =>
        fun j : Fin (2 * q - 1) => fun i : Fin S.card =>
          (blindedQuotientSlice n q b c ρ ⟨j.val + 1, by omega⟩).eval (xs i)) := by
    funext ρ j x
    simp [eOut, xs]
  rw [hcomp]
  exact isUniformPushforward_comp_equiv hquot eOut

/-- **Core Uniformity Theorem:** `v6ZkRealToCore pub ch w` pushes uniform prover randomness
onto the **exact uniform distribution** on `V6ZkCoreSample K P ch`! -/
private theorem v6ZkRealToCore_uniform {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch) :
    IsUniformPushforward (v6ZkRealToCore pub ch w) := by
  obtain ⟨hq1, hqFin, hTb, hQb⟩ := hB
  have hTdisj := ch.traceEvalSet_disjoint_of_ok hch
  have hQdisj := ch.quotEvalSet_disjoint_of_ok hch
  have : Nonempty ((Fin P.numLogupCols → Fin P.blindingBudget → K) ×
      ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) ×
      (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
      (Fin P.friRandomizerDeg → K)) :=
    ⟨(fun _ _ => 0, (fun _ => 0, fun _ _ => 0), fun _ _ => 0, fun _ => 0)⟩
  have : Nonempty ((Fin P.numLogupCols → {x : K // x ∈ ch.traceEvalSet} → K) ×
      ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) ×
      (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
      (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals.{0, 0} K P.arities P.numQueries))) :=
    ⟨(fun _ _ => 0, (fun _ => 0, fun _ _ => 0), fun _ _ => 0,
      (0, (fun _ => 0, zeroFriRoundSiblingEvals P.arities P.numQueries)))⟩
  have : Nonempty (((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) ×
      (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
      (Fin P.friRandomizerDeg → K)) :=
    ⟨((fun _ => 0, fun _ _ => 0), fun _ _ => 0, fun _ => 0)⟩
  have : Nonempty (((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) ×
      (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
      (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals.{0, 0} K P.arities P.numQueries))) :=
    ⟨((fun _ => 0, fun _ _ => 0), fun _ _ => 0,
      (0, (fun _ => 0, zeroFriRoundSiblingEvals P.arities P.numQueries)))⟩
  have : Nonempty ((Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
      (Fin P.friRandomizerDeg → K)) :=
    ⟨(fun _ _ => 0, fun _ => 0)⟩
  have : Nonempty ((Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
      (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals.{0, 0} K P.arities P.numQueries))) :=
    ⟨(fun _ _ => 0, (0, (fun _ => 0, zeroFriRoundSiblingEvals P.arities P.numQueries)))⟩
  have : Nonempty (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals.{0, 0} K P.arities P.numQueries)) :=
    ⟨(0, (fun _ => 0, zeroFriRoundSiblingEvals P.arities P.numQueries))⟩
  -- Layer 1: `rMain`
  let f1 : (Fin P.numMainCols → Fin P.blindingBudget → K) →
      (Fin P.numMainCols → {x : K // x ∈ ch.traceEvalSet} → K) :=
    fun rMain c x => (blindPoly P.traceHeight (w.mainPolys c) (rMain c)).eval x.1
  let g1 : (Fin P.numMainCols → Fin P.blindingBudget → K) →
      ((Fin P.numLogupCols → Fin P.blindingBudget → K) ×
       ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) ×
       (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
       (Fin P.friRandomizerDeg → K)) →
      ((Fin P.numLogupCols → {x : K // x ∈ ch.traceEvalSet} → K) ×
       ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) ×
       (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
       (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals K P.arities P.numQueries))) :=
    fun rMain rest =>
      let rLogup := rest.1
      let μ := rest.2.1.1
      let rMask := rest.2.1.2
      let ρ := rest.2.2.1
      let rFri := rest.2.2.2
      let qSlices := w.quotientSlices rMain rLogup μ rMask
      let friSplit := v6ZkFriRandSplit P ch.z rFri
      let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
      let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
        friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
      (fun c x => (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval x.1,
       (fun p => w.interAccs p + μ p,
        fun p x => (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval x.1),
       fun j x => (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
         qSlices ρ ⟨j.val + 1, by omega⟩).eval x.1,
       (friSplit.1,
        (friDec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints friDec.2)))
  have hL1 : v6ZkRealToCore pub ch w = fun p => (f1 p.1, g1 p.1 p.2) := rfl
  rw [hL1]
  refine isUniformPushforward_fiberwise f1 g1
    (eval_matrix_uniform_finset P.traceHeight P.numMainCols P.blindingBudget
      w.mainPolys ch.traceEvalSet hTb hTdisj) fun rMain => ?_
  -- Layer 2: `rLogup`
  let f2 : (Fin P.numLogupCols → Fin P.blindingBudget → K) →
      (Fin P.numLogupCols → {x : K // x ∈ ch.traceEvalSet} → K) :=
    fun rLogup c x => (blindPoly P.traceHeight (w.logupPolys c) (rLogup c)).eval x.1
  let g2 : (Fin P.numLogupCols → Fin P.blindingBudget → K) →
      (((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) ×
       (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
       (Fin P.friRandomizerDeg → K)) →
      (((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) ×
       (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
       (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals K P.arities P.numQueries))) :=
    fun rLogup rest =>
      let μ := rest.1.1
      let rMask := rest.1.2
      let ρ := rest.2.1
      let rFri := rest.2.2
      let qSlices := w.quotientSlices rMain rLogup μ rMask
      let friSplit := v6ZkFriRandSplit P ch.z rFri
      let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
      let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
        friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
      ((fun p => w.interAccs p + μ p,
        fun p x => (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval x.1),
       fun j x => (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
         qSlices ρ ⟨j.val + 1, by omega⟩).eval x.1,
       (friSplit.1,
        (friDec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints friDec.2)))
  have hL2 : g1 rMain = fun p => (f2 p.1, g2 p.1 p.2) := rfl
  rw [hL2]
  refine isUniformPushforward_fiberwise f2 g2
    (eval_matrix_uniform_finset P.traceHeight P.numLogupCols P.blindingBudget
      w.logupPolys ch.traceEvalSet hTb hTdisj) fun rLogup => ?_
  -- Layer 3: `(μ, rMask)`
  let f3 : ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) →
      ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → {x : K // x ∈ ch.quotEvalSet} → K)) :=
    fun mRand =>
      (fun p => w.interAccs p + mRand.1 p,
       fun p x => (blindPoly P.traceHeight (w.maskBasePolys p (mRand.1 p)) (mRand.2 p)).eval x.1)
  let g3 : ((Fin (P.numCircuits - 1) → K) × (Fin (P.numCircuits - 1) → Fin P.blindingBudget → K)) →
      ((Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) ×
       (Fin P.friRandomizerDeg → K)) →
      ((Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) ×
       (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals K P.arities P.numQueries))) :=
    fun mRand rest =>
      let ρ := rest.1
      let rFri := rest.2
      let qSlices := w.quotientSlices rMain rLogup mRand.1 mRand.2
      let friSplit := v6ZkFriRandSplit P ch.z rFri
      let W_batch := w.friWitnessBatch rMain rLogup mRand.1 mRand.2 ρ
      let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
        friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
      (fun j x => (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
         qSlices ρ ⟨j.val + 1, by omega⟩).eval x.1,
       (friSplit.1,
        (friDec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints friDec.2)))
  have hL3 : g2 rLogup = fun p => (f3 p.1, g3 p.1 p.2) := rfl
  rw [hL3]
  refine isUniformPushforward_fiberwise f3 g3 ?_ fun ⟨μ, rMask⟩ => ?_
  · refine isUniformPushforward_fiberwise
      (fun μ : Fin (P.numCircuits - 1) → K => fun p => w.interAccs p + μ p)
      (fun μ (rMask : Fin (P.numCircuits - 1) → Fin P.blindingBudget → K) p
        (x : {x : K // x ∈ ch.quotEvalSet}) =>
        (blindPoly P.traceHeight (w.maskBasePolys p (μ p)) (rMask p)).eval x.1)
      (isUniformPushforward_of_linear_surj (LinearMap.id (R := K)) Function.surjective_id w.interAccs)
      fun μ => ?_
    exact eval_matrix_uniform_finset P.traceHeight (P.numCircuits - 1) P.blindingBudget
      (fun p => w.maskBasePolys p (μ p)) ch.quotEvalSet hQb hQdisj
  -- Layer 4: `ρ` (telescoping quotient slices)
  let f4 : (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) →
      (Fin (2 * P.halfQuotientSlices - 1) → {x : K // x ∈ ch.quotEvalSet} → K) :=
    fun ρ j x => (blindedQuotientSlice P.traceHeight P.halfQuotientSlices P.blindingBudget
      (w.quotientSlices rMain rLogup μ rMask) ρ ⟨j.val + 1, by omega⟩).eval x.1
  let g4 : (Fin (2 * P.halfQuotientSlices - 1) → Fin P.blindingBudget → K) →
      (Fin P.friRandomizerDeg → K) →
      (K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals K P.arities P.numQueries)) :=
    fun ρ rFri =>
      let friSplit := v6ZkFriRandSplit P ch.z rFri
      let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
      let friDec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
        friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + friSplit.2)
      (friSplit.1,
       (friDec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints friDec.2))
  have hL4 : g3 (μ, rMask) = fun p => (f4 p.1, g4 p.1 p.2) := rfl
  rw [hL4]
  refine isUniformPushforward_fiberwise f4 g4
    (quotient_slices_uniform_finset P.traceHeight P.halfQuotientSlices P.blindingBudget hq1
      (w.quotientSlices rMain rLogup μ rMask) ch.quotEvalSet hQb) fun ρ => ?_
  -- Layer 5: `rFri` (OOD split + multi-arity FRI randomizer folding)
  let eSplit := v6ZkFriRandSplit P ch.z
  let W_batch := w.friWitnessBatch rMain rLogup μ rMask ρ
  let postMap : K × (Fin (2 ^ P.arities.sum * P.finalPolyLen) → K) →
      K × ((Fin P.finalPolyLen → K) × FriRoundSiblingEvals.{0, 0} K P.arities P.numQueries) :=
    fun p =>
      let dec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
        friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + p.2)
      (p.1, (dec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints dec.2))
  have hPost : IsUniformPushforward postMap :=
    isUniformPushforward_prod (id : K → K)
      (fun R : Fin (2 ^ P.arities.sum * P.finalPolyLen) → K =>
        let dec : (Fin P.finalPolyLen → K) × FriRoundSiblings.{0, 0} K P.arities P.finalPolyLen :=
          friMultiDecomp P.arities P.finalPolyLen ch.friBetas (W_batch + R)
        (dec.1, evalFriRoundSiblings P.arities P.finalPolyLen P.numQueries ch.friRoundPoints dec.2))
      isUniformPushforward_id
      (fri_multi_round_randomizer_uniform P.arities P.finalPolyLen P.numQueries hqFin
        ch.friBetas ch.friRoundPoints hch.2.2.2 W_batch)
  have hSplitUnif : IsUniformPushforward eSplit := isUniformPushforward_of_equiv eSplit
  have hL5 : g4 ρ = postMap ∘ eSplit := rfl
  rw [hL5]
  intro y
  rw [unifMass_comp_eq_of_eq (F₂ := id)
    (fun z => (hSplitUnif z).trans (isUniformPushforward_id z).symm) postMap y]
  exact hPost y

/-- Exact pushforward distribution equality between `v6ZkRealAlgProver` and `v6ZkAlgSimulator`. -/
theorem v6Zk_alg_unifMass_eq {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch) (v : V6ZkAlgView K P ch) :
    unifMass (v6ZkRealAlgProver pub ch w) v = unifMass (v6ZkAlgSimulator pub ch hB.1) v := by
  have : Nonempty (V6ZkCoreSample K P ch) := nonempty_v6ZkCoreSample P ch
  have hfac : v6ZkRealAlgProver pub ch w = v6ZkAlgSimulator pub ch hB.1 ∘ v6ZkRealToCore pub ch w := by
    funext rand
    exact v6ZkRealAlgProver_eq_sim_comp pub ch hB.1 w rand
  rw [hfac]
  exact unifMass_comp_eq_of_eq (F₂ := id)
    (fun s => (v6ZkRealToCore_uniform pub ch hB hch w s).trans (isUniformPushforward_id s).symm)
    (v6ZkAlgSimulator pub ch hB.1) v

/-- **Exact Perfect Algebraic HVZK Theorem (`v6Zk_alg_perfect_hvzk`):**
in the idealized commitment / oracle-free algebraic layer, for ANY valid `v6-zk` witness `w`,
the total-variation distance between the real `v6-zk` prover and the witness-free simulator
`v6ZkAlgSimulator` is **literally zero** (`tvDist = 0`), and every event `E` has identical
probability under Real and Simulator! -/
theorem v6Zk_alg_perfect_hvzk {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch)
    [Fintype (V6ZkAlgView K P ch)] :
    tvDist (v6ZkRealAlgProver pub ch w) (v6ZkAlgSimulator pub ch hB.1) = 0 ∧
    ∀ E : V6ZkAlgView K P ch → Prop,
      unifProb (v6ZkRealAlgProver pub ch w) E = unifProb (v6ZkAlgSimulator pub ch hB.1) E :=
  ⟨tvDist_eq_zero_of_unifMass_eq (v6Zk_alg_unifMass_eq pub ch hB hch w),
   fun E => unifProb_eq_of_unifMass_eq (v6Zk_alg_unifMass_eq pub ch hB hch w) E⟩

/-- Expectation equality corollary (requires no `Fintype` instance on `V6ZkAlgView`). -/
theorem v6Zk_alg_unifExpect_eq {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch) (g : V6ZkAlgView K P ch → ℝ) :
    unifExpect (v6ZkRealAlgProver pub ch w) g = unifExpect (v6ZkAlgSimulator pub ch hB.1) g := by
  have : Nonempty (V6ZkCoreSample K P ch) := nonempty_v6ZkCoreSample P ch
  have hfac : v6ZkRealAlgProver pub ch w = v6ZkAlgSimulator pub ch hB.1 ∘ v6ZkRealToCore pub ch w := by
    funext rand
    exact v6ZkRealAlgProver_eq_sim_comp pub ch hB.1 w rand
  rw [hfac]
  change unifExpect (v6ZkRealToCore pub ch w) (g ∘ v6ZkAlgSimulator pub ch hB.1) =
    unifExpect (id : V6ZkCoreSample K P ch → V6ZkCoreSample K P ch) (g ∘ v6ZkAlgSimulator pub ch hB.1)
  exact unifExpect_eq_of_unifMass_eq
    (fun s => (v6ZkRealToCore_uniform pub ch hB hch w s).trans (isUniformPushforward_id s).symm) _

end AlgebraicV6Zk

/-! ## Section 3: Full ROM `v6-zk` HVZK Theorem (Algebraic Blinding + Salted Merkle Hiding) -/

section FullRomHvzk

/-- **Complete `v6-zk` Verifier Transcript View (`V6ZkView`):**
pairs the full algebraic opening view (`V6ZkAlgView`: OOD evaluations at `z, g*z`, coset FRI
openings, masked LogUp openings & accumulators, telescoping quotient slices, randomizer OOD,
multi-arity FRI siblings, and final polynomial) with the salted Merkle commitment and
authentication-path view (`SaltedMerkleView`). -/
abbrev V6ZkView (K : Type) [DecidableEq K] (P : V6ZkParams) (ch : V6ZkChallenges K P)
    (L_total : ℕ) (Row Salt Digest : Type) (opened : Finset (Fin L_total)) : Type :=
  V6ZkAlgView K P ch × SaltedMerkleView L_total Row Salt Digest opened

/-- Real `v6-zk` ROM experiment: draws prover blinding randomness `rand`, runs
`v6ZkRealAlgProver` and commits the full blinded LDE rows `leafRows rand` via a salted
Merkle tree in the ROM, and executes the adaptive `N_RO`-query distinguisher `D` on the
complete `V6ZkView`. -/
noncomputable def v6ZkRealGame {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand K P → Fin L_total → Row)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L_total Row Salt Digest) Bool) : ℝ :=
  unifExpect (fun rand : V6ZkProverRand K P => rand) fun rand =>
    realSaltedMerkleGame depth (leafRows rand) opened fun mv =>
      D (v6ZkRealAlgProver pub ch w rand, mv)

/-- **Witness-Free `v6-zk` ROM Simulator (`v6ZkSimulator`):**
takes **ZERO** secret witness! Runs `v6ZkAlgSimulator` to sample a verifier-consistent
algebraic view `algView`, derives ONLY the opened leaf rows `openedRowsOf algView`, runs
the ideal salted-Merkle simulator (uniform random digests for all unopened leaves), and
executes the distinguisher `D`. -/
noncomputable def v6ZkSimulator {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hq : 1 ≤ P.halfQuotientSlices) (depth : ℕ) (opened : Finset (Fin L_total))
    (openedRowsOf : V6ZkAlgView K P ch → {i : Fin L_total // i ∈ opened} → Row)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L_total Row Salt Digest) Bool) : ℝ :=
  unifExpect (v6ZkAlgSimulator pub ch hq) fun algView =>
    idealSaltedMerkleGame depth opened (openedRowsOf algView) fun mv =>
      D (algView, mv)

/-- **MAIN HONEST-VERIFIER ZERO-KNOWLEDGE THEOREM FOR PROTOCOL `v6-zk` (`v6Zk_hvzk`):**
when the blinding budget satisfies `P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card`
(automatically satisfied whenever `b ≥ 2 * numQueries * maxArity + 2`, or
`b ≥ numQueries * maxArity + 2` for `g`-closed query cosets) and `ch.Ok`, for EVERY
valid secret witness `w` and EVERY adaptive `N_RO`-query ROM distinguisher `D`:

  **`|v6ZkRealGame - v6ZkSimulator| ≤ N_RO * L_unopened / |Salt|`**

(and equals **0** in the idealized algebraic layer `v6Zk_alg_perfect_hvzk`). -/
theorem v6Zk_hvzk {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total N_RO : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Nonempty Salt] [Fintype Digest] [Nonempty Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand K P → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView K P ch → {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand K P) (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (SaltedMerkleAns L_total Row Salt Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hB.1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (Fintype.card Salt : ℝ) := by
  have : Nonempty (V6ZkProverRand K P) := nonempty_v6ZkProverRand P
  -- Hybrid 1: real algebraic prover + ideal Merkle simulator.
  let hybrid : ℝ :=
    unifExpect (v6ZkRealAlgProver pub ch w) fun algView =>
      idealSaltedMerkleGame depth opened (openedRowsOf algView) fun mv => D (algView, mv)
  -- Step 1: Hybrid 1 = Simulator Game identically by exact zero algebraic TV (`v6Zk_alg_unifExpect_eq`)!
  have hHybSim : hybrid = v6ZkSimulator pub ch hB.1 depth opened openedRowsOf D :=
    v6Zk_alg_unifExpect_eq pub ch hB hch w _
  rw [← hHybSim]
  -- Step 2: |Real Game - Hybrid 1| ≤ N_RO * L_unopened / |Salt| pointwise via `salted_leaf_rom_indistinguishable`!
  unfold v6ZkRealGame
  dsimp only [hybrid, unifExpect]
  have hcardPos : (0 : ℝ) < Fintype.card (V6ZkProverRand K P) := Nat.cast_pos.mpr Fintype.card_pos
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcardPos]
  calc |∑ rand : V6ZkProverRand K P, _| / (Fintype.card (V6ZkProverRand K P) : ℝ)
      ≤ (∑ rand : V6ZkProverRand K P, |_|) / (Fintype.card (V6ZkProverRand K P) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcardPos.le
    _ ≤ (∑ _rand : V6ZkProverRand K P,
          ((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (Fintype.card Salt : ℝ))) /
        (Fintype.card (V6ZkProverRand K P) : ℝ) := by
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun rand _ => ?_) hcardPos.le
        have hopenEq : (fun i : {i : Fin L_total // i ∈ opened} => leafRows rand i.1) =
            openedRowsOf (v6ZkRealAlgProver pub ch w rand) := by
          funext i; exact hOpenedMatch rand i
        rw [← hopenEq]
        exact salted_leaf_rom_indistinguishable depth (leafRows rand) opened
          (fun mv => D (v6ZkRealAlgProver pub ch w rand, mv)) (fun mv => hD _)
    _ = (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (Fintype.card Salt : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hcardPos.ne']

/-- **Full ROM `v6-zk` HVZK in the Exact Unindexed `RO(row || salt)` Leaf Model (`v6Zk_hvzk_unindexed`):**
matches `multi-stark/v6-zk`'s `hash_leaf_rows_with_salt` (no leaf index in leaf hash),
yielding exact distinguishing bound `(N_RO * L_unopened + L_unopened * (L_total - 1)) / |Salt|`. -/
noncomputable def v6ZkRealGameUnindexed {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand K P → Fin L_total → Row)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool) : ℝ :=
  unifExpect (fun rand : V6ZkProverRand K P => rand) fun rand =>
    realUnindexedMerkleGame depth (leafRows rand) opened fun mv =>
      D (v6ZkRealAlgProver pub ch w rand, mv)

noncomputable def v6ZkSimulatorUnindexed {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Fintype Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hq : 1 ≤ P.halfQuotientSlices) (depth : ℕ) (opened : Finset (Fin L_total))
    (openedRowsOf : V6ZkAlgView K P ch → {i : Fin L_total // i ∈ opened} → Row)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool) : ℝ :=
  unifExpect (v6ZkAlgSimulator pub ch hq) fun algView =>
    idealUnindexedMerkleGame depth opened (openedRowsOf algView) fun mv =>
      D (algView, mv)

theorem v6Zk_hvzk_unindexed {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {P : V6ZkParams} {L_total N_RO : ℕ} {Row Salt Digest : Type}
    [DecidableEq Row] [DecidableEq Salt] [DecidableEq Digest]
    [Fintype Salt] [Nonempty Salt] [Fintype Digest] [Nonempty Digest]
    (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand K P → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView K P ch → {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand K P) (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView K P ch L_total Row Salt Digest opened →
      OracleComp (UnindexedSaltedAns Row Salt Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGameUnindexed pub ch w depth opened leafRows D -
      v6ZkSimulatorUnindexed pub ch hB.1 depth opened openedRowsOf D| ≤
      ((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) +
        ((Finset.univ \ opened).card : ℝ) * ((L_total - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
  have : Nonempty (V6ZkProverRand K P) := nonempty_v6ZkProverRand P
  let hybrid : ℝ :=
    unifExpect (v6ZkRealAlgProver pub ch w) fun algView =>
      idealUnindexedMerkleGame depth opened (openedRowsOf algView) fun mv => D (algView, mv)
  have hHybSim : hybrid = v6ZkSimulatorUnindexed pub ch hB.1 depth opened openedRowsOf D :=
    v6Zk_alg_unifExpect_eq pub ch hB hch w _
  rw [← hHybSim]
  unfold v6ZkRealGameUnindexed
  dsimp only [hybrid, unifExpect]
  have hcardPos : (0 : ℝ) < Fintype.card (V6ZkProverRand K P) := Nat.cast_pos.mpr Fintype.card_pos
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcardPos]
  calc |∑ rand : V6ZkProverRand K P, _| / (Fintype.card (V6ZkProverRand K P) : ℝ)
      ≤ (∑ rand : V6ZkProverRand K P, |_|) / (Fintype.card (V6ZkProverRand K P) : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcardPos.le
    _ ≤ (∑ _rand : V6ZkProverRand K P,
          (((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) +
            ((Finset.univ \ opened).card : ℝ) * ((L_total - 1 : ℕ) : ℝ)) /
            (Fintype.card Salt : ℝ))) /
        (Fintype.card (V6ZkProverRand K P) : ℝ) := by
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun rand _ => ?_) hcardPos.le
        have hopenEq : (fun i : {i : Fin L_total // i ∈ opened} => leafRows rand i.1) =
            openedRowsOf (v6ZkRealAlgProver pub ch w rand) := by
          funext i; exact hOpenedMatch rand i
        rw [← hopenEq]
        exact salted_leaf_unindexed_rom_indistinguishable depth (leafRows rand) opened
          (fun mv => D (v6ZkRealAlgProver pub ch w rand, mv)) (fun mv => hD _)
    _ = ((N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) +
          ((Finset.univ \ opened).card : ℝ) * ((L_total - 1 : ℕ) : ℝ)) / (Fintype.card Salt : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hcardPos.ne']

/-- Helper: discharging `V6ZkParams.BlindingOk` from the explicit budget
`2 * numQueries * maxArity + 2 ≤ blindingBudget` (or `numQueries * maxArity + 2 ≤ blindingBudget`
when `traceEvalSet.card ≤ numOpenings + 2`). -/
theorem blindingOk_of_query_budget {K : Type} [Field K] [DecidableEq K]
    {P : V6ZkParams} {ch : V6ZkChallenges K P}
    (hq1 : 1 ≤ P.halfQuotientSlices) (hqFin : P.numQueries ≤ P.finalPolyLen)
    (hopen : ch.numOpenings ≤ P.numQueries * P.maxArity)
    (hbud : 2 * P.numQueries * P.maxArity + 2 ≤ P.blindingBudget) :
    P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card := by
  have hmul : 2 * P.numQueries * P.maxArity = 2 * (P.numQueries * P.maxArity) :=
    Nat.mul_assoc 2 P.numQueries P.maxArity
  refine ⟨hq1, hqFin, ?_, ?_⟩
  · have h1 := ch.card_traceEvalSet_le
    omega
  · have h2 := ch.card_quotEvalSet_le
    omega

theorem blindingOk_of_closed_query_budget {K : Type} [Field K] [DecidableEq K]
    {P : V6ZkParams} {ch : V6ZkChallenges K P}
    (hq1 : 1 ≤ P.halfQuotientSlices) (hqFin : P.numQueries ≤ P.finalPolyLen)
    (hopen : ch.numOpenings ≤ P.numQueries * P.maxArity)
    (hclosed : ∀ i : Fin ch.numOpenings,
      ∃ j : Fin ch.numOpenings, ch.g * ch.queryPoints i = ch.queryPoints j)
    (hbud : P.numQueries * P.maxArity + 2 ≤ P.blindingBudget) :
    P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card := by
  refine ⟨hq1, hqFin, ?_, ?_⟩
  · have h1 := ch.card_traceEvalSet_le_of_closed hclosed
    omega
  · have h2 := ch.card_quotEvalSet_le
    omega

end FullRomHvzk

/-! ## Section 4: Concrete `GoldilocksExt3` & `ultraCompact400KBZk` HVZK Instantiations -/

section ConcreteGoldilocksExt3

/-- Builds a `V6ZkParams` record from any `CertiFri.FriParams` (such as
`FriParams.ultraCompact400KBZk` or `FriParams.compact400KBBalanced`) with 2× odd-coset
blinding budget `b = 2 ^ logTraceHeight`. -/
abbrev v6ZkParamsOfFri (fri : FriParams) (logTraceHeight : ℕ) (arities : List ℕ)
    (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ) :
    V6ZkParams :=
  { logTraceHeight := logTraceHeight
    blindingBudget := 2 ^ logTraceHeight
    logBlowup := fri.logBlowup
    numQueries := fri.numQueries
    maxLogArity := fri.maxLogArity
    arities := arities
    logFinalPolyLen := fri.logFinalPolyLen
    numMainCols := numMainCols
    numLogupCols := numLogupCols
    numCircuits := numCircuits
    halfQuotientSlices := halfQuotientSlices
    randomizerWidth := randomizerWidth }

/-- Concrete `V6ZkParams` for `FriParams.ultraCompact400KBZk` (`logBlowup = 4`,
`maxLogArity = 3`, `logFinalPolyLen = 8`, `numQueries = 55`, `queryPowBits = 30`). -/
abbrev ultraCompact400KBZkV6Params (logTraceHeight : ℕ) (arities : List ℕ)
    (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ) :
    V6ZkParams :=
  v6ZkParamsOfFri FriParams.ultraCompact400KBZk logTraceHeight arities
    numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth

/-- **Concrete `GoldilocksExt3` (`Fp3Model`) `v6-zk` HVZK Theorem (`goldilocksExt3_v6Zk_hvzk`):**
for ANY `V6ZkParams` over `Fp3Model` satisfying `BlindingOk`, ANY digest type (`Digest` =
32B `BLAKE3-256` or `Digest64` = 64B `BLAKE2b-512`), shipped 16-byte `DomainSep.Salt16`
(`|Salt16| = 2 ^ 128`), ANY valid witness `w`, and ANY adaptive `N_RO`-query ROM
distinguisher `D`:
* Idealized algebraic layer: **exact zero** total-variation distance (`v6Zk_alg_perfect_hvzk`).
* Full ROM with 16-byte `DomainSep.Salt16`:
  distinguishing advantage **`≤ N_RO * L_unopened / 2 ^ 128`**. -/
theorem goldilocksExt3_v6Zk_hvzk
    {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type}
    [DecidableEq Row] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (pub : V6ZkPublic Fp3Model P) (ch : V6ZkChallenges Fp3Model P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model P ch → {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model P) (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened →
      OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hB.1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 128 := by
  have h := v6Zk_hvzk pub ch hB hch w depth opened leafRows openedRowsOf hOpenedMatch D hD
  simpa only [card_salt16, Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Concrete `GoldilocksExt3` (`Fp3Model`) `v6-zk` HVZK Theorem with 32-Byte Post-Quantum-Margin Salt (`Salt32`):**
full ROM distinguishing advantage **`≤ N_RO * L_unopened / 2 ^ 256`**. -/
theorem goldilocksExt3_v6Zk_hvzk_salt32
    {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type}
    [DecidableEq Row] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (pub : V6ZkPublic Fp3Model P) (ch : V6ZkChallenges Fp3Model P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model P ch → {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model P) (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model P ch L_total Row Salt32 Digest opened →
      OracleComp (SaltedMerkleAns L_total Row Salt32 Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hB.1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 256 := by
  have h := v6Zk_hvzk pub ch hB hch w depth opened leafRows openedRowsOf hOpenedMatch D hD
  simpa only [card_salt32, Nat.cast_pow, Nat.cast_ofNat] using h

/-- **Concrete `GoldilocksExt3` HVZK for `FriParams.ultraCompact400KBZk`** (`logBlowup = 4`,
`maxLogArity = 3` → `maxArity = 8`, `logFinalPolyLen = 8` → `finalPolyLen = 256`,
`numQueries = 55`, `queryPowBits = 30`) with 16-byte `DomainSep.Salt16` and 64-byte `Digest64`:
for ANY trace log-height `logTraceHeight ≥ 10` (`N ≥ 1024 ≥ 882 = 2 * 55 * 8 + 2`),
automatically discharges `55 ≤ 256` and `traceEvalSet.card ≤ 2 ^ logTraceHeight`, proving
distinguishing advantage **`≤ N_RO * L_unopened / 2 ^ 128`**. -/
theorem goldilocksExt3_ultraCompact400KBZk_hvzk
    (logTraceHeight : ℕ) (hlogN : 10 ≤ logTraceHeight) (arities : List ℕ)
    (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
    (hq1 : 1 ≤ halfQuotientSlices)
    {L_total N_RO : ℕ} {Row : Type} [DecidableEq Row]
    (pub : V6ZkPublic Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (ch : V6ZkChallenges Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (hopen : ch.numOpenings ≤ (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries *
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).maxArity)
    (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) pub ch)
    (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch →
      {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
      (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch
      L_total Row DomainSep.Salt16 Digest64 opened →
      OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest64) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 128 := by
  have h1024 : 1024 ≤ 2 ^ logTraceHeight :=
    (by decide : 1024 ≤ 2 ^ 10).trans (Nat.pow_le_pow_right two_pos hlogN)
  have hqFin : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries ≤
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).finalPolyLen := by
    change 55 ≤ 2 ^ 8
    decide
  have hB : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).BlindingOk
      ch.traceEvalSet.card ch.quotEvalSet.card := by
    refine blindingOk_of_query_budget hq1 hqFin hopen ?_
    change 2 * 55 * 2 ^ 3 + 2 ≤ 2 ^ logTraceHeight
    omega
  exact goldilocksExt3_v6Zk_hvzk pub ch hB hch w depth opened leafRows openedRowsOf
    hOpenedMatch D hD

/-- **Concrete `GoldilocksExt3` HVZK for `FriParams.ultraCompact400KBZk` with 32-Byte Post-Quantum-Margin Salt (`Salt32`):**
for `logTraceHeight ≥ 10`, distinguishing advantage **`≤ N_RO * L_unopened / 2 ^ 256`**. -/
theorem goldilocksExt3_ultraCompact400KBZk_hvzk_salt32
    (logTraceHeight : ℕ) (hlogN : 10 ≤ logTraceHeight) (arities : List ℕ)
    (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
    (hq1 : 1 ≤ halfQuotientSlices)
    {L_total N_RO : ℕ} {Row : Type} [DecidableEq Row]
    (pub : V6ZkPublic Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (ch : V6ZkChallenges Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (hopen : ch.numOpenings ≤ (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries *
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).maxArity)
    (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) pub ch)
    (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch →
      {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
      (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch
      L_total Row Salt32 Digest64 opened →
      OracleComp (SaltedMerkleAns L_total Row Salt32 Digest64) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 256 := by
  have h1024 : 1024 ≤ 2 ^ logTraceHeight :=
    (by decide : 1024 ≤ 2 ^ 10).trans (Nat.pow_le_pow_right two_pos hlogN)
  have hqFin : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries ≤
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).finalPolyLen := by
    change 55 ≤ 2 ^ 8
    decide
  have hB : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).BlindingOk
      ch.traceEvalSet.card ch.quotEvalSet.card := by
    refine blindingOk_of_query_budget hq1 hqFin hopen ?_
    change 2 * 55 * 2 ^ 3 + 2 ≤ 2 ^ logTraceHeight
    omega
  exact goldilocksExt3_v6Zk_hvzk_salt32 pub ch hB hch w depth opened leafRows openedRowsOf
    hOpenedMatch D hD

/-- **Concrete `GoldilocksExt3` HVZK for `FriParams.ultraCompact400KBZk` at `logTraceHeight ≥ 9` (`N ≥ 512 ≥ 442 = 55 * 8 + 2`)**
under `g`-closed coset query sets (or exact `ch.traceEvalSet.card ≤ 2 ^ logTraceHeight`). -/
theorem goldilocksExt3_ultraCompact400KBZk_hvzk_logN9
    (logTraceHeight : ℕ) (hlogN : 9 ≤ logTraceHeight) (arities : List ℕ)
    (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
    (hq1 : 1 ≤ halfQuotientSlices)
    {L_total N_RO : ℕ} {Row : Type} [DecidableEq Row]
    (pub : V6ZkPublic Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (ch : V6ZkChallenges Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
    (hopen : ch.numOpenings ≤ (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries *
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).maxArity)
    (hclosed : ∀ i : Fin ch.numOpenings,
      ∃ j : Fin ch.numOpenings, ch.g * ch.queryPoints i = ch.queryPoints j)
    (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) pub ch)
    (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch →
      {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth))
      (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth) ch
      L_total Row DomainSep.Salt16 Digest opened →
      OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 128 := by
  have h512 : 512 ≤ 2 ^ logTraceHeight :=
    (by decide : 512 ≤ 2 ^ 9).trans (Nat.pow_le_pow_right two_pos hlogN)
  have hqFin : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).numQueries ≤
      (ultraCompact400KBZkV6Params logTraceHeight arities
        numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).finalPolyLen := by
    change 55 ≤ 2 ^ 8
    decide
  have hB : (ultraCompact400KBZkV6Params logTraceHeight arities
      numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth).BlindingOk
      ch.traceEvalSet.card ch.quotEvalSet.card := by
    refine blindingOk_of_closed_query_budget hq1 hqFin hopen hclosed ?_
    change 55 * 2 ^ 3 + 2 ≤ 2 ^ logTraceHeight
    omega
  exact goldilocksExt3_v6Zk_hvzk pub ch hB hch w depth opened leafRows openedRowsOf
    hOpenedMatch D hD

/-- **Combined `v6-zk` HVZK + `W_R = 4` Tensor Randomizer Span Theorem over `GoldilocksExt3`:**
pairs the full ROM `v6-zk` HVZK bound (`≤ N_RO * L_unopened / 2 ^ 128` for 16-byte `Salt16`)
with `fp3_tensor4_span_failure_prob_le` (`≤ 2 / Goldilocks.order ^ 2 < 1 / 2 ^ 126`) for
the `W_R = 4` base-field tensor randomizer columns of `multi-stark/v6-zk`. -/
theorem goldilocksExt3_v6Zk_hvzk_with_tensor4_span
    {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type}
    [DecidableEq Row] [DecidableEq Digest] [Fintype Digest] [Nonempty Digest]
    (pub : V6ZkPublic Fp3Model P) (ch : V6ZkChallenges Fp3Model P)
    (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card) (hch : ch.Ok)
    (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
    (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
    (openedRowsOf : V6ZkAlgView Fp3Model P ch → {i : Fin L_total // i ∈ opened} → Row)
    (hOpenedMatch : ∀ (rand : V6ZkProverRand Fp3Model P) (i : {i : Fin L_total // i ∈ opened}),
      leafRows rand i.1 = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i)
    (D : V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened →
      OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool)
    (hD : ∀ v, (D v).QueryBound N_RO) :
    |v6ZkRealGame pub ch w depth opened leafRows D -
      v6ZkSimulator pub ch hB.1 depth opened openedRowsOf D| +
    (Nat.card {p : Fp3Model × Fp3Model //
        ¬ FpSpan3 (![1, p.1, p.2, p.1 * p.2] : Fin 4 → Fp3Model)} : ℝ) /
      (Nat.card (Fp3Model × Fp3Model) : ℝ) ≤
      (N_RO : ℝ) * ((Finset.univ \ opened).card : ℝ) / (2 : ℝ) ^ 128 +
        1 / (2 : ℝ) ^ 126 :=
  add_le_add
    (goldilocksExt3_v6Zk_hvzk pub ch hB hch w depth opened leafRows openedRowsOf
      hOpenedMatch D hD)
    (fp3_tensor4_span_failure_prob_le.trans fp3_tensor4_span_failure_lt_two_neg_126.le)

end ConcreteGoldilocksExt3

end CertiFri.P3.Exec
