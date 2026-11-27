import CertiFriP3.DomainSep
import CertiFriProofs.P3.DigestCard
import CertiFriProofs.Exec.SoundnessSponge
import CertiFriProofs.Exec.SoundnessTensor
import CertiFriProofs.Exec.SoundnessZk
import CertiFriProofs.P3.GoldilocksExt3Soundness
import CertiFriProofs.P3.GoldilocksExt3MultiAritySoundness
import CertiFriProofs.Theory.Zk.PolyBlinding
import CertiFriProofs.Theory.Zk.SaltedMerkle
import CertiFriProofs.Exec.Zk.V6ZkHvzk

/-!
# 128-Bit Formal Security Audit (`Audit128`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the
128-bit FRI soundness stack in `CertiFRI`:

1. **Production 128-bit classical instantiation:** native BLAKE3 `derive_key`
   alignment with `multi-stark` `v6`/`v6-zk` and 32-byte `BLAKE3-256` (`Digest`,
   `2^256`, `127.71b` classical BCS `c = 3 / 2`).
2. **64-byte RFC 7693 `BLAKE2b-512` classical-ROM instantiation:** pure-Lean
   `BLAKE2b-512` (`Digest64`, `8 × UInt64`, 512-bit internal state, 128-byte
   block = 1-block 2-to-1 compression) with kernel-checked RFC 7693 KATs,
   16-byte `personal` domain separation (`Blake2b512Domain`), `255.71b`
   classical BCS collision resistance (`c = 3 / 2`, keeping the classical
   collision term `≤ N / (4 * 2 ^ 128)` for `N ≤ 2 ^ 128`), plus arithmetic
   cardinality-ratio inequalities (`DigestCard.lean`). *Note:*
   all soundness proofs are in the **classical** ROM and do not certify 128-bit
   post-quantum protocol soundness (QROM Fiat–Shamir and Grover search on FRI
   queries/PoW are not formalized).
   *(Replaces legacy `BLAKE3-XOF48`/`BLAKE3-XOF64`, whose 256-bit internal `cv`
   limits generic hash-output cardinality.)*
3. Executable Horner-FRI (`spongeAccepts`) literal `≤ N / 2 ^ 128` classical-ROM
   soundness over `GoldilocksExt3` (`Fp3Model`, `p^3 ≈ 2^192`) with `Digest64` for:
   * Unconditional unique decoding `(logBlowup = 2, numQueries = 160, queryPowBits = 20)`;
   * 100% unconditional Johnson regime (`lb = 2, 3, 4`, zero `CurveListCA` hypothesis),
     together with `ZkGuardrailsOk`-conditioned Horner-FRI corollaries in
     `SoundnessZk.lean` (note: `SoundnessZk.lean` itself proves soundness
     lemmas/guardrails only; formal hiding and HVZK theorems live in item 8 below).
4. `FriBatching::Tensor` (`col_weights ⊗ open_weights`) executable refinement
   and unconditional `Tensor2DMCA` soundness (`≤ (3 / 4) / 2 ^ 128` for up to
   `2 ^ 16 × 2 ^ 16 = 2 ^ 32` claims over `GoldilocksExt3`).
5. Constructive negative controls proving that `Fp2`, `(2, 100, 0, 20)`, and
   32-byte digests at `N = 2 ^ 128` / BHT `Q = 2 ^ 86` strictly violate the
   128-bit target.
6. Cubic extension (`Fp3Model`) `StarkModel` (`GoldilocksExt3.starkModel`),
   shape-independent `DynamicRom` `RbrSound` bridge (`rbrSound_starkTensor_ud`,
   `sdoomedTensor_nil_fp3`, `settles_interpTensor_fp3`), 100% unconditional
   Johnson-regime tensor PCS `RbrSound` (`rbrSound_pcsTensor_johnson`), and
   unconditional tensor-batched STARK soundness (`Stark.verifyTensor` /
   `Stark.verifyBatchTensor`) for both unpruned `merkleMmcs` and Plonky3's
   `prunedMmcs` (instantiated concretely for `Digest` / `2^256` and `Digest64` / `2^512`).
7. Multi-arity (`2^a`, `a ≥ 1`, covering `logArity ∈ {1, 2, 3}`, fold factors `2, 4, 8`,
   and variable per-round schedules `Fri.scheduleOfShape`) tensor-batched FRI &
   `GoldilocksExt3` STARK soundness: iterated binary fold equivalence
   (`foldRowMultiM_eq_foldAtPow`), unique-decoding & Johnson multi-arity proximity-gap
   theorems (`stepMCAArity_ud`, `stepMCAArity_of_curveListCA_rel`), executable sponge
   chaining (`c = 3 / 2`) literal `≤ N / 2 ^ 128` 100% unconditional Johnson soundness
   for `FriParams.compact400KBBalanced` (`lb = 4, maxLogArity = 3, q = 58, pow = 28`)
   and `FriParams.ultraCompact400KBZk` (`lb = 4, maxLogArity = 3, q = 55, pow = 30`),
   and unpruned & pruned-MMCS multi-arity tensor STARK soundness over `GoldilocksExt3`.
8. Formal Honest-Verifier Zero-Knowledge (HVZK), polynomial blinding, masked-LogUp,
   and salted-Merkle hiding for Protocol `v6-zk`:
   * Algebraic vanishing-polynomial blinding (`eval_vec_uniform_of_blinding`,
     `eval_ood_and_coset_uniform_of_blinding`), telescoping quotient slicing
     (`quotient_slices_uniform_of_telescoping`), masked-LogUp running-sum and
     cross-circuit boundary blinding (`masked_logup_hiding`,
     `masked_logup_boundary_telescoping`, `masked_logup_boundary_hiding`), and
     multi-arity FRI randomizer decomposition (`fri_multi_round_randomizer_uniform`).
   * Salted Merkle leaf hiding in the classical ROM (`salted_leaf_rom_indistinguishable`
     with bound `≤ N_RO * L_unopened / |Salt|`, plus unindexed `RO(row || salt)`
     variant `salted_leaf_unindexed_rom_indistinguishable`), concretely instantiated
     for 16-byte classical (`s = 128`, `DomainSep.Salt16`) and 32-byte post-quantum-margin
     (`s = 256`, `Salt32`) salts.
   * Witness-free `v6-zk` simulator (`v6ZkAlgSimulator` / `v6ZkSimulator`), exact zero
     total-variation algebraic HVZK (`v6Zk_alg_perfect_hvzk`), full ROM HVZK
     (`v6Zk_hvzk`, `v6Zk_hvzk_unindexed`), and concrete `GoldilocksExt3` /
     `FriParams.ultraCompact400KBZk` instantiations (`goldilocksExt3_v6Zk_hvzk`,
     `goldilocksExt3_v6Zk_hvzk_salt32`, `goldilocksExt3_ultraCompact400KBZk_hvzk`,
     `goldilocksExt3_ultraCompact400KBZk_hvzk_salt32`,
     `goldilocksExt3_ultraCompact400KBZk_hvzk_logN9`, and
     `goldilocksExt3_v6Zk_hvzk_with_tensor4_span`).

Every theorem audited here depends strictly on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom
axioms, zero `native_decide`, zero `bv_decide`.
-/

namespace CertiFri.Audit128

open CertiFri CertiFri.Zk CertiFri.Fri CertiFri.P3 CertiFri.P3.Exec CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.Exec

/-! ## Constructive Negative Controls (Boundary Tightness) -/

/-- Negative control 1: Goldilocks `Fp2` (`p^2 < 2^128`) has strictly fewer than
128 bits of field entropy (`p = 2^64 - 2^32 + 1 < 2^64`). -/
theorem negControl_fp2_below_128 :
    Goldilocks.order ^ 2 < 2 ^ 128 := by
  unfold Goldilocks.order
  norm_num

/-- Negative control 2: `(logBlowup = 2, numQueries = 100, queryPowBits = 20)`
strictly FAILS 128-bit unique-decoding soundness (`(5/8)^100 / 2^20 > 1 / 2^128`). -/
theorem negControl_ud_100_pow20_fails_128 :
    (1 : ℝ) / (2 : ℝ) ^ 128 < ((5 / 8 : ℝ) ^ 100) / (2 : ℝ) ^ 20 := by
  have h5 : 2 ^ 192 < (5 : ℕ) ^ 100 := by
    have h25 : 2 ^ 58 < (5 : ℕ) ^ 25 := by norm_num
    have hpow : (2 ^ 58) ^ 4 < ((5 : ℕ) ^ 25) ^ 4 := Nat.pow_lt_pow_left h25 (by decide)
    have h232 : (2 : ℕ) ^ 192 ≤ (2 ^ 58) ^ 4 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right two_pos (by decide)
    have h100 : ((5 : ℕ) ^ 25) ^ 4 = 5 ^ 100 := by rw [← pow_mul]
    exact lt_of_le_of_lt h232 (h100 ▸ hpow)
  have h5r : (2 : ℝ) ^ 192 < (5 : ℝ) ^ 100 := by exact_mod_cast h5
  have h8 : ((5 / 8 : ℝ) ^ 100) / (2 : ℝ) ^ 20 = (5 : ℝ) ^ 100 / (2 : ℝ) ^ 320 := by
    rw [div_pow, div_div, show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, ← pow_mul, ← pow_add]
  have h320 : (2 : ℝ) ^ 320 = (2 : ℝ) ^ 192 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  rw [h8, h320]
  have hpos192 : (0 : ℝ) < (2 : ℝ) ^ 192 := pow_pos (by norm_num) 192
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  rw [div_lt_div_iff₀ hpos128 (mul_pos hpos192 hpos128), one_mul]
  exact mul_lt_mul_of_pos_right h5r hpos128

/-- Negative control 3: 32-byte digests strictly FAIL classical sponge collision
soundness at `N = 2 ^ 128` (`3 * (2^128)^2 / (2 * 2^256) = 3/2 > 1`), whereas
64-byte RFC 7693 `BLAKE2b-512` (`Digest64`) clears `255.71b` classical BCS. -/
theorem negControl_digest32_fails_classical_at_128 :
    (1 : ℝ) < 3 * ((2 ^ 128 : ℕ) : ℝ) ^ 2 / (2 * (Fintype.card Digest : ℝ)) :=
  digest_sponge_collision_exceeds_one_at_128

/-- Negative control 4: 32-byte digests (and any hash with a 256-bit internal `cv`,
including legacy `BLAKE3-XOF48`/`BLAKE3-XOF64`) strictly FAIL BHT quantum collision
resistance at `Q = 2 ^ 86` (`(2^86)^3 / 2^256 = 4 > 1`), whereas `BLAKE2b-512`
(`Digest64`, true 512-bit internal state) achieves `170.7b` BHT (`+42.7b` headroom),
`204.8b` CNS, and `256b` Grover preimage security. -/
theorem negControl_digest32_fails_bht_at_86 :
    (1 : ℝ) < ((2 ^ 86 : ℕ) : ℝ) ^ 3 / (Fintype.card Digest : ℝ) :=
  digest_bht_quantum_collision_fails_at_86

/-! ## Pinned Theorem Statements (`#guard_msgs` + `#check` + Signature Locks) -/

/--
info: @Blake3Domain.mode_injective : ∀ {d₁ d₂ : Blake3Domain},
  (d₁.keyWords, d₁.domainFlags) = (d₂.keyWords, d₂.domainFlags) → d₁ = d₂
-/
#guard_msgs in
#check @Blake3Domain.mode_injective

/--
info: @Blake2b512Domain.initState_injective : ∀ {d₁ d₂ : Blake2b512Domain}, d₁.initState = d₂.initState → d₁ = d₂
-/
#guard_msgs in
#check @Blake2b512Domain.initState_injective

/--
info: @Blake2b512Domain.v6Zk_initState_ne_nonZk : ∀ {d₁ d₂ : Blake2b512Domain},
  d₁.isZk = true → d₂.isZk = false → d₁.initState ≠ d₂.initState
-/
#guard_msgs in
#check @Blake2b512Domain.v6Zk_initState_ne_nonZk

/-- info: card_digest64 : Fintype.card Digest64 = 2 ^ 512 -/
#guard_msgs in
#check @card_digest64

/--
info: @digest64_sponge_collision_at_255 : ∀ {N : ℕ}, N ≤ 2 ^ 255 → 3 * ↑N ^ 2 / (2 * ↑(Fintype.card Digest64)) ≤ 3 / 8
-/
#guard_msgs in
#check @digest64_sponge_collision_at_255

/--
info: @digest64_bht_quantum_collision_at_128 : ∀ {Q : ℕ}, Q ≤ 2 ^ 128 → ↑Q ^ 3 / ↑(Fintype.card Digest64) ≤ 1 / 2 ^ 128
-/
#guard_msgs in
#check @digest64_bht_quantum_collision_at_128

/--
info: @digest64_bht_quantum_collision_at_170 : ∀ {Q : ℕ}, Q ≤ 2 ^ 170 → ↑Q ^ 3 / ↑(Fintype.card Digest64) ≤ 1 / 4
-/
#guard_msgs in
#check @digest64_bht_quantum_collision_at_170

/--
info: @digest64_cns_quantum_collision_at_204 : ∀ {Q : ℕ}, Q ≤ 2 ^ 204 → ↑Q ^ 5 / ↑(Fintype.card Digest64) ^ 2 ≤ 1 / 16
-/
#guard_msgs in
#check @digest64_cns_quantum_collision_at_204

/--
info: digest64_grover_preimage : ∀ (Q : ℕ), ↑Q ^ 2 / ↑(Fintype.card Digest64) = (↑Q / 2 ^ 256) ^ 2
-/
#guard_msgs in
#check @digest64_grover_preimage

/--
info: @digest_sponge_collision_at_127 : ∀ {N : ℕ}, N ≤ 2 ^ 127 → 3 * ↑N ^ 2 / (2 * ↑(Fintype.card Digest)) ≤ 3 / 8
-/
#guard_msgs in
#check @digest_sponge_collision_at_127

/-- info: ud_160_pow20_le_three_quarters_128 : (5 / 8) ^ 160 / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128 -/
#guard_msgs in
#check @ud_160_pow20_le_three_quarters_128

/--
info: @johnson_ge_118_pow20_le_three_quarters_128 : ∀ {q : ℕ}, 118 ≤ q → (65 / 128) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_ge_118_pow20_le_three_quarters_128

/--
info: goldilocksExt3_tensor2DMCA_ud_128 : ∀ (D : Finset Fp3Model) (d W M : ℕ),
  D.card ≤ 2 ^ 32 →
    W ≤ 2 ^ 16 → M ≤ 2 ^ 16 → 2 * (3 / 8 * ↑D.card) + ↑d ≤ ↑D.card → Tensor2DMCA D d W M (5 / 8) (3 / 4 / 2 ^ 128)
-/
#guard_msgs in
#check @goldilocksExt3_tensor2DMCA_ud_128

/-- info: negControl_fp2_below_128 : Goldilocks.order ^ 2 < 2 ^ 128 -/
#guard_msgs in
#check @negControl_fp2_below_128

/-- info: negControl_ud_100_pow20_fails_128 : 1 / 2 ^ 128 < (5 / 8) ^ 100 / 2 ^ 20 -/
#guard_msgs in
#check @negControl_ud_100_pow20_fails_128

/-- Signature lock: literal `≤ N / 2 ^ 128` UD `(2, 160, 0, 20)` executable
soundness under 64B RFC 7693 `BLAKE2b-512` and incremental sponge chaining (`c = 3 / 2`). -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : params.numQueries = 160) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 60)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128 params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: literal `≤ N / 2 ^ 128` Johnson `(2, 118..128, 0, 20)`
executable soundness under 64B RFC 7693 `BLAKE2b-512` and incremental sponge chaining. -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64) {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ Fri.numRounds params shape → 2 ≤ k →
      (T (2 ^ (Fri.logMaxHeight params.logBlowup shape - j))
        (2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈(65 / 128 : ℝ) * (2 : ℝ) ^ (Fri.logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    (hα_budget : ((Fri.claimRefs params.logBlowup shape).length : ℝ) *
        (cT + 17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤ (2 : ℝ) ^ 62)
    (hβ_budget : 2 * cT + 17 * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 62)
    {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (65 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_128 params shape hbl hqn hqpow
    hmax hheight s₀ hca hcT0 hT hα_budget hβ_budget hadv hN attempt

/-! ## Strict Axiom Audits (`#guard_msgs` + `#print axioms`) -/

/-- info: 'CertiFri.P3.Blake2b.kat_empty_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_empty_hex

/-- info: 'CertiFri.P3.Blake2b.kat_abc_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_abc_hex

/-- info: 'CertiFri.P3.Blake2b.kat_exact128_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_exact128_hex

/-- info: 'CertiFri.P3.Blake2b.kat_hashPair64_exact128' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_hashPair64_exact128

/-- info: 'CertiFri.P3.Blake2b.kat_multi129_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_multi129_hex

/-- info: 'CertiFri.P3.Blake2b.kat_personal_abc_hex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b.kat_personal_abc_hex

/-- info: 'CertiFri.P3.Blake2b512Domain.initState_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b512Domain.initState_injective

/-- info: 'CertiFri.P3.Blake2b512Domain.v6Zk_initState_ne_nonZk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Blake2b512Domain.v6Zk_initState_ne_nonZk

/-- info: 'CertiFri.P3.DomainSepBlake2b512.node64Input_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DomainSepBlake2b512.node64Input_injective

/-- info: 'CertiFri.P3.v6MerkleLeafKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6MerkleLeafKey_eq

/-- info: 'CertiFri.P3.v6MerkleCompressKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6MerkleCompressKey_eq

/-- info: 'CertiFri.P3.v6TranscriptSingleKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6TranscriptSingleKey_eq

/-- info: 'CertiFri.P3.v6TranscriptBatchKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6TranscriptBatchKey_eq

/-- info: 'CertiFri.P3.v6VkKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6VkKey_eq

/-- info: 'CertiFri.P3.Blake3Domain.mode_injective' does not depend on any axioms -/
#guard_msgs in
#print axioms Blake3Domain.mode_injective

/-- info: 'CertiFri.Oracle.prob_hasBad_jointHit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prob_hasBad_jointHit_le

/--
info: 'CertiFri.Oracle.prob_spongeExperiment_bind_committedRow_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms prob_spongeExperiment_bind_committedRow_le

/-- info: 'CertiFri.P3.card_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_digest

/-- info: 'CertiFri.P3.card_digest64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_digest64

/-- info: 'CertiFri.P3.digest64_sponge_collision_at_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest64_sponge_collision_at_255

/--
info: 'CertiFri.P3.digest64_bht_quantum_collision_at_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms digest64_bht_quantum_collision_at_128

/--
info: 'CertiFri.P3.digest64_bht_quantum_collision_at_170' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms digest64_bht_quantum_collision_at_170

/--
info: 'CertiFri.P3.digest64_cns_quantum_collision_at_204' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms digest64_cns_quantum_collision_at_204

/-- info: 'CertiFri.P3.digest64_grover_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest64_grover_preimage

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_uniqueDecoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_uniqueDecoding

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_uniqueDecoding_128

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_johnson_128

/-- info: 'CertiFri.Exec.toModel_tensorWeights_getD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toModel_tensorWeights_getD

/-- info: 'CertiFri.Exec.toModel_tensorOpeningTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms toModel_tensorOpeningTerm

/-- info: 'CertiFri.tensor2DMCA_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tensor2DMCA_ud

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_ud_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_tensor2DMCA_ud_128

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_tensor2DMCA_johnson_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_tensor2DMCA_johnson_128

/-- info: 'CertiFri.Audit128.negControl_fp2_below_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negControl_fp2_below_128

/-- info: 'CertiFri.Audit128.negControl_ud_100_pow20_fails_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negControl_ud_100_pow20_fails_128

/--
info: 'CertiFri.Audit128.negControl_digest32_fails_classical_at_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms negControl_digest32_fails_classical_at_128

/--
info: 'CertiFri.Audit128.negControl_digest32_fails_bht_at_86' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms negControl_digest32_fails_bht_at_86

/-! ## `multi-stark/v6-zk` Lemmas, Guardrails & Horner-FRI Soundness Corollaries Audit (`#guard_msgs` + `#print axioms`) -/

/-- info: v6ZkMerkleLeafKey_eq : Blake3.deriveContextKey v6ZkMerkleLeafContext = v6ZkMerkleLeafKey -/
#guard_msgs in
#check @v6ZkMerkleLeafKey_eq

/--
info: @Blake3Domain.v6Zk_keyWords_ne_nonZk : ∀ {d₁ d₂ : Blake3Domain},
  d₁.isZk = true → d₂.isZk = false → d₁.keyWords ≠ d₂.keyWords
-/
#guard_msgs in
#check @Blake3Domain.v6Zk_keyWords_ne_nonZk

/--
info: @DomainSep.saltedRowBytes_injective : ∀ {r₁ r₂ : Array Goldilocks} {s₁ s₂ : DomainSep.Salt16},
  DomainSep.saltedRowBytes r₁ s₁ = DomainSep.saltedRowBytes r₂ s₂ → r₁ = r₂ ∧ s₁ = s₂
-/
#guard_msgs in
#check @DomainSep.saltedRowBytes_injective

/--
info: @salted_merkle_binding_of_no_collision : ∀ {Row Salt D : Type} (hashLeaf : Row × Salt → D) (compress : D → D → D),
  Function.Injective hashLeaf →
    (∀ (l₁ r₁ l₂ r₂ : D), compress l₁ r₁ = compress l₂ r₂ → l₁ = l₂ ∧ r₁ = r₂) →
      ∀ {idx : ℕ} {row₁ row₂ : Row} {salt₁ salt₂ : Salt} {path₁ path₂ : List D},
        path₁.length = path₂.length →
          evalMerklePath compress idx (hashLeaf (row₁, salt₁)) path₁ =
              evalMerklePath compress idx (hashLeaf (row₂, salt₂)) path₂ →
            row₁ = row₂ ∧ salt₁ = salt₂
-/
#guard_msgs in
#check @salted_merkle_binding_of_no_collision

/--
info: @zk_oddCoset_blinding_agrees_on_trace : ∀ {K : Type u_1} [inst : Field K] (N : ℕ) (T₀ b : Polynomial K) (x : K),
  x ^ N = 1 → Polynomial.eval x (T₀ + (Polynomial.X ^ N - 1) * b) = Polynomial.eval x T₀
-/
#guard_msgs in
#check @zk_oddCoset_blinding_agrees_on_trace

/--
info: @zk_quotient_telescoping_sum : ∀ {K : Type u_1} [inst : Field K] (N q : ℕ),
  1 ≤ q →
    ∀ (c : Fin (2 * q) → Polynomial K) (ρ : Fin (2 * q - 1) → Polynomial K),
      ∑ k, Polynomial.X ^ (↑k * N) * zkBlindedSlice N q c ρ k = ∑ k, Polynomial.X ^ (↑k * N) * c k
-/
#guard_msgs in
#check @zk_quotient_telescoping_sum

/--
info: @fp3_tensor4_spans_of_not_base : ∀ {r₀ r₁ : Fp3Model},
  r₀.c1 ≠ 0 ∨ r₀.c2 ≠ 0 → r₁.c1 ≠ 0 ∨ r₁.c2 ≠ 0 → FpSpan3 ![1, r₀, r₁, r₀ * r₁]
-/
#guard_msgs in
#check @fp3_tensor4_spans_of_not_base

/--
info: fp3_tensor4_span_failure_prob_le : ↑(Nat.card { p // ¬FpSpan3 ![1, p.1, p.2, p.1 * p.2] }) /
    ↑(Nat.card (Fp3Model × Fp3Model)) ≤
  2 / ↑Goldilocks.order ^ 2
-/
#guard_msgs in
#check @fp3_tensor4_span_failure_prob_le

/-- info: fp3_tensor4_span_failure_lt_two_neg_126 : 2 / ↑Goldilocks.order ^ 2 < 1 / 2 ^ 126 -/
#guard_msgs in
#check @fp3_tensor4_span_failure_lt_two_neg_126

/--
info: negControl_fp3_tensor3_span_failure_ge : 1 / ↑Goldilocks.order ≤
    ↑(Nat.card { p // ¬FpSpan3 ![1, p.1, p.2] }) / ↑(Nat.card (Fp3Model × Fp3Model)) ∧
  1 / 2 ^ 64 < 1 / ↑Goldilocks.order
-/
#guard_msgs in
#check @negControl_fp3_tensor3_span_failure_ge

/--
info: goldilocksExt3_zk_tensor2DMCA_ud_128 : ∀ (D : Finset Fp3Model) (d W_orig W_R M : ℕ),
  D.card ≤ 2 ^ 32 →
    W_orig + W_R ≤ 2 ^ 16 →
      M ≤ 2 ^ 16 → 2 * (3 / 8 * ↑D.card) + ↑d ≤ ↑D.card → Tensor2DMCA D d (W_orig + W_R) M (5 / 8) (3 / 4 / 2 ^ 128)
-/
#guard_msgs in
#check @goldilocksExt3_zk_tensor2DMCA_ud_128

/-- info: zkProfileUd128_ok : ZkGuardrailsOk zkProfileUd128 -/
#guard_msgs in
#check @zkProfileUd128_ok

/-- info: zkProfileJohnsonLb2_ok : ZkGuardrailsOk zkProfileJohnsonLb2 -/
#guard_msgs in
#check @zkProfileJohnsonLb2_ok

/-- info: zkProfileJohnsonLb3_ok : ZkGuardrailsOk zkProfileJohnsonLb3 -/
#guard_msgs in
#check @zkProfileJohnsonLb3_ok

/-- info: zkProfileJohnsonLb4_ok : ZkGuardrailsOk zkProfileJohnsonLb4 -/
#guard_msgs in
#check @zkProfileJohnsonLb4_ok

/-- info: 'CertiFri.P3.v6ZkMerkleLeafKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkMerkleLeafKey_eq

/-- info: 'CertiFri.P3.v6ZkMerkleCompressKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkMerkleCompressKey_eq

/-- info: 'CertiFri.P3.v6ZkTranscriptSingleKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkTranscriptSingleKey_eq

/-- info: 'CertiFri.P3.v6ZkTranscriptBatchKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkTranscriptBatchKey_eq

/-- info: 'CertiFri.P3.v6ZkVkKey_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkVkKey_eq

/-- info: 'CertiFri.P3.Blake3Domain.v6Zk_keyWords_ne_nonZk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Blake3Domain.v6Zk_keyWords_ne_nonZk

/-- info: 'CertiFri.P3.DomainSep.saltedRowBytes_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DomainSep.saltedRowBytes_injective

/-- info: 'CertiFri.P3.DomainSep.saltedExt3RowBytes_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DomainSep.saltedExt3RowBytes_injective

/--
info: 'CertiFri.P3.Exec.salted_merkle_binding_of_no_collision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms salted_merkle_binding_of_no_collision

/-- info: 'CertiFri.P3.Exec.salted_sponge_soundness_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms salted_sponge_soundness_le

/-- info: 'CertiFri.P3.Exec.v6Zk_saltedLeaf_injective_and_disjoint' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms v6Zk_saltedLeaf_injective_and_disjoint

/--
info: 'CertiFri.P3.Exec.v6Zk_saltedLeaf_blake2b512_injective_and_disjoint' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms v6Zk_saltedLeaf_blake2b512_injective_and_disjoint

/--
info: 'CertiFri.P3.Exec.zk_oddCoset_blinding_agrees_on_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zk_oddCoset_blinding_agrees_on_trace

/--
info: 'CertiFri.P3.Exec.zk_oddCoset_blinding_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zk_oddCoset_blinding_natDegree_lt

/-- info: 'CertiFri.P3.Exec.zk_quotient_telescoping_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zk_quotient_telescoping_sum

/-- info: 'CertiFri.P3.Exec.zk_blindedSlice_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zk_blindedSlice_natDegree_lt

/-- info: 'CertiFri.P3.Exec.fp3_tensor4_spans_of_not_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fp3_tensor4_spans_of_not_base

/--
info: 'CertiFri.P3.Exec.fp3_tensor4_span_failure_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fp3_tensor4_span_failure_prob_le

/--
info: 'CertiFri.P3.Exec.fp3_tensor4_span_failure_lt_two_neg_126' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms fp3_tensor4_span_failure_lt_two_neg_126

/--
info: 'CertiFri.P3.Exec.negControl_fp3_tensor3_span_failure_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms negControl_fp3_tensor3_span_failure_ge

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_zk_tensor2DMCA_ud_128' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_zk_tensor2DMCA_ud_128

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_ud_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_soundness_blake2b512_ud_128

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128

/-- info: 'CertiFri.P3.Exec.zkProfileUd128_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zkProfileUd128_ok

/-- info: 'CertiFri.P3.Exec.zkProfileJohnsonLb2_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zkProfileJohnsonLb2_ok

/-- info: 'CertiFri.P3.Exec.zkProfileJohnsonLb3_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zkProfileJohnsonLb3_ok

/-- info: 'CertiFri.P3.Exec.zkProfileJohnsonLb4_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms zkProfileJohnsonLb4_ok

/-- info: 'CertiFri.P3.Exec.negControl_zk_trap1_small_trace' depends on axioms: [propext] -/
#guard_msgs in
#print axioms negControl_zk_trap1_small_trace

/-- info: 'CertiFri.P3.Exec.negControl_zk_trap2_small_randomizer_width' depends on axioms: [propext] -/
#guard_msgs in
#print axioms negControl_zk_trap2_small_randomizer_width

/-- info: 'CertiFri.P3.Exec.negControl_zk_trap3_quotient_blowup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms negControl_zk_trap3_quotient_blowup

/-- info: 'CertiFri.P3.Exec.negControl_zk_trap4_v6_domain_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms negControl_zk_trap4_v6_domain_rejected

/-! ## Unconditional `CurveListCA` Discharge & 128-Bit Johnson Audit (`lb = 2, 3, 4` & `v6-zk`) -/

/-- info: curveListCA_fp3 : CurveListCA Fp3Model CurveListCAProof.curveListThreshold -/
#guard_msgs in
#check @curveListCA_fp3

/--
info: @johnson_71_128_ge_128_pow20_le_three_quarters_128 : ∀ {q : ℕ}, 128 ≤ q → (71 / 128) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_71_128_ge_128_pow20_le_three_quarters_128

/--
info: @johnson_135_256_ge_118_pow20_le_three_quarters_128 : ∀ {q : ℕ}, 118 ≤ q → (135 / 256) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_135_256_ge_118_pow20_le_three_quarters_128

/--
info: @johnson_19_50_ge_78_pow20_le_three_quarters_128 : ∀ {q : ℕ}, 78 ≤ q → (19 / 50) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_19_50_ge_78_pow20_le_three_quarters_128

/--
info: @johnson_35_128_ge_58_pow20_le_three_quarters_128 : ∀ {q : ℕ}, 58 ≤ q → (35 / 128) ^ q / 2 ^ 20 ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_35_128_ge_58_pow20_le_three_quarters_128

/-- Signature lock: **100% UNCONDITIONAL** (zero `CurveListCA` assumption!)
literal `≤ N / 2 ^ 128` Johnson `(lb = 2, q ≥ 128, queryPow = 20)` executable
soundness under 64B RFC 7693 `BLAKE2b-512` and incremental sponge chaining. -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 128 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: **100% UNCONDITIONAL** (zero `CurveListCA` assumption!)
literal `≤ N / 2 ^ 128` Johnson `(lb = 2, q ≥ 118, queryPow = 20)` executable
soundness under 64B RFC 7693 `BLAKE2b-512`. -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 30)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 31)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans (by decide))
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (135 / 256)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: **100% UNCONDITIONAL** Native STARK Shrinker Johnson
`(lb = 3, q ≥ 78, queryPow = 20)` executable soundness (`≤ N / 2 ^ 128`, `BLAKE2b-512`). -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 3) (hqn : 78 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 31)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 32)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans (by decide)))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans (by decide))
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (19 / 50)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: **100% UNCONDITIONAL** Native STARK Shrinker Johnson
`(lb = 4, q ≥ 58, queryPow = 20)` executable soundness (`≤ N / 2 ^ 128`, `BLAKE2b-512`). -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 4) (hqn : 58 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (35 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: **100% UNCONDITIONAL** `multi-stark/v6-zk` Johnson
`(lb = 2, q ≥ 128, queryPow = 20)` executable soundness (`≤ N / 2 ^ 128`, `BLAKE2b-512`). -/
example (cfg : ZkConfig) (hcfg : ZkGuardrailsOk cfg)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = cfg.logBlowup) (hbl2 : cfg.logBlowup = 2)
    (hqn : params.numQueries = cfg.numQueries) (hqn128 : 128 ≤ cfg.numQueries)
    (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ cfg.logTraceHeight + 1 + cfg.logBlowup)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hcfg.2.1)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional cfg hcfg params shape
    hbl hbl2 hqn hqn128 hqpow hmax hheight hclaims s₀ hadv hN attempt

/--
info: 'CertiFri.CurveListCAProof.curveListCA_of_fintype_char' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CurveListCAProof.curveListCA_of_fintype_char

/-- info: 'CertiFri.P3.Exec.curveListCA_fp3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms curveListCA_fp3

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_johnson_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_johnson_118_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_johnson_lb3_78_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_blake2b512_johnson_lb4_58_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_soundness_blake2b512_johnson_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb3_78_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb3_78_128_unconditional

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb4_58_128_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_soundness_blake2b512_johnson_lb4_58_128_unconditional

/-! ## Cubic Extension (`Fp3`) `StarkModel`, Tensor-FRI STARK & `prunedMmcs` Soundness Audit -/

/--
info: GoldilocksExt3.starkModel : Stark.StarkModel Goldilocks GoldilocksExt3 Fp3Model
-/
#guard_msgs in
#check @CertiFri.P3.GoldilocksExt3.starkModel

/--
info: 'CertiFri.P3.GoldilocksExt3.starkModel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.starkModel

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verify' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verify

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatch' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatch

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_starkTensor_ud' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_starkTensor_ud

/--
info: 'CertiFri.P3.GoldilocksExt3.sdoomedTensor_nil_fp3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.sdoomedTensor_nil_fp3

/--
info: 'CertiFri.P3.GoldilocksExt3.settles_interpTensor_fp3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.settles_interpTensor_fp3

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensor_johnson' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensor_johnson

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensor

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensor

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensor_lookups' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensor_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensor_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensor_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorPruned' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorPruned

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorPruned_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorPruned_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64

/-! ## Multi-Arity (`2 ^ a`, `logArity ∈ {1, 2, 3}`) Tensor-FRI & `GoldilocksExt3` STARK Audit -/

/-- info: FriParams.compact400KBBalanced : FriParams -/
#guard_msgs in
#check @FriParams.compact400KBBalanced

/-- info: FriParams.ultraCompact400KBZk : FriParams -/
#guard_msgs in
#check @FriParams.ultraCompact400KBZk

/--
info: @johnson_35_128_compact400KB_le : ∀ {q pow : ℕ}, 58 ≤ q → 28 ≤ pow → (35 / 128) ^ q / 2 ^ pow ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_35_128_compact400KB_le

/--
info: @johnson_35_128_ultraCompact400KB_le : ∀ {q pow : ℕ}, 55 ≤ q → 30 ≤ pow → (35 / 128) ^ q / 2 ^ pow ≤ 3 / 4 / 2 ^ 128
-/
#guard_msgs in
#check @johnson_35_128_ultraCompact400KB_le

/-- Signature lock: **100% UNCONDITIONAL** literal `≤ N / 2 ^ 128` 8-ary multi-arity tensor-FRI
Johnson soundness for `FriParams.compact400KBBalanced` (`lb = 4, maxLogArity = 3, logFinalPolyLen = 8,
queries = 58, queryPow = 28`) under 64B RFC 7693 `BLAKE2b-512` and incremental sponge chaining. -/
example (shape : ClaimShape) (arities : List ℕ)
    (hmax : Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.compact400KBBalanced.logFinalHeight =
      Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight
          FriParams.compact400KBBalanced.logBlowup shape)) *
        2 ^ Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel
      FriParams.compact400KBBalanced shape arities
      (goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities (goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax) hpos
        (by omega)).batches +
      ((modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities (goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax) hpos
        (by omega)).rounds + 2)) +
      (modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities (goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax) hpos
        (by omega)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax
    let hsum : arities.sum ≤ Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape := by
      omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape arities
      wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel
            FriParams.compact400KBBalanced shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
              arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_compact400KBBalanced_sponge_blake2b512 shape arities hmax hpos hsum_eq htensor
    s₀ hadv hN attempt

/-- Signature lock: **100% UNCONDITIONAL** literal `≤ N / 2 ^ 128` 8-ary multi-arity tensor-FRI
Johnson soundness for `FriParams.ultraCompact400KBZk` (`lb = 4, maxLogArity = 3, logFinalPolyLen = 8,
queries = 55, queryPow = 30`) under 64B RFC 7693 `BLAKE2b-512` and incremental sponge chaining. -/
example (shape : ClaimShape) (arities : List ℕ)
    (hmax : Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.ultraCompact400KBZk.logFinalHeight =
      Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight
          FriParams.ultraCompact400KBZk.logBlowup shape)) *
        2 ^ Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel
      FriParams.ultraCompact400KBZk shape arities
      (goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities (goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax) hpos
        (by omega)).batches +
      ((modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities (goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax) hpos
        (by omega)).rounds + 2)) +
      (modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities (goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax) hpos
        (by omega)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax
    let hsum : arities.sum ≤ Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape := by
      omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape arities
      wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel
            FriParams.ultraCompact400KBZk shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
              arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512 shape arities hmax hpos hsum_eq htensor
    s₀ hadv hN attempt

/-- info: 'CertiFri.Fri.scheduleValid_scheduleOfShape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertiFri.Fri.scheduleValid_scheduleOfShape

/-- info: 'CertiFri.Fri.scheduleOfShape_binary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms CertiFri.Fri.scheduleOfShape_binary

/-- info: 'CertiFri.foldRowMultiM_eq_foldAtPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertiFri.foldRowMultiM_eq_foldAtPow

/-- info: 'CertiFri.stepMCAArity_ud' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CertiFri.stepMCAArity_ud

/--
info: 'CertiFri.stepMCAArity_of_curveListCA_rel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.stepMCAArity_of_curveListCA_rel

/--
info: 'CertiFri.Exec.soundnessTensorMulti_uniqueDecoding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.Exec.soundnessTensorMulti_uniqueDecoding

/--
info: 'CertiFri.Exec.soundnessTensorMulti_sponge_uniqueDecoding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.Exec.soundnessTensorMulti_sponge_uniqueDecoding

/--
info: 'CertiFri.Exec.soundnessTensorMulti_sponge_johnson_of_curveListCA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.Exec.soundnessTensorMulti_sponge_johnson_of_curveListCA

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake3

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake2b512' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.Exec.goldilocksExt3_compact400KBBalanced_sponge_blake2b512

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake3

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_starkTensorMulti_ud' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_starkTensorMulti_ud

/--
info: 'CertiFri.P3.GoldilocksExt3.sdoomedTensorMulti_nil_fp3' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.sdoomedTensorMulti_nil_fp3

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_johnson' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_johnson

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced

/--
info: 'CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArity

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArity

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArity_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArity_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArity_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArity_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArityPruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArityPruned

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArityPruned_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyTensorMultiArityPruned_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest64

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest64

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32

/--
info: 'CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CertiFri.P3.GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64

/-! ## Protocol `v6-zk` Formal HVZK, Polynomial Blinding, Masked-LogUp & Salted-Merkle Hiding Audit (`#guard_msgs` + `#print axioms`) -/

/--
info: @eval_vec_uniform_of_blinding : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K] (n : ℕ)
  (f : Polynomial K) {b k : ℕ},
  k ≤ b →
    ∀ {xs : Fin k → K},
      Function.Injective xs →
        (∀ (i : Fin k), xs i ^ n ≠ 1) → IsUniformPushforward fun r i => Polynomial.eval (xs i) (blindPoly n f r)
-/
#guard_msgs in
#check @eval_vec_uniform_of_blinding

/--
info: @eval_ood_and_coset_uniform_of_blinding : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K] (n : ℕ)
  (f : Polynomial K) {b m : ℕ},
  m + 2 ≤ b →
    ∀ {g z : K} {xs : Fin m → K},
      Function.Injective xs →
        (∀ (i : Fin m), xs i ^ n ≠ 1) →
          g ^ n = 1 →
            g ≠ 1 →
              z ≠ 0 →
                z ^ n ≠ 1 →
                  (∀ (i : Fin m), xs i ≠ z) →
                    (∀ (i : Fin m), xs i ≠ g * z) →
                      IsUniformPushforward fun r i => Polynomial.eval (oodAndCosetPoints g z xs i) (blindPoly n f r)
-/
#guard_msgs in
#check @eval_ood_and_coset_uniform_of_blinding

/--
info: @quotient_slices_uniform_of_telescoping : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K]
  (n q : ℕ) (hq : 1 ≤ q) (c : Fin (2 * q) → Polynomial K) {b k : ℕ},
  k ≤ b →
    ∀ {xs : Fin k → K},
      Function.Injective xs →
        IsUniformPushforward fun ρ j i => Polynomial.eval (xs i) (blindedQuotientSlice n q b c ρ ⟨↑j + 1, ⋯⟩)
-/
#guard_msgs in
#check @quotient_slices_uniform_of_telescoping

/--
info: @masked_logup_hiding : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K] (n : ℕ)
  (φ₁ φ₂ : Polynomial K) {b k : ℕ},
  k ≤ b →
    ∀ {xs : Fin k → K},
      Function.Injective xs →
        (∀ (i : Fin k), xs i ^ n ≠ 1) →
          (∀ (r_φ : Fin b → K) (x : K), x ^ n = 1 → Polynomial.eval x (blindPoly n φ₁ r_φ) = Polynomial.eval x φ₁) ∧
            (IsUniformPushforward fun r_φ i => Polynomial.eval (xs i) (blindPoly n φ₁ r_φ)) ∧
              (tvDist (fun r_φ i => Polynomial.eval (xs i) (blindPoly n φ₁ r_φ)) fun r_φ i =>
                  Polynomial.eval (xs i) (blindPoly n φ₂ r_φ)) =
                0
-/
#guard_msgs in
#check @masked_logup_hiding

/--
info: @masked_logup_boundary_telescoping : ∀ {K : Type u_1} [inst : Field K] {M : ℕ},
  1 ≤ M →
    ∀ (S_init S_final : K) (S μ : Fin (M - 1) → K),
      (∀ p < M,
          maskedBoundaryAcc S_init S_final S μ (p + 1) - maskedBoundaryAcc S_init S_final S μ p -
              (boundaryMaskVal μ (p + 1) - boundaryMaskVal μ p) =
            trueBoundaryAcc S_init S_final S (p + 1) - trueBoundaryAcc S_init S_final S p) ∧
        ∑ p ∈ Finset.range M,
            (maskedBoundaryAcc S_init S_final S μ (p + 1) - maskedBoundaryAcc S_init S_final S μ p -
              (boundaryMaskVal μ (p + 1) - boundaryMaskVal μ p)) =
          S_final - S_init
-/
#guard_msgs in
#check @masked_logup_boundary_telescoping

/--
info: @masked_logup_boundary_hiding : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K] (n M : ℕ)
  (S : Fin (M - 1) → K) (U₀ : Fin (M - 1) → K → Polynomial K) {b k : ℕ},
  k ≤ b →
    ∀ {xs : Fin k → K},
      Function.Injective xs →
        (∀ (i : Fin k), xs i ^ n ≠ 1) →
          IsUniformPushforward fun rand =>
            (fun p => S p + rand.1 p, fun p i => Polynomial.eval (xs i) (blindPoly n (U₀ p (rand.1 p)) (rand.2 p)))
-/
#guard_msgs in
#check @masked_logup_boundary_hiding

/--
info: @fri_multi_round_randomizer_uniform : ∀ {K : Type u_1} [inst : Field K] [inst_1 : Fintype K] [DecidableEq K]
  (arities : List ℕ) (d_final q : ℕ),
  q ≤ d_final →
    ∀ (betas : Fin arities.length → K) (ys : FriRoundQueryPoints K arities q),
      FriRoundQueryPointsInj arities q ys →
        ∀ (W : Fin (2 ^ arities.sum * d_final) → K),
          IsUniformPushforward fun R =>
            have dec := friMultiDecomp arities d_final betas (W + R);
            (dec.1, evalFriRoundSiblings arities d_final q ys dec.2)
-/
#guard_msgs in
#check @fri_multi_round_randomizer_uniform

/--
info: @salted_leaf_rom_indistinguishable : ∀ {L N_RO : ℕ} {Row Salt Digest : Type} [inst : DecidableEq Row]
  [inst_1 : DecidableEq Salt] [inst_2 : DecidableEq Digest] [inst_3 : Fintype Salt] [Nonempty Salt]
  [inst_5 : Fintype Digest] [Nonempty Digest] (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
  (D : SaltedMerkleView L Row Salt Digest opened → OracleComp (SaltedMerkleAns L Row Salt Digest) Bool),
  (∀ (v : SaltedMerkleView L Row Salt Digest opened), (D v).QueryBound N_RO) →
    |realSaltedMerkleGame depth rows opened D - idealSaltedMerkleGame depth opened (fun i => rows ↑i) D| ≤
      ↑N_RO * ↑(Finset.univ \ opened).card / ↑(Fintype.card Salt)
-/
#guard_msgs in
#check @salted_leaf_rom_indistinguishable

/--
info: @salted_leaf_unindexed_rom_indistinguishable : ∀ {L N_RO : ℕ} {Row Salt Digest : Type} [inst : DecidableEq Row]
  [inst_1 : DecidableEq Salt] [inst_2 : DecidableEq Digest] [inst_3 : Fintype Salt] [Nonempty Salt]
  [inst_5 : Fintype Digest] [Nonempty Digest] (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
  (D : SaltedMerkleView L Row Salt Digest opened → OracleComp (UnindexedSaltedAns Row Salt Digest) Bool),
  (∀ (v : SaltedMerkleView L Row Salt Digest opened), (D v).QueryBound N_RO) →
    |realUnindexedMerkleGame depth rows opened D - idealUnindexedMerkleGame depth opened (fun i => rows ↑i) D| ≤
      (↑N_RO * ↑(Finset.univ \ opened).card + ↑(Finset.univ \ opened).card * ↑(L - 1)) / ↑(Fintype.card Salt)
-/
#guard_msgs in
#check @salted_leaf_unindexed_rom_indistinguishable

/--
info: @salted_leaf_rom_128bit : ∀ {L N_RO : ℕ} {Row Digest : Type} [inst : DecidableEq Row] [inst_1 : DecidableEq Digest]
  [inst_2 : Fintype Digest] [Nonempty Digest] (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
  (D :
    SaltedMerkleView L Row (Fin (2 ^ 128)) Digest opened →
      OracleComp (SaltedMerkleAns L Row (Fin (2 ^ 128)) Digest) Bool),
  (∀ (v : SaltedMerkleView L Row (Fin (2 ^ 128)) Digest opened), (D v).QueryBound N_RO) →
    |realSaltedMerkleGame depth rows opened D - idealSaltedMerkleGame depth opened (fun i => rows ↑i) D| ≤
      ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 128
-/
#guard_msgs in
#check @salted_leaf_rom_128bit

/--
info: @salted_leaf_rom_256bit : ∀ {L N_RO : ℕ} {Row Digest : Type} [inst : DecidableEq Row] [inst_1 : DecidableEq Digest]
  [inst_2 : Fintype Digest] [Nonempty Digest] (depth : ℕ) (rows : Fin L → Row) (opened : Finset (Fin L))
  (D :
    SaltedMerkleView L Row (Fin (2 ^ 256)) Digest opened →
      OracleComp (SaltedMerkleAns L Row (Fin (2 ^ 256)) Digest) Bool),
  (∀ (v : SaltedMerkleView L Row (Fin (2 ^ 256)) Digest opened), (D v).QueryBound N_RO) →
    |realSaltedMerkleGame depth rows opened D - idealSaltedMerkleGame depth opened (fun i => rows ↑i) D| ≤
      ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 256
-/
#guard_msgs in
#check @salted_leaf_rom_256bit

/--
info: @salt128_advantage_le_of_leaves_le_pow32 : ∀ {N_RO L_unopened : ℕ},
  L_unopened ≤ 2 ^ 32 → ↑N_RO * ↑L_unopened / 2 ^ 128 ≤ ↑N_RO / 2 ^ 96
-/
#guard_msgs in
#check @salt128_advantage_le_of_leaves_le_pow32

/--
info: @salt256_advantage_le_of_leaves_le_pow32 : ∀ {N_RO L_unopened : ℕ},
  L_unopened ≤ 2 ^ 32 → N_RO ≤ 2 ^ 128 → ↑N_RO * ↑L_unopened / 2 ^ 256 ≤ 1 / 2 ^ 96
-/
#guard_msgs in
#check @salt256_advantage_le_of_leaves_le_pow32

/--
info: salt128_vs_salt256_grover_ratio_tradeoff : 1 ≤ ↑(2 ^ 64) ^ 2 * 1 / 2 ^ 128 ∧
  ↑(2 ^ 96) ^ 2 * ↑(2 ^ 32) / 2 ^ 256 ≤ 1 / 2 ^ 32
-/
#guard_msgs in
#check @salt128_vs_salt256_grover_ratio_tradeoff

/-- info: card_salt16 : Fintype.card DomainSep.Salt16 = 2 ^ 128 -/
#guard_msgs in
#check @card_salt16

/-- info: card_salt32 : Fintype.card Salt32 = 2 ^ 256 -/
#guard_msgs in
#check @card_salt32

/--
info: @goldilocks_coset_disjoint_from_trace : ∀ {logN : ℕ},
  logN ≤ 32 → ∀ {d : GoldilocksField}, d ^ 2 ^ 32 = 1 → (7 * d) ^ 2 ^ logN ≠ 1
-/
#guard_msgs in
#check @goldilocks_coset_disjoint_from_trace

/--
info: @fp3_coset_disjoint_from_trace : ∀ {logN : ℕ},
  logN ≤ 32 → ∀ {d : GoldilocksField}, d ^ 2 ^ 32 = 1 → (Fp3Model.embed 7 * Fp3Model.embed d) ^ 2 ^ logN ≠ 1
-/
#guard_msgs in
#check @fp3_coset_disjoint_from_trace

/--
info: @v6ZkAlgSimulator_ood_check : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] {P : V6ZkParams}
  (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hq : 1 ≤ P.halfQuotientSlices) (s : V6ZkCoreSample K P ch),
  have v := v6ZkAlgSimulator pub ch hq s;
  ∑ k, ch.z ^ (↑k * P.traceHeight) * v.quotientOodSlices k =
    pub.evalComposition ch.z v.mainOodCur v.mainOodNext v.logupOodCur v.logupOodNext v.maskedInterAccs v.maskPolyOod *
      (ch.z ^ P.traceHeight - 1)⁻¹
-/
#guard_msgs in
#check @v6ZkAlgSimulator_ood_check

/--
info: @v6Zk_alg_perfect_hvzk : ∀ {K : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] {P : V6ZkParams}
  (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness K P pub ch) [inst_3 : Fintype (V6ZkAlgView K P ch)],
      tvDist (v6ZkRealAlgProver pub ch w) (v6ZkAlgSimulator pub ch ⋯) = 0 ∧
        ∀ (E : V6ZkAlgView K P ch → Prop),
          unifProb (v6ZkRealAlgProver pub ch w) E = unifProb (v6ZkAlgSimulator pub ch ⋯) E
-/
#guard_msgs in
#check @v6Zk_alg_perfect_hvzk

/--
info: @v6Zk_hvzk : ∀ {K : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] {P : V6ZkParams}
  {L_total N_RO : ℕ} {Row Salt Digest : Type} [inst_3 : DecidableEq Row] [inst_4 : DecidableEq Salt]
  [inst_5 : DecidableEq Digest] [inst_6 : Fintype Salt] [Nonempty Salt] [inst_8 : Fintype Digest] [Nonempty Digest]
  (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
      (leafRows : V6ZkProverRand K P → Fin L_total → Row) (openedRowsOf : V6ZkAlgView K P ch → ↥opened → Row),
      (∀ (rand : V6ZkProverRand K P) (i : ↥opened),
          leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
        ∀
          (D :
            V6ZkView K P ch L_total Row Salt Digest opened → OracleComp (SaltedMerkleAns L_total Row Salt Digest) Bool),
          (∀ (v : V6ZkView K P ch L_total Row Salt Digest opened), (D v).QueryBound N_RO) →
            |v6ZkRealGame pub ch w depth opened leafRows D - v6ZkSimulator pub ch ⋯ depth opened openedRowsOf D| ≤
              ↑N_RO * ↑(Finset.univ \ opened).card / ↑(Fintype.card Salt)
-/
#guard_msgs in
#check @v6Zk_hvzk

/--
info: @v6Zk_hvzk_unindexed : ∀ {K : Type} [inst : Field K] [inst_1 : Fintype K] [inst_2 : DecidableEq K] {P : V6ZkParams}
  {L_total N_RO : ℕ} {Row Salt Digest : Type} [inst_3 : DecidableEq Row] [inst_4 : DecidableEq Salt]
  [inst_5 : DecidableEq Digest] [inst_6 : Fintype Salt] [Nonempty Salt] [inst_8 : Fintype Digest] [Nonempty Digest]
  (pub : V6ZkPublic K P) (ch : V6ZkChallenges K P) (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness K P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
      (leafRows : V6ZkProverRand K P → Fin L_total → Row) (openedRowsOf : V6ZkAlgView K P ch → ↥opened → Row),
      (∀ (rand : V6ZkProverRand K P) (i : ↥opened),
          leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
        ∀ (D : V6ZkView K P ch L_total Row Salt Digest opened → OracleComp (UnindexedSaltedAns Row Salt Digest) Bool),
          (∀ (v : V6ZkView K P ch L_total Row Salt Digest opened), (D v).QueryBound N_RO) →
            |v6ZkRealGameUnindexed pub ch w depth opened leafRows D -
                  v6ZkSimulatorUnindexed pub ch ⋯ depth opened openedRowsOf D| ≤
              (↑N_RO * ↑(Finset.univ \ opened).card + ↑(Finset.univ \ opened).card * ↑(L_total - 1)) /
                ↑(Fintype.card Salt)
-/
#guard_msgs in
#check @v6Zk_hvzk_unindexed

/--
info: @goldilocksExt3_v6Zk_hvzk : ∀ {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type} [inst : DecidableEq Row]
  [inst_1 : DecidableEq Digest] [inst_2 : Fintype Digest] [Nonempty Digest] (pub : V6ZkPublic Fp3Model P)
  (ch : V6ZkChallenges Fp3Model P) (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
      (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
      (openedRowsOf : V6ZkAlgView Fp3Model P ch → ↥opened → Row),
      (∀ (rand : V6ZkProverRand Fp3Model P) (i : ↥opened),
          leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
        ∀
          (D :
            V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened →
              OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool),
          (∀ (v : V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened), (D v).QueryBound N_RO) →
            |v6ZkRealGame pub ch w depth opened leafRows D - v6ZkSimulator pub ch ⋯ depth opened openedRowsOf D| ≤
              ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 128
-/
#guard_msgs in
#check @goldilocksExt3_v6Zk_hvzk

/--
info: @goldilocksExt3_v6Zk_hvzk_salt32 : ∀ {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type} [inst : DecidableEq Row]
  [inst_1 : DecidableEq Digest] [inst_2 : Fintype Digest] [Nonempty Digest] (pub : V6ZkPublic Fp3Model P)
  (ch : V6ZkChallenges Fp3Model P) (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
      (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
      (openedRowsOf : V6ZkAlgView Fp3Model P ch → ↥opened → Row),
      (∀ (rand : V6ZkProverRand Fp3Model P) (i : ↥opened),
          leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
        ∀
          (D :
            V6ZkView Fp3Model P ch L_total Row Salt32 Digest opened →
              OracleComp (SaltedMerkleAns L_total Row Salt32 Digest) Bool),
          (∀ (v : V6ZkView Fp3Model P ch L_total Row Salt32 Digest opened), (D v).QueryBound N_RO) →
            |v6ZkRealGame pub ch w depth opened leafRows D - v6ZkSimulator pub ch ⋯ depth opened openedRowsOf D| ≤
              ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 256
-/
#guard_msgs in
#check @goldilocksExt3_v6Zk_hvzk_salt32

/--
info: goldilocksExt3_ultraCompact400KBZk_hvzk : ∀ (logTraceHeight : ℕ),
  10 ≤ logTraceHeight →
    ∀ (arities : List ℕ) (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
      (hq1 : 1 ≤ halfQuotientSlices) {L_total N_RO : ℕ} {Row : Type} [inst : DecidableEq Row]
      (pub :
        V6ZkPublic Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth))
      (ch :
        V6ZkChallenges Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth)),
      ch.numOpenings ≤
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).numQueries *
            (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).maxArity →
        ch.Ok →
          ∀
            (w :
              V6ZkWitness Fp3Model
                (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                  halfQuotientSlices randomizerWidth)
                pub ch)
            (depth : ℕ) (opened : Finset (Fin L_total))
            (leafRows :
              V6ZkProverRand Fp3Model
                  (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                    halfQuotientSlices randomizerWidth) →
                Fin L_total → Row)
            (openedRowsOf :
              V6ZkAlgView Fp3Model
                  (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                    halfQuotientSlices randomizerWidth)
                  ch →
                ↥opened → Row),
            (∀
                (rand :
                  V6ZkProverRand Fp3Model
                    (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                      halfQuotientSlices randomizerWidth))
                (i : ↥opened), leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
              ∀
                (D :
                  V6ZkView Fp3Model
                      (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                        halfQuotientSlices randomizerWidth)
                      ch L_total Row DomainSep.Salt16 Digest64 opened →
                    OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest64) Bool),
                (∀
                    (v :
                      V6ZkView Fp3Model
                        (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                          halfQuotientSlices randomizerWidth)
                        ch L_total Row DomainSep.Salt16 Digest64 opened),
                    (D v).QueryBound N_RO) →
                  |v6ZkRealGame pub ch w depth opened leafRows D -
                        v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
                    ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 128
-/
#guard_msgs in
#check @goldilocksExt3_ultraCompact400KBZk_hvzk

/--
info: goldilocksExt3_ultraCompact400KBZk_hvzk_salt32 : ∀ (logTraceHeight : ℕ),
  10 ≤ logTraceHeight →
    ∀ (arities : List ℕ) (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
      (hq1 : 1 ≤ halfQuotientSlices) {L_total N_RO : ℕ} {Row : Type} [inst : DecidableEq Row]
      (pub :
        V6ZkPublic Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth))
      (ch :
        V6ZkChallenges Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth)),
      ch.numOpenings ≤
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).numQueries *
            (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).maxArity →
        ch.Ok →
          ∀
            (w :
              V6ZkWitness Fp3Model
                (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                  halfQuotientSlices randomizerWidth)
                pub ch)
            (depth : ℕ) (opened : Finset (Fin L_total))
            (leafRows :
              V6ZkProverRand Fp3Model
                  (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                    halfQuotientSlices randomizerWidth) →
                Fin L_total → Row)
            (openedRowsOf :
              V6ZkAlgView Fp3Model
                  (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                    halfQuotientSlices randomizerWidth)
                  ch →
                ↥opened → Row),
            (∀
                (rand :
                  V6ZkProverRand Fp3Model
                    (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                      halfQuotientSlices randomizerWidth))
                (i : ↥opened), leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
              ∀
                (D :
                  V6ZkView Fp3Model
                      (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                        halfQuotientSlices randomizerWidth)
                      ch L_total Row Salt32 Digest64 opened →
                    OracleComp (SaltedMerkleAns L_total Row Salt32 Digest64) Bool),
                (∀
                    (v :
                      V6ZkView Fp3Model
                        (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                          halfQuotientSlices randomizerWidth)
                        ch L_total Row Salt32 Digest64 opened),
                    (D v).QueryBound N_RO) →
                  |v6ZkRealGame pub ch w depth opened leafRows D -
                        v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
                    ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 256
-/
#guard_msgs in
#check @goldilocksExt3_ultraCompact400KBZk_hvzk_salt32

/--
info: goldilocksExt3_ultraCompact400KBZk_hvzk_logN9 : ∀ (logTraceHeight : ℕ),
  9 ≤ logTraceHeight →
    ∀ (arities : List ℕ) (numMainCols numLogupCols numCircuits halfQuotientSlices randomizerWidth : ℕ)
      (hq1 : 1 ≤ halfQuotientSlices) {L_total N_RO : ℕ} {Row : Type} [inst : DecidableEq Row]
      (pub :
        V6ZkPublic Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth))
      (ch :
        V6ZkChallenges Fp3Model
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
            randomizerWidth)),
      ch.numOpenings ≤
          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).numQueries *
            (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits halfQuotientSlices
                randomizerWidth).maxArity →
        (∀ (i : Fin ch.numOpenings), ∃ j, ch.g * ch.queryPoints i = ch.queryPoints j) →
          ch.Ok →
            ∀
              (w :
                V6ZkWitness Fp3Model
                  (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                    halfQuotientSlices randomizerWidth)
                  pub ch)
              (depth : ℕ) (opened : Finset (Fin L_total))
              (leafRows :
                V6ZkProverRand Fp3Model
                    (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                      halfQuotientSlices randomizerWidth) →
                  Fin L_total → Row)
              (openedRowsOf :
                V6ZkAlgView Fp3Model
                    (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                      halfQuotientSlices randomizerWidth)
                    ch →
                  ↥opened → Row),
              (∀
                  (rand :
                    V6ZkProverRand Fp3Model
                      (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                        halfQuotientSlices randomizerWidth))
                  (i : ↥opened), leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
                ∀
                  (D :
                    V6ZkView Fp3Model
                        (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                          halfQuotientSlices randomizerWidth)
                        ch L_total Row DomainSep.Salt16 Digest opened →
                      OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool),
                  (∀
                      (v :
                        V6ZkView Fp3Model
                          (ultraCompact400KBZkV6Params logTraceHeight arities numMainCols numLogupCols numCircuits
                            halfQuotientSlices randomizerWidth)
                          ch L_total Row DomainSep.Salt16 Digest opened),
                      (D v).QueryBound N_RO) →
                    |v6ZkRealGame pub ch w depth opened leafRows D -
                          v6ZkSimulator pub ch hq1 depth opened openedRowsOf D| ≤
                      ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 128
-/
#guard_msgs in
#check @goldilocksExt3_ultraCompact400KBZk_hvzk_logN9

/--
info: @goldilocksExt3_v6Zk_hvzk_with_tensor4_span : ∀ {P : V6ZkParams} {L_total N_RO : ℕ} {Row Digest : Type}
  [inst : DecidableEq Row] [inst_1 : DecidableEq Digest] [inst_2 : Fintype Digest] [Nonempty Digest]
  (pub : V6ZkPublic Fp3Model P) (ch : V6ZkChallenges Fp3Model P)
  (hB : P.BlindingOk ch.traceEvalSet.card ch.quotEvalSet.card),
  ch.Ok →
    ∀ (w : V6ZkWitness Fp3Model P pub ch) (depth : ℕ) (opened : Finset (Fin L_total))
      (leafRows : V6ZkProverRand Fp3Model P → Fin L_total → Row)
      (openedRowsOf : V6ZkAlgView Fp3Model P ch → ↥opened → Row),
      (∀ (rand : V6ZkProverRand Fp3Model P) (i : ↥opened),
          leafRows rand ↑i = openedRowsOf (v6ZkRealAlgProver pub ch w rand) i) →
        ∀
          (D :
            V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened →
              OracleComp (SaltedMerkleAns L_total Row DomainSep.Salt16 Digest) Bool),
          (∀ (v : V6ZkView Fp3Model P ch L_total Row DomainSep.Salt16 Digest opened), (D v).QueryBound N_RO) →
            |v6ZkRealGame pub ch w depth opened leafRows D - v6ZkSimulator pub ch ⋯ depth opened openedRowsOf D| +
                ↑(Nat.card { p // ¬FpSpan3 ![1, p.1, p.2, p.1 * p.2] }) / ↑(Nat.card (Fp3Model × Fp3Model)) ≤
              ↑N_RO * ↑(Finset.univ \ opened).card / 2 ^ 128 + 1 / 2 ^ 126
-/
#guard_msgs in
#check @goldilocksExt3_v6Zk_hvzk_with_tensor4_span

/-- info: 'CertiFri.Zk.eval_vec_uniform_of_blinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_vec_uniform_of_blinding

/--
info: 'CertiFri.Zk.eval_ood_and_coset_uniform_of_blinding' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eval_ood_and_coset_uniform_of_blinding

/--
info: 'CertiFri.Zk.quotient_slices_uniform_of_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms quotient_slices_uniform_of_telescoping

/-- info: 'CertiFri.Zk.masked_logup_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masked_logup_hiding

/-- info: 'CertiFri.Zk.masked_logup_boundary_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masked_logup_boundary_telescoping

/-- info: 'CertiFri.Zk.masked_logup_boundary_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms masked_logup_boundary_hiding

/-- info: 'CertiFri.Zk.fri_multi_round_randomizer_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fri_multi_round_randomizer_uniform

/-- info: 'CertiFri.Zk.salted_leaf_rom_indistinguishable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms salted_leaf_rom_indistinguishable

/--
info: 'CertiFri.Zk.salted_leaf_unindexed_rom_indistinguishable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms salted_leaf_unindexed_rom_indistinguishable

/-- info: 'CertiFri.Zk.salted_leaf_rom_128bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms salted_leaf_rom_128bit

/-- info: 'CertiFri.Zk.salted_leaf_rom_256bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms salted_leaf_rom_256bit

/--
info: 'CertiFri.Zk.salt128_advantage_le_of_leaves_le_pow32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms salt128_advantage_le_of_leaves_le_pow32

/--
info: 'CertiFri.Zk.salt256_advantage_le_of_leaves_le_pow32' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms salt256_advantage_le_of_leaves_le_pow32

/--
info: 'CertiFri.Zk.salt128_vs_salt256_grover_ratio_tradeoff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms salt128_vs_salt256_grover_ratio_tradeoff

/-- info: 'CertiFri.P3.Exec.card_salt16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_salt16

/-- info: 'CertiFri.P3.Exec.card_salt32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_salt32

/--
info: 'CertiFri.P3.Exec.goldilocks_coset_disjoint_from_trace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocks_coset_disjoint_from_trace

/-- info: 'CertiFri.P3.Exec.fp3_coset_disjoint_from_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fp3_coset_disjoint_from_trace

/-- info: 'CertiFri.P3.Exec.v6ZkAlgSimulator_ood_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms v6ZkAlgSimulator_ood_check

/-- info: 'CertiFri.P3.Exec.v6Zk_alg_perfect_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms v6Zk_alg_perfect_hvzk

/-- info: 'CertiFri.P3.Exec.v6Zk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms v6Zk_hvzk

/-- info: 'CertiFri.P3.Exec.v6Zk_hvzk_unindexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms v6Zk_hvzk_unindexed

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_hvzk

/-- info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_salt32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_hvzk_salt32

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_ultraCompact400KBZk_hvzk

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk_salt32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_ultraCompact400KBZk_hvzk_salt32

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_ultraCompact400KBZk_hvzk_logN9' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_ultraCompact400KBZk_hvzk_logN9

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_v6Zk_hvzk_with_tensor4_span' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_v6Zk_hvzk_with_tensor4_span

end CertiFri.Audit128
