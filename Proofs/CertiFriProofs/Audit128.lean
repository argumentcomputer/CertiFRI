import CertiFriP3.DomainSep
import CertiFriProofs.P3.DigestCard
import CertiFriProofs.Exec.SoundnessSponge
import CertiFriProofs.Exec.SoundnessTensor

/-!
# 128-Bit Formal Security Audit (`Audit128`)

Mechanically pins (via `#guard_msgs` on `#check` and `#print axioms`) the
128-bit FRI soundness stack in `CertiFRI`:

1. Native BLAKE3 `derive_key` alignment with `multi-stark` `v6` and 48-byte
   BLAKE3 XOF (`Digest48`).
2. Tight incremental sponge BCS collision bound (`entryCap = 1`, `c = 3 / 2`,
   raising 32B BCS from `126.52b` to `127.71b` and giving `191.71b ≥ 190.5b`
   classical + exact `128.0b` BHT quantum collision resistance for 48B XOF).
3. Executable `Fri.verify` literal `≤ N / 2 ^ 128` soundness over
   `GoldilocksExt3` (`Fp3Model`, `p^3 ≈ 2^192`) for:
   * Unconditional unique decoding `(logBlowup = 2, numQueries = 160, queryPowBits = 20)`;
   * Johnson regime `(logBlowup = 2, numQueries ≥ 118, queryPowBits = 20)`
     (covering `q = 118..128`), conditional only on `CurveListCA Fp3Model T`.
4. `FriBatching::Tensor` (`col_weights ⊗ open_weights`) executable refinement
   and unconditional `Tensor2DMCA` soundness (`≤ (3 / 4) / 2 ^ 128` for up to
   `2 ^ 16 × 2 ^ 16 = 2 ^ 32` claims over `GoldilocksExt3`).
5. Constructive negative controls proving that `Fp2`, `(2, 100, 0, 20)`, and
   32-byte digests at `N = 2 ^ 128` / BHT `Q = 2 ^ 86` strictly violate the
   128-bit target.

Every theorem audited here depends strictly on standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`) — zero `sorry`, zero custom
axioms, zero `native_decide`, zero `bv_decide`.
-/

namespace CertiFri.Audit128

open CertiFri CertiFri.Fri CertiFri.P3 CertiFri.P3.Exec CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.Exec

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
soundness at `N = 2 ^ 128` (`3 * (2^128)^2 / (2 * 2^256) = 3/2 > 1`), proving
that 48-byte BLAKE3 XOF (`Digest48`) is necessary for literal `≤ N / 2^128` at
`N = 2^128`. -/
theorem negControl_digest32_fails_classical_at_128 :
    (1 : ℝ) < 3 * ((2 ^ 128 : ℕ) : ℝ) ^ 2 / (2 * (Fintype.card Digest : ℝ)) :=
  digest_sponge_collision_exceeds_one_at_128

/-- Negative control 4: 32-byte digests strictly FAIL BHT quantum collision
resistance at `Q = 2 ^ 86` (`(2^86)^3 / 2^256 = 4 > 1`), whereas 48-byte XOF
achieves exact `128.0b` BHT quantum collision resistance. -/
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
info: @digest48_sponge_collision_at_191 : ∀ {N : ℕ}, N ≤ 2 ^ 191 → 3 * ↑N ^ 2 / (2 * ↑(Fintype.card Digest48)) ≤ 3 / 8
-/
#guard_msgs in
#check @digest48_sponge_collision_at_191

/--
info: digest48_bht_quantum_collision : ∀ (Q : ℕ), ↑Q ^ 3 / ↑(Fintype.card Digest48) = (↑Q / 2 ^ 128) ^ 3
-/
#guard_msgs in
#check @digest48_bht_quantum_collision

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
soundness under 48B BLAKE3 XOF and incremental sponge chaining (`c = 3 / 2`). -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : params.numQueries = 160) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hclaims : (Fri.claimRefs params.logBlowup shape).length *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 60)
    (s₀ : Digest48) {A : Type*}
    {adv : OracleComp (SpongeOracleAnswer (D := Digest48) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest48) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest48) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_xof48_uniqueDecoding_128 params shape hbl hqn hqpow
    hmax hheight hclaims s₀ hadv hN attempt

/-- Signature lock: literal `≤ N / 2 ^ 128` Johnson `(2, 118..128, 0, 20)`
executable soundness under 48B BLAKE3 XOF and incremental sponge chaining. -/
example (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest48) {T : ℕ → ℕ → ℕ → ℕ → ℕ} (hca : CurveListCA Fp3Model T)
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
    {adv : OracleComp (SpongeOracleAnswer (D := Digest48) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape hmax)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest48) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeOracleAnswer (D := Digest48) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAccepts goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        PcsRbr.ClaimsFail P.ldt P.shift (65 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperiment goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 :=
  goldilocksExt3_soundness_sponge_xof48_johnson_128 params shape hbl hqn hqpow
    hmax hheight s₀ hca hcT0 hT hα_budget hβ_budget hadv hN attempt

/-! ## Strict Axiom Audits (`#guard_msgs` + `#print axioms`) -/

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

/-- info: 'CertiFri.P3.card_digest48' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_digest48

/-- info: 'CertiFri.P3.digest48_sponge_collision_at_191' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest48_sponge_collision_at_191

/-- info: 'CertiFri.P3.digest48_bht_quantum_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms digest48_bht_quantum_collision

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_uniqueDecoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_uniqueDecoding

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_uniqueDecoding_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_xof48_uniqueDecoding_128

/--
info: 'CertiFri.P3.Exec.goldilocksExt3_soundness_sponge_xof48_johnson_128' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms goldilocksExt3_soundness_sponge_xof48_johnson_128

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

end CertiFri.Audit128
