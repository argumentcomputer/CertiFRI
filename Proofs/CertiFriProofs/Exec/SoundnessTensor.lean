import CertiFriProofs.Exec.TensorExec
import CertiFriProofs.Exec.SoundnessSponge

/-!
# Executable `FriBatching::Tensor` Refinement & 128-Bit `GoldilocksExt3` Soundness

Re-exports the executable `Fri.verifyTensor` refinement and chained-ROM soundness
theorems from `Proofs/CertiFriProofs/Exec/TensorExec.lean` (`toModel_tensorWeights*`,
`toModel_reducedOpeningTensor*`, `Exec.run_model_of_acceptsTensor`,
`Exec.soundnessTensor`, `Exec.soundnessTensor_uniqueDecoding`) and provides
concrete `GoldilocksExt3` (`Fp3Model`) 128-bit `Tensor2DMCA` bounds.

Incremental-sponge (`c = 3 / 2`) executable `Fri.verifyTensor` soundness for
both 32-byte `BLAKE3-256` (`Digest`) and 64-byte `BLAKE2b-512` (`Digest64`) is
proved in `Proofs/CertiFriProofs/Exec/SoundnessTensorSponge.lean` — both
unconditionally in the unique-decoding regime (for all `W ≤ 2 ^ 16`, `M ≤ 2 ^ 16`,
`logMaxHeight ≤ 32`) and unconditionally in the Johnson regime (`lb = 2, 3, 4`)
via the union-bound reduction `tensor2DMCA_of_curveMCA_two` from `curveListCA_fp3`.

## Technical note: `CurveListCA` constant vs. `M`-independent `BatchedLineListCA`

Two distinct bounds govern Johnson-regime tensor batching over `GoldilocksExt3`
(`|Fp3Model| = p ^ 3 ≈ 2 ^ 192`):

1. **Unconditional discharge via `CurveListCA` (`m = 2`) union bound (proved in
   `TensorMCA.lean` / `SoundnessTensorSponge.lean`):**
   Applying `curveListCA_fp3` at `m = 2` to each of the `2 ^ i` parallel lines
   in halving round `i` gives `Tensor2DMCA` with error `(2 ^ (kCol + kOpen) - 1) * ε_line`
   (zero unproven assumptions). In `CurveListCA.lean`, the leading term in
   `curveListCoeff n d A` is `L_Y * B3 ≈ 2 * (r + 1) * L_Y ^ 5 * d`, coming from
   the cleared-denominator Hensel residual `henselResidualCoeff` (`D₀ ^ (2 * d * ℓ)`
   with `deg_Z(D₀) = ((ℓ + 1) * t + 3 * ℓ + 1) * D_Z` in `HenselLift.lean`),
   whereas the Hasse-multiplicity double-counting term `L_Y * B4 ≈ L_Y * (r + 2) * L_Y * n`
   is 8.8–10.7 bits smaller:

   * `lb = 2, θ = 71 / 128` (`r = 9, L_Y = 28`): `curveListCoeff / n ≤ 2 ^ 26.58`
     (`PowExp = 27`, `B4`-only `2 ^ 17.83`, gap `8.75` bits). Unconditionally
     discharges `2 ^ (kCol + kOpen) * 2 ^ H ≤ 2 ^ 36` (e.g. `d ≤ 2 ^ 23`,
     `H = 25`, up to `2048` tensor claims).
   * `lb = 2, θ = 135 / 256` (`r = 18, L_Y = 50`): `2 ^ 31.59` vs `B4`-only `2 ^ 21.22` (`10.37` bits).
   * `lb = 3, θ = 19 / 50` (`r = 13, L_Y = 51`): `2 ^ 30.29` vs `B4`-only `2 ^ 19.90` (`10.39` bits).
   * `lb = 4, θ = 35 / 128` (`r = 11, L_Y = 58`): `2 ^ 29.98` vs `B4`-only `2 ^ 19.27` (`10.71` bits).

   Closing this ~9–11 bit gap in `CurveListCA` requires avoiding the linear-in-`d`
   denominator growth `D₀ ^ (2 * d)` in `HenselLift.lean` (reducing `D₀` alone to
   `2 * L_Y * D_Z` saves only ~3.7–4.6 bits).

2. **`M`-independent `BatchedLineListCA Fp3Model T` (`(kCol + kOpen) * ε_line`):**
   Eliminating the exponential `2 ^ (kCol + kOpen)` union-bound factor to achieve
   `(kCol + kOpen)` logarithmic scaling for arbitrary `W, M ≤ 2 ^ 16` across all
   rates (`lb = 2, 3, 4` at `d ≤ 2 ^ 23`) requires an interleaved-word Johnson
   peeling proof (discharging `BatchedLineListCA` simultaneously across `M`
   parallel lines sharing one challenge `β` over a common extension field
   `E = F(Z)[T] / (H)` of degree `≤ L_Y`, rather than taking a union bound over
   `M` independent single-line calls).
-/

/-! ## Concrete `GoldilocksExt3` 128-bit Tensor batching soundness -/

namespace CertiFri.P3.Exec

open CertiFri CertiFri.P3 CertiFri.Exec

/-- **Unconditional `Tensor2DMCA` over `GoldilocksExt3` (`Fp3Model`) in the
unique-decoding regime (`2 * δ + ρ ≤ 1`).** -/
theorem goldilocksExt3_tensor2DMCA_ud (D : Finset Fp3Model) (d W M : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * (δ * D.card) + d ≤ D.card) :
    Tensor2DMCA D d W M (1 - δ)
      (((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        (((1 + δ) * D.card) / ((Goldilocks.order : ℝ) ^ 3))) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  simpa only [hcard] using tensor2DMCA_ud (F := Fp3Model) D d W M hδ hrate

/-- Helper bound: if `n ≤ 2 ^ k`, then `tensorNumChallenges n ≤ k`. -/
theorem tensorNumChallenges_le_of_le_pow {n k : ℕ} (h : n ≤ 2 ^ k) :
    Fri.tensorNumChallenges n ≤ k := by
  unfold Fri.tensorNumChallenges
  split_ifs with hle
  · exact Nat.zero_le _
  · have hlt : n - 1 < 2 ^ k := by omega
    have hlog : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).mpr hlt
    omega

/-- **Concrete 128-bit unconditional `GoldilocksExt3` Tensor batching theorem:**
for ANY width `W ≤ 2 ^ 16` (`≤ 65,536` columns), ANY opening count `M ≤ 2 ^ 16`
(up to **4.29 billion** claims!), ANY evaluation domain `|D| ≤ 2 ^ 32`, and
unique-decoding blowup `4` (`δ = 3 / 8`, `d / |D| ≤ 1 / 4`), the 2D Tensor
batching error is strictly `≤ (3 / 4) / 2 ^ 128` (leaving `> 25` bits of margin
above 128 bits, with ZERO unproven assumptions!). -/
theorem goldilocksExt3_tensor2DMCA_ud_128 (D : Finset Fp3Model) (d W M : ℕ)
    (hD : D.card ≤ 2 ^ 32) (hW : W ≤ 2 ^ 16) (hM : M ≤ 2 ^ 16)
    (hrate : 2 * ((3 / 8 : ℝ) * D.card) + d ≤ D.card) :
    Tensor2DMCA D d W M (5 / 8) ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  have hbase := goldilocksExt3_tensor2DMCA_ud D d W M (δ := 3 / 8) (by norm_num) hrate
  rw [show (1 - 3 / 8 : ℝ) = 5 / 8 by norm_num] at hbase
  have hkCol : Fri.tensorNumChallenges W ≤ 16 := tensorNumChallenges_le_of_le_pow hW
  have hkOpen : Fri.tensorNumChallenges M ≤ 16 := tensorNumChallenges_le_of_le_pow hM
  have hkSum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) ≤ 32 := by
    exact_mod_cast (by omega : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ 32)
  have hD_real : (D.card : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hD
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have herr : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
      (((1 + (3 / 8 : ℝ)) * D.card) / ((Goldilocks.order : ℝ) ^ 3)) ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hnum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        ((1 + (3 / 8 : ℝ)) * D.card) ≤ 32 * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) := by
      have h1 : (1 + (3 / 8 : ℝ)) * D.card ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ 32 := by nlinarith
      exact mul_le_mul hkSum h1 (by positivity) (by norm_num)
    have hdiv : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        (((1 + (3 / 8 : ℝ)) * D.card) / ((Goldilocks.order : ℝ) ^ 3)) ≤
        (32 * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32)) / (2 : ℝ) ^ 191 := by
      rw [← mul_div_assoc]
      exact div_le_div₀ (by positivity) hnum (by positivity) h191
    refine hdiv.trans ?_
    have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
    rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
    have hconst : (32 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by
      norm_num
    rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
    exact mul_le_mul_of_nonneg_right hconst hpos128.le
  intro u
  obtain ⟨bad, hbad_card, hbad⟩ := hbase u
  refine ⟨bad, hbad_card.trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)), hbad⟩

/-- **Johnson-regime `Tensor2DMCA` over `GoldilocksExt3` (`Fp3Model`)** under
`BatchedLineListCA Fp3Model T`, at agreement `θ = 65 / 128` (`logBlowup = 2`). -/
theorem goldilocksExt3_tensor2DMCA_johnson_128 {T : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hca : BatchedLineListCA Fp3Model T)
    (D : Finset Fp3Model) (hDne : D.Nonempty) (d W M : ℕ)
    (hD : D.card ≤ 2 ^ 32) (hW : W ≤ 2 ^ 16) (hM : M ≤ 2 ^ 16)
    (hrate : (d : ℝ) / D.card ≤ 1 / 4)
    {cT : ℝ} (hcT : cT ≤ (2 : ℝ) ^ 56)
    (hT : ∀ i < Fri.tensorNumChallenges W + Fri.tensorNumChallenges M,
      (T D.card d ⌈(65 / 128 : ℝ) * D.card⌉₊ (2 ^ i) : ℝ) ≤ cT) :
    Tensor2DMCA D d W M (65 / 128) ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  have hgap : (d : ℝ) / D.card < (65 / 128 : ℝ) ^ 2 := lt_of_le_of_lt hrate (by norm_num)
  have hbase := tensor2DMCA_johnson hca D hDne d W M (θ := 65 / 128) (cT := cT)
    (by norm_num) (by norm_num) hgap hT
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  rw [hcard] at hbase
  have hkCol : Fri.tensorNumChallenges W ≤ 16 := tensorNumChallenges_le_of_le_pow hW
  have hkOpen : Fri.tensorNumChallenges M ≤ 16 := tensorNumChallenges_le_of_le_pow hM
  have hkSum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) ≤ 32 := by
    exact_mod_cast (by omega : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ 32)
  have hD_real : (D.card : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hD
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have hLJ : ((65 / 128 : ℝ) - (d : ℝ) / D.card) /
      ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card) * (1 - 65 / 128) ≤ 17 := by
    have hden_pos : (0 : ℝ) < (65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card := by linarith
    have hmono : ((65 / 128 : ℝ) - (d : ℝ) / D.card) /
        ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card) ≤
        ((65 / 128 : ℝ) - 1 / 4) / ((65 / 128 : ℝ) ^ 2 - 1 / 4) := by
      rw [div_le_div_iff₀ hden_pos (by norm_num)]
      linarith
    have hbound : ((65 / 128 : ℝ) - 1 / 4) / ((65 / 128 : ℝ) ^ 2 - 1 / 4) * (1 - 65 / 128) ≤ 17 := by
      norm_num
    linarith
  have herr : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
      ((cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
        ((1 - 65 / 128) * D.card)) / ((Goldilocks.order : ℝ) ^ 3)) ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    by_cases h0 : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0
    · rw [h0, Nat.cast_zero, zero_mul]
      exact div_nonneg (by norm_num) (pow_pos (by norm_num) 128).le
    · have hpos0 : 0 < Fri.tensorNumChallenges W + Fri.tensorNumChallenges M := Nat.pos_of_ne_zero h0
      have hcT_nn : 0 ≤ cT := (Nat.cast_nonneg _).trans (hT 0 hpos0)
      have hterm : ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
          ((1 - 65 / 128) * D.card) ≤ 17 * (2 : ℝ) ^ 32 := by
        rw [← mul_assoc]
        exact mul_le_mul hLJ hD_real (Nat.cast_nonneg _) (by norm_num)
      have hden_pos : (0 : ℝ) < (65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card := by linarith
      have hnum_nn : 0 ≤ (65 / 128 : ℝ) - (d : ℝ) / D.card := by linarith
      have hterm_nn : 0 ≤ ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
          ((1 - 65 / 128) * D.card) :=
        mul_nonneg (div_nonneg hnum_nn hden_pos.le) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      have hinner_nn : 0 ≤ cT + ((65 / 128 - (d : ℝ) / D.card) /
          ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) * ((1 - 65 / 128) * D.card) := by linarith
      have hnum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
          (cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
            ((1 - 65 / 128) * D.card)) ≤ 32 * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32) := by
        exact mul_le_mul hkSum (by linarith) hinner_nn (by norm_num)
      have hdiv : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
          ((cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
            ((1 - 65 / 128) * D.card)) / ((Goldilocks.order : ℝ) ^ 3)) ≤
          (32 * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32)) / (2 : ℝ) ^ 191 := by
        rw [← mul_div_assoc]
        exact div_le_div₀ (by positivity) hnum (by positivity) h191
      refine hdiv.trans ?_
      have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
      rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
      have hconst : (32 : ℝ) * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32) ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by
        norm_num
      rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
      exact mul_le_mul_of_nonneg_right hconst hpos128.le
  intro u
  obtain ⟨bad, hbad_card, hbad⟩ := hbase u
  refine ⟨bad, hbad_card.trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)), hbad⟩

end CertiFri.P3.Exec
