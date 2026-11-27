import CertiFriProofs.P3.GoldilocksExt3Soundness
import CertiFriProofs.Exec.MultiArity.StarkSoundness
import CertiFriProofs.Exec.MultiArity.SpongeSoundness

/-!
# Multi-Arity Tensor-Batched STARK Soundness over Goldilocks Cubic Extension `Fp3`

Instantiates the complete multi-arity (`2 ^ a`, `a ≥ 1`, covering `logArity ∈ {1, 2, 3}`,
fold factors `2, 4, 8`, and variable per-round schedules `Fri.scheduleOfShape`) tensor-batched
STARK soundness stack (`Exec/MultiArity/{StarkState,StarkSoundness,SpongeSoundness}.lean`) at
`GoldilocksExt3.starkModel` (`Fp3Model ≃+* GF(p)[Y] / (Y^3 - Y - 1)`,
`|Fp3Model| = Goldilocks.order ^ 3 ≈ 2 ^ 192`) with ZERO field-model or unproven proximity
assumptions.

## Contents

1. **Adaptive-ROM `RbrSound` Interface (`DynamicRom` Bridge):**
   * `GoldilocksExt3.rbrSound_starkTensorMulti_ud`: unconditional unique-decoding
     `RbrSound r (sdoomedTensorMulti starkModel sys hcap V (1 - δ) B)` over shape-independent
     `UTensorChal Fp3Model fslots slots width` with tight tensor PCS error `pcsErrTensor sys 3 δ`.
   * `GoldilocksExt3.sdoomedTensorMulti_nil_fp3`: empty-transcript doom base case.
   * `GoldilocksExt3.rbrSound_pcsTensorMulti_johnson`: **100% unconditional**
     Johnson-regime `RbrSound` for multi-arity tensor-batched FRI over `Fp3Model` for ANY
     variable schedule `arities`, discharging `CurveListCA` internally via `curveListCA_fp3`.
   * `GoldilocksExt3.rbrSound_pcsTensorMulti_compact400KBBalanced` &
     `GoldilocksExt3.rbrSound_pcsTensorMulti_ultraCompact400KBZk`: concrete **100% unconditional
     128-bit Johnson `RbrSound`** (`εmax = (3 / 4) / 2 ^ 128`, `θ = 35 / 128`) for the compact
     8-ary FRI parameter profiles (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8`,
     `queries = 58 / 55`, `queryPow = 28 / 30`).

2. **Unpruned Multi-Arity Tensor STARK Soundness over `GoldilocksExt3`:**
   * `GoldilocksExt3.soundness_verifyTensorMultiArity`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArity`
   * `GoldilocksExt3.soundness_verifyTensorMultiArity_lookups`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArity_lookups`

3. **Pruned-MMCS (`CertiFri.P3.prunedMmcs`) Multi-Arity Tensor STARK Soundness over `GoldilocksExt3`:**
   * `GoldilocksExt3.soundness_verifyTensorMultiArityPruned`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned`
   * `GoldilocksExt3.soundness_verifyTensorMultiArityPruned_lookups`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups`

4. **Concrete Digest (`Digest` = `2^256`, `Digest64` = `2^512`) and Compact 8-ary FRI Instantiations:**
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_digest64`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_lookups_digest64`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64`
-/

namespace CertiFri.P3.GoldilocksExt3

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Exec CertiFri.Exec.Stark
  CertiFri.Oracle CertiFri.PcsRbr CertiFri.P3.Exec OracleComp

/-! ## 1. Adaptive-ROM `RbrSound` Interface (`DynamicRom` Bridge) -/

section MultiDynamicRomInterface

variable {D : Type} [Inhabited D] [DecidableEq D] {fslots slots width : ℕ}

/-- **Unconditional unique-decoding `RbrSound` for the `Fp3` multi-arity tensor-batched STARK**
over shape-independent challenges `UTensorChal Fp3Model fslots slots width`.
Directly plugs into adaptive-ROM theorems (`DynamicRom.soundness_dynamic_rom`). -/
theorem rbrSound_starkTensorMulti_ud (sys : System Goldilocks D)
    (hcap : 0 < sys.fri.maxLogArity) (V : Variant Goldilocks GoldilocksExt3 D) (B : Bounds)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) (r : ℕ) :
    RbrSound r (sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
        starkModel sys hcap V (1 - δ) B)
      (roundErr starkModel sys B (pcsErrTensor (K := Fp3Model) sys 3 δ)) :=
  rbrSound_sdoomedTensorMulti_ud starkModel sys hcap V B hδ hrate htwo hfslots hslots hcommit
    hquery hwidth r

/-- The empty `Fp3` multi-arity tensor-batched STARK transcript is doomed. -/
theorem sdoomedTensorMulti_nil_fp3 (sys : System Goldilocks D) (hcap : 0 < sys.fri.maxLogArity)
    (V : Variant Goldilocks GoldilocksExt3 D) (θ : ℝ) (B : Bounds) :
    sdoomedTensorMulti (fslots := fslots) (slots := slots) (width := width)
      starkModel sys hcap V θ B 0 .nil :=
  sdoomedTensorMulti_nil starkModel sys hcap V θ B

/-- **100% Unconditional Johnson-regime `RbrSound` for multi-arity tensor-batched FRI over
`Fp3Model`**, discharging `CurveListCA` internally via `CertiFri.P3.Exec.curveListCA_fp3`
(zero unproven proximity hypotheses) for ANY variable per-round schedule `arities`. -/
theorem rbrSound_pcsTensorMulti_johnson (params : FriParams) (shape : ClaimShape)
    (arities : List ℕ) (hmax : logMaxHeight params.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT_batch : ∀ j ≤ arities.length,
      (CurveListCAProof.curveListThreshold
        (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j))
        (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j)⌉₊ 2 : ℝ) ≤ cT)
    (hT_fold : ∀ i < arities.length,
      (CurveListCAProof.curveListThreshold
        (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) : ℝ) ≤ cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        (Goldilocks.order : ℝ) ^ 3 ≤ εmax)
    (hβ : (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        (Goldilocks.order : ℝ) ^ 3 / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let hsum : arities.sum ≤ logMaxHeight params.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti params arities)
        (PcsRbr.doomedTensorMulti P.ldt P.shift (tensorCoordMulti params shape arities)
          θ P.queries))
      (fun _ => εmax) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  rw [← hcard] at hα hβ
  exact rbrSound_pcsTensorMulti_johnson_of_curveListCA goldilocksExt3_fieldModel params shape
    arities (goldilocksExt3_wellFormed params shape hmax) hpos (by omega)
    CertiFri.P3.Exec.curveListCA_fp3 hsum_eq hθ0 hθ1 hgap hcT0 hT_batch hT_fold hα hβ hq

/-- Profile-driven 100% unconditional 128-bit Johnson `RbrSound` for multi-arity tensor FRI
over `Fp3Model` (`εmax = (3 / 4) / 2 ^ 128`). -/
private theorem rbrSound_pcsTensorMulti_johnson_of_profile
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (tensorNumChallenges (maxWidth shape) +
        tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp)
    (hq : ((p : ℝ) / q) ^ params.numQueries / 2 ^ params.queryPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (hq_pos : 0 < q) (hpq : p ≤ q) (hgap_nat : q ^ 2 < 2 ^ lb * p ^ 2)
    (hR : (2 * q ^ 2) / (2 ^ lb * p ^ 2 - q ^ 2) + 1 ≤ Rmax)
    (hL : (2 * q ^ 2 * p * 2 ^ lb + q ^ 3 + 2 * (2 ^ lb * p ^ 2 - q ^ 2) * p * 2 ^ lb) /
      ((2 ^ lb * p ^ 2 - q ^ 2) * q) ≤ Lmax)
    (hLJ : (((p : ℝ) / q - (1 / 2 : ℝ) ^ lb) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ lb)) * (1 - (p : ℝ) / q) ≤ LJ_ub)
    (hCd : curveListRatioBound (2 ^ lb) Rmax Lmax + 2 ^ lb * LJ_ub ≤ 2 ^ lb * 2 ^ PowExp)
    (hClaimExp : ClaimExp + PowExp ≤ 63) (hHmax : Hmax + PowExp ≤ 63) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let hsum : arities.sum ≤ logMaxHeight params.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti params arities)
        (PcsRbr.doomedTensorMulti P.ldt P.shift (tensorCoordMulti params shape arities)
          ((p : ℝ) / q) P.queries))
      (fun _ => (3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  intro wf hsum P
  set H := logMaxHeight params.logBlowup shape
  set B : ℕ := 2 ^ lb
  have hB2 : 2 ≤ B := calc 2 = 2 ^ 1 := by decide
    _ ≤ 2 ^ lb := Nat.pow_le_pow_right two_pos hlb
  have hp_pos : 0 < p := by
    by_contra hp0
    have hpz : p = 0 := by omega
    subst hpz
    have hq2_pos : 0 < q ^ 2 := pow_pos hq_pos 2
    simp at hgap_nat
  have hθ0 : (0 : ℝ) < (p : ℝ) / q := div_pos (Nat.cast_pos.mpr hp_pos) (Nat.cast_pos.mpr hq_pos)
  have hθ1 : (p : ℝ) / q ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hq_pos)]
    exact_mod_cast hpq
  have hgap : (1 / 2 : ℝ) ^ params.logBlowup < ((p : ℝ) / q) ^ 2 := by
    rw [hbl, div_pow, one_pow, div_pow]
    have hgap_r : ((q : ℝ) ^ 2) < (2 : ℝ) ^ lb * (p : ℝ) ^ 2 := by exact_mod_cast hgap_nat
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, mul_comm ((p : ℝ) ^ 2)]
    exact hgap_r
  set Cd := curveListRatioBound B Rmax Lmax
  set cT : ℝ := ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H
  have hcT0 : 0 ≤ cT := by positivity
  have hcoeff_level : ∀ (c k : ℕ), c ≤ arities.sum → 2 ≤ k →
      CurveListCAProof.curveListThreshold (2 ^ (H - c))
        (2 ^ (arities.sum - c) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - c)⌉₊ k ≤
      (k - 1) * (Cd * (2 ^ (arities.sum - c) * 2 ^ params.logFinalPolyLen)) := by
    intro c k hc hk
    set nc : ℕ := 2 ^ (H - c)
    set dc : ℕ := 2 ^ (arities.sum - c) * 2 ^ params.logFinalPolyLen
    set Ac : ℕ := ⌈((p : ℝ) / q) * (nc : ℝ)⌉₊
    have hH_eq : H = arities.sum + lb + params.logFinalPolyLen := by
      unfold FriParams.logFinalHeight at hsum_eq; rw [hbl] at hsum_eq; omega
    have hnc_eq : nc = B * dc := by
      dsimp only [nc, dc, B]; rw [← pow_add, ← pow_add]; congr 1; omega
    have hdc_pos : 1 ≤ dc := Nat.mul_pos (pow_pos two_pos _) (pow_pos two_pos _)
    have hnc_pos : 0 < nc := pow_pos two_pos _
    have hprod_pos : (0 : ℝ) < ((p : ℝ) / q) * (nc : ℝ) :=
      mul_pos hθ0 (Nat.cast_pos.mpr hnc_pos)
    have hAc_pos : 1 ≤ Ac := Nat.ceil_pos.mpr hprod_pos
    have hAc_le : Ac ≤ nc := by
      apply Nat.ceil_le.mpr
      calc ((p : ℝ) / q) * (nc : ℝ) ≤ 1 * (nc : ℝ) :=
            mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg _)
        _ = (nc : ℝ) := one_mul _
    have hAc_lo : p * nc ≤ q * Ac := by
      have h1 : ((p : ℝ) / q) * (nc : ℝ) ≤ (Ac : ℝ) := Nat.le_ceil _
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (p : ℝ) * (nc : ℝ) ≤ (q : ℝ) * (Ac : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hq_r.le
        field_simp [hq_r.ne'] at this; linarith
      exact_mod_cast h2
    have hAc_hi : q * (Ac - 1) < p * nc := by
      have h1 : (Ac : ℝ) < ((p : ℝ) / q) * (nc : ℝ) + 1 := Nat.ceil_lt_add_one hprod_pos.le
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (q : ℝ) * ((Ac - 1 : ℕ) : ℝ) < (p : ℝ) * (nc : ℝ) := by
        rw [Nat.cast_sub hAc_pos, Nat.cast_one]
        have hsub : (Ac : ℝ) - 1 < ((p : ℝ) / q) * (nc : ℝ) := by linarith
        have := mul_lt_mul_of_pos_left hsub hq_r
        field_simp [hq_r.ne'] at this; linarith
      exact_mod_cast h2
    have hnat1 := CurveListCAProof.curveListThreshold_le_mul_coeff nc dc Ac k hk
    have hnat2 := curveListCoeff_le_of_ratio hdc_pos hB2 hnc_eq hq_pos hgap_nat
      hAc_lo hAc_hi hAc_le hAc_pos hR hL
    have hnc_cast : ((nc : ℕ) : ℝ) = (2 : ℝ) ^ (H - c) := by dsimp only [nc]; push_cast; rfl
    rw [← hnc_cast]
    exact hnat1.trans (Nat.mul_le_mul_left (k - 1) hnat2)
  have hT_batch : ∀ j ≤ arities.length,
      (CurveListCAProof.curveListThreshold (2 ^ (H - cumLogArity arities j))
        (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - cumLogArity arities j)⌉₊ 2 : ℝ) ≤ cT := by
    intro j _
    have hc : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
    have hnat := hcoeff_level (cumLogArity arities j) 2 hc le_rfl
    have hdj_le : B * (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen) ≤
        2 ^ H := by
      have hH_eq : H = arities.sum + lb + params.logFinalPolyLen := by
        unfold FriParams.logFinalHeight at hsum_eq; rw [hbl] at hsum_eq; omega
      dsimp only [B]; rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right two_pos (by omega)
    have hcast : ((CurveListCAProof.curveListThreshold (2 ^ (H - cumLogArity arities j))
        (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - cumLogArity arities j)⌉₊ 2 : ℕ) : ℝ) ≤
        (Cd : ℝ) * ((2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) := by
      simpa only [Nat.reduceSub, one_mul, Nat.cast_mul] using (Nat.cast_le (α := ℝ)).mpr hnat
    have hBdj : (B : ℝ) *
        ((2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) ≤
        (2 : ℝ) ^ H := by exact_mod_cast hdj_le
    have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
    refine hcast.trans ?_
    dsimp only [cT]
    rw [div_mul_eq_mul_div, le_div_iff₀ hBpos]
    calc (Cd : ℝ) * _ * (B : ℝ) = (Cd : ℝ) * ((B : ℝ) * _) := by ring
      _ ≤ (Cd : ℝ) * (2 : ℝ) ^ H := mul_le_mul_of_nonneg_left hBdj (Nat.cast_nonneg _)
  have hT_fold : ∀ i < arities.length,
      (CurveListCAProof.curveListThreshold (2 ^ (H - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) : ℝ) ≤ cT := by
    intro i hi
    have hc1 : cumLogArity arities (i + 1) ≤ arities.sum := cumLogArity_le_sum arities (i + 1)
    have h2le : 2 ≤ 2 ^ arities.getD i 1 + 1 := by
      have : 1 ≤ 2 ^ arities.getD i 1 := Nat.one_le_pow _ 2 two_pos; omega
    have hnat := hcoeff_level (cumLogArity arities (i + 1)) (2 ^ arities.getD i 1 + 1) hc1 h2le
    have hcum_s : cumLogArity arities (i + 1) = cumLogArity arities i + arities.getD i 1 := by
      have hs := P.cum_succ hi
      simpa only [P, modelParamsMulti, Compiled.MultiParams.cum, Compiled.MultiParams.logArity,
        List.getD_eq_getElem _ _ hi] using hs
    have hmd : 2 ^ arities.getD i 1 *
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen) =
        2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen := by
      rw [← mul_assoc, ← pow_add]; congr 2; omega
    have hdj_le : B * (2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen) ≤
        2 ^ H := by
      have hH_eq : H = arities.sum + lb + params.logFinalPolyLen := by
        unfold FriParams.logFinalHeight at hsum_eq; rw [hbl] at hsum_eq; omega
      dsimp only [B]; rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right two_pos (by omega)
    have hnat' : CurveListCAProof.curveListThreshold (2 ^ (H - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) ≤
        Cd * (2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen) := by
      rw [Nat.add_sub_cancel] at hnat
      calc _ ≤ 2 ^ arities.getD i 1 *
              (Cd * (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)) :=
            hnat
        _ = Cd * (2 ^ arities.getD i 1 *
              (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)) := by
            ring
        _ = Cd * (2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen) := by
            rw [hmd]
    have hcast : ((CurveListCAProof.curveListThreshold (2 ^ (H - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) : ℕ) : ℝ) ≤
        (Cd : ℝ) * ((2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) := by
      exact_mod_cast hnat'
    have hBdj : (B : ℝ) *
        ((2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen : ℕ) : ℝ) ≤
        (2 : ℝ) ^ H := by exact_mod_cast hdj_le
    have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
    refine hcast.trans ?_
    dsimp only [cT]
    rw [div_mul_eq_mul_div, le_div_iff₀ hBpos]
    calc (Cd : ℝ) * _ * (B : ℝ) = (Cd : ℝ) * ((B : ℝ) * _) := by ring
      _ ≤ (Cd : ℝ) * (2 : ℝ) ^ H := mul_le_mul_of_nonneg_left hBdj (Nat.cast_nonneg _)
  have h63 : (2 : ℝ) ^ 63 / ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    refine (div_le_div_of_nonneg_left (by positivity) (by positivity)
      ninetyNine_hundredths_two_pow_192_le_goldilocks_cube).trans ?_
    rw [show (2 : ℝ) ^ 192 = (2 : ℝ) ^ 64 * (2 : ℝ) ^ 128 by rw [← pow_add],
      show (2 : ℝ) ^ 64 = 2 * (2 : ℝ) ^ 63 by rw [show (64 : ℕ) = 63 + 1 by decide, pow_succ'],
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 by positivity]
  have hcomb : cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H := by
    have hCd_r : (Cd : ℝ) + (B : ℝ) * (LJ_ub : ℝ) ≤ (B : ℝ) * (2 : ℝ) ^ PowExp := by
      exact_mod_cast hCd
    have hfrac : (Cd : ℝ) / (B : ℝ) + (LJ_ub : ℝ) ≤ (2 : ℝ) ^ PowExp := by
      have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
      rw [div_add' _ _ _ hBpos.ne', div_le_iff₀ hBpos]; linarith
    have hLJ' : (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (LJ_ub : ℝ) * (2 : ℝ) ^ H := by
      rw [hbl, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hLJ (by positivity)
    calc cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
            (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
            ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)
        ≤ ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H + (LJ_ub : ℝ) * (2 : ℝ) ^ H :=
          add_le_add le_rfl hLJ'
      _ = ((Cd : ℝ) / (B : ℝ) + (LJ_ub : ℝ)) * (2 : ℝ) ^ H := by ring
      _ ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H := mul_le_mul_of_nonneg_right hfrac (by positivity)
  have hεα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
        tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
      (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      (Goldilocks.order : ℝ) ^ 3 ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hcr : ((2 ^ (tensorNumChallenges (maxWidth shape) +
        tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (2 : ℝ) ^ H ≤ (2 : ℝ) ^ ClaimExp := by exact_mod_cast htensor
    have hpow63 : (2 : ℝ) ^ (ClaimExp + PowExp) ≤ (2 : ℝ) ^ 63 := by
      exact_mod_cast Nat.pow_le_pow_right two_pos hClaimExp
    have hnum : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
            (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) ≤ (2 : ℝ) ^ 63 := by
      calc _ ≤ ((2 ^ (tensorNumChallenges (maxWidth shape) +
              tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
            ((2 : ℝ) ^ PowExp * (2 : ℝ) ^ H) :=
            mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg _)
        _ = (((2 ^ (tensorNumChallenges (maxWidth shape) +
              tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
            (2 : ℝ) ^ H) * (2 : ℝ) ^ PowExp := by ring
        _ ≤ (2 : ℝ) ^ ClaimExp * (2 : ℝ) ^ PowExp :=
            mul_le_mul_of_nonneg_right hcr (by positivity)
        _ = (2 : ℝ) ^ (ClaimExp + PowExp) := (pow_add _ _ _).symm
        _ ≤ (2 : ℝ) ^ 63 := hpow63
    exact (div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg _) 3)).trans h63
  have hεβ : (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      (Goldilocks.order : ℝ) ^ 3 / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hLJ_nn : 0 ≤ (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) := by
      have hnum_nn : 0 ≤ (p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup := by
        have h1 : ((p : ℝ) / q) ^ 2 ≤ (p : ℝ) / q := by nlinarith
        linarith
      have hden_pos : 0 < ((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup := sub_pos.mpr hgap
      have h1m : 0 ≤ 1 - (p : ℝ) / q := sub_nonneg.mpr hθ1
      positivity
    have hnum : cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (2 : ℝ) ^ 63 := by
      have h2H : (2 : ℝ) ^ (H + PowExp) ≤ (2 : ℝ) ^ 63 := by
        exact_mod_cast Nat.pow_le_pow_right two_pos (show H + PowExp ≤ 63 by omega)
      calc _ ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H := hcomb
        _ = (2 : ℝ) ^ (H + PowExp) := by rw [pow_add, mul_comm]
        _ ≤ (2 : ℝ) ^ 63 := h2H
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
      exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
    exact (div_le_self (div_nonneg (by linarith) (pow_nonneg (Nat.cast_nonneg _) 3)) hpow1).trans
      ((div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg _) 3)).trans h63)
  exact rbrSound_pcsTensorMulti_johnson params shape arities (hmax.trans hmax32) hpos hsum_eq
    hθ0 hθ1 hgap hcT0 hT_batch hT_fold hεα hεβ hq

/-- **100% Unconditional 128-Bit Johnson `RbrSound` for `FriParams.compact400KBBalanced`**
(`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8, numQueries = 58, queryPowBits = 28`,
8-ary folding) for ANY valid schedule `arities` (including `scheduleOfShape`), with
round error literally `(3 / 4) / 2 ^ 128` and ZERO unproven assumptions! -/
theorem rbrSound_pcsTensorMulti_compact400KBBalanced (shape : ClaimShape) (arities : List ℕ)
    (hmax : logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.compact400KBBalanced.logFinalHeight =
      logMaxHeight FriParams.compact400KBBalanced.logBlowup shape)
    (htensor : 2 ^ (tensorNumChallenges (maxWidth shape) +
        tensorNumChallenges (maxOpeningsPerHeight
          FriParams.compact400KBBalanced.logBlowup shape)) *
        2 ^ logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 2 ^ 33) :
    let wf := goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax
    let hsum : arities.sum ≤ logMaxHeight FriParams.compact400KBBalanced.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
      arities wf hpos hsum
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti FriParams.compact400KBBalanced arities)
        (PcsRbr.doomedTensorMulti P.ldt P.shift
          (tensorCoordMulti FriParams.compact400KBBalanced shape arities)
          (35 / 128) P.queries))
      (fun _ => (3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  simpa only [Nat.cast_ofNat] using
    rbrSound_pcsTensorMulti_johnson_of_profile 4 35 128 11 58 13 30 32 33
      FriParams.compact400KBBalanced shape arities rfl (by decide) hmax le_rfl hpos hsum_eq
      htensor (johnson_35_128_compact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide)

/-- **100% Unconditional 128-Bit Johnson `RbrSound` for `FriParams.ultraCompact400KBZk`**
(`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8, numQueries = 55, queryPowBits = 30`,
8-ary folding) for ANY valid schedule `arities` (including `scheduleOfShape`), with
round error literally `(3 / 4) / 2 ^ 128` and ZERO unproven assumptions! -/
theorem rbrSound_pcsTensorMulti_ultraCompact400KBZk (shape : ClaimShape) (arities : List ℕ)
    (hmax : logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.ultraCompact400KBZk.logFinalHeight =
      logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape)
    (htensor : 2 ^ (tensorNumChallenges (maxWidth shape) +
        tensorNumChallenges (maxOpeningsPerHeight
          FriParams.ultraCompact400KBZk.logBlowup shape)) *
        2 ^ logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 2 ^ 33) :
    let wf := goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax
    let hsum : arities.sum ≤ logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
      arities wf hpos hsum
    RbrSound (P.rounds + 2)
      (grindDoomed (powBitsMulti FriParams.ultraCompact400KBZk arities)
        (PcsRbr.doomedTensorMulti P.ldt P.shift
          (tensorCoordMulti FriParams.ultraCompact400KBZk shape arities)
          (35 / 128) P.queries))
      (fun _ => (3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  simpa only [Nat.cast_ofNat] using
    rbrSound_pcsTensorMulti_johnson_of_profile 4 35 128 11 58 13 30 32 33
      FriParams.ultraCompact400KBZk shape arities rfl (by decide) hmax le_rfl hpos hsum_eq
      htensor (johnson_35_128_ultraCompact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide)

end MultiDynamicRomInterface

/-! ## 2. Unpruned Multi-Arity Tensor STARK Soundness over `GoldilocksExt3` -/

section TensorMultiUnpruned

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {fslots slots width : ℕ}
  (sys : System Goldilocks D) (hcap : 0 < sys.fri.maxLogArity) (B : Bounds) {δ : ℝ}

/-- **Unconditional soundness of `Stark.verifyTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorMultiArity (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            verifyTensorMultiArityAccepts starkModel sys f (attempt out.1) = true ∧
            Covered B (attempt out.1) ∧
            ViolatesTensor starkModel sys (1 - δ) l f (attempt out.1))
      (experimentTensorMultiStark starkModel sys hcap adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorMultiArity_ud starkModel sys hcap B hδ hrate hfixed hheightOk hshards hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional soundness of `Stark.verifyBatchTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorMultiArity (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCovered B (attempt out.1) ∧
            BatchViolatesTensor starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStark starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorMultiArity_ud starkModel sys hcap B hδ hrate hfixed hheightOk hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional lookup balance for `Stark.verifyTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorMultiArity_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            verifyTensorMultiArityAccepts starkModel sys f (attempt out.1) = true ∧
            Covered B (attempt out.1) ∧
            ¬ LookupsBalancedTensor starkModel sys (1 - δ) B l (attempt out.1))
      (experimentTensorMultiStark starkModel sys hcap adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorMultiArity_lookups_ud starkModel sys hcap B hδ hrate hplain
    Fp3Model.two_ne_zero hfixed hheightOk hshards hN (Fp3Model.natCast_inj_le hNp) htwo hfslots
    hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional lookup balance for `Stark.verifyBatchTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorMultiArity_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCovered B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensor starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStark starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorMultiArity_lookups_ud starkModel sys hcap B hδ hrate hplain
    Fp3Model.two_ne_zero hfixed hheightOk hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots
    hcommit hquery hwidth hadv attempt

end TensorMultiUnpruned

/-! ## 3. Pruned-MMCS (`prunedMmcs`) Multi-Arity Tensor STARK Soundness over `GoldilocksExt3` -/

section TensorMultiPruned

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {fslots slots width : ℕ}
  (sys : System Goldilocks D) (hcap : 0 < sys.fri.maxLogArity) (B : Bounds) {δ : ℝ}

/-- **Unconditional pruned-MMCS soundness of `Stark.verifyTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorMultiArityPruned (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttemptPruned Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            verifyTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            CoveredPruned B (attempt out.1) ∧
            ViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (experimentTensorMultiStarkPruned starkModel sys hcap adv attempt) [] ≤
      (Q + shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueriesPruned sys 32 : ℕ) * ((Q + shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorMultiArityPruned_ud starkModel sys hcap B hδ hrate hfixed hheightOk
    hshards hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional pruned-MMCS soundness of `Stark.verifyBatchTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorMultiArityPruned (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorMultiArityPruned_ud starkModel sys hcap B hδ hrate hfixed hheightOk hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional pruned-MMCS lookup balance for `Stark.verifyTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorMultiArityPruned_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttemptPruned Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            verifyTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            CoveredPruned B (attempt out.1) ∧
            ¬ LookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (experimentTensorMultiStarkPruned starkModel sys hcap adv attempt) [] ≤
      (Q + shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueriesPruned sys 32 : ℕ) * ((Q + shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorMultiArityPruned_lookups_ud starkModel sys hcap B hδ hrate hplain
    Fp3Model.two_ne_zero hfixed hheightOk hshards hN (Fp3Model.natCast_inj_le hNp) htwo hfslots
    hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional pruned-MMCS lookup balance for `Stark.verifyBatchTensorMultiArity` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorMultiArityPruned_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorMultiArityPruned_lookups_ud starkModel sys hcap B hδ hrate hplain
    Fp3Model.two_ne_zero hfixed hheightOk hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots
    hcommit hquery hwidth hadv attempt

end TensorMultiPruned

/-! ## 4. Concrete `Digest` (`2^256`), `Digest64` (`2^512`), and Compact 8-ary FRI Profiles -/

section ConcreteMultiDigests

variable {fslots slots width : ℕ} (B : Bounds) {δ : ℝ}

/-- **`BLAKE3-256` (`Digest`, `2 ^ 256`) pruned batch multi-arity tensor STARK soundness**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_digest32 (sys : System Goldilocks Digest)
    (hcap : 0 < sys.fri.maxLogArity) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  have h := soundness_verifyBatchTensorMultiArityPruned sys hcap B hδ hrate hfixed hheightOk hN hNp
    htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **`BLAKE2b-512` (`Digest64`, `2 ^ 512`) pruned batch multi-arity tensor STARK soundness**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_digest64 (sys : System Goldilocks Digest64)
    (hcap : 0 < sys.fri.maxLogArity) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest64) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  have h := soundness_verifyBatchTensorMultiArityPruned sys hcap B hδ hrate hfixed hheightOk hN hNp
    htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **`BLAKE3-256` (`Digest`, `2 ^ 256`) pruned batch multi-arity tensor STARK lookup balance**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_lookups_digest32
    (sys : System Goldilocks Digest) (hcap : 0 < sys.fri.maxLogArity) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  have h := soundness_verifyBatchTensorMultiArityPruned_lookups sys hcap B hδ hrate hplain hfixed
    hheightOk hN hNp htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **`BLAKE2b-512` (`Digest64`, `2 ^ 512`) pruned batch multi-arity tensor STARK lookup balance**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_lookups_digest64
    (sys : System Goldilocks Digest64) (hcap : 0 < sys.fri.maxLogArity) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest64) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  have h := soundness_verifyBatchTensorMultiArityPruned_lookups sys hcap B hδ hrate hplain hfixed
    hheightOk hN hNp htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **Concrete `FriParams.compact400KBBalanced` (`maxLogArity = 3`, `logBlowup = 4`, `queries = 58`,
`queryPow = 28`, `logFinalPolyLen = 8`) pruned batch STARK soundness (`BLAKE3-256`, `Digest`)**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest32
    (sys : System Goldilocks Digest) (hfri : sys.fri = FriParams.compact400KBBalanced) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + 1 / 16 < 1) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : 59 ≤ slots) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest) :
    have hcap : 0 < sys.fri.maxLogArity := by rw [hfri]; decide
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  intro hcap
  exact soundness_verifyBatchTensorMultiArityPruned_digest32 B sys hcap hδ
    (by rw [hfri]; simpa [FriParams.compact400KBBalanced] using (by norm_num; exact hrate :
      2 * δ + (1 / 2 : ℝ) ^ 4 < 1))
    hfixed hheightOk hN hNp htwo hfslots
    (by rw [hfri]; exact hslots)
    (by rw [hfri]; exact Nat.zero_le _)
    (by rw [hfri]; dsimp only [FriParams.compact400KBBalanced]; omega)
    hwidth hadv attempt

/-- **Concrete `FriParams.compact400KBBalanced` (`maxLogArity = 3`, `logBlowup = 4`, `queries = 58`,
`queryPow = 28`, `logFinalPolyLen = 8`) pruned batch STARK soundness (`BLAKE2b-512`, `Digest64`)**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_compact400KBBalanced_digest64
    (sys : System Goldilocks Digest64) (hfri : sys.fri = FriParams.compact400KBBalanced) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + 1 / 16 < 1) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : 59 ≤ slots) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest64) :
    have hcap : 0 < sys.fri.maxLogArity := by rw [hfri]; decide
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  intro hcap
  exact soundness_verifyBatchTensorMultiArityPruned_digest64 B sys hcap hδ
    (by rw [hfri]; simpa [FriParams.compact400KBBalanced] using (by norm_num; exact hrate :
      2 * δ + (1 / 2 : ℝ) ^ 4 < 1))
    hfixed hheightOk hN hNp htwo hfslots
    (by rw [hfri]; exact hslots)
    (by rw [hfri]; exact Nat.zero_le _)
    (by rw [hfri]; dsimp only [FriParams.compact400KBBalanced]; omega)
    hwidth hadv attempt

/-- **Concrete `FriParams.ultraCompact400KBZk` (`maxLogArity = 3`, `logBlowup = 4`, `queries = 55`,
`queryPow = 30`, `logFinalPolyLen = 8`) pruned batch STARK soundness (`BLAKE3-256`, `Digest`)**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest32
    (sys : System Goldilocks Digest) (hfri : sys.fri = FriParams.ultraCompact400KBZk) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + 1 / 16 < 1) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : 56 ≤ slots) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest) :
    have hcap : 0 < sys.fri.maxLogArity := by rw [hfri]; decide
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  intro hcap
  exact soundness_verifyBatchTensorMultiArityPruned_digest32 B sys hcap hδ
    (by rw [hfri]; simpa [FriParams.ultraCompact400KBZk] using (by norm_num; exact hrate :
      2 * δ + (1 / 2 : ℝ) ^ 4 < 1))
    hfixed hheightOk hN hNp htwo hfslots
    (by rw [hfri]; exact hslots)
    (by rw [hfri]; exact Nat.zero_le _)
    (by rw [hfri]; dsimp only [FriParams.ultraCompact400KBZk]; omega)
    hwidth hadv attempt

/-- **Concrete `FriParams.ultraCompact400KBZk` (`maxLogArity = 3`, `logBlowup = 4`, `queries = 55`,
`queryPow = 30`, `logFinalPolyLen = 8`) pruned batch STARK soundness (`BLAKE2b-512`, `Digest64`)**
over `GoldilocksExt3`. -/
theorem soundness_verifyBatchTensorMultiArityPruned_ultraCompact400KBZk_digest64
    (sys : System Goldilocks Digest64) (hfri : sys.fri = FriParams.ultraCompact400KBZk) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + 1 / 16 < 1) (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : 56 ≤ slots) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest64) :
    have hcap : 0 < sys.fri.maxLogArity := by rw [hfri]; decide
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest64 Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorMultiArityPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorMultiStarkPruned starkModel sys hcap B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  intro hcap
  exact soundness_verifyBatchTensorMultiArityPruned_digest64 B sys hcap hδ
    (by rw [hfri]; simpa [FriParams.ultraCompact400KBZk] using (by norm_num; exact hrate :
      2 * δ + (1 / 2 : ℝ) ^ 4 < 1))
    hfixed hheightOk hN hNp htwo hfslots
    (by rw [hfri]; exact hslots)
    (by rw [hfri]; exact Nat.zero_le _)
    (by rw [hfri]; dsimp only [FriParams.ultraCompact400KBZk]; omega)
    hwidth hadv attempt

end ConcreteMultiDigests

end CertiFri.P3.GoldilocksExt3
