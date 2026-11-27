import CertiFriProofs.P3.GoldilocksExt3Model
import CertiFriProofs.P3.DigestCard
import CertiFriProofs.Exec.Stark.PrunedTensor
import CertiFriProofs.Exec.SoundnessSponge

/-!
# Tensor-Batched STARK Soundness over Goldilocks Cubic Extension `Fp3` (`Protocol v6`)

Instantiates the complete tensor-batched STARK soundness stack
(`Exec/Stark/{StateTensor,GoodLogTensor,SoundnessTensor,PrunedTensor}.lean`) at
`GoldilocksExt3.starkModel` (`Fp3Model ≃+* GF(p)[Y] / (Y^3 - Y - 1)`,
`|Fp3Model| = Goldilocks.order ^ 3 ≈ 2 ^ 192`) with ZERO field-model or
unproven proximity assumptions.

## Contents

1. **Adaptive-ROM `RbrSound` interface (directly instantiable by `DynamicRom`):**
   * `GoldilocksExt3.rbrSound_starkTensor_ud`: unconditional unique-decoding
     `RbrSound r (sdoomedTensor starkModel sys V (1 - δ) B)` over shape-independent
     `UTensorChal Fp3Model fslots slots width` with tight tensor PCS error
     `pcsErrTensor sys 3 δ` (linear in `kColMax + kOpenMax` and `2 ^ (maxLogDegree + logBlowup)`).
   * `GoldilocksExt3.sdoomedTensor_nil`, `GoldilocksExt3.settles_interpTensor`:
     base-case doom and Merkle-hit `Settles` lemmas matching `DynamicRom.soundness_dynamic_rom`.
   * `GoldilocksExt3.rbrSound_pcsTensor_johnson`: **100% unconditional**
     Johnson-regime `RbrSound` for tensor-batched FRI over `Fp3Model`, discharging
     `CurveListCA` internally via `CertiFri.P3.Exec.curveListCA_fp3`.
     *(Note: the unconditional `CurveListCA` (`m = 2`) union-bound reduction carries the
     factor `2 ^ (kCol + kOpen) - 1`; achieving `M`-independent logarithmic `(kCol + kOpen)`
     scaling in the Johnson regime requires discharging `BatchedLineListCA Fp3Model` via an
     interleaved-word Johnson peeling proof — see `Exec/SoundnessTensor.lean`.)*

2. **Unpruned Tensor STARK Soundness over `GoldilocksExt3`:**
   * `GoldilocksExt3.soundness_verifyTensor`
   * `GoldilocksExt3.soundness_verifyBatchTensor`
   * `GoldilocksExt3.soundness_verifyTensor_lookups`
   * `GoldilocksExt3.soundness_verifyBatchTensor_lookups`

3. **Pruned-MMCS (`CertiFri.P3.prunedMmcs`) Tensor STARK Soundness over `GoldilocksExt3`:**
   * `GoldilocksExt3.soundness_verifyTensorPruned`
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned`
   * `GoldilocksExt3.soundness_verifyTensorPruned_lookups`
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups`

4. **Concrete Digest Instantiations (`Digest` = `2 ^ 256`, `Digest64` = `2 ^ 512`):**
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned_digest64`
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest32`
   * `GoldilocksExt3.soundness_verifyBatchTensorPruned_lookups_digest64`
-/

namespace CertiFri.P3.GoldilocksExt3

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Exec CertiFri.Exec.Stark
  CertiFri.Oracle CertiFri.PcsRbr OracleComp

/-! ## 1. Adaptive-ROM `RbrSound` Interface (`DynamicRom` Bridge) -/

section DynamicRomInterface

variable {D : Type} [Inhabited D] [DecidableEq D] {fslots slots width : ℕ}

/-- **Unconditional unique-decoding `RbrSound` for the `Fp3` tensor-batched STARK**
over shape-independent challenges `UTensorChal Fp3Model fslots slots width`.
Directly plugs into adaptive-ROM theorems (`DynamicRom.soundness_dynamic_rom`). -/
theorem rbrSound_starkTensor_ud (sys : System Goldilocks D)
    (V : Variant Goldilocks GoldilocksExt3 D) (B : Bounds) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup ≤ 1) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) (r : ℕ) :
    RbrSound r (sdoomedTensor (fslots := fslots) (slots := slots) (width := width)
        starkModel sys V (1 - δ) B)
      (roundErr starkModel sys B (pcsErrTensor (K := Fp3Model) sys 3 δ)) :=
  rbrSound_sdoomedTensor_ud starkModel sys V B hδ hrate htwo hfslots hslots hcommit hquery hwidth r

/-- The empty `Fp3` tensor-batched STARK transcript is doomed. -/
theorem sdoomedTensor_nil_fp3 (sys : System Goldilocks D)
    (V : Variant Goldilocks GoldilocksExt3 D) (θ : ℝ) (B : Bounds) :
    sdoomedTensor (fslots := fslots) (slots := slots) (width := width)
      starkModel sys V θ B 0 .nil :=
  sdoomedTensor_nil starkModel sys V θ B

omit [Inhabited D] in
/-- `interpTensor` settles on committed Merkle rows up to a digest hit (`Settles`). -/
theorem settles_interpTensor_fp3 (B : Bounds) (r : ℕ) :
    Settles
      (fun (l : Log (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width)) j m =>
        interpTensor B r l j m)
      (Hit (fun _ => digestsOf B) r) :=
  settles_interpTensor B r

/-- **100% Unconditional Johnson-regime `RbrSound` for tensor-batched FRI over `Fp3Model`**,
discharging `CurveListCA` internally via `CertiFri.P3.Exec.curveListCA_fp3` (zero unproven
proximity hypotheses). Uses the `m = 2` union-bound reduction `tensor2DMCA_of_curveMCA_two`;
the batching round error carries the factor `2 ^ (kCol + kOpen)`. -/
theorem rbrSound_pcsTensor_johnson (params : FriParams) (shape : ClaimShape)
    (hmax : logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    {cT : ℝ} (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (CurveListCAProof.curveListThreshold
        (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        (Goldilocks.order : ℝ) ^ 3 ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        (Goldilocks.order : ℝ) ^ 3 / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    RbrSound (P.rounds + 2)
      (grindDoomed (powBits params shape)
        (PcsRbr.doomedTensor P.ldt P.shift (tensorCoord params shape) θ P.queries))
      (fun _ => εmax) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  rw [← hcard] at hα hβ
  exact rbrSound_pcsTensor_johnson_of_curveListCA goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) CertiFri.P3.Exec.curveListCA_fp3
    hheight hθ0 hθ1 hgap hcT0 hT hα hβ hq

end DynamicRomInterface

/-! ## 2. Unpruned Tensor STARK Soundness over `GoldilocksExt3` -/

section TensorUnpruned

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {fslots slots width : ℕ}
  (sys : System Goldilocks D) (B : Bounds) {δ : ℝ}

/-- **Unconditional soundness of `Stark.verifyTensor` over `GoldilocksExt3` (`Fp3Model`).** -/
theorem soundness_verifyTensor (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hfslots : fslotsBound sys 3 ≤ fslots) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 D Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            verifyTensorAccepts starkModel sys f (attempt out.1) = true ∧
            Covered B (attempt out.1) ∧
            ViolatesTensor starkModel sys (1 - δ) l f (attempt out.1))
      (experimentTensorStark starkModel sys adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensor_ud starkModel sys B hδ hrate hfixed hheightOk hshards hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional soundness of `Stark.verifyBatchTensor` over `GoldilocksExt3` (`Fp3Model`).** -/
theorem soundness_verifyBatchTensor (hδ : 0 ≤ δ)
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
            batchTensorAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCovered B (attempt out.1) ∧
            BatchViolatesTensor starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStark starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensor_ud starkModel sys B hδ hrate hfixed hheightOk hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional lookup balance for `Stark.verifyTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensor_lookups (hδ : 0 ≤ δ)
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
            verifyTensorAccepts starkModel sys f (attempt out.1) = true ∧
            Covered B (attempt out.1) ∧
            ¬ LookupsBalancedTensor starkModel sys (1 - δ) B l (attempt out.1))
      (experimentTensorStark starkModel sys adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensor_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero hfixed
    hheightOk hshards hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth
    hadv attempt

/-- **Unconditional lookup balance for `Stark.verifyBatchTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensor_lookups (hδ : 0 ≤ δ)
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
            batchTensorAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCovered B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensor starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStark starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensor_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero
    hfixed hheightOk hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth
    hadv attempt

end TensorUnpruned

/-! ## 3. Pruned-MMCS (`prunedMmcs`) Tensor STARK Soundness over `GoldilocksExt3` -/

section TensorPruned

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {fslots slots width : ℕ}
  (sys : System Goldilocks D) (B : Bounds) {δ : ℝ}

/-- **Unconditional pruned-MMCS soundness of `Stark.verifyTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorPruned (hδ : 0 ≤ δ)
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
            verifyTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            CoveredPruned B (attempt out.1) ∧
            ViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (experimentTensorStarkPruned starkModel sys adv attempt) [] ≤
      (Q + shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueriesPruned sys 32 : ℕ) * ((Q + shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorPruned_ud starkModel sys B hδ hrate hfixed hheightOk hshards hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional pruned-MMCS soundness of `Stark.verifyBatchTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorPruned (hδ : 0 ≤ δ)
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
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorPruned_ud starkModel sys B hδ hrate hfixed hheightOk hN
    (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth hadv attempt

/-- **Unconditional pruned-MMCS lookup balance for `Stark.verifyTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyTensorPruned_lookups (hδ : 0 ≤ δ)
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
            verifyTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            CoveredPruned B (attempt out.1) ∧
            ¬ LookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (experimentTensorStarkPruned starkModel sys adv attempt) [] ≤
      (Q + shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueriesPruned sys 32 : ℕ) * ((Q + shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyTensorPruned_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero
    hfixed hheightOk hshards hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery
    hwidth hadv attempt

/-- **Unconditional pruned-MMCS lookup balance for `Stark.verifyBatchTensor` over `GoldilocksExt3`.** -/
theorem soundness_verifyBatchTensorPruned_lookups (hδ : 0 ≤ δ)
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
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatchTensorPruned_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero
    hfixed hheightOk hN (Fp3Model.natCast_inj_le hNp) htwo hfslots hslots hcommit hquery hwidth
    hadv attempt

end TensorPruned

/-! ## 4. Concrete `Digest` (`2^256`) and `Digest64` (`2^512`) Instantiations -/

section ConcreteDigests

variable {fslots slots width : ℕ} (B : Bounds) {δ : ℝ}

/-- **Protocol `v6` (`BLAKE3-256`, `Digest`, `2 ^ 256`) pruned batch tensor STARK soundness**
over `GoldilocksExt3` (`Fp3Model`). -/
theorem soundness_verifyBatchTensorPruned_digest32 (sys : System Goldilocks Digest) (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hfslots : fslotsBound sys 3 ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → BAttemptPruned Goldilocks GoldilocksExt3 Digest) :
    prob (fun out l =>
        ∃ f : ∀ x, STAns Goldilocks GoldilocksExt3 Digest Fp3Model fslots slots width x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  have h := soundness_verifyBatchTensorPruned sys B hδ hrate hfixed hheightOk hN hNp htwo hfslots
    hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **Protocol `v6` (`BLAKE2b-512`, `Digest64`, `2 ^ 512`) pruned batch tensor STARK soundness**
over `GoldilocksExt3` (`Fp3Model`). -/
theorem soundness_verifyBatchTensorPruned_digest64 (sys : System Goldilocks Digest64) (hδ : 0 ≤ δ)
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
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            BatchViolatesTensorPruned starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  have h := soundness_verifyBatchTensorPruned sys B hδ hrate hfixed hheightOk hN hNp htwo hfslots
    hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **Protocol `v6` (`BLAKE3-256`, `Digest`, `2 ^ 256`) pruned batch tensor STARK lookup balance**
over `GoldilocksExt3` (`Fp3Model`). -/
theorem soundness_verifyBatchTensorPruned_lookups_digest32 (sys : System Goldilocks Digest)
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
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
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 256) := by
  have h := soundness_verifyBatchTensorPruned_lookups sys B hδ hrate hplain hfixed hheightOk hN
    hNp htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest, Nat.cast_pow, Nat.cast_ofNat] at h

/-- **Protocol `v6` (`BLAKE2b-512`, `Digest64`, `2 ^ 512`) pruned batch tensor STARK lookup balance**
over `GoldilocksExt3` (`Fp3Model`). -/
theorem soundness_verifyBatchTensorPruned_lookups_digest64 (sys : System Goldilocks Digest64)
    (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
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
            batchTensorPrunedAccepts starkModel sys f (attempt out.1) = true ∧
            BatchCoveredPruned B (attempt out.1) ∧
            ¬ BatchLookupsBalancedTensorPruned starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperimentTensorStarkPruned starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueriesPruned sys 32 : ℕ) * starkErrTensor starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueriesPruned sys 32 : ℕ) *
          ((Q + B.shards * shardQueriesPruned sys 32 : ℕ) - 1) /
            (2 * (2 : ℝ) ^ 512) := by
  have h := soundness_verifyBatchTensorPruned_lookups sys B hδ hrate hplain hfixed hheightOk hN
    hNp htwo hfslots hslots hcommit hquery hwidth hadv attempt
  rwa [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at h

end ConcreteDigests

end CertiFri.P3.GoldilocksExt3
