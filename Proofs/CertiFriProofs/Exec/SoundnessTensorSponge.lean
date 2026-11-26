import CertiFriProofs.Exec.TensorExec
import CertiFriProofs.Exec.SoundnessSponge
import CertiFriProofs.Exec.SoundnessTensor

/-!
# Incremental Sponge Soundness (`c = 3 / 2`) for Executable `Fri.verifyTensor`

This module lifts the compiled and executable tensor-batched FRI soundness
theorems (`Theory/Compiled/Tensor.lean` and `Exec/TensorExec.lean`) from
full-transcript Fiat–Shamir chaining (`entryCap = batches + rounds`) to
single-root incremental sponge chaining (`entryCap = 1`, collision prefactor
**`c = 3 / 2`**) via `Oracle.prob_spongeExperiment_bind_committedRow_le`.

Each input batch commitment root is absorbed individually (steps `0 .. batches - 1`,
`1` digest each, `0` error), followed by the opening points and claimed values
(step `batches`, `0` digests, squeezing the 2D tensor schedule `(rCol, rOpen)`),
each folding commitment root (steps `batches + 1 .. batches + rounds`, `1` digest
each, squeezing `β_i`), and the final polynomial (step `batches + rounds + 1`,
`0` digests, squeezing query indices). Every step introduces at most **`1`**
digest (`entryCap = 1`), giving the exact classical BCS collision term
**`3 * N ^ 2 / (2 * Fintype.card D)`**.

## Concrete theorems proved (zero `sorry`, standard axioms only)

* `Exec.soundnessTensor_sponge`: general executable `Fri.verifyTensor` soundness
  under incremental sponge chaining (`c = 3 / 2`) for arbitrary `Tensor2DMCA` +
  `StepMCA`, with single-level max error `ε₀` (no sum over heights).
* `Exec.soundnessTensor_sponge_uniqueDecoding`: unconditional unique-decoding
  soundness (`c = 3 / 2`) with tensor batching error linear in `kCol + kOpen`.
* `CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_uniqueDecoding` and
  `goldilocksExt3_soundnessTensor_sponge_uniqueDecoding_128_blake3`:
  32-byte `BLAKE3-256` (`Digest`, `|Digest| = 2 ^ 256`) instantiations over
  `GoldilocksExt3` in the classical random-oracle model.
* `CertiFri.P3.Exec.goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding`
  and `goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding_128`:
  64-byte RFC 7693 `BLAKE2b-512` (`Digest64`, `|Digest64| = 2 ^ 512`)
  instantiations, yielding literal `≤ N / 2 ^ 128` unconditional UD soundness
  for executable `Fri.verifyTensor` for all `logMaxHeight ≤ 32`, `W ≤ 2 ^ 16`,
  `M ≤ 2 ^ 16`, and `N ≤ 2 ^ 128`.
-/

namespace CertiFri.Sponge

open Oracle OracleComp MerkleRO Compiled
open PcsRbr (TensorChal ChalTensor GrindChal ClaimsFail AcceptsTensor PowPasses ungrind
  roundErrorTensor)

/-! ## Single-root incremental absorption lift for tensor-batched FRI (`entryCap = 1`) -/

section CompiledSpongeTensor

variable {F D : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D]
  [DecidableEq D]

/-- Challenge type of the `(P.batches + P.rounds + 2)`-step incremental sponge
tensor protocol: steps `0 .. P.batches - 1` absorb one input batch root each
(`PUnit`), and steps `P.batches + k` carry round `k`'s `GrindChal` over
`ChalTensor P.ldt W M P.queries`. -/
def SpongeChalTensor (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) : Type :=
  if i < P.batches then PUnit
  else GrindChal bits (ChalTensor P.ldt W M P.queries) (i - P.batches)

instance (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) :
    Fintype (SpongeChalTensor P W M bits i) := by
  unfold SpongeChalTensor
  split_ifs
  · exact inferInstanceAs (Fintype PUnit)
  · exact inferInstanceAs
      (Fintype (GrindChal bits (ChalTensor P.ldt W M P.queries) (i - P.batches)))

instance (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) (i : ℕ) :
    Nonempty (SpongeChalTensor P W M bits i) := by
  have : ∀ k, Nonempty (ChalTensor P.ldt W M P.queries k) :=
    PcsRbr.ChalTensor.nonempty P.domain_zero_nonempty W M P.queries
  unfold SpongeChalTensor
  split_ifs
  · exact ⟨()⟩
  · exact inferInstanceAs
      (Nonempty (GrindChal bits (ChalTensor P.ldt W M P.queries) (i - P.batches)))

omit [Fintype F] in
private theorem spongeChalTensor_add_eq (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) (k : ℕ) :
    SpongeChalTensor P W M bits (P.batches + k) =
      GrindChal bits (ChalTensor P.ldt W M P.queries) k := by
  unfold SpongeChalTensor
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

/-- Cast a sponge tensor challenge at step `P.batches + k` to round `k`'s `GrindChal`. -/
def spongeChalTensorCast (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChalTensor P W M bits (P.batches + k)) :
    GrindChal bits (ChalTensor P.ldt W M P.queries) k :=
  cast (spongeChalTensor_add_eq P W M bits k) c

/-- Inverse cast: round `k`'s `GrindChal` as a sponge tensor challenge at step `P.batches + k`. -/
def spongeChalTensorOf (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (ChalTensor P.ldt W M P.queries) k) :
    SpongeChalTensor P W M bits (P.batches + k) :=
  cast (spongeChalTensor_add_eq P W M bits k).symm c

omit [Fintype F] in
theorem spongeChalTensorCast_of (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : GrindChal bits (ChalTensor P.ldt W M P.queries) k) :
    spongeChalTensorCast P W M bits (spongeChalTensorOf P W M bits c) = c := by
  simp [spongeChalTensorCast, spongeChalTensorOf]

omit [Fintype F] in
theorem spongeChalTensorOf_cast (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) {k : ℕ}
    (c : SpongeChalTensor P W M bits (P.batches + k)) :
    spongeChalTensorOf P W M bits (spongeChalTensorCast P W M bits c) = c := by
  simp [spongeChalTensorCast, spongeChalTensorOf]

/-- Extract the `k`-round tensor `PcsRbr` transcript from a `(P.batches + k)`-step
incremental sponge transcript of `StepMsg`s. -/
noncomputable def extractPcsTensor (P : Params F) (W M : ℕ) (bits : ℕ → ℕ) :
    (k : ℕ) → Transcript (StepMsg F P.numClaims) (SpongeChalTensor P W M bits) (P.batches + k) →
      Transcript (PcsRbr.Msg F P.numClaims) (GrindChal bits (ChalTensor P.ldt W M P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t m c =>
    (extractPcsTensor P W M bits k t).snoc (extractStepPcsMsg P (extractBatchFn P t) k m)
      (spongeChalTensorCast P W M bits c)

/-- Lifted round-by-round `doomed` predicate for the `(P.batches + P.rounds + 2)`-step
incremental sponge tensor protocol. -/
def spongeDoomedTensor (P : Params F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) (i : ℕ)
    (t : Transcript (StepMsg F P.numClaims) (SpongeChalTensor P W M bits) i) : Prop :=
  if h : P.batches < i then
    PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries) (i - P.batches)
      (extractPcsTensor P W M bits (i - P.batches)
        (cast (by rw [Nat.add_sub_of_le (Nat.le_of_lt h)]) t))
  else True

omit [Fintype F] in
theorem spongeDoomedTensor_nil (P : Params F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) :
    spongeDoomedTensor P W M coord bits θ 0 .nil := by
  simp [spongeDoomedTensor]

omit [Fintype F] in
/-- Evaluating `spongeDoomedTensor` at `P.batches + (k + 1)` without casts. -/
theorem spongeDoomedTensor_add_succ (P : Params F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ) (θ : ℝ) (k : ℕ)
    (t : Transcript (StepMsg F P.numClaims) (SpongeChalTensor P W M bits) (P.batches + (k + 1))) :
    spongeDoomedTensor P W M coord bits θ (P.batches + (k + 1)) t ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries) (k + 1)
        (extractPcsTensor P W M bits (k + 1) t) := by
  unfold spongeDoomedTensor
  rw [dite_eq_left (by omega)]
  have hsub : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left P.batches (k + 1)
  have hgen : ∀ (n : ℕ) (hn : n = k + 1) (heq : P.batches + n = P.batches + (k + 1)),
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries) n
        (extractPcsTensor P W M bits n (cast (by rw [heq]) t)) ↔
      PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries) (k + 1)
        (extractPcsTensor P W M bits (k + 1) t) := by
    rintro n rfl heq
    rfl
  exact hgen _ hsub (Nat.add_sub_of_le (by omega))

/-- **Round-by-round soundness of the single-root incremental sponge tensor protocol.**
Absorption steps `< P.batches` have error `0`, and steps `P.batches + k` have
error `roundErrorTensor P.rounds ε₀ εβ θ P.queries k / 2 ^ bits k`. -/
theorem rbrSound_spongeTensor (P : Params F) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (hinj : ∀ j ≤ P.rounds, Function.Injective (coord j))
    (bits : ℕ → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ P.rounds, Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) W M θ (εα j))
    (hε₀ : ∀ j ≤ P.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i)) :
    RbrSound (P.batches + (P.rounds + 2)) (spongeDoomedTensor P W M coord bits θ)
      (fun i => if i < P.batches then 0
        else roundErrorTensor P.rounds ε₀ εβ θ P.queries (i - P.batches) /
          2 ^ bits (i - P.batches)) := by
  have hrbr := PcsRbr.rbrSound_grind_tensor P.ldt P.shift_ne coord hinj hθ P.queries bits
    hmca hε₀ hstep
  intro i hi t m hdoom
  by_cases hlt : i < P.batches
  · simp only [hlt, ↓reduceIte]
    refine FractionLE.false.mono_left fun c hc => hc ?_
    unfold spongeDoomedTensor
    rw [dite_eq_right (by omega)]
    trivial
  · simp only [hlt, ↓reduceIte]
    have hge : P.batches ≤ i := Nat.le_of_not_lt hlt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hge
    have hk_lt : k < P.rounds + 2 := by omega
    rw [Nat.add_sub_cancel_left]
    have hdoom0 : PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries) k
        (extractPcsTensor P W M bits k t) := by
      cases k with
      | zero =>
        exact PcsRbr.grindDoomed_nil (PcsRbr.doomedTensor_zero P.ldt P.shift coord θ P.queries _)
      | succ k' =>
        exact (spongeDoomedTensor_add_succ P W M coord bits θ k' t).mp hdoom
    have hfrac := hrbr k hk_lt (extractPcsTensor P W M bits k t)
      (extractStepPcsMsg P (extractBatchFn P t) k m) hdoom0
    obtain ⟨S, hScard, hSmem⟩ := hfrac
    refine ⟨S.map ⟨spongeChalTensorOf P W M bits, fun a b hab => by
        have := congrArg (spongeChalTensorCast P W M bits) hab
        simpa [spongeChalTensorCast_of] using this⟩, ?_, fun c hc => ?_⟩
    · rw [Finset.card_map]
      have hcardEq : Fintype.card (SpongeChalTensor P W M bits (P.batches + k)) =
          Fintype.card (GrindChal bits (ChalTensor P.ldt W M P.queries) k) :=
        Fintype.card_congr
          { toFun := spongeChalTensorCast P W M bits
            invFun := spongeChalTensorOf P W M bits
            left_inv := spongeChalTensorOf_cast P W M bits
            right_inv := spongeChalTensorCast_of P W M bits }
      rw [hcardEq]
      exact hScard
    · rw [Finset.mem_map]
      refine ⟨spongeChalTensorCast P W M bits c, hSmem _ ?_, spongeChalTensorOf_cast P W M bits c⟩
      intro hgood
      apply hc
      exact (spongeDoomedTensor_add_succ P W M coord bits θ k (t.snoc m c)).mpr hgood

end CompiledSpongeTensor

end CertiFri.Sponge

/-! ## Executable `Fri.verifyTensor` soundness under incremental sponge chaining (`c = 3 / 2`) -/

namespace CertiFri.Exec

open Oracle OracleComp Fri Sponge
open PcsRbr (TensorChal ChalTensor GrindChal ClaimsFail AcceptsTensor PowPasses ungrind
  roundErrorTensor tensorOf betasOfTensor queriesOfTensor)

section ExecSpongeTensor

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- Answer type of the incremental sponge oracle for `Fri.verifyTensor` with
single-root absorption (`batches` root-absorption steps + `rounds + 2` FRI
challenge rounds). -/
abbrev SpongeTensorOracleAnswer :=
  SpongeMerkleAnswer (RawMsg F EF D)
    (SpongeChalTensor (modelParams m params shape wf) (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape)) K D

/-- Public length of the post-commitments portion of `firstMessage` (`points` + `values`). -/
def firstMessageTailLen (params : FriParams) (shape : ClaimShape) : ℕ :=
  (pointRefs params.logBlowup shape).length + (claimRefs params.logBlowup shape).length

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
theorem firstMessageLen_eq_batches_add_tailLen (params : FriParams) (shape : ClaimShape) :
    firstMessageLen params shape = shape.length + firstMessageTailLen params shape := by
  unfold firstMessageLen firstMessageTailLen
  omega

/-- Extract the `k`-round tensor `GrindChal` transcript from the incremental sponge
transcript of an attempt, mapping round `j` to `f_view j`. -/
def spongeToGrindTranscriptTensor {P : Compiled.Params K} {W M : ℕ} {bits : ℕ → ℕ} {M' : Type}
    (f_view : ℕ → M') :
    (k : ℕ) → Oracle.Transcript (RawMsg F EF D) (SpongeChalTensor P W M bits) (P.batches + k) →
      Oracle.Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t _ c =>
    (spongeToGrindTranscriptTensor f_view k t).snoc (f_view k) (spongeChalTensorCast P W M bits c)

/-- Query the tensor sponge oracle at the current step and cast to `GrindChal`. -/
def spongeAnswerTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (s : SpongeState F EF D) :
    GrindChal bits (ChalTensor P.ldt W M P.queries) (s.step - P.batches) :=
  if h : P.batches ≤ s.step then
    spongeChalTensorCast P W M bits
      (cast (by rw [Nat.add_sub_of_le h]) (f (.chal s.step s.chain s.cur)).2)
  else
    have h0 : s.step - P.batches = 0 := Nat.sub_eq_zero_of_le (by omega)
    cast (by rw [h0]) (spongeChalTensorCast P W M bits (k := 0)
      (cast (by rw [Nat.add_zero]) (f (.chal P.batches s.chain s.cur)).2))

/-- **Idealised incremental sponge challenger for `Fri.verifyTensor`** with
single-root absorption (`entryCap = 1`). Handles both `kCol + kOpen > 0` and
the degenerate `kCol + kOpen = 0` (`W ≤ 1 ∧ M ≤ 1`) case cleanly via `tailLen`. -/
noncomputable def spongeChallengerTensor (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (m : FieldModel F EF K) : Challenger (SpongeState F EF D) F EF D where
  observe s o :=
    if s.nsamp = 0 then
      if s.step < P.batches then
        ⟨s.step + 1, (f (.chal s.step s.chain [o])).1, [], 0⟩
      else if s.step = P.batches ∧
          Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
          s.cur.length = tailLen then
        ⟨s.step + 1, (f (.chal s.step s.chain s.cur)).1, [o], 0⟩
      else
        { s with cur := s.cur ++ [o] }
    else
      ⟨s.step + 1, (f (.chal s.step s.chain s.cur)).1, [o], 0⟩
  sampleExt s :=
    let ans := spongeAnswerTensor P W M bits f s
    let val : K :=
      if s.step ≤ P.batches then
        let kCol := Fri.tensorNumChallenges W
        let kOpen := Fri.tensorNumChallenges M
        if h1 : s.nsamp < kCol then ans.2.tensor.1 ⟨s.nsamp, h1⟩
        else if h2 : s.nsamp - kCol < kOpen then ans.2.tensor.2 ⟨s.nsamp - kCol, h2⟩
        else 0
      else ans.2.field
    (Function.surjInv m.surj val, { s with nsamp := s.nsamp + 1 })
  sampleBits s _ :=
    let ans := spongeAnswerTensor P W M bits f s
    (if s.nsamp = 0 ∧ bits (s.step - P.batches) ≠ 0 then (ans.1 : ℕ)
      else P.indexOf (queryPointTensor P ans.2
        (s.nsamp - if bits (s.step - P.batches) = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

/-- **Executable `Fri.verifyTensor` against an incremental sponge oracle `f` from `s₀`.** -/
noncomputable def spongeAcceptsTensor (s₀ : D)
    (f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D) : Bool :=
  Fri.verifyTensor (merkleMmcs (inputHasher m (spongeHasherOf f)))
    (merkleMmcs (friHasher m (spongeHasherOf f)))
    (spongeChallengerTensor (modelParams m params shape wf) (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (firstMessageTailLen params shape)
      (powBits params shape) f m)
    (SpongeState.init s₀) params shape a.commitments a.points a.values a.proof

/-! ## Simulation between `spongeChallengerTensor` and `freeChallengerTensor` -/

private def foldSpongeListT {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) : List (Observation F EF D) → ℕ × D
  | [] => (step, chain)
  | o :: rest => foldSpongeListT f (step + 1) (f (.chal step chain [o])).1 rest

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeListT_append {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs ys : List (Observation F EF D)) :
    foldSpongeListT f step chain (xs ++ ys) =
      let p := foldSpongeListT f step chain xs
      foldSpongeListT f p.1 p.2 ys := by
  induction xs generalizing step chain with
  | nil => rfl
  | cons o xs ih => exact ih (step + 1) (f (.chal step chain [o])).1

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeListT_fst {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs : List (Observation F EF D)) :
    (foldSpongeListT f step chain xs).1 = step + xs.length := by
  induction xs generalizing step chain with
  | nil => simp [foldSpongeListT]
  | cons o xs ih =>
    simp only [foldSpongeListT, List.length_cons]
    rw [ih]
    omega

/-- Sponge state reached by running `f` along the `i` rounds of a full tensor transcript `t`. -/
def transcriptSpongeStateTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x) :
    {i : ℕ} → Oracle.Transcript (RawMsg F EF D)
      (GrindChal bits (ChalTensor P.ldt W M P.queries)) i → D
  | 0, .nil => s₀
  | 1, .snoc .nil m₀ _ =>
    let st := (foldSpongeListT f 0 s₀ (m₀.take P.batches)).2
    (f (.chal P.batches st (m₀.drop P.batches))).1
  | i + 2, .snoc t m _ =>
    let prev := transcriptSpongeStateTensor P W M bits s₀ f t
    (f (.chal (P.batches + (i + 1)) prev m)).1

/-- Lift a tensor sponge oracle `f` to the induced full-transcript `FSQuery` oracle. -/
def liftSpongeOracleTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x) :
    ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries)) (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries)) K D x
  | .other q => f (.other q)
  | .chal (i := 0) .nil m =>
    let st := (foldSpongeListT f 0 s₀ (m.take P.batches)).2
    spongeChalTensorCast P W M bits (f (.chal P.batches st (m.drop P.batches))).2
  | .chal (i := k + 1) t m =>
    let prev := transcriptSpongeStateTensor P W M bits s₀ f t
    spongeChalTensorCast P W M bits (f (.chal (P.batches + (k + 1)) prev m)).2

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K]
  [DecidableEq D] [Inhabited D] in
theorem hasherOf_liftSpongeOracleTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x) :
    hasherOf (liftSpongeOracleTensor P W M bits s₀ f) = spongeHasherOf f := rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem drop_firstMessage_eqT (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    (firstMessage (F := F) a.commitments a.points a.values).drop shape.length =
      a.points.toList.map .ext ++ a.values.toList.map .ext := by
  simp only [firstMessage, List.append_assoc]
  have hlen : (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))).length =
      shape.length := by
    simp [hcomm]
  rw [← hlen]
  exact List.drop_left' rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem spongeTranscript_succ_fstT {M' : Type} {C : ℕ → Type} {O : Type}
    {A : O → Type} (f : ∀ x : SpongeQuery M' D O, SpongeAnswer C D A x)
    (s₀ : D) (msgs : ℕ → M') (i : ℕ) :
    (spongeTranscript f s₀ msgs (i + 1)).1 =
      (spongeTranscript f s₀ msgs i).1.snoc (msgs i)
        (f (.chal i (spongeTranscript f s₀ msgs i).2 (msgs i))).2 := by
  change (match spongeTranscript f s₀ msgs i with
    | (t, prev) =>
      match f (.chal i prev (msgs i)) with
      | (next, c) => (t.snoc (msgs i) c, next)).1 = _
  rcases spongeTranscript f s₀ msgs i with ⟨t, prev⟩
  dsimp only
  rcases f (.chal i prev (msgs i)) with ⟨next, c⟩
  rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem spongeTranscript_succ_sndT {M' : Type} {C : ℕ → Type} {O : Type}
    {A : O → Type} (f : ∀ x : SpongeQuery M' D O, SpongeAnswer C D A x)
    (s₀ : D) (msgs : ℕ → M') (i : ℕ) :
    (spongeTranscript f s₀ msgs (i + 1)).2 =
      (f (.chal i (spongeTranscript f s₀ msgs i).2 (msgs i))).1 := by
  change (match spongeTranscript f s₀ msgs i with
    | (t, prev) =>
      match f (.chal i prev (msgs i)) with
      | (next, c) => (t.snoc (msgs i) c, next)).2 = _
  rcases spongeTranscript f s₀ msgs i with ⟨t, prev⟩
  dsimp only
  rcases f (.chal i prev (msgs i)) with ⟨next, c⟩
  rfl

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_prefix_eqT (s₀ : D)
    (f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k ≤ shape.length,
      (spongeTranscript f s₀ (a.spongeMessages params shape) k).2 =
        (foldSpongeListT f 0 s₀
          ((firstMessage (F := F) a.commitments a.points a.values).take k)).2
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := spongeTranscript_prefix_eqT s₀ f a hcomm k (by omega)
    have htake : (firstMessage (F := F) a.commitments a.points a.values).take (k + 1) =
        (firstMessage (F := F) a.commitments a.points a.values).take k ++
          [.digest (a.commitments.getD k default)] := by
      have hklt : k < (firstMessage (F := F) a.commitments a.points a.values).length := by
        simp [firstMessage, hcomm]; omega
      rw [List.take_succ_eq_append_getElem hklt]
      congr 1
      have hltc : k < (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))).length := by
        simp [hcomm]; omega
      simp only [firstMessage, List.append_assoc, List.getElem_append_left hltc, List.getElem_map]
      simp [Array.getD, show k < a.commitments.size by omega]
    rw [htake, foldSpongeListT_append]
    dsimp only
    have hfst : (foldSpongeListT f 0 s₀
        ((firstMessage (F := F) a.commitments a.points a.values).take k)).1 = k := by
      rw [foldSpongeListT_fst, Nat.zero_add, List.length_take, Nat.min_eq_left]
      simp [firstMessage, hcomm]; omega
    have hmsg : a.spongeMessages params shape k = [.digest (a.commitments.getD k default)] := by
      unfold Attempt.spongeMessages
      rw [ite_eq_left (by omega)]
    rw [hfst, foldSpongeListT, foldSpongeListT, spongeTranscript_succ_sndT, ih, hmsg]

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_eq_liftT (s₀ : D)
    (f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      (spongeTranscript f s₀ (a.spongeMessages params shape) (shape.length + k)).2 =
        (if k = 0 then
          (foldSpongeListT f 0 s₀
            ((firstMessage (F := F) a.commitments a.points a.values).take shape.length)).2
        else
          transcriptSpongeStateTensor (modelParams m params shape wf) (maxWidth shape)
            (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape) s₀ f
            (fsTranscript (liftSpongeOracleTensor (modelParams m params shape wf) (maxWidth shape)
              (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape) s₀ f)
              (a.messages params shape) k))
  | 0 => by
    simp only [Nat.add_zero, ↓reduceIte]
    exact spongeTranscript_prefix_eqT m params shape wf s₀ f a hcomm shape.length le_rfl
  | 1 => by
    have h0 := spongeTranscript_prefix_eqT m params shape wf s₀ f a hcomm shape.length le_rfl
    have hmsg : a.spongeMessages params shape shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length := by
      rw [drop_firstMessage_eqT shape a hcomm]
      unfold Attempt.spongeMessages
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    rw [spongeTranscript_succ_sndT, h0, hmsg]
    rfl
  | k + 2 => by
    have ih := spongeTranscript_eq_liftT s₀ f a hcomm (k + 1)
    simp only [Nat.succ_ne_zero, ↓reduceIte] at ih ⊢
    have hmsg : a.spongeMessages params shape (shape.length + (k + 1)) =
        a.messages params shape (k + 1) := by
      unfold Attempt.spongeMessages
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [show shape.length + (k + 2) = (shape.length + (k + 1)) + 1 by omega,
      spongeTranscript_succ_sndT, ih, hmsg]
    rfl

/-- Simulation relation between `FreeState` (under `liftSpongeOracleTensor`) and
`SpongeState` (under `spongeChallengerTensor`). -/
private def StateRelTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (fs : FreeState F EF D) (ss : SpongeState F EF D) : Prop :=
  (fs.round = 0 ∧ fs.nsamp = 0 ∧ fs.cur.length ≤ P.batches ∧
    ss = ⟨fs.cur.length, (foldSpongeListT f 0 s₀ fs.cur).2, [], 0⟩) ∨
  (fs.round = 0 ∧ P.batches ≤ fs.cur.length ∧
    ss = ⟨P.batches, (foldSpongeListT f 0 s₀ (fs.cur.take P.batches)).2,
      fs.cur.drop P.batches, fs.nsamp⟩) ∨
  (1 ≤ fs.round ∧
    ss = ⟨P.batches + fs.round,
      transcriptSpongeStateTensor P W M bits s₀ f
        (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) fs.hist fs.round),
      fs.cur, fs.nsamp⟩)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_observe (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss) (o : Observation F EF D) :
    StateRelTensor P W M bits s₀ f
      ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).observe fs o)
      ((spongeChallengerTensor P W M tailLen bits f m).observe ss o) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · dsimp only at hr hns hlen
    subst hr hns
    by_cases hlt : cur.length < P.batches
    · have hne_first : cur.length ≠ P.batches + tailLen := by omega
      have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
          ⟨0, hist, cur ++ [o], 0⟩ := by
        simp [freeChallengerTensor, hne_first]
      rw [hobs_f]
      left
      simp only [spongeChallengerTensor, hlt, ↓reduceIte, List.length_append, List.length_singleton]
      refine ⟨trivial, trivial, by omega, ?_⟩
      rw [foldSpongeListT_append]
      dsimp only
      rw [foldSpongeListT_fst, Nat.zero_add]
      rfl
    · have heq : cur.length = P.batches := by omega
      by_cases hadv : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧ tailLen = 0
      · obtain ⟨hz, htail0⟩ := hadv
        have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
          simp [freeChallengerTensor, hz, heq, htail0]
        have hss_eq : (⟨cur.length, (foldSpongeListT f 0 s₀ cur).2, [], 0⟩ : SpongeState F EF D) =
            ⟨P.batches, (foldSpongeListT f 0 s₀ cur).2, [], 0⟩ := by
          rw [heq]
        have hobs_s : (spongeChallengerTensor P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListT f 0 s₀ cur).2, [], 0⟩ o =
            ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListT f 0 s₀ cur).2 [])).1, [o], 0⟩ := by
          unfold spongeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _),
            ite_eq_left ⟨rfl, hz, by simp [htail0]⟩]
        rw [hobs_f, hss_eq, hobs_s]
        right; right
        refine ⟨le_rfl, ?_⟩
        simp only [fsTranscript, Function.update_self]
        change (⟨P.batches + 1, (f (.chal P.batches (foldSpongeListT f 0 s₀ cur).2 [])).1, [o], 0⟩ :
            SpongeState F EF D) =
          ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListT f 0 s₀ (cur.take P.batches)).2
            (cur.drop P.batches))).1, [o], 0⟩
        rw [← heq, List.take_length, List.drop_length]
      · have hnotf : ¬ (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
            cur.length = P.batches + tailLen) := by
          intro ⟨h1, h2⟩; exact hadv ⟨h1, by omega⟩
        have hnots : ¬ (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
            0 = tailLen) := by
          intro ⟨h1, h2⟩; exact hadv ⟨h1, h2.symm⟩
        have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨0, hist, cur ++ [o], 0⟩ := by
          unfold freeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (fun h => hnotf ⟨h.2.1, h.2.2⟩)]
        have hobs_s : (spongeChallengerTensor P W M tailLen bits f m).observe
              ⟨cur.length, (foldSpongeListT f 0 s₀ cur).2, [], 0⟩ o =
            ⟨cur.length, (foldSpongeListT f 0 s₀ cur).2, [o], 0⟩ := by
          unfold spongeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right hlt,
            ite_eq_right (fun h => hnots ⟨h.2.1, by simpa using h.2.2⟩)]
          rfl
        rw [hobs_f, hobs_s]
        right; left
        refine ⟨rfl, by simp; omega, ?_⟩
        rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
          ← heq, List.take_length, List.drop_length, List.nil_append]
  · dsimp only at hr hlen
    subst hr
    by_cases hns : nsamp = 0
    · subst hns
      by_cases hadv : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
          cur.length = P.batches + tailLen
      · obtain ⟨hz, hlen_eq⟩ := hadv
        have hdrop_len : (cur.drop P.batches).length = tailLen := by
          rw [List.length_drop]; omega
        have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
          simp [freeChallengerTensor, hz, hlen_eq]
        have hobs_s : (spongeChallengerTensor P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListT f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ o =
            ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListT f 0 s₀ (cur.take P.batches)).2
              (cur.drop P.batches))).1, [o], 0⟩ := by
          unfold spongeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _), ite_eq_left ⟨rfl, hz, hdrop_len⟩]
        rw [hobs_f, hobs_s]
        right; right
        refine ⟨le_rfl, ?_⟩
        simp only [fsTranscript, Function.update_self]
        rfl
      · have hnot_drop : ¬ (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
            (cur.drop P.batches).length = tailLen) := by
          rw [List.length_drop]
          intro ⟨h1, h2⟩; exact hadv ⟨h1, by omega⟩
        have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨0, hist, cur ++ [o], 0⟩ := by
          unfold freeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (fun h => hadv ⟨h.2.1, h.2.2⟩)]
        have hobs_s : (spongeChallengerTensor P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListT f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ o =
            ⟨P.batches, (foldSpongeListT f 0 s₀ (cur.take P.batches)).2,
              cur.drop P.batches ++ [o], 0⟩ := by
          unfold spongeChallengerTensor
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _),
            ite_eq_right (fun h => hnot_drop ⟨h.2.1, h.2.2⟩)]
        rw [hobs_f, hobs_s]
        right; left
        refine ⟨rfl, by simp; omega, ?_⟩
        rw [List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen]
    · have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨0, hist, cur, nsamp⟩ o =
          ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
        simp [freeChallengerTensor, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensor, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      simp only [fsTranscript, Function.update_self]
      rfl
  · dsimp only at hr
    by_cases hns : nsamp = 0
    · have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨round, hist, cur, nsamp⟩ o =
          ⟨round, hist, cur ++ [o], nsamp⟩ := by
        simp [freeChallengerTensor, hns, show round ≠ 0 by omega]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensor, hns, ↓reduceIte,
        show ¬ (P.batches + round < P.batches) by omega,
        show P.batches + round ≠ P.batches by omega, false_and]
      exact ⟨hr, trivial⟩
    · have hobs_f : (freeChallengerTensor P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensor P W M bits s₀ f) m).observe ⟨round, hist, cur, nsamp⟩ o =
          ⟨round + 1, Function.update hist round cur, [o], 0⟩ := by
        simp [freeChallengerTensor, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensor, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
      have hr' : round = k + 1 := by omega
      have hcongr : fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
          (Function.update hist round cur) round =
          fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) hist round :=
        Transcript.fsTranscript_congr _ fun j hj => Function.update_of_ne (by omega) _ _
      have heq_step : P.batches + round + 1 = P.batches + (round + 1) := by omega
      rw [heq_step]
      congr 1
      have hst : transcriptSpongeStateTensor P W M bits s₀ f
          (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            (Function.update hist round cur) (round + 1)) =
          (f (.chal (P.batches + round)
            (transcriptSpongeStateTensor P W M bits s₀ f
              (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) hist round)) cur)).1 := by
        rw [← hcongr]
        generalize hist = hh at *
        let t0 := fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            (Function.update hh round cur) round
        have hstep : fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            (Function.update hh round cur) (round + 1) =
            t0.snoc cur (liftSpongeOracleTensor P W M bits s₀ f (.chal t0 cur)) := by
          have hupd : Function.update hh round cur round = cur := Function.update_self round cur hh
          show t0.snoc (Function.update hh round cur round)
              (liftSpongeOracleTensor P W M bits s₀ f
                (.chal t0 (Function.update hh round cur round))) =
            t0.snoc cur (liftSpongeOracleTensor P W M bits s₀ f (.chal t0 cur))
          rw [hupd]
        rw [hstep]
        have h1 : ∀ (n : ℕ) (hn : n = k + 1)
            (t : Oracle.Transcript (RawMsg F EF D)
              (GrindChal bits (ChalTensor P.ldt W M P.queries)) n)
            (msg : RawMsg F EF D)
            (c : GrindChal bits (ChalTensor P.ldt W M P.queries) n),
            transcriptSpongeStateTensor P W M bits s₀ f (t.snoc msg c) =
              (f (.chal (P.batches + n) (transcriptSpongeStateTensor P W M bits s₀ f t) msg)).1 := by
          rintro n rfl t msg c
          rfl
        exact h1 round hr' t0 cur (liftSpongeOracleTensor P W M bits s₀ f (.chal t0 cur))
      exact hst.symm

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_observeAll (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (obs : List (Observation F EF D)) {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss) :
    StateRelTensor P W M bits s₀ f
      ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).observeAll fs obs)
      ((spongeChallengerTensor P W M tailLen bits f m).observeAll ss obs) := by
  induction obs generalizing fs ss with
  | nil => exact hrel
  | cons o obs ih => exact ih (stateRelTensor_observe m P W M tailLen bits s₀ f hrel o)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K] [DecidableEq D]
  [Inhabited D] in
private theorem freeAnswerTensor_eq_spongeAnswerTensor (P : Compiled.Params K) (W M : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ss.step - P.batches = fs.round ∧
      (ss.step ≤ P.batches ↔ fs.round = 0) ∧
      HEq (freeAnswerTensor P W M bits (liftSpongeOracleTensor P W M bits s₀ f) fs)
        (spongeAnswerTensor P W M bits f ss) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  dsimp only at hready hrel ⊢
  rcases hrel with ⟨hr, _, hlen, rfl⟩ | ⟨hr, _, rfl⟩ | ⟨hr, rfl⟩
  · subst hr
    dsimp only at hready hlen
    have heq : cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    have htake : cur.take P.batches = cur := by rw [← heq, List.take_length]
    have hdrop : cur.drop P.batches = [] := by rw [← heq, List.drop_length]
    have hss : (⟨cur.length, (foldSpongeListT f 0 s₀ cur).2, [], 0⟩ : SpongeState F EF D) =
        ⟨P.batches, (foldSpongeListT f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ := by
      simp [heq, htake, hdrop]
    rw [hss]
    refine ⟨by simp, by simp, ?_⟩
    unfold freeAnswerTensor spongeAnswerTensor
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracleTensor]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChalTensor P W M bits (P.batches + n))
        (b : SpongeChalTensor P W M bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalTensorCast P W M bits b) (spongeChalTensorCast P W M bits a) := by
      rintro n rfl a b hab
      rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · subst hr
    refine ⟨by simp, by simp, ?_⟩
    unfold freeAnswerTensor spongeAnswerTensor
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracleTensor]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChalTensor P W M bits (P.batches + n))
        (b : SpongeChalTensor P W M bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalTensorCast P W M bits b) (spongeChalTensorCast P W M bits a) := by
      rintro n rfl a b hab
      rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · dsimp only at hr
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
    have hr' : round = k + 1 := by omega
    subst hr'
    refine ⟨by dsimp only; omega, by dsimp only; constructor <;> intro h <;> omega, ?_⟩
    unfold freeAnswerTensor spongeAnswerTensor
    simp only [show P.batches ≤ P.batches + (k + 1) by omega, ↓reduceDIte, liftSpongeOracleTensor]
    have hstep : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left _ _
    have hgen2 : ∀ (n : ℕ) (hn : n = k + 1)
        (c : SpongeChalTensor P W M bits (P.batches + n)),
        HEq c (f (.chal (P.batches + (k + 1))
          (transcriptSpongeStateTensor P W M bits s₀ f
            (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) hist (k + 1))) cur)).2 →
        HEq (spongeChalTensorCast P W M bits (f (.chal (P.batches + (k + 1))
          (transcriptSpongeStateTensor P W M bits s₀ f
            (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) hist (k + 1))) cur)).2)
            (spongeChalTensorCast P W M bits c) := by
      rintro n rfl c hc
      rw [eq_of_heq hc]
    exact hgen2 _ hstep _ (cast_heq _ _)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_sampleExt (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).sampleExt fs).1 =
      ((spongeChallengerTensor P W M tailLen bits f m).sampleExt ss).1 ∧
    StateRelTensor P W M bits s₀ f
      ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).sampleExt fs).2
      ((spongeChallengerTensor P W M tailLen bits f m).sampleExt ss).2 := by
  obtain ⟨hstep, hle_iff, hans⟩ := freeAnswerTensor_eq_spongeAnswerTensor P W M bits s₀ f hrel hready
  have hns_eq : fs.nsamp = ss.nsamp := by
    rcases hrel with ⟨_, hns, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
    · exact hns
    · rfl
    · rfl
  have htens : (freeAnswerTensor P W M bits (liftSpongeOracleTensor P W M bits s₀ f) fs).2.tensor =
      (spongeAnswerTensor P W M bits f ss).2.tensor := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensor P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensor P.ldt W M P.queries) b),
        HEq x y → x.2.tensor = y.2.tensor := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  have hfield : (freeAnswerTensor P W M bits (liftSpongeOracleTensor P W M bits s₀ f) fs).2.field =
      (spongeAnswerTensor P W M bits f ss).2.field := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensor P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensor P.ldt W M P.queries) b),
        HEq x y → x.2.field = y.2.field := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨?_, ?_⟩
  · unfold freeChallengerTensor spongeChallengerTensor
    dsimp only
    by_cases hr0 : fs.round = 0
    · have hss_le : ss.step ≤ P.batches := hle_iff.mpr hr0
      simp only [hr0, hss_le, ↓reduceIte, hns_eq, htens]
    · have hss_gt : ¬ (ss.step ≤ P.batches) := fun h => hr0 (hle_iff.mp h)
      simp only [hr0, hss_gt, ↓reduceIte, hfield]
  · rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
    · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
      right; left
      refine ⟨hr, by dsimp only [freeChallengerTensor]; omega, ?_⟩
      simp only [freeChallengerTensor, spongeChallengerTensor, heq, hns]
      rw [← heq, List.take_length, List.drop_length]
    · right; left; exact ⟨hr, hlen, rfl⟩
    · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_sampleExtMany (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x) :
    ∀ (cnt : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensor P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (sampleExtMany (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m) cnt fs).1 =
        (sampleExtMany (spongeChallengerTensor P W M tailLen bits f m) cnt ss).1 ∧
      StateRelTensor P W M bits s₀ f
        (sampleExtMany (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m) cnt fs).2
        (sampleExtMany (spongeChallengerTensor P W M tailLen bits f m) cnt ss).2 ∧
      (1 ≤ (sampleExtMany (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m) cnt fs).2.round ∨
        P.batches ≤ (sampleExtMany (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m) cnt fs).2.cur.length)
  | 0, _, _, hrel, hready => ⟨rfl, hrel, hready⟩
  | cnt + 1, fs, ss, hrel, hready => by
    obtain ⟨h1, h2⟩ := stateRelTensor_sampleExt m P W M tailLen bits s₀ f hrel hready
    have hready1 : 1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).sampleExt fs).2.round ∨
        P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).sampleExt fs).2.cur.length := hready
    obtain ⟨hr1, hr2, hr3⟩ := stateRelTensor_sampleExtMany P W M tailLen bits s₀ f cnt h2 hready1
    exact ⟨by simp only [sampleExtMany, h1, hr1], hr2, hr3⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_sampleBits (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) (nbits : ℕ) :
    ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).sampleBits fs nbits).1 =
      ((spongeChallengerTensor P W M tailLen bits f m).sampleBits ss nbits).1 ∧
    StateRelTensor P W M bits s₀ f
      ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).sampleBits fs nbits).2
      ((spongeChallengerTensor P W M tailLen bits f m).sampleBits ss nbits).2 := by
  obtain ⟨hstep, _, hans⟩ := freeAnswerTensor_eq_spongeAnswerTensor P W M bits s₀ f hrel hready
  have hns_eq : fs.nsamp = ss.nsamp := by
    rcases hrel with ⟨_, hns, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
    · exact hns
    · rfl
    · rfl
  have hfst : ((freeAnswerTensor P W M bits (liftSpongeOracleTensor P W M bits s₀ f) fs).1 : ℕ) =
      ((spongeAnswerTensor P W M bits f ss).1 : ℕ) := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensor P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensor P.ldt W M P.queries) b),
        HEq x y → (x.1 : ℕ) = (y.1 : ℕ) := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  have hqp : ∀ k,
      queryPointTensor P (freeAnswerTensor P W M bits
        (liftSpongeOracleTensor P W M bits s₀ f) fs).2 k =
      queryPointTensor P (spongeAnswerTensor P W M bits f ss).2 k := by
    intro k
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensor P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensor P.ldt W M P.queries) b),
        HEq x y → queryPointTensor P x.2 k = queryPointTensor P y.2 k := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨by simp [freeChallengerTensor, spongeChallengerTensor, hstep, hns_eq, hfst, hqp], ?_⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    right; left
    refine ⟨hr, by dsimp only [freeChallengerTensor]; omega, ?_⟩
    simp only [freeChallengerTensor, spongeChallengerTensor, heq, hns]
    rw [← heq, List.take_length, List.drop_length]
  · right; left; exact ⟨hr, hlen, rfl⟩
  · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_checkWitness (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensor P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) (powBits : ℕ) (w : F) :
    ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).checkWitness fs powBits w).1 =
      ((spongeChallengerTensor P W M tailLen bits f m).checkWitness ss powBits w).1 ∧
    StateRelTensor P W M bits s₀ f
      ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).checkWitness fs powBits w).2
      ((spongeChallengerTensor P W M tailLen bits f m).checkWitness ss powBits w).2 ∧
    (1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).checkWitness fs powBits w).2.round ∨
      P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).checkWitness fs powBits w).2.cur.length) := by
  unfold Challenger.checkWitness
  have hokF : ∀ s, (freeChallengerTensor P W M (P.batches + tailLen) bits
      (liftSpongeOracleTensor P W M bits s₀ f) m).ok s = true := fun _ => rfl
  have hokS : ∀ s, (spongeChallengerTensor P W M tailLen bits f m).ok s = true := fun _ => rfl
  simp only [hokF, hokS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
  split_ifs with h0
  · exact ⟨rfl, hrel, hready⟩
  · have hobs := stateRelTensor_observe m P W M tailLen bits s₀ f hrel (.base w)
    have hready' : 1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).observe fs (.base w)).round ∨
        P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).observe fs (.base w)).cur.length := by
      simp only [freeChallengerTensor]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases hready with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by dsimp only; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hb1, hb2⟩ := stateRelTensor_sampleBits m P W M tailLen bits s₀ f hobs hready' powBits
    exact ⟨by simp [hb1], hb2, hready'⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensor_sampleIndices (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (nbits : ℕ) : ∀ (count : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensor P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).sampleIndices nbits count fs =
        (spongeChallengerTensor P W M tailLen bits f m).sampleIndices nbits count ss
  | 0, _, _, _, _ => rfl
  | count + 1, fs, ss, hrel, hready => by
    simp only [Challenger.sampleIndices]
    obtain ⟨h1, h2⟩ := stateRelTensor_sampleBits m P W M tailLen bits s₀ f hrel hready nbits
    rw [h1, stateRelTensor_sampleIndices P W M tailLen bits s₀ f nbits count h2 hready]

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] in
private theorem stateRelTensor_commitPhase (P : Compiled.Params K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensor P W M bits) K D x)
    (commitPowBits : ℕ) (commits : Array D) (witnesses : Array F) :
    ∀ (rounds : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensor P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).1 =
        (commitPhase (spongeChallengerTensor P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).1 ∧
      (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.1 =
        (commitPhase (spongeChallengerTensor P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).2.1 ∧
      StateRelTensor P W M bits s₀ f
        (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2
        (commitPhase (spongeChallengerTensor P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).2.2 ∧
      (1 ≤ (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.round ∨
        P.batches ≤ (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.cur.length)
  | 0, _, _, hrel, hready => ⟨rfl, rfl, hrel, hready⟩
  | r + 1, fs, ss, hrel, hready => by
    obtain ⟨h1, h2, h3, h4⟩ := stateRelTensor_commitPhase P W M tailLen bits s₀ f
      commitPowBits commits witnesses r hrel hready
    simp only [commitPhase]
    let fs_prev := (commitPhase (freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m)
        commitPowBits commits witnesses r fs).2.2
    have hobs := stateRelTensor_observe m P W M tailLen bits s₀ f h3 (.digest (commits.getD r default))
    have hready' : 1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).round ∨
        P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensor P W M bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).cur.length := by
      simp only [freeChallengerTensor]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases h4 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (by dsimp only [fs_prev] at *; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hw1, hw2, hw3⟩ := stateRelTensor_checkWitness m P W M tailLen bits s₀ f
      hobs hready' commitPowBits (witnesses.getD r 0)
    obtain ⟨he1, he2⟩ := stateRelTensor_sampleExt m P W M tailLen bits s₀ f hw2 hw3
    exact ⟨by rw [h1, he1], by rw [h2, hw1], he2, hw3⟩

omit [Fintype K] in
/-- **Exact refinement of `spongeAcceptsTensor` to `Exec.acceptsTensor (liftSpongeOracleTensor ...)`!** -/
theorem acceptsTensor_liftSpongeOracle_of_spongeAcceptsTensor (s₀ : D)
    (f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (h : spongeAcceptsTensor m params shape wf s₀ f a = true) :
    acceptsTensor m params shape wf
      (liftSpongeOracleTensor (modelParams m params shape wf) (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape) s₀ f) a = true := by
  unfold spongeAcceptsTensor Fri.verifyTensor at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  have hcomm : a.commitments.size = shape.length := by
    unfold Fri.shapeOk at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.1.2
  have hpts_sz : a.points.size = (pointRefs params.logBlowup shape).length := by
    unfold Fri.shapeOk at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.2
  have hvals_sz : a.values.size = (claimRefs params.logBlowup shape).length := by
    unfold Fri.shapeOk at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.2
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let tailLen := firstMessageTailLen params shape
  let bits := powBits params shape
  let fl := liftSpongeOracleTensor P W M bits s₀ f
  have hfl_len : firstMessageLen params shape = P.batches + tailLen :=
    firstMessageLen_eq_batches_add_tailLen params shape
  have hinit : StateRelTensor P W M bits s₀ f FreeState.init (SpongeState.init s₀) := by
    left; exact ⟨rfl, rfl, Nat.zero_le _, rfl⟩
  have hfirst := stateRelTensor_observeAll m P W M tailLen bits s₀ f
    (firstMessage (F := F) a.commitments a.points a.values) hinit
  have hfirst_len : (firstMessage (F := F) a.commitments a.points a.values).length =
      P.batches + tailLen := by
    simp only [firstMessage, List.length_append, List.length_map, Array.length_toList,
      hcomm, hpts_sz, hvals_sz, P, modelParams, tailLen, firstMessageTailLen]
    omega
  have hready0 : 1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll
        FreeState.init (firstMessage (F := F) a.commitments a.points a.values)).round ∨
      P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll
        FreeState.init (firstMessage (F := F) a.commitments a.points a.values)).cur.length := by
    right
    have hobs_cur : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
        fs.round = 0 → fs.nsamp = 0 → fs.cur.length + obs.length ≤ P.batches + tailLen →
        ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll fs obs).cur =
          fs.cur ++ obs ∧
        ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll fs obs).round = 0 ∧
        ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll fs obs).nsamp = 0 := by
      intro obs
      induction obs with
      | nil => intro fs hr hns _; simp [Challenger.observeAll, hr, hns]
      | cons o obs ih =>
        intro fs hr hns hlen
        have hlt : fs.cur.length < P.batches + tailLen := by simp at hlen; omega
        have hstep : (freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll
              fs (o :: obs) =
            (freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll
              { fs with cur := fs.cur ++ [o] } obs := by
          simp only [Challenger.observeAll, List.foldl_cons, freeChallengerTensor, hns, ↓reduceIte,
            show fs.cur.length ≠ P.batches + tailLen by omega, and_false]
        rw [hstep]
        obtain ⟨hcur, hr', hns'⟩ := ih { fs with cur := fs.cur ++ [o] } hr hns
          (by simp at hlen ⊢; omega)
        exact ⟨by simpa [List.append_assoc] using hcur, hr', hns'⟩
    have hc := (hobs_cur (firstMessage (F := F) a.commitments a.points a.values) FreeState.init
      rfl rfl (by simp [FreeState.init, hfirst_len])).1
    rw [hc]
    simp [FreeState.init, hfirst_len]
  -- Tensor schedule sampling (`colChallenges`, then `openChallenges`).
  obtain ⟨hcol1, hcol2, hcol3⟩ := stateRelTensor_sampleExtMany m P W M tailLen bits s₀ f
    (tensorNumChallenges W) hfirst hready0
  obtain ⟨hopen1, hopen2, hopen3⟩ := stateRelTensor_sampleExtMany m P W M tailLen bits s₀ f
    (tensorNumChallenges M) hcol2 hcol3
  have hsched1 : (TensorSchedule.sample
        (freeChallengerTensor P W M (P.batches + tailLen) bits fl m)
        ((freeChallengerTensor P W M (P.batches + tailLen) bits fl m).observeAll
          FreeState.init (firstMessage (F := F) a.commitments a.points a.values)) W M).1 =
      (TensorSchedule.sample (spongeChallengerTensor P W M tailLen bits f m)
        ((spongeChallengerTensor P W M tailLen bits f m).observeAll
          (SpongeState.init s₀) (firstMessage (F := F) a.commitments a.points a.values)) W M).1 := by
    dsimp only [fl, TensorSchedule.sample]
    rw [hcol1, hopen1]
  -- Commit phase.
  obtain ⟨hc1, hc2, hc3, hc4⟩ := stateRelTensor_commitPhase m P W M tailLen bits s₀ f
    params.commitPowBits a.proof.commitPhaseCommits a.proof.commitPowWitnesses
    (numRounds params shape) hopen2 hopen3
  -- Final polynomial absorption.
  have hfin := stateRelTensor_observeAll m P W M tailLen bits s₀ f
    (finalMessage (F := F) (D := D) (numRounds params shape) a.proof.finalPoly) hc3
  have hpres : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
      (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      1 ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).observeAll fs obs).round ∨
      P.batches ≤ ((freeChallengerTensor P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensor P W M bits s₀ f) m).observeAll fs obs).cur.length := by
    intro obs
    induction obs with
    | nil => intro fs h; exact h
    | cons o obs ih =>
      intro fs h
      refine ih _ ?_
      simp only [freeChallengerTensor]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by dsimp only; simp; omega)
      · exact Or.inl (by dsimp only; omega)
  have hready_fin := hpres
    (finalMessage (F := F) (D := D) (numRounds params shape) a.proof.finalPoly) _ hc4
  -- Query PoW witness and query indices.
  obtain ⟨hp1, hp2, hp3⟩ := stateRelTensor_checkWitness m P W M tailLen bits s₀ f hfin hready_fin
    params.queryPowBits a.proof.queryPowWitness
  have hidx := stateRelTensor_sampleIndices m P W M tailLen bits s₀ f
    (logMaxHeight params.logBlowup shape) params.numQueries hp2 hp3
  have htr : Fri.transcriptTensor
        (freeChallengerTensor P W M (P.batches + tailLen) bits fl m)
        FreeState.init params shape a.commitments a.points a.values a.proof =
      Fri.transcriptTensor (spongeChallengerTensor P W M tailLen bits f m)
        (SpongeState.init s₀) params shape a.commitments a.points a.values a.proof := by
    unfold Fri.transcriptTensor Fri.transcriptTailTensor
    dsimp only
    rw [hsched1]
    dsimp only [fl, TensorSchedule.sample]
    rw [hc1, hc2, hp1, hidx]
  unfold acceptsTensor Fri.verifyTensor
  rw [Bool.and_eq_true]
  refine ⟨hshape, ?_⟩
  change Fri.verifyWithTensor (merkleMmcs (inputHasher m (hasherOf fl)))
      (merkleMmcs (friHasher m (hasherOf fl))) params shape a.commitments a.points a.values
      a.proof (Fri.transcriptTensor (freeChallengerTensor P W M (firstMessageLen params shape)
        bits fl m) FreeState.init params shape a.commitments a.points a.values a.proof) = true
  rw [hfl_len, htr, hasherOf_liftSpongeOracleTensor P W M bits s₀ f]
  exact hwith

/-! ## Incremental sponge experiment & executable soundness for `Fri.verifyTensor` (`c = 3 / 2`) -/

variable [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D]

/-- Verify a tensor-batched proof against the sponge-derived transcript by lifting
`P.verifyWithTensor` (which only makes hash queries) into `SpongeTensorOracleAnswer`. -/
noncomputable def spongeVerifyTensor (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChalTensor (modelParams m params shape wf) (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape))
      ((modelParams m params shape wf).batches +
        ((modelParams m params shape wf).rounds + 2)) × D) :
    OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) Bool :=
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let bits := powBits params shape
  let tg := spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
    (fun j => view m params shape (a.messages params shape j)) (P.rounds + 2) ts.1
  @ite _ (PowPasses tg) (Classical.propDecidable _)
    (let tu := ungrind tg
    mapHashToSponge (M := RawMsg F EF D) (C := SpongeChalTensor P W M bits)
      (P.verifyWithTensor (M' := Empty) (C := fun _ => PUnit) W M (tensorCoord params shape)
        (modelProof m params shape a.proof) (Compiled.msgAt tu)
        (tensorOf tu) (betasOfTensor tu) (fun k => P.indexOf (queriesOfTensor tu k))))
    (.pure false)

omit [Fintype K] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
theorem queryBound_spongeVerifyTensor (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChalTensor (modelParams m params shape wf) (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape))
      ((modelParams m params shape wf).batches +
        ((modelParams m params shape wf).rounds + 2)) × D) :
    (spongeVerifyTensor m params shape wf a ts).QueryBound
      (modelParams m params shape wf).verifierQueries := by
  unfold spongeVerifyTensor
  dsimp only
  split
  · exact queryBound_mapHashToSponge
      ((modelParams m params shape wf).queryBound_verifyWithTensor _ _ _ _ _ _ _ _)
  · exact queryBound_pure _ _

/-- **The incremental sponge soundness experiment for `Fri.verifyTensor`.** -/
noncomputable def spongeExperimentTensor {A : Type*} (s₀ : D)
    (adv : OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) A)
    (attempt : A → Attempt F EF D) :
    OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) (A × Bool) :=
  (Oracle.spongeExperiment s₀
      ((modelParams m params shape wf).batches + ((modelParams m params shape wf).rounds + 2))
      adv (fun a => (attempt a).spongeMessages params shape)).bind fun out =>
    (spongeVerifyTensor m params shape wf (attempt out.1) out.2).bind fun b => .pure (out.1, b)

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem spongeToGrindTranscriptTensor_eq_fsTranscript (s₀ : D)
    (f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      spongeToGrindTranscriptTensor (P := modelParams m params shape wf)
        (W := maxWidth shape) (M := maxOpeningsPerHeight params.logBlowup shape)
        (bits := powBits params shape)
        (M' := Compiled.Msg K D (modelParams m params shape wf).batches)
        (fun j => view m params shape (a.messages params shape j)) k
        (spongeTranscript f s₀ (a.spongeMessages params shape)
          ((modelParams m params shape wf).batches + k)).1 =
      (fsTranscript
        (liftSpongeOracleTensor (modelParams m params shape wf) (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape) s₀ f)
        (a.messages params shape) k).mapIdx (fun _ msg =>
          (view m params shape msg : Compiled.Msg K D (modelParams m params shape wf).batches))
  | 0 => rfl
  | 1 => by
    let P := modelParams m params shape wf
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBits params shape
    have h0 : (spongeTranscript f s₀ (a.spongeMessages params shape) P.batches).2 =
        (foldSpongeListT f 0 s₀
          ((firstMessage (F := F) a.commitments a.points a.values).take P.batches)).2 :=
      spongeTranscript_prefix_eqT m params shape wf s₀ f a hcomm shape.length le_rfl
    have hmsg : a.spongeMessages params shape P.batches =
        (firstMessage (F := F) a.commitments a.points a.values).drop P.batches := by
      change a.spongeMessages params shape shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length
      rw [drop_firstMessage_eqT shape a hcomm]
      unfold Attempt.spongeMessages
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    have hsucc := spongeTranscript_succ_fstT f s₀ (a.spongeMessages params shape) P.batches
    change spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape (a.messages params shape j)) 1
        (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc .nil (view m params shape (a.messages params shape 0))
        (spongeChalTensorCast P W M bits (k := 0) (f (.chal P.batches
          (spongeTranscript f s₀ (a.spongeMessages params shape) P.batches).2
          (a.spongeMessages params shape P.batches))).2) =
      Oracle.Transcript.snoc .nil (view m params shape (a.messages params shape 0))
        (liftSpongeOracleTensor P W M bits s₀ f (.chal .nil (a.messages params shape 0)))
    rw [h0, hmsg]
    rfl
  | k + 2 => by
    let P := modelParams m params shape wf
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBits params shape
    have ih := spongeToGrindTranscriptTensor_eq_fsTranscript s₀ f a hcomm (k + 1)
    have hst : (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).2 =
        transcriptSpongeStateTensor P W M bits s₀ f
          (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) (a.messages params shape) (k + 1)) := by
      have h := spongeTranscript_eq_liftT m params shape wf s₀ f a hcomm (k + 1)
      simp only [Nat.succ_ne_zero, ↓reduceIte] at h
      exact h
    have hmsg : a.spongeMessages params shape (P.batches + (k + 1)) =
        a.messages params shape (k + 1) := by
      change a.spongeMessages params shape (shape.length + (k + 1)) = a.messages params shape (k + 1)
      unfold Attempt.spongeMessages
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    have hsucc := spongeTranscript_succ_fstT f s₀ (a.spongeMessages params shape)
      (P.batches + (k + 1))
    change spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape (a.messages params shape j)) (k + 2)
        (spongeTranscript f s₀ (a.spongeMessages params shape) ((P.batches + (k + 1)) + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc
        (spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
          (M' := Compiled.Msg K D P.batches)
          (fun j => view m params shape (a.messages params shape j)) (k + 1)
          (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).1)
        (view m params shape (a.messages params shape (k + 1)))
        (spongeChalTensorCast P W M bits (k := k + 1) (f (.chal (P.batches + (k + 1))
          (spongeTranscript f s₀ (a.spongeMessages params shape) (P.batches + (k + 1))).2
          (a.spongeMessages params shape (P.batches + (k + 1))))).2) =
      Oracle.Transcript.snoc
        ((fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) (a.messages params shape)
          (k + 1)).mapIdx (fun _ msg => (view m params shape msg : Compiled.Msg K D P.batches)))
        (view m params shape (a.messages params shape (k + 1)))
        (liftSpongeOracleTensor P W M bits s₀ f
          (.chal (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f) (a.messages params shape)
            (k + 1)) (a.messages params shape (k + 1))))
    rw [ih, hst, hmsg]
    rfl

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem extractPcsTensor_mapIdx_eq (a : Attempt F EF D)
    (c : D → Array Dimensions → ℕ → ℕ → Option (Array K)) :
    ∀ (k : ℕ)
      (t : Oracle.Transcript (RawMsg F EF D)
        (SpongeChalTensor (modelParams m params shape wf) (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape))
        ((modelParams m params shape wf).batches + k)),
      t.msgs = (List.range ((modelParams m params shape wf).batches + k)).map
        (a.spongeMessages params shape) →
      extractPcsTensor (modelParams m params shape wf) (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (powBits params shape) k
          (t.mapIdx fun j msg => spongeStepRead m params shape wf j msg c) =
        (spongeToGrindTranscriptTensor (P := modelParams m params shape wf)
            (W := maxWidth shape) (M := maxOpeningsPerHeight params.logBlowup shape)
            (bits := powBits params shape)
            (M' := Compiled.Msg K D (modelParams m params shape wf).batches)
            (fun j => view m params shape (a.messages params shape j)) k t).mapIdx
          fun j msg => (modelParams m params shape wf).read j msg c
  | 0, _, _ => rfl
  | k + 1, .snoc t' msg chal, hmsgs => by
    let P := modelParams m params shape wf
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBits params shape
    have hmsgs' : t'.msgs = (List.range (P.batches + k)).map (a.spongeMessages params shape) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.append_inj h1 (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).1
    have hmsg_eq : msg = a.spongeMessages params shape (P.batches + k) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      have hlast := (List.append_inj h1
        (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).2
      exact (List.cons.inj hlast).1
    change Oracle.Transcript.snoc
        (extractPcsTensor P W M bits k
          (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c))
        (extractStepPcsMsg P
          (extractBatchFn P (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c))
          k (spongeStepRead m params shape wf (P.batches + k) msg c))
        (spongeChalTensorCast P W M bits chal) =
      Oracle.Transcript.snoc
        ((spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
            (M' := Compiled.Msg K D P.batches)
            (fun j => view m params shape (a.messages params shape j)) k t').mapIdx
          fun j msg => P.read j msg c)
        (P.read k (view m params shape (a.messages params shape k)) c)
        (spongeChalTensorCast P W M bits chal)
    rw [extractPcsTensor_mapIdx_eq a c k t' hmsgs']
    congr 1
    cases k with
    | zero =>
      subst hmsg_eq
      change extractStepPcsMsg P (extractBatchFn P _) 0
          (spongeStepRead m params shape wf P.batches (a.spongeMessages params shape P.batches) c) =
        P.read 0 (view m params shape (a.messages params shape 0)) c
      have hread0 : spongeStepRead m params shape wf P.batches
          (a.spongeMessages params shape P.batches) c =
          .round0Meta (view m params shape (a.spongeMessages params shape P.batches)).points
            (view m params shape (a.spongeMessages params shape P.batches)).values := by
        unfold spongeStepRead
        dsimp only
        rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
      rw [hread0]
      change assembleClaims P (extractBatchFn P _)
          (view m params shape (a.spongeMessages params shape P.batches)).points
          (view m params shape (a.spongeMessages params shape P.batches)).values =
        assembleClaims P (fun b => c ((view m params shape (a.messages params shape 0)).inputRoots b))
          (view m params shape (a.messages params shape 0)).points
          (view m params shape (a.messages params shape 0)).values
      congr 1
      · funext b
        have hb : b.val < P.batches := b.isLt
        have hm_map : ∀ {i : ℕ} (u : Oracle.Transcript (RawMsg F EF D) (SpongeChalTensor P W M bits) i)
            (g : ℕ → RawMsg F EF D → StepMsg K P.numClaims),
            (u.mapIdx g).msgs = u.msgs.zipIdx.map fun p => g p.2 p.1 := by
          intro i u g
          induction u with
          | nil => rfl
          | snoc u _ _ ihu =>
            simp only [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu, List.zipIdx_append,
              List.map_append, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,
              u.length_msgs, Nat.zero_add]
        have hget : (t'.mapIdx fun j msg => spongeStepRead m params shape wf j msg c).msgs[b.val]? =
            some (spongeStepRead m params shape wf b.val (a.spongeMessages params shape b.val) c) := by
          rw [hm_map, List.getElem?_map, List.getElem?_zipIdx, hmsgs', List.getElem?_map,
            List.getElem?_range (by omega)]
          simp
        have hsr : spongeStepRead m params shape wf b.val (a.spongeMessages params shape b.val) c =
            .batchRoot (c (a.commitments.getD b.val default)) := by
          unfold spongeStepRead
          dsimp only
          rw [ite_eq_left (show b.val < (modelParams m params shape wf).batches from hb)]
          have hsm : a.spongeMessages params shape b.val =
              [.digest (a.commitments.getD b.val default)] := by
            unfold Attempt.spongeMessages
            rw [ite_eq_left (show b.val < shape.length from hb)]
          rw [hsm]
          rfl
        unfold extractBatchFn
        rw [hget, hsr]
        dsimp only
        have hfirst : (view m params shape (a.messages params shape 0)).inputRoots b =
            a.commitments.getD b.val default := by
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          change (digestsIn (a.messages params shape 0)).getD b.val default =
            a.commitments.getD b.val default
          rw [hm0]
          have hdig_append : ∀ l₁ l₂ : List (Observation F EF D),
              digestsIn (l₁ ++ l₂) = digestsIn l₁ ++ digestsIn l₂ := fun l₁ l₂ => by
            simp [digestsIn, List.filterMap_append]
          have hpts : digestsIn (a.points.toList.map (Observation.ext (F := F) (D := D))) = [] := by
            unfold digestsIn; induction a.points.toList <;> simp [*]
          have hvals : digestsIn (a.values.toList.map (Observation.ext (F := F) (D := D))) = [] := by
            unfold digestsIn; induction a.values.toList <;> simp [*]
          have hdigs : digestsIn (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) =
              a.commitments.toList := by
            unfold digestsIn; induction a.commitments.toList <;> simp [*]
          rw [firstMessage, hdig_append, hdig_append, hdigs, hpts, hvals,
            List.append_nil, List.append_nil]
          by_cases hlt : b.val < a.commitments.size <;>
            simp [Array.getD, List.getD_eq_getElem?_getD, hlt]
        rw [hfirst]
      · have hexts : extsIn m (a.spongeMessages params shape P.batches) =
            extsIn m (a.messages params shape 0) := by
          have hs : a.spongeMessages params shape P.batches =
              a.points.toList.map .ext ++ a.values.toList.map .ext := by
            change a.spongeMessages params shape shape.length = _
            unfold Attempt.spongeMessages
            rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          have hext_append : ∀ l₁ l₂ : List (Observation F EF D),
              extsIn m (l₁ ++ l₂) = extsIn m l₁ ++ extsIn m l₂ := fun l₁ l₂ => by
            simp [extsIn, List.filterMap_append]
          have hdigs : extsIn m (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) = [] := by
            unfold extsIn; induction a.commitments.toList <;> simp [*]
          rw [hs, hm0, firstMessage, hext_append, hext_append, hext_append, hdigs, List.nil_append]
        simp [view, hexts]
      · have hexts : extsIn m (a.spongeMessages params shape P.batches) =
            extsIn m (a.messages params shape 0) := by
          have hs : a.spongeMessages params shape P.batches =
              a.points.toList.map .ext ++ a.values.toList.map .ext := by
            change a.spongeMessages params shape shape.length = _
            unfold Attempt.spongeMessages
            rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
          have hm0 : a.messages params shape 0 =
              firstMessage (F := F) a.commitments a.points a.values := rfl
          have hext_append : ∀ l₁ l₂ : List (Observation F EF D),
              extsIn m (l₁ ++ l₂) = extsIn m l₁ ++ extsIn m l₂ := fun l₁ l₂ => by
            simp [extsIn, List.filterMap_append]
          have hdigs : extsIn m (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) = [] := by
            unfold extsIn; induction a.commitments.toList <;> simp [*]
          rw [hs, hm0, firstMessage, hext_append, hext_append, hext_append, hdigs, List.nil_append]
        simp [view, hexts]
    | succ k' =>
      subst hmsg_eq
      have hgt : ¬ (P.batches + (k' + 1) < P.batches) := by omega
      have hne : P.batches + (k' + 1) ≠ P.batches := by omega
      have hsub : P.batches + (k' + 1) - P.batches = k' + 1 := Nat.add_sub_cancel_left _ _
      have hmsg' : a.spongeMessages params shape (P.batches + (k' + 1)) =
          a.messages params shape (k' + 1) := by
        unfold Attempt.spongeMessages
        have hb : P.batches = shape.length := rfl
        rw [hb, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [hmsg']
      unfold spongeStepRead
      dsimp only
      rw [ite_eq_right hgt, ite_eq_right hne, hsub]
      rfl

/-- **Soundness of executable `Fri.verifyTensor` under incremental sponge chaining
(`c = 3 / 2`).** Whatever the adversary (making at most `Q` oracle queries),
the probability that `Fri.verifyTensor` accepts under the incremental sponge
challenger (`spongeAcceptsTensor`) while the committed claims fail is at most
`N * εmax + 3 * N ^ 2 / (2 * Fintype.card D)`,
where `N = Q + (batches + rounds + 2) + P.verifierQueries`. -/
theorem soundnessTensor_sponge (s₀ : D) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds,
      Tensor2DMCA ((twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n j).image
          ((modelParams m params shape wf).shift * ·))
        (2 ^ ((modelParams m params shape wf).rounds - j) *
          (modelParams m params shape wf).finalDegree)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) θ (εα j))
    (hε₀ : ∀ j ≤ (modelParams m params shape wf).rounds, εα j ≤ ε₀)
    (hstep : ∀ i < (modelParams m params shape wf).rounds,
      StepMCA (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n i)
        (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n (i + 1))
        (2 ^ ((modelParams m params shape wf).rounds - (i + 1)) *
          (modelParams m params shape wf).finalDegree) θ (εβ i))
    (hα : ε₀ ≤ εmax)
    (hβ : ∀ i < (modelParams m params shape wf).rounds,
      εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let bits := powBits params shape
  have hε0 : 0 ≤ εmax := (div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq
  have hε : ∀ i < P.batches + (P.rounds + 2),
      (if i < P.batches then 0
        else roundErrorTensor P.rounds ε₀ εβ θ P.queries (i - P.batches) /
          2 ^ bits (i - P.batches)) ≤ εmax := by
    intro i hi
    split_ifs with hlt
    · exact hε0
    · rcases hsub : i - P.batches with _ | k
      · rw [PcsRbr.roundErrorTensor_zero, show bits 0 = 0 from powBits_zero params shape,
          pow_zero, div_one]
        exact hα
      · by_cases hk : k < P.rounds
        · rw [PcsRbr.roundErrorTensor_succ_of_lt hk,
            show bits (k + 1) = params.commitPowBits from powBits_succ_of_lt params shape hk]
          exact hβ k hk
        · obtain rfl : k = P.rounds := by omega
          rw [PcsRbr.roundErrorTensor_last,
            show bits (P.rounds + 1) = params.queryPowBits from powBits_last params shape]
          exact hq
  have hbound := prob_spongeExperiment_bind_committedRow_le (s₀ := s₀)
    (r := P.batches + (P.rounds + 2))
    (rbrSound_spongeTensor P W M (tensorCoord params shape)
      (fun j _ => tensorCoord_injective params shape j) bits hθ hmca hε₀ hstep)
    hε hε0 (spongeDoomedTensor_nil P W M (tensorCoord params shape) bits θ)
    (stepDigestsOf := spongeStepDigests (F := F) (EF := EF) P) (M := 1) (by decide)
    (fun i _ msg => length_spongeStepDigests_le_one P i msg)
    (read := spongeStepRead m params shape wf)
    (fun j msg c c' hc => spongeStepRead_congr m params shape wf j msg c c' hc)
    hadv (fun a => (attempt a).spongeMessages params shape)
    (rest := fun out =>
      (spongeVerifyTensor m params shape wf (attempt out.1) out.2).bind fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (queryBound_spongeVerifyTensor m params shape wf (attempt out.1) out.2).bind
      (m := 0) fun _ => queryBound_pure _ _)
    (E := fun res l =>
      (∃ f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          spongeAcceptsTensor m params shape wf s₀ f (attempt res.1) = true) ∧
      ClaimsFail P.ldt P.shift θ
        (P.claims (view m params shape (firstMessage (attempt res.1).commitments
          (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
    fun out l res l' hexp hrun ⟨⟨f, hf, hacc⟩, hfail⟩ hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      have hcomm : (attempt out.1).commitments.size = shape.length := by
        unfold spongeAcceptsTensor Fri.verifyTensor Fri.shapeOk at hacc
        simp only [Bool.and_eq_true, beq_iff_eq] at hacc
        exact hacc.1.1.1.1.1.1.1.1.1.1.2
      have hacc_free := acceptsTensor_liftSpongeOracle_of_spongeAcceptsTensor m params shape wf s₀ f
        (attempt out.1) hacc
      have hmodel_true : (P.verifyGrindViewTensor W M (tensorCoord params shape) bits
          (view m params shape) (modelProof m params shape (attempt out.1).proof)
          (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))).run
          (liftSpongeOracleTensor P W M bits s₀ f) = true :=
        run_model_of_acceptsTensor m params shape wf
          (liftSpongeOracleTensor P W M bits s₀ f) (attempt out.1) hacc_free
      have hts : out.2 = spongeTranscript f s₀ ((attempt out.1).spongeMessages params shape)
          (P.batches + (P.rounds + 2)) := by
        have h1 := eq_spongeTranscript_of_outcome_spongeExperiment hexp hver.prefix f
        rwa [toFun_eq_self hf] at h1
      let tg := spongeToGrindTranscriptTensor (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => view m params shape ((attempt out.1).messages params shape j))
        (P.rounds + 2) out.2.1
      have htg_eq : tg = (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
          ((attempt out.1).messages params shape) (P.rounds + 2)).mapIdx
          (fun _ msg => (view m params shape msg : Compiled.Msg K D P.batches)) := by
        dsimp only [tg]
        rw [hts]
        exact spongeToGrindTranscriptTensor_eq_fsTranscript m params shape wf s₀ f (attempt out.1)
          hcomm (P.rounds + 2)
      have hb_true : b = true := by
        have hrun_f : (spongeVerifyTensor m params shape wf (attempt out.1) out.2).run f = b := by
          have := hver.run_toFun f
          rwa [toFun_eq_self hf] at this
        rw [← hrun_f]
        unfold spongeVerifyTensor
        dsimp only
        obtain ⟨hpow_fs, hvw⟩ :=
          (P.run_verifyGrindViewTensor W M (tensorCoord params shape) bits (view m params shape)
            (liftSpongeOracleTensor P W M bits s₀ f) _ _).mp hmodel_true
        have hpow_tg : PowPasses tg := by
          rw [htg_eq]
          exact (PcsRbr.powPasses_mapIdx _ _).mpr hpow_fs
        change (@ite _ (PowPasses tg) (Classical.propDecidable _)
            (mapHashToSponge (M := RawMsg F EF D) (C := SpongeChalTensor P W M bits)
              (P.verifyWithTensor (M' := Empty) (C := fun _ => PUnit) W M (tensorCoord params shape)
                (modelProof m params shape (attempt out.1).proof) (Compiled.msgAt (ungrind tg))
                (tensorOf (ungrind tg)) (betasOfTensor (ungrind tg))
                (fun k => P.indexOf (queriesOfTensor (ungrind tg) k))))
            (.pure false)).run f = true
        rw [ite_eq_left hpow_tg, run_mapHashToSponge]
        have hrun_vw := P.run_verifyWithTensor W M (tensorCoord params shape) (projHashFun f)
          (modelProof m params shape (attempt out.1).proof)
          (Compiled.msgAt (ungrind tg)) (tensorOf (ungrind tg)) (betasOfTensor (ungrind tg))
          (fun k => P.indexOf (queriesOfTensor (ungrind tg) k))
        have hrun_fs := P.run_verifyWithTensor W M (tensorCoord params shape)
          (liftSpongeOracleTensor P W M bits s₀ f)
          (modelProof m params shape (attempt out.1).proof)
          (fun j => view m params shape (Compiled.msgAt (ungrind (fsTranscript
            (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))) j))
          (tensorOf (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))))
          (betasOfTensor (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))))
          (fun k => P.indexOf (queriesOfTensor (ungrind (fsTranscript
            (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))) k))
        rw [hrun_vw]
        rw [hrun_fs] at hvw
        have hhash_eq : hasherOf (projHashFun f) =
            hasherOf (liftSpongeOracleTensor P W M bits s₀ f) := rfl
        let vP : RawMsg F EF D → Compiled.Msg K D P.batches := view m params shape
        have htu_eq : ungrind tg = (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
            ((attempt out.1).messages params shape) (P.rounds + 2))).mapIdx
            (fun _ msg => vP msg) := by
          rw [htg_eq]
          exact PcsRbr.ungrind_mapIdx _ _
        have hmsgs_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
            (u : Oracle.Transcript M₁ C n) (g : M₁ → M₂),
            (u.mapIdx fun _ msg => g msg).msgs = u.msgs.map g := by
          intro M₁ M₂ C n u g
          induction u with
          | nil => rfl
          | snoc u _ _ ihu => simp [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu]
        have hmsgAt_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
            (u : Oracle.Transcript M₁ C (n + 1)) (g : M₁ → M₂) (j : ℕ),
            Compiled.msgAt (u.mapIdx fun _ msg => g msg) j = g (Compiled.msgAt u j) := by
          intro M₁ M₂ C n u g j
          cases u with
          | snoc u' msg ch =>
            simp only [Transcript.mapIdx_snoc, Compiled.msgAt, hmsgs_map,
              List.getD_eq_getElem?_getD, List.getElem?_map]
            cases u'.msgs[j]? <;> rfl
        have hmsg_eq : Compiled.msgAt (ungrind tg) =
            fun j => vP (Compiled.msgAt (ungrind (fsTranscript
              (liftSpongeOracleTensor P W M bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) j) := by
          funext j
          rw [htu_eq]
          exact hmsgAt_map _ vP j
        have ht_eq : tensorOf (ungrind tg) =
            tensorOf (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.tensorOf_mapIdx _ _
        have hβ_eq : betasOfTensor (ungrind tg) =
            betasOfTensor (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.betasOfTensor_mapIdx _ _
        have hq_eq : queriesOfTensor (ungrind tg) =
            queriesOfTensor (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
              ((attempt out.1).messages params shape) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.queriesOfTensor_mapIdx _ _
        rw [hhash_eq, hmsg_eq, ht_eq, hβ_eq, hq_eq]
        exact hvw
      subst hb_true
      unfold spongeVerifyTensor at hver
      dsimp only at hver
      split at hver
      · next hpow_tg =>
        have hproj_out := outcome_projHashLog hver
        have hnocol_proj : ¬ LogCollision hashObs (projHashLog l') := fun hc =>
          not_logCollision_sponge_of_not_jointHit hno (logCollision_projHashLog_iff.mp hc)
        have hacc_pcs := P.acceptsTensor_of_outcome_verifyWithTensor_view id (ungrind tg)
          hproj_out hnocol_proj
        rw [committedRow_projHashLog] at hacc_pcs
        obtain ⟨_, -, hder⟩ := outcome_spongeExperiment hexp
        obtain ⟨_, hmsgs⟩ := outcome_spongeDerive_supports hder
        have hextr : extractPcsTensor P W M bits (P.rounds + 2)
            (out.2.1.mapIdx fun j msg => spongeStepRead m params shape wf j msg (spongeCommittedRow l')) =
            tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          extractPcsTensor_mapIdx_eq m params shape wf (attempt out.1)
            (spongeCommittedRow l') (P.rounds + 2) out.2.1 hmsgs
        rw [spongeDoomedTensor_add_succ P W M (tensorCoord params shape) bits θ (P.rounds + 1), hextr]
        have hungrind_tg : ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l')) =
            (ungrind tg).mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          PcsRbr.ungrind_mapIdx _ tg
        refine PcsRbr.not_grindDoomedTensor_of_accepts _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow_tg)
          ?_ ?_
        · let vP : RawMsg F EF D → Compiled.Msg K D P.batches := view m params shape
          have h0 : (ungrind tg).msgs[0]? =
              some (vP ((attempt out.1).messages params shape 0)) := by
            have hu : ungrind tg = (ungrind (fsTranscript (liftSpongeOracleTensor P W M bits s₀ f)
                ((attempt out.1).messages params shape) (P.rounds + 2))).mapIdx
                (fun _ msg => vP msg) := by
              rw [htg_eq]
              exact PcsRbr.ungrind_mapIdx _ _
            have hmsgs_map : ∀ {M₁ M₂ : Type} {C : ℕ → Type} {n : ℕ}
                (u : Oracle.Transcript M₁ C n) (g : M₁ → M₂),
                (u.mapIdx fun _ msg => g msg).msgs = u.msgs.map g := by
              intro M₁ M₂ C n u g
              induction u with
              | nil => rfl
              | snoc u _ _ ihu => simp [Transcript.mapIdx_snoc, Transcript.msgs_snoc, ihu]
            rw [hu, hmsgs_map _ vP, Compiled.msgs_ungrind, fsTranscript_msgs,
              List.getElem?_map, List.getElem?_map, List.getElem?_range (Nat.succ_pos _)]
            rfl
          change ClaimsFail P.ldt P.shift θ
            (PcsRbr.claimsOf (ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l'))))
          rw [hungrind_tg, PcsRbr.claimsOf_mapIdx _ (ungrind tg) h0]
          exact hfail
        · exact Eq.mpr
            (congrArg (fun u => AcceptsTensor P.ldt P.shift (tensorCoord params shape) u)
              hungrind_tg)
            hacc_pcs
      · exact absurd (outcome_pure.mp hver).1 (by simp)
  have hcast : ((Q : ℝ) + ((P.batches + (P.rounds + 2) : ℕ) : ℝ) + P.verifierQueries) =
      (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    push_cast; ring
  rw [hcast] at hbound
  exact hbound

/-- **Unconditional unique-decoding soundness of executable `Fri.verifyTensor` under
incremental sponge chaining (`c = 3 / 2`).**
The tensor batching error is linear in `kCol + kOpen` (logarithmic in total
claims `W * M`) and independent of the number of heights. -/
theorem soundnessTensor_sponge_uniqueDecoding (s₀ : D)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift (1 - δ)
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hθ : 0 ≤ 1 - δ := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) W M (1 - δ)
        (((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K)) := by
    intro j hj
    refine tensor2DMCA_ud _ _ W M hδ ?_
    have hcard : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card =
        2 ^ params.logBlowup * (2 ^ (P.rounds - j) * P.finalDegree) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj
    have hinv : (2 : ℝ) ^ params.logBlowup * (1 / 2 : ℝ) ^ params.logBlowup = 1 := by
      rw [← mul_pow]; norm_num
    have hdeg_le : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) =
        (1 / 2 : ℝ) ^ params.logBlowup *
          (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
      rw [hcard]; push_cast
      linear_combination -((2 : ℝ) ^ (P.rounds - j) * (P.finalDegree : ℝ)) * hinv
    rw [hdeg_le]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card]
  have hε₀ : ∀ j ≤ P.rounds,
      ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K) ≤
        ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K := by
    intro j hj
    have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne),
        card_twoAdicDomain P.prim (hj.trans P.rounds_le)]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le P.n j) :
        2 ^ (P.n - j) ≤ 2 ^ P.n)
    have hmul : ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) ≤
        ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * (2 : ℝ) ^ P.n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard_le (by linarith))
        (Nat.cast_nonneg _)
    calc ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K)
        = ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            ((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K := by
          ring
      _ ≤ ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K :=
          div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ)
        (((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) :=
    fun i hi => P.stepMCA_of_rate_of_curveCA (curveCA_udThreshold (F := K)) hn rfl hδ hrate hi
  exact soundnessTensor_sponge m params shape wf s₀ hθ hmca hε₀ hstep hα (fun _ _ => hβ) hq hadv
    attempt

/-- **Johnson-regime soundness of executable `Fri.verifyTensor` under incremental
sponge chaining (`c = 3 / 2`) from `CurveListCA K T` alone** (no
`BatchedLineListCA` assumption needed). Applies `tensor2DMCA_of_curveMCA_two`
(union bound across the `2 ^ (kCol + kOpen) - 1` single-line halvings), yielding
single-level max batching error
`(2 ^ (kCol + kOpen) - 1) * (cT + L_J * (1 - θ) * 2 ^ n) / |K|`. -/
theorem soundnessTensor_sponge_johnson_of_curveListCA (s₀ : D) {T : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hca : CurveListCA K T)
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT : ∀ (j k : ℕ), j ≤ numRounds params shape → 2 ≤ k →
      (T (2 ^ (logMaxHeight params.logBlowup shape - j))
        (2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - j)⌉₊ k : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K ≤ εmax)
    (hβ : (2 * cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor m params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor m params shape wf s₀ adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        3 * ((Q : ℝ) + ((modelParams m params shape wf).batches +
            ((modelParams m params shape wf).rounds + 2)) +
          (modelParams m params shape wf).verifierQueries) ^ 2 / (2 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  let LJ : ℝ := (θ - ρ) / (θ ^ 2 - ρ)
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hfinal : P.finalDegree = 2 ^ params.logFinalPolyLen := rfl
  have hLJ_nn : 0 ≤ LJ := by
    have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
    have hnum : 0 ≤ θ - ρ := by nlinarith
    exact div_nonneg hnum hden.le
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  have hdeg_le : ∀ j ≤ P.rounds,
      ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * ((twoAdicDomain P.ω P.n j).card : ℝ) := by
    intro j hj
    rw [hfinal, Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj]
    push_cast
    have h1 : ρ * (2 : ℝ) ^ params.logBlowup = 1 := by
      dsimp only [ρ]; rw [← mul_pow]; norm_num
    rw [← mul_assoc, h1, one_mul]
  have hcard_dom : ∀ j ≤ P.rounds, (twoAdicDomain P.ω P.n j).card = 2 ^ (P.n - j) :=
    fun j hj => card_twoAdicDomain P.prim (by omega)
  let εline : ℝ := (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  let εβ : ℕ → ℝ := fun _ => (2 * cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hline_nn : 0 ≤ εline := by
    dsimp only [εline]; positivity
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) W M θ
        (((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) * εline) := by
    intro j hj
    have hcard_img : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card = 2 ^ (P.n - j) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), hcard_dom j hj]
    have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
      rw [hcard_img]
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le P.n j)
    have hd_img : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) ≤
        ρ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hdeg_le j hj
    have hTj : (T ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card
        (2 ^ (P.rounds - j) * P.finalDegree)
        ⌈θ * (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ)⌉₊ 2 : ℝ) ≤
        ((2 - 1 : ℕ) : ℝ) * cT := by
      rw [hcard_img, hfinal]
      push_cast
      have h := hT j 2 hj le_rfl
      norm_num at h
      simpa [P, modelParams] using h
    have hcurve := curveMCA_of_curveListCA_of_card_le hca
      ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) 2
      hθ0 hθ1 hd_img hgap (by positivity) hTj hcard_le
    have hcurve' : CurveMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) 2 θ εline := by
      refine ProximityGap.curveMCA_mono hcurve le_rfl ?_
      dsimp only [εline, LJ, ρ]
      exact le_of_eq (by norm_num)
    exact tensor2DMCA_of_curveMCA_two hcurve'
  have hε₀ : ∀ j ≤ P.rounds,
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) * εline ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) *
          (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K := by
    intro _ _
    have hsub_le : ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ 1
    calc ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) * εline
        ≤ ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) * εline :=
          mul_le_mul_of_nonneg_right hsub_le hline_nn
      _ = ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) *
            (cT + LJ * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K := by
          dsimp only [εline]; ring
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i) := by
    intro i hi
    have hi1 : i + 1 ≤ P.rounds := hi
    have hn1 : 1 ≤ P.n := by omega
    have hcard_i1 : (twoAdicDomain P.ω P.n (i + 1)).card = 2 ^ (P.n - (i + 1)) :=
      hcard_dom (i + 1) hi1
    have hcard_le : ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ) ≤ (2 : ℝ) ^ (P.n - 1) := by
      rw [hcard_i1]
      exact_mod_cast Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have hTi : (T (twoAdicDomain P.ω P.n (i + 1)).card
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
        ⌈θ * ((twoAdicDomain P.ω P.n (i + 1)).card : ℝ)⌉₊ 3 : ℝ) ≤ 2 * cT := by
      rw [hcard_i1, hfinal]
      push_cast
      have h := hT (i + 1) 3 hi1 (by omega)
      norm_num at h
      exact h
    have hst := stepMCA_of_curveListCA_of_card_le hca (P.ldt.step i hi)
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree)
      hθ0 hθ1 (hdeg_le (i + 1) hi1) hgap (by positivity) hTi hcard_le
    have h2pow : 2 * (2 : ℝ) ^ (P.n - 1) = (2 : ℝ) ^ P.n := by
      conv_rhs => rw [← Nat.sub_add_cancel hn1, pow_succ']
    have heq : (2 * cT + 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1)))) / Fintype.card K = εβ i := by
      dsimp only [εβ]
      have : 2 * (LJ * ((1 - θ) * (2 : ℝ) ^ (P.n - 1))) =
          LJ * ((1 - θ) * (2 * (2 : ℝ) ^ (P.n - 1))) := by ring
      rw [this, h2pow]
    rwa [heq] at hst
  exact soundnessTensor_sponge m params shape wf s₀ hθ0.le hmca hε₀ hstep hα (fun _ _ => hβ) hq
    hadv attempt

end ExecSpongeTensor

end CertiFri.Exec

/-! ## Concrete `GoldilocksExt3` instantiations (`Digest` 32B BLAKE3 & `Digest64` 64B BLAKE2b-512) -/

namespace CertiFri.P3.Exec

open CertiFri.Exec CertiFri.Fri CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.PcsRbr

/-- **32-byte `BLAKE3-256` (`Digest`) incremental-sponge unconditional UD soundness for
executable `Fri.verifyTensor` over `GoldilocksExt3`** in the classical ROM.
Gives collision term `3 * N ^ 2 / (2 * 2 ^ 256)` (`127.71`-bit classical BCS
collision threshold) and tensor batching error linear in `kCol + kOpen`. -/
theorem goldilocksExt3_soundnessTensor_sponge_uniqueDecoding
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((Fri.tensorNumChallenges (Fri.maxWidth shape) +
          Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (1 - δ)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * (2 : ℝ) ^ 256) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hcardD : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 256 := by
    rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hcardD] using soundnessTensor_sponge_uniqueDecoding goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) s₀ hheight hδ hrate
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

/-- **64-byte RFC 7693 `BLAKE2b-512` (`Digest64`) incremental-sponge unconditional UD
soundness for executable `Fri.verifyTensor` over `GoldilocksExt3`** in the classical
ROM (`|Digest64| = 2 ^ 512`), giving collision term `3 * N ^ 2 / (2 * 2 ^ 512)`. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (s₀ : Digest64)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((Fri.tensorNumChallenges (Fri.maxWidth shape) +
          Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
        ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax)
    {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (1 - δ)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * (2 : ℝ) ^ 512) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hcardD : (Fintype.card Digest64 : ℝ) = (2 : ℝ) ^ 512 := by
    rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hcardD] using soundnessTensor_sponge_uniqueDecoding goldilocksExt3_fieldModel params shape
    (goldilocksExt3_wellFormed params shape hmax) s₀ hheight hδ hrate
    (by rwa [hcard]) (by rwa [hcard]) hq hadv attempt

private theorem tensor_ud_alpha_le_three_quarters_128
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hW : Fri.maxWidth shape ≤ 2 ^ 16)
    (hM : Fri.maxOpeningsPerHeight params.logBlowup shape ≤ 2 ^ 16) :
    ((Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
      ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
      ((Goldilocks.order : ℝ) ^ 3) ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hkW : Fri.tensorNumChallenges (Fri.maxWidth shape) ≤ 16 :=
    tensorNumChallenges_le_of_le_pow hW
  have hkM : Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) ≤ 16 :=
    tensorNumChallenges_le_of_le_pow hM
  have hkSum : ((Fri.tensorNumChallenges (Fri.maxWidth shape) +
      Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) ≤ 32 := by
    exact_mod_cast (by omega :
      Fri.tensorNumChallenges (Fri.maxWidth shape) +
      Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) ≤ 32)
  have h2n : (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 32 := by
    exact_mod_cast Nat.pow_le_pow_right two_pos hmax
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have hnum : ((Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
      ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) ≤
      32 * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) := by
    have h1 : (1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤
        (11 / 8 : ℝ) * (2 : ℝ) ^ 32 := by nlinarith
    exact mul_le_mul hkSum h1 (by positivity) (by norm_num)
  refine (div_le_div₀ (by positivity) hnum (by positivity) h191).trans ?_
  have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  have hconst : (32 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by
    norm_num
  rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
  exact mul_le_mul_of_nonneg_right hconst hpos128.le

private theorem tensor_ud_beta_le_three_quarters_128
    (params : FriParams) (shape : ClaimShape)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32) :
    ((1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape) /
      ((Goldilocks.order : ℝ) ^ 3) / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have h2n : (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤ (2 : ℝ) ^ 32 := by
    exact_mod_cast Nat.pow_le_pow_right two_pos hmax
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
    exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
  have hnum : (1 + (3 / 8 : ℝ)) * (2 : ℝ) ^ Fri.logMaxHeight params.logBlowup shape ≤
      (11 / 8 : ℝ) * (2 : ℝ) ^ 32 := by nlinarith
  refine (div_le_self (by positivity) hpow1).trans
    ((div_le_div₀ (by positivity) hnum (by positivity) h191).trans ?_)
  have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
  rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
  have hconst : (11 / 8 : ℝ) * (2 : ℝ) ^ 32 ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by norm_num
  rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
  exact mul_le_mul_of_nonneg_right hconst hpos128.le

/-- **Concrete 32-byte `BLAKE3-256` (`Digest`) unconditional unique-decoding
soundness for executable `Fri.verifyTensor` over `GoldilocksExt3`** at
`(logBlowup = 2, numQueries = 160, queryPowBits = 20)` for ANY width `W ≤ 2 ^ 16`,
ANY opening count `M ≤ 2 ^ 16`, and ANY `logMaxHeight ≤ 32`:
`(3 / 4) * N / 2 ^ 128 + 3 * N ^ 2 / (2 * 2 ^ 256)`. -/
theorem goldilocksExt3_soundnessTensor_sponge_uniqueDecoding_128_blake3
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : params.numQueries = 160) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hW : Fri.maxWidth shape ≤ 2 ^ 16)
    (hM : Fri.maxOpeningsPerHeight params.logBlowup shape ≤ 2 ^ 16)
    (s₀ : Digest) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256) := by
  intro wf P N
  have hrate : 2 * (3 / 8 : ℝ) + (1 / 2) ^ params.logBlowup ≤ 1 := by
    rw [hbl]; norm_num
  have hεq : (1 - (3 / 8 : ℝ)) ^ params.numQueries / 2 ^ params.queryPowBits ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hqn, hqpow, show (1 - 3 / 8 : ℝ) = 5 / 8 by norm_num]
    exact ud_160_pow20_le_three_quarters_128
  have hmain := goldilocksExt3_soundnessTensor_sponge_uniqueDecoding params shape hmax hheight s₀
    (δ := 3 / 8) (by norm_num) hrate (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (tensor_ud_alpha_le_three_quarters_128 params shape hmax hW hM)
    (tensor_ud_beta_le_three_quarters_128 params shape hmax)
    hεq hadv attempt
  dsimp only at hmain
  have h58 : (1 - (3 / 8 : ℝ)) = 5 / 8 := by norm_num
  rw [h58] at hmain
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rwa [← hNcast] at hmain

/-- **Literal `≤ N / 2 ^ 128` unconditional unique-decoding soundness for executable
`Fri.verifyTensor`** over `GoldilocksExt3` with 64-byte RFC 7693 `BLAKE2b-512`
(`Digest64`), incremental sponge chaining (`c = 3 / 2`), and
`(logBlowup = 2, numQueries = 160, commitPowBits = 0, queryPowBits = 20)`.
Holds for EVERY query budget `N ≤ 2 ^ 128`, ANY width `W ≤ 2 ^ 16`, ANY opening
count `M ≤ 2 ^ 16`, and ANY `logMaxHeight ≤ 32` — with ZERO unproven proximity
assumptions! -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding_128
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : params.numQueries = 160) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (hW : Fri.maxWidth shape ≤ 2 ^ 16)
    (hM : Fri.maxOpeningsPerHeight params.logBlowup shape ≤ 2 ^ 16)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
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
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (5 / 8)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf P N
  have hrate : 2 * (3 / 8 : ℝ) + (1 / 2) ^ params.logBlowup ≤ 1 := by
    rw [hbl]; norm_num
  have hεq : (1 - (3 / 8 : ℝ)) ^ params.numQueries / 2 ^ params.queryPowBits ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hqn, hqpow, show (1 - 3 / 8 : ℝ) = 5 / 8 by norm_num]
    exact ud_160_pow20_le_three_quarters_128
  have hmain := goldilocksExt3_soundnessTensor_sponge_blake2b512_uniqueDecoding params shape hmax
    hheight s₀ (δ := 3 / 8) (by norm_num) hrate (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (tensor_ud_alpha_le_three_quarters_128 params shape hmax hW hM)
    (tensor_ud_beta_le_three_quarters_128 params shape hmax)
    hεq hadv attempt
  dsimp only at hmain
  have h58 : (1 - (3 / 8 : ℝ)) = 5 / 8 := by norm_num
  rw [h58] at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  rw [card_digest64, Nat.cast_pow, Nat.cast_ofNat] at hcol
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rw [← hNcast] at hmain
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 512)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-! ### Unconditional 128-Bit Johnson-Regime Soundness for Executable `Fri.verifyTensor` -/

/-- Shared arithmetic core for unconditional Johnson-regime `Fri.verifyTensor`
soundness over `GoldilocksExt3` (discharging `CurveListCA` internally via
`curveListCA_fp3`, with zero unproven proximity assumptions). -/
private theorem goldilocksExt3_soundnessTensor_sponge_johnson_of_profile_aux
    (D : Type) [Fintype D] [Nonempty D] [DecidableEq D] [Inhabited D]
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp)
    (hq : ((p : ℝ) / q) ^ params.numQueries / 2 ^ params.queryPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (hq_pos : 0 < q) (hpq : p ≤ q) (hgap_nat : q ^ 2 < 2 ^ lb * p ^ 2)
    (hR : (2 * q ^ 2) / (2 ^ lb * p ^ 2 - q ^ 2) + 1 ≤ Rmax)
    (hL : (2 * q ^ 2 * p * 2 ^ lb + q ^ 3 + 2 * (2 ^ lb * p ^ 2 - q ^ 2) * p * 2 ^ lb) /
      ((2 ^ lb * p ^ 2 - q ^ 2) * q) ≤ Lmax)
    (hLJ : (((p : ℝ) / q - (1 / 2 : ℝ) ^ lb) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ lb)) * (1 - (p : ℝ) / q) ≤ LJ_ub)
    (hCd : curveListRatioBound (2 ^ lb) Rmax Lmax + 2 ^ lb * LJ_ub ≤ 2 ^ lb * 2 ^ PowExp)
    (hClaimExp : ClaimExp + PowExp ≤ 63)
    (hHmax : Hmax + PowExp + 1 ≤ 63)
    (s₀ : D) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 D) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := D) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift ((p : ℝ) / q)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * Fintype.card D) := by
  intro wf P N
  set H := Fri.logMaxHeight params.logBlowup shape
  set B : ℕ := 2 ^ lb
  have hB2 : 2 ≤ B := by
    calc 2 = 2 ^ 1 := by decide
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
  have hT : ∀ (j k : ℕ), j ≤ Fri.numRounds params shape → 2 ≤ k →
      (CurveListCAProof.curveListThreshold (2 ^ (H - j))
        (2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen)
        ⌈((p : ℝ) / q) * (2 : ℝ) ^ (H - j)⌉₊ k : ℝ) ≤ ((k - 1 : ℕ) : ℝ) * cT := by
    intro j k hj hk
    set nj : ℕ := 2 ^ (H - j)
    set dj : ℕ := 2 ^ (Fri.numRounds params shape - j) * 2 ^ params.logFinalPolyLen
    set Aj : ℕ := ⌈((p : ℝ) / q) * (nj : ℝ)⌉₊
    have hH_eq : H = Fri.numRounds params shape + lb + params.logFinalPolyLen := by
      have h1 : Fri.numRounds params shape = H - params.logFinalHeight := rfl
      have h2 : params.logFinalHeight ≤ H := hheight
      unfold FriParams.logFinalHeight at h1 h2
      rw [hbl] at h1 h2
      omega
    have hnj_eq : nj = B * dj := by
      dsimp only [nj, dj, B]
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    have hdj_pos : 1 ≤ dj := Nat.mul_pos (pow_pos two_pos _) (pow_pos two_pos _)
    have hnj_pos : 0 < nj := pow_pos two_pos _
    have hprod_pos : (0 : ℝ) < ((p : ℝ) / q) * (nj : ℝ) :=
      mul_pos hθ0 (Nat.cast_pos.mpr hnj_pos)
    have hAj_pos : 1 ≤ Aj := Nat.ceil_pos.mpr hprod_pos
    have hAj_le : Aj ≤ nj := by
      apply Nat.ceil_le.mpr
      calc ((p : ℝ) / q) * (nj : ℝ) ≤ 1 * (nj : ℝ) :=
            mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg _)
        _ = (nj : ℝ) := one_mul _
    have hAj_lo : p * nj ≤ q * Aj := by
      have h1 : ((p : ℝ) / q) * (nj : ℝ) ≤ (Aj : ℝ) := Nat.le_ceil _
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (p : ℝ) * (nj : ℝ) ≤ (q : ℝ) * (Aj : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hq_r.le
        field_simp [hq_r.ne'] at this
        linarith
      exact_mod_cast h2
    have hAj_hi : q * (Aj - 1) < p * nj := by
      have h1 : (Aj : ℝ) < ((p : ℝ) / q) * (nj : ℝ) + 1 := Nat.ceil_lt_add_one hprod_pos.le
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (q : ℝ) * ((Aj - 1 : ℕ) : ℝ) < (p : ℝ) * (nj : ℝ) := by
        rw [Nat.cast_sub hAj_pos, Nat.cast_one]
        have hsub : (Aj : ℝ) - 1 < ((p : ℝ) / q) * (nj : ℝ) := by linarith
        have := mul_lt_mul_of_pos_left hsub hq_r
        field_simp [hq_r.ne'] at this
        linarith
      exact_mod_cast h2
    have hnat1 : CurveListCAProof.curveListThreshold nj dj Aj k ≤
        (k - 1) * CurveListCAProof.curveListCoeff nj dj Aj :=
      CurveListCAProof.curveListThreshold_le_mul_coeff nj dj Aj k hk
    have hnat2 : CurveListCAProof.curveListCoeff nj dj Aj ≤ Cd * dj :=
      curveListCoeff_le_of_ratio hdj_pos hB2 hnj_eq hq_pos hgap_nat hAj_lo hAj_hi hAj_le hAj_pos hR hL
    have hnat : CurveListCAProof.curveListThreshold nj dj Aj k ≤ (k - 1) * (Cd * dj) :=
      hnat1.trans (Nat.mul_le_mul_left (k - 1) hnat2)
    have hdj_le : (dj : ℝ) ≤ (2 : ℝ) ^ H / (B : ℝ) := by
      have hBdj : B * dj ≤ 2 ^ H := by
        rw [← hnj_eq]
        exact Nat.pow_le_pow_right two_pos (Nat.sub_le H j)
      have hBdj_r : (B : ℝ) * (dj : ℝ) ≤ (2 : ℝ) ^ H := by exact_mod_cast hBdj
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hcast : ((CurveListCAProof.curveListThreshold nj dj Aj k : ℕ) : ℝ) ≤
        ((k - 1 : ℕ) : ℝ) * ((Cd : ℝ) * (dj : ℝ)) := by
      exact_mod_cast hnat
    have hnj_cast : ((nj : ℕ) : ℝ) = (2 : ℝ) ^ (H - j) := by
      dsimp only [nj]; push_cast; rfl
    rw [← hnj_cast]
    refine hcast.trans ?_
    dsimp only [cT]
    have hstep : (Cd : ℝ) * (dj : ℝ) ≤ ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H := by
      calc (Cd : ℝ) * (dj : ℝ) ≤ (Cd : ℝ) * ((2 : ℝ) ^ H / (B : ℝ)) :=
            mul_le_mul_of_nonneg_left hdj_le (Nat.cast_nonneg _)
        _ = ((Cd : ℝ) / (B : ℝ)) * (2 : ℝ) ^ H := by ring
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
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
      rw [div_add' _ _ _ hBpos.ne', div_le_iff₀ hBpos]
      linarith
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
      _ ≤ (2 : ℝ) ^ PowExp * (2 : ℝ) ^ H :=
          mul_le_mul_of_nonneg_right hfrac (by positivity)
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  have hεα : ((2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
      (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      Fintype.card Fp3Model ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hcard]
    have hcr : ((2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (2 : ℝ) ^ H ≤ (2 : ℝ) ^ ClaimExp := by exact_mod_cast htensor
    have hpow63 : (2 : ℝ) ^ (ClaimExp + PowExp) ≤ (2 : ℝ) ^ 63 := by
      exact_mod_cast Nat.pow_le_pow_right two_pos hClaimExp
    have hnum : ((2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
          Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
            (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) ≤ (2 : ℝ) ^ 63 := by
      calc _ ≤ ((2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
              Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
            ((2 : ℝ) ^ PowExp * (2 : ℝ) ^ H) :=
            mul_le_mul_of_nonneg_left hcomb (Nat.cast_nonneg _)
        _ = (((2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
              Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
            (2 : ℝ) ^ H) * (2 : ℝ) ^ PowExp := by ring
        _ ≤ (2 : ℝ) ^ ClaimExp * (2 : ℝ) ^ PowExp :=
            mul_le_mul_of_nonneg_right hcr (by positivity)
        _ = (2 : ℝ) ^ (ClaimExp + PowExp) := (pow_add _ _ _).symm
        _ ≤ (2 : ℝ) ^ 63 := hpow63
    exact (div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg _) 3)).trans h63
  have hεβ : (2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
          (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) /
      Fintype.card Fp3Model / 2 ^ params.commitPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    rw [hcard]
    have hLJ_nn : 0 ≤ (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) := by
      have hnum_nn : 0 ≤ (p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup := by
        have h1 : ((p : ℝ) / q) ^ 2 ≤ (p : ℝ) / q := by nlinarith
        linarith
      have hden_pos : 0 < ((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup := sub_pos.mpr hgap
      have h1m : 0 ≤ 1 - (p : ℝ) / q := sub_nonneg.mpr hθ1
      positivity
    have hnum : 2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
        ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H) ≤ (2 : ℝ) ^ 63 := by
      have h2H : (2 : ℝ) ^ (H + PowExp + 1) ≤ (2 : ℝ) ^ 63 := by
        exact_mod_cast Nat.pow_le_pow_right two_pos (show H + PowExp + 1 ≤ 63 by omega)
      calc 2 * cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
              (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
              ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)
          ≤ 2 * (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
              (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
              ((1 - (p : ℝ) / q) * (2 : ℝ) ^ H)) := by linarith
        _ ≤ 2 * ((2 : ℝ) ^ PowExp * (2 : ℝ) ^ H) := mul_le_mul_of_nonneg_left hcomb (by norm_num)
        _ = (2 : ℝ) ^ (H + PowExp + 1) := by rw [pow_succ', pow_add]; ring
        _ ≤ (2 : ℝ) ^ 63 := h2H
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ params.commitPowBits := by
      exact_mod_cast Nat.one_le_pow params.commitPowBits 2 two_pos
    exact (div_le_self (div_nonneg (by linarith) (pow_nonneg (Nat.cast_nonneg _) 3)) hpow1).trans
      ((div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg _) 3)).trans h63)
  have hmain := soundnessTensor_sponge_johnson_of_curveListCA goldilocksExt3_fieldModel params shape
    wf s₀ curveListCA_fp3 hheight hθ0 hθ1 hgap hcT0 hT
    (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128) hεα hεβ hq hadv attempt
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rwa [← hNcast] at hmain

/-- **Master Unconditional 128-Bit Johnson Soundness Schema for `Fri.verifyTensor`
over `GoldilocksExt3` (`Digest64`, RFC 7693 `BLAKE2b-512`):** discharges
`CurveListCA` internally via `curveListCA_fp3` (zero unproven assumptions!),
producing literal `≤ N / 2 ^ 128` executable `Fri.verifyTensor` soundness. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_of_profile
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ ClaimExp)
    (hq : ((p : ℝ) / q) ^ params.numQueries / 2 ^ params.queryPowBits ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128)
    (hq_pos : 0 < q) (hpq : p ≤ q) (hgap_nat : q ^ 2 < 2 ^ lb * p ^ 2)
    (hR : (2 * q ^ 2) / (2 ^ lb * p ^ 2 - q ^ 2) + 1 ≤ Rmax)
    (hL : (2 * q ^ 2 * p * 2 ^ lb + q ^ 3 + 2 * (2 ^ lb * p ^ 2 - q ^ 2) * p * 2 ^ lb) /
      ((2 ^ lb * p ^ 2 - q ^ 2) * q) ≤ Lmax)
    (hLJ : (((p : ℝ) / q - (1 / 2 : ℝ) ^ lb) /
        (((p : ℝ) / q) ^ 2 - (1 / 2 : ℝ) ^ lb)) * (1 - (p : ℝ) / q) ≤ LJ_ub)
    (hCd : curveListRatioBound (2 ^ lb) Rmax Lmax + 2 ^ lb * LJ_ub ≤ 2 ^ lb * 2 ^ PowExp)
    (hClaimExp : ClaimExp + PowExp ≤ 63)
    (hHmax : Hmax + PowExp + 1 ≤ 63)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).batches +
      ((modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).rounds + 2)) +
      (modelParams goldilocksExt3_fieldModel params shape
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32))).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift ((p : ℝ) / q)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf P N
  have hmain := goldilocksExt3_soundnessTensor_sponge_johnson_of_profile_aux Digest64
    lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp params shape hbl hlb hmax hmax32 hheight htensor
    hq hq_pos hpq hgap_nat hR hL hLJ hCd hClaimExp hHmax s₀ hadv attempt
  dsimp only at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest64)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-- **Unconditional 32-byte `BLAKE3-256` (`Digest`) Johnson-regime soundness for
executable `Fri.verifyTensor` (`lb = 2, q ≥ 128, queryPow = 20, θ = 71 / 128`):**
ZERO unproven proximity assumptions! Covers all shapes with `logMaxHeight ≤ 32`
and `2 ^ (kCol + kOpen) * 2 ^ logMaxHeight ≤ 2 ^ 36` (e.g. `d ≤ 2 ^ 23` with
up to `2048` tensor claims). -/
theorem goldilocksExt3_soundnessTensor_sponge_johnson_128_blake3_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 128 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape
      (goldilocksExt3_wellFormed params shape hmax)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed params shape hmax
    let P := modelParams goldilocksExt3_fieldModel params shape wf
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256) := by
  have hcardD : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 256 := by
    rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Nat.cast_ofNat, hcardD] using
    goldilocksExt3_soundnessTensor_sponge_johnson_of_profile_aux Digest
      2 71 128 9 28 3 27 32 36 params shape hbl (by decide) hmax le_rfl hheight htensor
      (by rw [hqpow]; exact johnson_71_128_ge_128_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv attempt

/-- **100% Unconditional 128-Bit Johnson Soundness for `Fri.verifyTensor`
(`lb = 2, q ≥ 128, queryPow = 20`, `Digest64` `BLAKE2b-512`):**
ZERO `CurveListCA` / `BatchedLineListCA` hypothesis! Literal `≤ N / 2 ^ 128`
at `θ = 71 / 128` for `2 ^ (kCol + kOpen) * 2 ^ logMaxHeight ≤ 2 ^ 36` and
`N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 128 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 36)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
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
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (71 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_of_profile
      2 71 128 9 28 3 27 32 36 params shape hbl (by decide) hmax le_rfl hheight htensor
      (by rw [hqpow]; exact johnson_71_128_ge_128_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% Unconditional 128-Bit Johnson Soundness for `Fri.verifyTensor`
(`lb = 2, q ≥ 118, queryPow = 20`, `Digest64` `BLAKE2b-512`):**
literal `≤ N / 2 ^ 128` at `θ = 135 / 256` for `logMaxHeight ≤ 30`,
`2 ^ (kCol + kOpen) * 2 ^ logMaxHeight ≤ 2 ^ 31`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_118_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 2) (hqn : 118 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 30)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 31)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
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
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (135 / 256)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_of_profile
      2 135 256 18 50 5 32 30 31 params shape hbl (by decide) hmax (by decide) hheight htensor
      (by rw [hqpow]; exact johnson_135_256_ge_118_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% Unconditional 128-Bit Johnson Soundness for `Fri.verifyTensor`
(`lb = 3, q ≥ 78, queryPow = 20`, `Digest64` `BLAKE2b-512`):**
literal `≤ N / 2 ^ 128` at `θ = 19 / 50` for `logMaxHeight ≤ 31`,
`2 ^ (kCol + kOpen) * 2 ^ logMaxHeight ≤ 2 ^ 32`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb3_78_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 3) (hqn : 78 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 31)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 32)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
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
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (19 / 50)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_of_profile
      3 19 50 13 51 9 31 31 32 params shape hbl (by decide) hmax (by decide) hheight htensor
      (by rw [hqpow]; exact johnson_19_50_ge_78_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% Unconditional 128-Bit Johnson Soundness for `Fri.verifyTensor`
(`lb = 4, q ≥ 58, queryPow = 20`, `Digest64` `BLAKE2b-512`):**
literal `≤ N / 2 ^ 128` at `θ = 35 / 128` for `logMaxHeight ≤ 32`,
`2 ^ (kCol + kOpen) * 2 ^ logMaxHeight ≤ 2 ^ 33`, and `N ≤ 2 ^ 128`. -/
theorem goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_lb4_58_128_unconditional
    (params : FriParams) (shape : ClaimShape)
    (hbl : params.logBlowup = 4) (hqn : 58 ≤ params.numQueries) (hqpow : params.queryPowBits = 20)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ 32)
    (hheight : params.logFinalHeight ≤ Fri.logMaxHeight params.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight params.logBlowup shape)) *
        2 ^ Fri.logMaxHeight params.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape
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
        (∃ f : ∀ x, SpongeTensorOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensor goldilocksExt3_fieldModel params shape wf s₀ f (attempt res.1) = true) ∧
        ClaimsFail P.ldt P.shift (35 / 128)
          (P.claims (view goldilocksExt3_fieldModel params shape
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensor goldilocksExt3_fieldModel params shape wf s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensor_sponge_blake2b512_johnson_of_profile
      4 35 128 11 58 13 30 32 33 params shape hbl (by decide) hmax le_rfl hheight htensor
      (by rw [hqpow]; exact johnson_35_128_ge_58_pow20_le_three_quarters_128 hqn)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

end CertiFri.P3.Exec
