import CertiFriProofs.Exec.MultiArity.TensorExec
import CertiFriProofs.Exec.SoundnessTensorSponge

/-!
# Incremental Sponge Soundness (`c = 3 / 2`) for Multi-Arity Tensor-Batched FRI

Lifts `Exec/MultiArity/TensorExec.lean` (`Fri.verifyTensorWithSchedule` / `Fri.verifyTensorMultiArity`)
from full-transcript Fiat–Shamir chaining to single-root incremental sponge chaining
(`entryCap = 1`, collision prefactor **`c = 3 / 2`**) via
`Oracle.prob_spongeExperiment_bind_committedRow_le`, covering arbitrary variable per-round
arity schedules `arities : List ℕ` (including `logArity ∈ {1, 2, 3}`, fold factors `2, 4, 8`).

## Main results (zero `sorry`, standard axioms `[propext, Classical.choice, Quot.sound]` only)

1. **Incremental sponge multi-arity soundness (`c = 3 / 2`):**
   * `Exec.soundnessTensorMulti_sponge`: generic `Tensor2DMCA` + `StepMCAArity` bound.
   * `Exec.soundnessTensorMulti_sponge_uniqueDecoding`: unconditional unique-decoding soundness
     for any valid schedule `arities` (completely independent of per-round arities!).
   * `Exec.soundnessTensorMulti_sponge_johnson_of_curveListCA`: Johnson-regime soundness from
     `CurveListCA` alone, showing exact `m = 2 ^ a` cancellation in BOTH the curve-list
     threshold term (`m * Cd * d' = Cd * d_src`) and the Johnson list-size term
     (`m * L_J * (1 - θ) * |D'| = L_J * (1 - θ) * |D_src|`).
2. **Unconditional 128-bit `GoldilocksExt3` (`Fp3Model`) Johnson theorems (ZERO unproven
   proximity assumptions — `CurveListCA` discharged internally via `curveListCA_fp3`):**
   * `CertiFri.P3.Exec.goldilocksExt3_soundnessTensorMulti_sponge_blake2b512_johnson_of_profile`:
     master unconditional `≤ N / 2 ^ 128` schema for ANY valid multi-arity schedule.
   * `CertiFri.P3.Exec.johnson_35_128_compact400KB_le` (`q ≥ 58, queryPow = 28`) and
     `CertiFri.P3.Exec.johnson_35_128_ultraCompact400KB_le` (`q ≥ 55, queryPow = 30`).
   * Concrete 128-bit theorems for `FriParams.compact400KBBalanced` (`lb = 4, maxLogArity = 3,
     logFinalPolyLen = 8, q = 58, queryPow = 28`) and `FriParams.ultraCompact400KBZk`
     (`q = 55, queryPow = 30`), for BOTH `Digest` (`BLAKE3-256`) and `Digest64` (`BLAKE2b-512`,
     literal `≤ N / 2 ^ 128`), and for both arbitrary valid schedules and the canonical
     schedule `Fri.scheduleOfShape`.
-/

namespace CertiFri.Exec

open Oracle OracleComp MerkleRO Compiled Fri Sponge
open PcsRbr (TensorChal ChalTensorMulti GrindChal ClaimsFailMulti AcceptsTensorMulti
  PowPasses ungrind roundErrorTensor tensorOfMulti betasOfTensorMulti queriesOfTensorMulti)

/-! ## 1. Incremental Sponge Challenger and Simulation for Multi-Arity Tensor FRI -/

section SpongeMultiSim

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K)

/-- Per-step messages of the `(shape.length + arities.length + 2)`-step incremental
sponge multi-arity protocol: one commitment digest per batch, then points + values,
then commit-phase steps, then `finalMessageMulti` + query PoW witness. -/
def spongeMessagesMulti (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (a : Attempt F EF D) (i : ℕ) : RawMsg F EF D :=
  if i < shape.length then [.digest (a.commitments.getD i default)]
  else if i = shape.length then a.points.toList.map .ext ++ a.values.toList.map .ext
  else messagesMulti params arities a.commitments a.points a.values a.proof (i - shape.length)

/-- Digests introduced at step `i` of the incremental sponge multi-arity protocol
(`length ≤ 1` at every step, giving `entryCap = 1` and collision prefactor `c = 3 / 2`). -/
def spongeStepDigestsMulti (P : Compiled.MultiParams K) (i : ℕ) (msg : RawMsg F EF D) : List D :=
  if i < P.batches then [(digestsIn msg).getD 0 default]
  else if i = P.batches then []
  else if i ≤ P.batches + P.rounds then [(digestsIn msg).getD 0 default]
  else []

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K] [DecidableEq K]
  [DecidableEq D] in
theorem length_spongeStepDigestsMulti_le_one (P : Compiled.MultiParams K) (i : ℕ)
    (msg : RawMsg F EF D) :
    (spongeStepDigestsMulti (F := F) (EF := EF) P i msg).length ≤ 1 := by
  unfold spongeStepDigestsMulti
  split_ifs <;> simp

/-- Extract the `k`-round multi-arity tensor `GrindChal` transcript from a
`(P.batches + k)`-step incremental sponge transcript. -/
def spongeToGrindTranscriptTensorMulti {P : Compiled.MultiParams K} {W M : ℕ} {bits : ℕ → ℕ}
    {M' : Type} (f_view : ℕ → M') :
    (k : ℕ) → Oracle.Transcript (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) (P.batches + k) →
      Oracle.Transcript M' (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) k
  | 0, _ => .nil
  | k + 1, .snoc t _ c =>
    (spongeToGrindTranscriptTensorMulti f_view k t).snoc (f_view k)
      (spongeChalTensorMultiCast P W M bits c)

/-- Query the multi-arity tensor sponge oracle at the current step and cast to `GrindChal`. -/
def spongeAnswerTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    (s : SpongeState F EF D) :
    GrindChal bits (ChalTensorMulti P.ldt W M P.queries) (s.step - P.batches) :=
  if h : P.batches ≤ s.step then
    spongeChalTensorMultiCast P W M bits
      (cast (by rw [Nat.add_sub_of_le h]) (f (.chal s.step s.chain s.cur)).2)
  else
    have h0 : s.step - P.batches = 0 := Nat.sub_eq_zero_of_le (by omega)
    cast (by rw [h0]) (spongeChalTensorMultiCast P W M bits (k := 0)
      (cast (by rw [Nat.add_zero]) (f (.chal P.batches s.chain s.cur)).2))

/-- **Idealised incremental sponge challenger for multi-arity `Fri.verifyTensorWithSchedule`**
with single-root absorption (`entryCap = 1`). -/
noncomputable def spongeChallengerTensorMulti (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
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
    let ans := spongeAnswerTensorMulti P W M bits f s
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
    let ans := spongeAnswerTensorMulti P W M bits f s
    (if s.nsamp = 0 ∧ bits (s.step - P.batches) ≠ 0 then (ans.1 : ℕ)
      else P.indexOf (queryPointTensorMulti P ans.2
        (s.nsamp - if bits (s.step - P.batches) = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

/-! ## Simulation between `spongeChallengerTensorMulti` and `freeChallengerTensorMulti` -/

private def foldSpongeListTM {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) : List (Observation F EF D) → ℕ × D
  | [] => (step, chain)
  | o :: rest => foldSpongeListTM f (step + 1) (f (.chal step chain [o])).1 rest

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeListTM_append {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs ys : List (Observation F EF D)) :
    foldSpongeListTM f step chain (xs ++ ys) =
      let p := foldSpongeListTM f step chain xs
      foldSpongeListTM f p.1 p.2 ys := by
  induction xs generalizing step chain with
  | nil => rfl
  | cons o xs ih => exact ih (step + 1) (f (.chal step chain [o])).1

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem foldSpongeListTM_fst {C : ℕ → Type}
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) C K D x)
    (step : ℕ) (chain : D) (xs : List (Observation F EF D)) :
    (foldSpongeListTM f step chain xs).1 = step + xs.length := by
  induction xs generalizing step chain with
  | nil => simp [foldSpongeListTM]
  | cons o xs ih =>
    simp only [foldSpongeListTM, List.length_cons]
    rw [ih]
    omega

/-- Sponge state reached by running `f` along a full multi-arity tensor transcript `t`. -/
def transcriptSpongeStateTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x) :
    {i : ℕ} → Oracle.Transcript (RawMsg F EF D)
      (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) i → D
  | 0, .nil => s₀
  | 1, .snoc .nil m₀ _ =>
    let st := (foldSpongeListTM f 0 s₀ (m₀.take P.batches)).2
    (f (.chal P.batches st (m₀.drop P.batches))).1
  | i + 2, .snoc t m _ =>
    let prev := transcriptSpongeStateTensorMulti P W M bits s₀ f t
    (f (.chal (P.batches + (i + 1)) prev m)).1

/-- Lift a multi-arity tensor sponge oracle `f` to the induced full-transcript `FSQuery` oracle. -/
def liftSpongeOracleTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x) :
    ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) K D x
  | .other q => f (.other q)
  | .chal (i := 0) .nil m =>
    let st := (foldSpongeListTM f 0 s₀ (m.take P.batches)).2
    spongeChalTensorMultiCast P W M bits (f (.chal P.batches st (m.drop P.batches))).2
  | .chal (i := k + 1) t m =>
    let prev := transcriptSpongeStateTensorMulti P W M bits s₀ f t
    spongeChalTensorMultiCast P W M bits (f (.chal (P.batches + (k + 1)) prev m)).2

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K]
  [DecidableEq D] [Inhabited D] in
theorem hasherOf_liftSpongeOracleTensorMulti (P : Compiled.MultiParams K) (W M : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x) :
    hasherOf (liftSpongeOracleTensorMulti P W M bits s₀ f) = spongeHasherOf f := rfl

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Fintype K]
  [DecidableEq K] [DecidableEq D] [Inhabited D] in
private theorem drop_firstMessage_eqTM (shape : ClaimShape) (a : Attempt F EF D)
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
private theorem spongeTranscript_succ_fstTM {M' : Type} {C : ℕ → Type} {O : Type}
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
private theorem spongeTranscript_succ_sndTM {M' : Type} {C : ℕ → Type} {O : Type}
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

private def StateRelTensorMulti (P : Compiled.MultiParams K) (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    (fs : FreeState F EF D) (ss : SpongeState F EF D) : Prop :=
  (fs.round = 0 ∧ fs.nsamp = 0 ∧ fs.cur.length ≤ P.batches ∧
    ss = ⟨fs.cur.length, (foldSpongeListTM f 0 s₀ fs.cur).2, [], 0⟩) ∨
  (fs.round = 0 ∧ P.batches ≤ fs.cur.length ∧
    ss = ⟨P.batches, (foldSpongeListTM f 0 s₀ (fs.cur.take P.batches)).2,
      fs.cur.drop P.batches, fs.nsamp⟩) ∨
  (1 ≤ fs.round ∧
    ss = ⟨P.batches + fs.round,
      transcriptSpongeStateTensorMulti P W M bits s₀ f
        (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f) fs.hist fs.round),
      fs.cur, fs.nsamp⟩)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_observe (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss) (o : Observation F EF D) :
    StateRelTensorMulti P W M bits s₀ f
      ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe fs o)
      ((spongeChallengerTensorMulti P W M tailLen bits f m).observe ss o) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · dsimp only at hr hns hlen
    subst hr hns
    by_cases hlt : cur.length < P.batches
    · have hne_first : cur.length ≠ P.batches + tailLen := by omega
      have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
          ⟨0, hist, cur ++ [o], 0⟩ := by
        simp [freeChallengerTensorMulti, hne_first]
      rw [hobs_f]
      left
      simp only [spongeChallengerTensorMulti, hlt, ↓reduceIte, List.length_append, List.length_singleton]
      refine ⟨trivial, trivial, by omega, ?_⟩
      rw [foldSpongeListTM_append]
      dsimp only
      rw [foldSpongeListTM_fst, Nat.zero_add]
      rfl
    · have heq : cur.length = P.batches := by omega
      by_cases hadv : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧ tailLen = 0
      · obtain ⟨hz, htail0⟩ := hadv
        have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
          simp [freeChallengerTensorMulti, hz, heq, htail0]
        have hss_eq : (⟨cur.length, (foldSpongeListTM f 0 s₀ cur).2, [], 0⟩ : SpongeState F EF D) =
            ⟨P.batches, (foldSpongeListTM f 0 s₀ cur).2, [], 0⟩ := by
          rw [heq]
        have hobs_s : (spongeChallengerTensorMulti P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListTM f 0 s₀ cur).2, [], 0⟩ o =
            ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListTM f 0 s₀ cur).2 [])).1, [o], 0⟩ := by
          unfold spongeChallengerTensorMulti
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _),
            ite_eq_left ⟨rfl, hz, by simp [htail0]⟩]
        rw [hobs_f, hss_eq, hobs_s]
        right; right
        refine ⟨le_rfl, ?_⟩
        simp only [fsTranscript, Function.update_self]
        change (⟨P.batches + 1, (f (.chal P.batches (foldSpongeListTM f 0 s₀ cur).2 [])).1, [o], 0⟩ :
            SpongeState F EF D) =
          ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2
            (cur.drop P.batches))).1, [o], 0⟩
        rw [← heq, List.take_length, List.drop_length]
      · have hnotf : ¬ (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
            cur.length = P.batches + tailLen) := by
          intro ⟨h1, h2⟩; exact hadv ⟨h1, by omega⟩
        have hnots : ¬ (Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
            0 = tailLen) := by
          intro ⟨h1, h2⟩; exact hadv ⟨h1, h2.symm⟩
        have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨0, hist, cur ++ [o], 0⟩ := by
          unfold freeChallengerTensorMulti
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (fun h => hnotf ⟨h.2.1, h.2.2⟩)]
        have hobs_s : (spongeChallengerTensorMulti P W M tailLen bits f m).observe
              ⟨cur.length, (foldSpongeListTM f 0 s₀ cur).2, [], 0⟩ o =
            ⟨cur.length, (foldSpongeListTM f 0 s₀ cur).2, [o], 0⟩ := by
          unfold spongeChallengerTensorMulti
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
        have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
          simp [freeChallengerTensorMulti, hz, hlen_eq]
        have hobs_s : (spongeChallengerTensorMulti P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ o =
            ⟨P.batches + 1, (f (.chal P.batches (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2
              (cur.drop P.batches))).1, [o], 0⟩ := by
          unfold spongeChallengerTensorMulti
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
        have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
              (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, 0⟩ o =
            ⟨0, hist, cur ++ [o], 0⟩ := by
          unfold freeChallengerTensorMulti
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (fun h => hadv ⟨h.2.1, h.2.2⟩)]
        have hobs_s : (spongeChallengerTensorMulti P W M tailLen bits f m).observe
              ⟨P.batches, (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ o =
            ⟨P.batches, (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2,
              cur.drop P.batches ++ [o], 0⟩ := by
          unfold spongeChallengerTensorMulti
          dsimp only
          rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _),
            ite_eq_right (fun h => hnot_drop ⟨h.2.1, h.2.2⟩)]
        rw [hobs_f, hobs_s]
        right; left
        refine ⟨rfl, by simp; omega, ?_⟩
        rw [List.take_append_of_le_length hlen, List.drop_append_of_le_length hlen]
    · have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨0, hist, cur, nsamp⟩ o =
          ⟨1, Function.update hist 0 cur, [o], 0⟩ := by
        simp [freeChallengerTensorMulti, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensorMulti, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      simp only [fsTranscript, Function.update_self]
      rfl
  · dsimp only at hr
    by_cases hns : nsamp = 0
    · have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨round, hist, cur, nsamp⟩ o =
          ⟨round, hist, cur ++ [o], nsamp⟩ := by
        simp [freeChallengerTensorMulti, hns, show round ≠ 0 by omega]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensorMulti, hns, ↓reduceIte,
        show ¬ (P.batches + round < P.batches) by omega,
        show P.batches + round ≠ P.batches by omega, false_and]
      exact ⟨hr, trivial⟩
    · have hobs_f : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
            (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe ⟨round, hist, cur, nsamp⟩ o =
          ⟨round + 1, Function.update hist round cur, [o], 0⟩ := by
        simp [freeChallengerTensorMulti, hns]
      rw [hobs_f]
      right; right
      simp only [spongeChallengerTensorMulti, hns, ↓reduceIte]
      refine ⟨by omega, ?_⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
      have hr' : round = k + 1 := by omega
      have hcongr : fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
          (Function.update hist round cur) round =
          fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f) hist round :=
        Transcript.fsTranscript_congr _ fun j hj => Function.update_of_ne (by omega) _ _
      have heq_step : P.batches + round + 1 = P.batches + (round + 1) := by omega
      rw [heq_step]
      congr 1
      have hst : transcriptSpongeStateTensorMulti P W M bits s₀ f
          (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (Function.update hist round cur) (round + 1)) =
          (f (.chal (P.batches + round)
            (transcriptSpongeStateTensorMulti P W M bits s₀ f
              (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f) hist round)) cur)).1 := by
        rw [← hcongr]
        generalize hist = hh at *
        let t0 := fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (Function.update hh round cur) round
        have hstep : fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (Function.update hh round cur) (round + 1) =
            t0.snoc cur (liftSpongeOracleTensorMulti P W M bits s₀ f (.chal t0 cur)) := by
          have hupd : Function.update hh round cur round = cur := Function.update_self round cur hh
          show t0.snoc (Function.update hh round cur round)
              (liftSpongeOracleTensorMulti P W M bits s₀ f
                (.chal t0 (Function.update hh round cur round))) =
            t0.snoc cur (liftSpongeOracleTensorMulti P W M bits s₀ f (.chal t0 cur))
          rw [hupd]
        rw [hstep]
        have h1 : ∀ (n : ℕ) (hn : n = k + 1)
            (t : Oracle.Transcript (RawMsg F EF D)
              (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) n)
            (msg : RawMsg F EF D)
            (c : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) n),
            transcriptSpongeStateTensorMulti P W M bits s₀ f (t.snoc msg c) =
              (f (.chal (P.batches + n) (transcriptSpongeStateTensorMulti P W M bits s₀ f t) msg)).1 := by
          rintro n rfl t msg c
          rfl
        exact h1 round hr' t0 cur (liftSpongeOracleTensorMulti P W M bits s₀ f (.chal t0 cur))
      exact hst.symm

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_observeAll (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    (obs : List (Observation F EF D)) {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss) :
    StateRelTensorMulti P W M bits s₀ f
      ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observeAll fs obs)
      ((spongeChallengerTensorMulti P W M tailLen bits f m).observeAll ss obs) := by
  induction obs generalizing fs ss with
  | nil => exact hrel
  | cons o obs ih => exact ih (stateRelTensorMulti_observe m P W M tailLen bits s₀ f hrel o)

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Fintype K] [DecidableEq D]
  [Inhabited D] in
private theorem freeAnswerTensorMulti_eq_spongeAnswerTensorMulti (P : Compiled.MultiParams K)
    (W M : ℕ) (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ss.step - P.batches = fs.round ∧
      (ss.step ≤ P.batches ↔ fs.round = 0) ∧
      HEq (freeAnswerTensorMulti P W M bits (liftSpongeOracleTensorMulti P W M bits s₀ f) fs)
        (spongeAnswerTensorMulti P W M bits f ss) := by
  rcases fs with ⟨round, hist, cur, nsamp⟩
  dsimp only at hready hrel ⊢
  rcases hrel with ⟨hr, _, hlen, rfl⟩ | ⟨hr, _, rfl⟩ | ⟨hr, rfl⟩
  · subst hr
    dsimp only at hready hlen
    have heq : cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    have htake : cur.take P.batches = cur := by rw [← heq, List.take_length]
    have hdrop : cur.drop P.batches = [] := by rw [← heq, List.drop_length]
    have hss : (⟨cur.length, (foldSpongeListTM f 0 s₀ cur).2, [], 0⟩ : SpongeState F EF D) =
        ⟨P.batches, (foldSpongeListTM f 0 s₀ (cur.take P.batches)).2, cur.drop P.batches, 0⟩ := by
      simp [heq, htake, hdrop]
    rw [hss]
    refine ⟨by simp, by simp, ?_⟩
    unfold freeAnswerTensorMulti spongeAnswerTensorMulti
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracleTensorMulti]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChalTensorMulti P W M bits (P.batches + n))
        (b : SpongeChalTensorMulti P W M bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalTensorMultiCast P W M bits b) (spongeChalTensorMultiCast P W M bits a) := by
      rintro n rfl a b hab; rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · subst hr
    refine ⟨by simp, by simp, ?_⟩
    unfold freeAnswerTensorMulti spongeAnswerTensorMulti
    simp only [le_rfl, ↓reduceDIte, fsTranscript, liftSpongeOracleTensorMulti]
    have hzero : P.batches - P.batches = 0 := Nat.sub_self P.batches
    have hgen : ∀ (n : ℕ) (hn : n = 0)
        (a : SpongeChalTensorMulti P W M bits (P.batches + n))
        (b : SpongeChalTensorMulti P W M bits (P.batches + 0)),
        HEq a b →
        HEq (spongeChalTensorMultiCast P W M bits b) (spongeChalTensorMultiCast P W M bits a) := by
      rintro n rfl a b hab; rw [eq_of_heq hab]
    exact hgen (P.batches - P.batches) hzero _ _ (cast_heq _ _)
  · dsimp only at hr
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
    have hr' : round = k + 1 := by omega
    subst hr'
    refine ⟨by dsimp only; omega, by dsimp only; constructor <;> intro h <;> omega, ?_⟩
    unfold freeAnswerTensorMulti spongeAnswerTensorMulti
    simp only [show P.batches ≤ P.batches + (k + 1) by omega, ↓reduceDIte,
      liftSpongeOracleTensorMulti]
    have hstep : P.batches + (k + 1) - P.batches = k + 1 := Nat.add_sub_cancel_left _ _
    have hgen2 : ∀ (n : ℕ) (hn : n = k + 1)
        (c : SpongeChalTensorMulti P W M bits (P.batches + n)),
        HEq c (f (.chal (P.batches + (k + 1))
          (transcriptSpongeStateTensorMulti P W M bits s₀ f
            (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f) hist (k + 1))) cur)).2 →
        HEq (spongeChalTensorMultiCast P W M bits (f (.chal (P.batches + (k + 1))
          (transcriptSpongeStateTensorMulti P W M bits s₀ f
            (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f) hist (k + 1))) cur)).2)
            (spongeChalTensorMultiCast P W M bits c) := by
      rintro n rfl c hc; rw [eq_of_heq hc]
    exact hgen2 _ hstep _ (cast_heq _ _)

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_sampleExt (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) :
    ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleExt fs).1 =
      ((spongeChallengerTensorMulti P W M tailLen bits f m).sampleExt ss).1 ∧
    StateRelTensorMulti P W M bits s₀ f
      ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleExt fs).2
      ((spongeChallengerTensorMulti P W M tailLen bits f m).sampleExt ss).2 := by
  obtain ⟨hstep, hle_iff, hans⟩ :=
    freeAnswerTensorMulti_eq_spongeAnswerTensorMulti P W M bits s₀ f hrel hready
  have hns_eq : fs.nsamp = ss.nsamp := by
    rcases hrel with ⟨_, hns, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
    · exact hns
    · rfl
    · rfl
  have htens : (freeAnswerTensorMulti P W M bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) fs).2.tensor =
      (spongeAnswerTensorMulti P W M bits f ss).2.tensor := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) b),
        HEq x y → x.2.tensor = y.2.tensor := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  have hfield : (freeAnswerTensorMulti P W M bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) fs).2.field =
      (spongeAnswerTensorMulti P W M bits f ss).2.field := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) b),
        HEq x y → x.2.field = y.2.field := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨?_, ?_⟩
  · unfold freeChallengerTensorMulti spongeChallengerTensorMulti
    dsimp only
    by_cases hr0 : fs.round = 0
    · have hss_le : ss.step ≤ P.batches := hle_iff.mpr hr0
      simp only [hr0, hss_le, ↓reduceIte, hns_eq, htens]
    · have hss_gt : ¬ (ss.step ≤ P.batches) := fun h => hr0 (hle_iff.mp h)
      simp only [hr0, hss_gt, ↓reduceIte, hfield]
  · rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
    · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
      right; left
      refine ⟨hr, by dsimp only [freeChallengerTensorMulti]; omega, ?_⟩
      simp only [freeChallengerTensorMulti, spongeChallengerTensorMulti, heq, hns]
      rw [← heq, List.take_length, List.drop_length]
    · right; left; exact ⟨hr, hlen, rfl⟩
    · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_sampleExtMany (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x) :
    ∀ (cnt : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensorMulti P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (sampleExtMany (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m) cnt fs).1 =
        (sampleExtMany (spongeChallengerTensorMulti P W M tailLen bits f m) cnt ss).1 ∧
      StateRelTensorMulti P W M bits s₀ f
        (sampleExtMany (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m) cnt fs).2
        (sampleExtMany (spongeChallengerTensorMulti P W M tailLen bits f m) cnt ss).2 ∧
      (1 ≤ (sampleExtMany (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m) cnt fs).2.round ∨
        P.batches ≤ (sampleExtMany (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m) cnt fs).2.cur.length)
  | 0, _, _, hrel, hready => ⟨rfl, hrel, hready⟩
  | cnt + 1, fs, ss, hrel, hready => by
    obtain ⟨h1, h2⟩ := stateRelTensorMulti_sampleExt m P W M tailLen bits s₀ f hrel hready
    have hready1 : 1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleExt fs).2.round ∨
        P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleExt fs).2.cur.length := hready
    obtain ⟨hr1, hr2, hr3⟩ :=
      stateRelTensorMulti_sampleExtMany P W M tailLen bits s₀ f cnt h2 hready1
    exact ⟨by simp only [sampleExtMany, h1, hr1], hr2, hr3⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_sampleBits (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) (nbits : ℕ) :
    ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleBits fs nbits).1 =
      ((spongeChallengerTensorMulti P W M tailLen bits f m).sampleBits ss nbits).1 ∧
    StateRelTensorMulti P W M bits s₀ f
      ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleBits fs nbits).2
      ((spongeChallengerTensorMulti P W M tailLen bits f m).sampleBits ss nbits).2 := by
  obtain ⟨hstep, _, hans⟩ :=
    freeAnswerTensorMulti_eq_spongeAnswerTensorMulti P W M bits s₀ f hrel hready
  have hns_eq : fs.nsamp = ss.nsamp := by
    rcases hrel with ⟨_, hns, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl⟩
    · exact hns
    · rfl
    · rfl
  have hfst : ((freeAnswerTensorMulti P W M bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) fs).1 : ℕ) =
      ((spongeAnswerTensorMulti P W M bits f ss).1 : ℕ) := by
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) b),
        HEq x y → (x.1 : ℕ) = (y.1 : ℕ) := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  have hqp : ∀ k,
      queryPointTensorMulti P (freeAnswerTensorMulti P W M bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) fs).2 k =
      queryPointTensorMulti P (spongeAnswerTensorMulti P W M bits f ss).2 k := by
    intro k
    have : ∀ (a b : ℕ) (hab : a = b)
        (x : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) a)
        (y : GrindChal bits (ChalTensorMulti P.ldt W M P.queries) b),
        HEq x y → queryPointTensorMulti P x.2 k = queryPointTensorMulti P y.2 k := by
      rintro a _ rfl x y h; rw [eq_of_heq h]
    exact this _ _ hstep.symm _ _ hans
  refine ⟨by simp [freeChallengerTensorMulti, spongeChallengerTensorMulti, hstep, hns_eq,
      hfst, hqp], ?_⟩
  rcases hrel with ⟨hr, hns, hlen, rfl⟩ | ⟨hr, hlen, rfl⟩ | ⟨hr, rfl⟩
  · have heq : fs.cur.length = P.batches := by rcases hready with h1 | h2 <;> omega
    right; left
    refine ⟨hr, by dsimp only [freeChallengerTensorMulti]; omega, ?_⟩
    simp only [freeChallengerTensorMulti, spongeChallengerTensorMulti, heq, hns]
    rw [← heq, List.take_length, List.drop_length]
  · right; left; exact ⟨hr, hlen, rfl⟩
  · right; right; exact ⟨hr, rfl⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_checkWitness (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    {fs : FreeState F EF D} {ss : SpongeState F EF D}
    (hrel : StateRelTensorMulti P W M bits s₀ f fs ss)
    (hready : 1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) (powBits : ℕ) (w : F) :
    ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).checkWitness fs powBits w).1 =
      ((spongeChallengerTensorMulti P W M tailLen bits f m).checkWitness ss powBits w).1 ∧
    StateRelTensorMulti P W M bits s₀ f
      ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).checkWitness fs powBits w).2
      ((spongeChallengerTensorMulti P W M tailLen bits f m).checkWitness ss powBits w).2 ∧
    (1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).checkWitness fs powBits w).2.round ∨
      P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).checkWitness fs powBits w).2.cur.length) := by
  unfold Challenger.checkWitness
  have hokF : ∀ s, (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
      (liftSpongeOracleTensorMulti P W M bits s₀ f) m).ok s = true := fun _ => rfl
  have hokS : ∀ s, (spongeChallengerTensorMulti P W M tailLen bits f m).ok s = true := fun _ => rfl
  simp only [hokF, hokS, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
  split_ifs with h0
  · exact ⟨rfl, hrel, hready⟩
  · have hobs := stateRelTensorMulti_observe m P W M tailLen bits s₀ f hrel (.base w)
    have hready' : 1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe fs (.base w)).round ∨
        P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe fs (.base w)).cur.length := by
      simp only [freeChallengerTensorMulti]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases hready with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by dsimp only; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hb1, hb2⟩ :=
      stateRelTensorMulti_sampleBits m P W M tailLen bits s₀ f hobs hready' powBits
    exact ⟨by simp [hb1], hb2, hready'⟩

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] [Inhabited D] in
private theorem stateRelTensorMulti_sampleIndices (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    (nbits : ℕ) : ∀ (count : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensorMulti P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).sampleIndices nbits count fs =
        (spongeChallengerTensorMulti P W M tailLen bits f m).sampleIndices nbits count ss
  | 0, _, _, _, _ => rfl
  | count + 1, fs, ss, hrel, hready => by
    simp only [Challenger.sampleIndices]
    obtain ⟨h1, h2⟩ := stateRelTensorMulti_sampleBits m P W M tailLen bits s₀ f hrel hready nbits
    rw [h1, stateRelTensorMulti_sampleIndices P W M tailLen bits s₀ f nbits count h2 hready]

omit [TwoAdicOps F] [Fintype K] [DecidableEq D] in
private theorem stateRelTensorMulti_commitPhase (P : Compiled.MultiParams K) (W M tailLen : ℕ)
    (bits : ℕ → ℕ) (s₀ : D)
    (f : ∀ x : SpongeQuery (RawMsg F EF D) D (HashQuery K D),
      SpongeMerkleAnswer (RawMsg F EF D) (SpongeChalTensorMulti P W M bits) K D x)
    (commitPowBits : ℕ) (commits : Array D) (witnesses : Array F) :
    ∀ (rounds : ℕ) {fs : FreeState F EF D} {ss : SpongeState F EF D},
      StateRelTensorMulti P W M bits s₀ f fs ss → (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).1 =
        (commitPhase (spongeChallengerTensorMulti P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).1 ∧
      (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.1 =
        (commitPhase (spongeChallengerTensorMulti P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).2.1 ∧
      StateRelTensorMulti P W M bits s₀ f
        (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2
        (commitPhase (spongeChallengerTensorMulti P W M tailLen bits f m)
          commitPowBits commits witnesses rounds ss).2.2 ∧
      (1 ≤ (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.round ∨
        P.batches ≤ (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
          commitPowBits commits witnesses rounds fs).2.2.cur.length)
  | 0, _, _, hrel, hready => ⟨rfl, rfl, hrel, hready⟩
  | r + 1, fs, ss, hrel, hready => by
    obtain ⟨h1, h2, h3, h4⟩ := stateRelTensorMulti_commitPhase P W M tailLen bits s₀ f
      commitPowBits commits witnesses r hrel hready
    simp only [commitPhase]
    let fs_prev := (commitPhase (freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m)
        commitPowBits commits witnesses r fs).2.2
    have hobs :=
      stateRelTensorMulti_observe m P W M tailLen bits s₀ f h3 (.digest (commits.getD r default))
    have hready' : 1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).round ∨
        P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
          (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observe
          fs_prev (.digest (commits.getD r default))).cur.length := by
      simp only [freeChallengerTensorMulti]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases h4 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (by dsimp only [fs_prev] at *; simp; omega)
      · exact Or.inl (by dsimp only; omega)
    obtain ⟨hw1, hw2, hw3⟩ := stateRelTensorMulti_checkWitness m P W M tailLen bits s₀ f
      hobs hready' commitPowBits (witnesses.getD r 0)
    obtain ⟨he1, he2⟩ := stateRelTensorMulti_sampleExt m P W M tailLen bits s₀ f hw2 hw3
    exact ⟨by rw [h1, he1], by rw [h2, hw1], he2, hw3⟩

end SpongeMultiSim

section ExecSpongeTensorMulti

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Fintype K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
  (wf : WellFormed m params shape)
  (hpos : ∀ a ∈ arities, 0 < a) (hsum : arities.sum ≤ logMaxHeight params.logBlowup shape)

/-- Incremental sponge oracle answer type for multi-arity `Fri.verifyTensorWithSchedule`. -/
abbrev SpongeTensorMultiOracleAnswer :=
  SpongeMerkleAnswer (RawMsg F EF D)
    (SpongeChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
      (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      (powBitsMulti params arities)) K D

/-- Step message reader against committed rows `c`: depends ONLY on the
`≤ 1` digest in `spongeStepDigestsMulti P i msg`. -/
noncomputable def spongeStepReadMulti (i : ℕ) (msg : RawMsg F EF D)
    (c : Compiled.Committed K D) :
    StepMsgMulti K (modelParamsMulti m params shape arities wf hpos hsum).numClaims :=
  let P := modelParamsMulti m params shape arities wf hpos hsum
  if hlt : i < P.batches then
    { batchFn := fun b mat idx col =>
        if b = i then
          Compiled.entry (c ((digestsIn msg).getD 0 default) (P.dims ⟨i, hlt⟩) mat idx) col
        else 0
      claims := fun _ _ => ⟨0, 0, 0⟩
      word := 0 }
  else if i = P.batches then
    let v := viewMulti m params shape arities msg
    { batchFn := fun _ _ _ _ => 0
      claims := fun r k => ⟨0, v.point r k.val, v.value r k.val⟩
      word := 0 }
  else
    { batchFn := fun _ _ _ _ => 0
      claims := fun _ _ => ⟨0, 0, 0⟩
      word := (P.read (i - P.batches) (viewMulti m params shape arities msg) c).word }

omit [Fintype K] [DecidableEq D] in
theorem spongeStepReadMulti_congr (i : ℕ) (msg : RawMsg F EF D)
    (c c' : Compiled.Committed K D)
    (hc : ∀ root ∈ spongeStepDigestsMulti (modelParamsMulti m params shape arities wf hpos hsum)
      i msg, c root = c' root) :
    spongeStepReadMulti m params shape arities wf hpos hsum i msg c =
      spongeStepReadMulti m params shape arities wf hpos hsum i msg c' := by
  unfold spongeStepReadMulti spongeStepDigestsMulti at *
  dsimp only
  split_ifs with h1 h2
  · simp only [h1, ↓reduceIte, List.mem_singleton, forall_eq] at hc
    congr 1
    funext b mat idx col
    split_ifs with hb
    · rw [hc]
    · rfl
  · rfl
  · congr 1
    have hread : (modelParamsMulti m params shape arities wf hpos hsum).read
          (i - (modelParamsMulti m params shape arities wf hpos hsum).batches)
          (viewMulti m params shape arities msg) c =
        (modelParamsMulti m params shape arities wf hpos hsum).read
          (i - (modelParamsMulti m params shape arities wf hpos hsum).batches)
          (viewMulti m params shape arities msg) c' := by
      refine (modelParamsMulti m params shape arities wf hpos hsum).read_congr _
        (viewMulti m params shape arities msg) c c' fun root hr => ?_
      have hne0 : i - (modelParamsMulti m params shape arities wf hpos hsum).batches ≠ 0 := by omega
      by_cases h3 : i ≤ (modelParamsMulti m params shape arities wf hpos hsum).batches +
          (modelParamsMulti m params shape arities wf hpos hsum).rounds
      · simp only [h1, h2, h3, ↓reduceIte, List.mem_singleton, forall_eq] at hc
        have hle : i - (modelParamsMulti m params shape arities wf hpos hsum).batches ≤
            (modelParamsMulti m params shape arities wf hpos hsum).rounds := by omega
        simp only [Compiled.digestsOfAt, hne0, ↓reduceIte, hle, List.mem_singleton] at hr
        subst hr
        exact hc
      · have hgt : ¬ (i - (modelParamsMulti m params shape arities wf hpos hsum).batches ≤
            (modelParamsMulti m params shape arities wf hpos hsum).rounds) := by omega
        simp only [Compiled.digestsOfAt, hne0, ↓reduceIte, hgt, List.not_mem_nil] at hr
    exact congrArg PcsRbr.Msg.word hread

/-- **Executable `Fri.verifyTensorWithSchedule` against an incremental sponge oracle `f`.** -/
noncomputable def spongeAcceptsTensorMulti (s₀ : D)
    (f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) : Bool :=
  Fri.verifyTensorWithSchedule (merkleMmcs (inputHasher m (spongeHasherOf f)))
    (merkleMmcs (friHasher m (spongeHasherOf f)))
    (spongeChallengerTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
      (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
      (firstMessageTailLen params shape) (powBitsMulti params arities) f m)
    (SpongeState.init s₀) params shape arities a.commitments a.points a.values a.proof

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_prefix_eqTM (s₀ : D)
    (f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) (hcomm : a.commitments.size = shape.length) :
    ∀ k ≤ shape.length,
      (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a) k).2 =
        (foldSpongeListTM f 0 s₀
          ((firstMessage (F := F) a.commitments a.points a.values).take k)).2
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := spongeTranscript_prefix_eqTM s₀ f a hcomm k (by omega)
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
    rw [htake, foldSpongeListTM_append]
    dsimp only
    have hfst : (foldSpongeListTM f 0 s₀
        ((firstMessage (F := F) a.commitments a.points a.values).take k)).1 = k := by
      rw [foldSpongeListTM_fst, Nat.zero_add, List.length_take, Nat.min_eq_left]
      simp [firstMessage, hcomm]; omega
    have hmsg : spongeMessagesMulti params shape arities a k =
        [.digest (a.commitments.getD k default)] := by
      unfold spongeMessagesMulti
      rw [ite_eq_left (by omega)]
    rw [hfst, foldSpongeListTM, foldSpongeListTM, spongeTranscript_succ_sndTM, ih, hmsg]

omit [Fintype K] [DecidableEq D] in
private theorem spongeTranscript_eq_liftTM (s₀ : D)
    (f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a) (shape.length + k)).2 =
        (if k = 0 then
          (foldSpongeListTM f 0 s₀
            ((firstMessage (F := F) a.commitments a.points a.values).take shape.length)).2
        else
          transcriptSpongeStateTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
            (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
            (powBitsMulti params arities) s₀ f
            (fsTranscript
              (liftSpongeOracleTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
                (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
                (powBitsMulti params arities) s₀ f)
              (messagesMulti params arities a.commitments a.points a.values a.proof) k))
  | 0 => by
    simp only [Nat.add_zero, ↓reduceIte]
    exact spongeTranscript_prefix_eqTM m params shape arities wf hpos hsum s₀ f a hcomm
      shape.length le_rfl
  | 1 => by
    have h0 := spongeTranscript_prefix_eqTM m params shape arities wf hpos hsum s₀ f a hcomm
      shape.length le_rfl
    have hmsg : spongeMessagesMulti params shape arities a shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length := by
      rw [drop_firstMessage_eqTM shape a hcomm]
      unfold spongeMessagesMulti
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    rw [spongeTranscript_succ_sndTM, h0, hmsg]
    rfl
  | k + 2 => by
    have ih := spongeTranscript_eq_liftTM s₀ f a hcomm (k + 1)
    simp only [Nat.succ_ne_zero, ↓reduceIte] at ih ⊢
    have hmsg : spongeMessagesMulti params shape arities a (shape.length + (k + 1)) =
        messagesMulti params arities a.commitments a.points a.values a.proof (k + 1) := by
      unfold spongeMessagesMulti
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    rw [show shape.length + (k + 2) = (shape.length + (k + 1)) + 1 by omega,
      spongeTranscript_succ_sndTM, ih, hmsg]
    rfl

omit [Fintype K] in
/-- **Refinement of `spongeAcceptsTensorMulti` to `acceptsTensorMulti (liftSpongeOracleTensorMulti ...)`.** -/
theorem acceptsTensorMulti_liftSpongeOracle_of_spongeAcceptsTensorMulti (s₀ : D)
    (f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D)
    (h : spongeAcceptsTensorMulti m params shape arities wf hpos hsum s₀ f a = true) :
    acceptsTensorMulti m params shape arities wf hpos hsum
      (liftSpongeOracleTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (powBitsMulti params arities) s₀ f) a = true := by
  unfold spongeAcceptsTensorMulti Fri.verifyTensorWithSchedule at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  have hcomm : a.commitments.size = shape.length := by
    unfold Fri.shapeOkMultiArity at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.1.2
  have hpts_sz : a.points.size = (pointRefs params.logBlowup shape).length := by
    unfold Fri.shapeOkMultiArity at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.1.2
  have hvals_sz : a.values.size = (claimRefs params.logBlowup shape).length := by
    unfold Fri.shapeOkMultiArity at hshape
    simp only [Bool.and_eq_true, beq_iff_eq] at hshape
    exact hshape.1.1.1.1.1.1.1.2
  let P := modelParamsMulti m params shape arities wf hpos hsum
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let tailLen := firstMessageTailLen params shape
  let bits := powBitsMulti params arities
  let fl := liftSpongeOracleTensorMulti P W M bits s₀ f
  have hfl_len : firstMessageLen params shape = P.batches + tailLen :=
    firstMessageLen_eq_batches_add_tailLen params shape
  have hinit : StateRelTensorMulti P W M bits s₀ f FreeState.init (SpongeState.init s₀) := by
    left; exact ⟨rfl, rfl, Nat.zero_le _, rfl⟩
  have hfirst := stateRelTensorMulti_observeAll m P W M tailLen bits s₀ f
    (firstMessage (F := F) a.commitments a.points a.values) hinit
  have hfirst_len : (firstMessage (F := F) a.commitments a.points a.values).length =
      P.batches + tailLen := by
    simp only [firstMessage, List.length_append, List.length_map, Array.length_toList,
      hcomm, hpts_sz, hvals_sz, P, modelParamsMulti, tailLen, firstMessageTailLen]
    omega
  have hready0 : 1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll
        FreeState.init (firstMessage (F := F) a.commitments a.points a.values)).round ∨
      P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll
        FreeState.init (firstMessage (F := F) a.commitments a.points a.values)).cur.length := by
    right
    have hobs_cur : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
        fs.round = 0 → fs.nsamp = 0 → fs.cur.length + obs.length ≤ P.batches + tailLen →
        ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll fs obs).cur =
          fs.cur ++ obs ∧
        ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll fs obs).round = 0 ∧
        ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll fs obs).nsamp = 0 := by
      intro obs
      induction obs with
      | nil => intro fs hr hns _; simp [Challenger.observeAll, hr, hns]
      | cons o obs ih =>
        intro fs hr hns hlen
        have hlt : fs.cur.length < P.batches + tailLen := by simp at hlen; omega
        have hstep : (freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll
              fs (o :: obs) =
            (freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll
              { fs with cur := fs.cur ++ [o] } obs := by
          simp only [Challenger.observeAll, List.foldl_cons, freeChallengerTensorMulti, hns,
            ↓reduceIte, show fs.cur.length ≠ P.batches + tailLen by omega, and_false]
        rw [hstep]
        obtain ⟨hcur, hr', hns'⟩ := ih { fs with cur := fs.cur ++ [o] } hr hns
          (by simp at hlen ⊢; omega)
        exact ⟨by simpa [List.append_assoc] using hcur, hr', hns'⟩
    have hc := (hobs_cur (firstMessage (F := F) a.commitments a.points a.values) FreeState.init
      rfl rfl (by simp [FreeState.init, hfirst_len])).1
    rw [hc]
    simp [FreeState.init, hfirst_len]
  obtain ⟨hcol1, hcol2, hcol3⟩ := stateRelTensorMulti_sampleExtMany m P W M tailLen bits s₀ f
    (tensorNumChallenges W) hfirst hready0
  obtain ⟨hopen1, hopen2, hopen3⟩ := stateRelTensorMulti_sampleExtMany m P W M tailLen bits s₀ f
    (tensorNumChallenges M) hcol2 hcol3
  have hsched1 : (TensorSchedule.sample
        (freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m)
        ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m).observeAll
          FreeState.init (firstMessage (F := F) a.commitments a.points a.values)) W M).1 =
      (TensorSchedule.sample (spongeChallengerTensorMulti P W M tailLen bits f m)
        ((spongeChallengerTensorMulti P W M tailLen bits f m).observeAll
          (SpongeState.init s₀) (firstMessage (F := F) a.commitments a.points a.values)) W M).1 := by
    dsimp only [fl, TensorSchedule.sample]
    rw [hcol1, hopen1]
  obtain ⟨hc1, hc2, hc3, hc4⟩ := stateRelTensorMulti_commitPhase m P W M tailLen bits s₀ f
    params.commitPowBits a.proof.commitPhaseCommits a.proof.commitPowWitnesses
    arities.length hopen2 hopen3
  have hfin := stateRelTensorMulti_observeAll m P W M tailLen bits s₀ f
    (finalMessageMulti (F := F) (D := D) arities a.proof.finalPoly) hc3
  have hpres : ∀ (obs : List (Observation F EF D)) (fs : FreeState F EF D),
      (1 ≤ fs.round ∨ P.batches ≤ fs.cur.length) →
      1 ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observeAll fs obs).round ∨
      P.batches ≤ ((freeChallengerTensorMulti P W M (P.batches + tailLen) bits
        (liftSpongeOracleTensorMulti P W M bits s₀ f) m).observeAll fs obs).cur.length := by
    intro obs
    induction obs with
    | nil => intro fs h; exact h
    | cons o obs ih =>
      intro fs h
      refine ih _ ?_
      simp only [freeChallengerTensorMulti]
      split_ifs
      · exact Or.inl (by dsimp only; omega)
      · rcases h with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by dsimp only; simp; omega)
      · exact Or.inl (by dsimp only; omega)
  have hready_fin := hpres
    (finalMessageMulti (F := F) (D := D) arities a.proof.finalPoly) _ hc4
  obtain ⟨hp1, hp2, hp3⟩ := stateRelTensorMulti_checkWitness m P W M tailLen bits s₀ f
    hfin hready_fin params.queryPowBits a.proof.queryPowWitness
  have hidx := stateRelTensorMulti_sampleIndices m P W M tailLen bits s₀ f
    (logMaxHeight params.logBlowup shape) params.numQueries hp2 hp3
  have htr : Fri.transcriptTensorMulti
        (freeChallengerTensorMulti P W M (P.batches + tailLen) bits fl m)
        FreeState.init params shape arities a.commitments a.points a.values a.proof =
      Fri.transcriptTensorMulti (spongeChallengerTensorMulti P W M tailLen bits f m)
        (SpongeState.init s₀) params shape arities a.commitments a.points a.values a.proof := by
    unfold Fri.transcriptTensorMulti Fri.transcriptTailTensorMulti
    dsimp only
    rw [hsched1]
    dsimp only [fl, TensorSchedule.sample]
    rw [hc1, hc2, hp1, hidx]
  unfold acceptsTensorMulti Fri.verifyTensorWithSchedule
  rw [Bool.and_eq_true]
  refine ⟨hshape, ?_⟩
  change Fri.verifyWithTensorMulti (merkleMmcs (inputHasher m (hasherOf fl)))
      (merkleMmcs (friHasher m (hasherOf fl))) params shape arities a.commitments a.points
      a.values a.proof (Fri.transcriptTensorMulti (freeChallengerTensorMulti P W M
        (firstMessageLen params shape) bits fl m) FreeState.init params shape arities
        a.commitments a.points a.values a.proof) = true
  rw [hfl_len, htr, hasherOf_liftSpongeOracleTensorMulti P W M bits s₀ f]
  exact hwith

/-! ## 2. Incremental Sponge Experiment & Generic Soundness (`c = 3 / 2`) -/

variable [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D]

/-- Verify a multi-arity tensor proof against the sponge-derived transcript. -/
noncomputable def spongeVerifyTensorMulti (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (powBitsMulti params arities))
      ((modelParamsMulti m params shape arities wf hpos hsum).batches +
        ((modelParamsMulti m params shape arities wf hpos hsum).rounds + 2)) × D) :
    OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) Bool :=
  let P := modelParamsMulti m params shape arities wf hpos hsum
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let bits := powBitsMulti params arities
  let tg := spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
    (fun j => viewMulti m params shape arities
      (messagesMulti params arities a.commitments a.points a.values a.proof j))
    (P.rounds + 2) ts.1
  @ite _ (PowPasses tg) (Classical.propDecidable _)
    (let tu := ungrind tg
    mapHashToSponge (M := RawMsg F EF D) (C := SpongeChalTensorMulti P W M bits)
      (P.verifyWithTensor (M' := Empty) (C := fun _ => PUnit) W M
        (tensorCoordMulti params shape arities)
        (modelProofMulti m params shape a.proof) (Compiled.msgAt tu)
        (tensorOfMulti tu) (betasOfTensorMulti tu) (fun k => P.indexOf (queriesOfTensorMulti tu k))))
    (.pure false)

omit [Fintype K] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
theorem queryBound_spongeVerifyTensorMulti (a : Attempt F EF D)
    (ts : Oracle.Transcript (RawMsg F EF D)
      (SpongeChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
        (powBitsMulti params arities))
      ((modelParamsMulti m params shape arities wf hpos hsum).batches +
        ((modelParamsMulti m params shape arities wf hpos hsum).rounds + 2)) × D) :
    (spongeVerifyTensorMulti m params shape arities wf hpos hsum a ts).QueryBound
      (modelParamsMulti m params shape arities wf hpos hsum).verifierQueries := by
  unfold spongeVerifyTensorMulti
  dsimp only
  split
  · exact queryBound_mapHashToSponge
      ((modelParamsMulti m params shape arities wf hpos hsum).queryBound_verifyWithTensor
        _ _ _ _ _ _ _ _)
  · exact queryBound_pure _ _

/-- **Incremental sponge soundness experiment for `Fri.verifyTensorWithSchedule`.** -/
noncomputable def spongeExperimentTensorMulti {A : Type*} (s₀ : D)
    (adv : OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A)
    (attempt : A → Attempt F EF D) :
    OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum)
      (A × Bool) :=
  (Oracle.spongeExperiment s₀
      ((modelParamsMulti m params shape arities wf hpos hsum).batches +
        ((modelParamsMulti m params shape arities wf hpos hsum).rounds + 2))
      adv (fun a => spongeMessagesMulti params shape arities (attempt a))).bind fun out =>
    (spongeVerifyTensorMulti m params shape arities wf hpos hsum (attempt out.1) out.2).bind
      fun b => .pure (out.1, b)

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem spongeToGrindTranscriptTensorMulti_eq_fsTranscript (s₀ : D)
    (f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x)
    (a : Attempt F EF D) (hcomm : a.commitments.size = shape.length) :
    ∀ k,
      spongeToGrindTranscriptTensorMulti
        (P := modelParamsMulti m params shape arities wf hpos hsum)
        (W := maxWidth shape) (M := maxOpeningsPerHeight params.logBlowup shape)
        (bits := powBitsMulti params arities)
        (M' := Compiled.Msg K D (modelParamsMulti m params shape arities wf hpos hsum).batches)
        (fun j => viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof j)) k
        (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a)
          ((modelParamsMulti m params shape arities wf hpos hsum).batches + k)).1 =
      (fsTranscript
        (liftSpongeOracleTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
          (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
          (powBitsMulti params arities) s₀ f)
        (messagesMulti params arities a.commitments a.points a.values a.proof) k).mapIdx
          (fun _ msg => (viewMulti m params shape arities msg :
            Compiled.Msg K D (modelParamsMulti m params shape arities wf hpos hsum).batches))
  | 0 => rfl
  | 1 => by
    let P := modelParamsMulti m params shape arities wf hpos hsum
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBitsMulti params arities
    have h0 : (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a) P.batches).2 =
        (foldSpongeListTM f 0 s₀
          ((firstMessage (F := F) a.commitments a.points a.values).take P.batches)).2 :=
      spongeTranscript_prefix_eqTM m params shape arities wf hpos hsum s₀ f a hcomm
        shape.length le_rfl
    have hmsg : spongeMessagesMulti params shape arities a P.batches =
        (firstMessage (F := F) a.commitments a.points a.values).drop P.batches := by
      change spongeMessagesMulti params shape arities a shape.length =
        (firstMessage (F := F) a.commitments a.points a.values).drop shape.length
      rw [drop_firstMessage_eqTM shape a hcomm]
      unfold spongeMessagesMulti
      rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
    have hsucc := spongeTranscript_succ_fstTM f s₀ (spongeMessagesMulti params shape arities a)
      P.batches
    change spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof j)) 1
        (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a) (P.batches + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc .nil
        (viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof 0))
        (spongeChalTensorMultiCast P W M bits (k := 0) (f (.chal P.batches
          (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a) P.batches).2
          (spongeMessagesMulti params shape arities a P.batches))).2) =
      Oracle.Transcript.snoc .nil
        (viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof 0))
        (liftSpongeOracleTensorMulti P W M bits s₀ f
          (.chal .nil (messagesMulti params arities a.commitments a.points a.values a.proof 0)))
    rw [h0, hmsg]
    rfl
  | k + 2 => by
    let P := modelParamsMulti m params shape arities wf hpos hsum
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBitsMulti params arities
    have ih := spongeToGrindTranscriptTensorMulti_eq_fsTranscript s₀ f a hcomm (k + 1)
    have hst : (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a)
          (P.batches + (k + 1))).2 =
        transcriptSpongeStateTensorMulti P W M bits s₀ f
          (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities a.commitments a.points a.values a.proof) (k + 1)) := by
      have h := spongeTranscript_eq_liftTM m params shape arities wf hpos hsum s₀ f a hcomm (k + 1)
      simp only [Nat.succ_ne_zero, ↓reduceIte] at h
      exact h
    have hmsg : spongeMessagesMulti params shape arities a (P.batches + (k + 1)) =
        messagesMulti params arities a.commitments a.points a.values a.proof (k + 1) := by
      change spongeMessagesMulti params shape arities a (shape.length + (k + 1)) = _
      unfold spongeMessagesMulti
      rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    have hsucc := spongeTranscript_succ_fstTM f s₀ (spongeMessagesMulti params shape arities a)
      (P.batches + (k + 1))
    change spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof j)) (k + 2)
        (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a)
          ((P.batches + (k + 1)) + 1)).1 = _
    rw [hsucc]
    change Oracle.Transcript.snoc
        (spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
          (M' := Compiled.Msg K D P.batches)
          (fun j => viewMulti m params shape arities
            (messagesMulti params arities a.commitments a.points a.values a.proof j)) (k + 1)
          (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a)
            (P.batches + (k + 1))).1)
        (viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof (k + 1)))
        (spongeChalTensorMultiCast P W M bits (k := k + 1) (f (.chal (P.batches + (k + 1))
          (spongeTranscript f s₀ (spongeMessagesMulti params shape arities a)
            (P.batches + (k + 1))).2
          (spongeMessagesMulti params shape arities a (P.batches + (k + 1))))).2) =
      Oracle.Transcript.snoc
        ((fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
          (messagesMulti params arities a.commitments a.points a.values a.proof)
          (k + 1)).mapIdx (fun _ msg => (viewMulti m params shape arities msg :
            Compiled.Msg K D P.batches)))
        (viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof (k + 1)))
        (liftSpongeOracleTensorMulti P W M bits s₀ f
          (.chal (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities a.commitments a.points a.values a.proof) (k + 1))
            (messagesMulti params arities a.commitments a.points a.values a.proof (k + 1))))
    rw [ih, hst, hmsg]
    rfl

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem extractBatchFnMulti_mapIdx_eq (a : Attempt F EF D) (c : Compiled.Committed K D) :
    ∀ (n : ℕ) (hn : n ≤ (modelParamsMulti m params shape arities wf hpos hsum).batches)
      (t : Oracle.Transcript (RawMsg F EF D)
        (SpongeChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
          (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
          (powBitsMulti params arities)) n),
      t.msgs = (List.range n).map (spongeMessagesMulti params shape arities a) →
      ∀ (b : ℕ) (hb : b < n),
        extractBatchFnMulti (modelParamsMulti m params shape arities wf hpos hsum)
          (t.mapIdx fun j msg => spongeStepReadMulti m params shape arities wf hpos hsum j msg c) b =
        fun mat idx col =>
          Compiled.entry (c (a.commitments.getD b default)
            ((modelParamsMulti m params shape arities wf hpos hsum).dims ⟨b, lt_of_lt_of_le hb hn⟩)
            mat idx) col
  | 0, _, _, _, b, hb => absurd hb (Nat.not_lt_zero b)
  | n + 1, hn, .snoc t' msg ch, hmsgs, b, hb => by
    let P := modelParamsMulti m params shape arities wf hpos hsum
    have hmsgs' : t'.msgs = (List.range n).map (spongeMessagesMulti params shape arities a) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.append_inj h1 (by rw [t'.length_msgs, List.length_map, List.length_range])).1
    have hmsg_eq : msg = spongeMessagesMulti params shape arities a n := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.cons.inj (List.append_inj h1
        (by rw [t'.length_msgs, List.length_map, List.length_range])).2).1
    have hn_lt : n < (modelParamsMulti m params shape arities wf hpos hsum).batches := hn
    simp only [Transcript.mapIdx_snoc, extractBatchFnMulti, ite_eq_left hn_lt]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
    · rw [Function.update_of_ne hlt.ne]
      exact extractBatchFnMulti_mapIdx_eq a c n (Nat.le_of_succ_le hn) t' hmsgs' b hlt
    · rw [Function.update_self, hmsg_eq]
      unfold spongeStepReadMulti
      dsimp only
      rw [dite_eq_left hn_lt]
      funext mat idx col
      simp only [↓reduceIte]
      have hsm : spongeMessagesMulti params shape arities a b =
          [.digest (a.commitments.getD b default)] := by
        unfold spongeMessagesMulti
        rw [ite_eq_left (show b < shape.length from hn_lt)]
      rw [hsm]
      rfl

omit [Fintype K] [DecidableEq D] [DecidableEq F] [DecidableEq EF] [Fintype D] [Nonempty D] in
private theorem extractPcsTensorMulti_mapIdx_eq (a : Attempt F EF D) (c : Compiled.Committed K D) :
    ∀ (k : ℕ)
      (t : Oracle.Transcript (RawMsg F EF D)
        (SpongeChalTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
          (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
          (powBitsMulti params arities))
        ((modelParamsMulti m params shape arities wf hpos hsum).batches + k)),
      t.msgs = (List.range ((modelParamsMulti m params shape arities wf hpos hsum).batches + k)).map
        (spongeMessagesMulti params shape arities a) →
      extractPcsTensorMulti (modelParamsMulti m params shape arities wf hpos hsum)
          (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)
          (powBitsMulti params arities) k
          (t.mapIdx fun j msg => spongeStepReadMulti m params shape arities wf hpos hsum j msg c) =
        (spongeToGrindTranscriptTensorMulti
            (P := modelParamsMulti m params shape arities wf hpos hsum)
            (W := maxWidth shape) (M := maxOpeningsPerHeight params.logBlowup shape)
            (bits := powBitsMulti params arities)
            (M' := Compiled.Msg K D (modelParamsMulti m params shape arities wf hpos hsum).batches)
            (fun j => viewMulti m params shape arities
              (messagesMulti params arities a.commitments a.points a.values a.proof j)) k t).mapIdx
          fun j msg => (modelParamsMulti m params shape arities wf hpos hsum).read j msg c
  | 0, _, _ => rfl
  | k + 1, .snoc t' msg chal, hmsgs => by
    let P := modelParamsMulti m params shape arities wf hpos hsum
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let bits := powBitsMulti params arities
    have hmsgs' : t'.msgs =
        (List.range (P.batches + k)).map (spongeMessagesMulti params shape arities a) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.append_inj h1 (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).1
    have hmsg_eq : msg = spongeMessagesMulti params shape arities a (P.batches + k) := by
      have h1 := hmsgs
      rw [Transcript.msgs_snoc, show P.batches + (k + 1) = P.batches + k + 1 by omega,
        List.range_succ, List.map_append, List.map_singleton] at h1
      exact (List.cons.inj (List.append_inj h1
        (by rw [t'.length_msgs, List.length_map, List.length_range]; rfl)).2).1
    change Oracle.Transcript.snoc
        (extractPcsTensorMulti P W M bits k
          (t'.mapIdx fun j msg => spongeStepReadMulti m params shape arities wf hpos hsum j msg c))
        (extractStepPcsMsgMulti P
          (extractBatchFnMulti P
            (t'.mapIdx fun j msg => spongeStepReadMulti m params shape arities wf hpos hsum j msg c))
          k (spongeStepReadMulti m params shape arities wf hpos hsum (P.batches + k) msg c))
        (spongeChalTensorMultiCast P W M bits chal) =
      Oracle.Transcript.snoc
        ((spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
            (M' := Compiled.Msg K D P.batches)
            (fun j => viewMulti m params shape arities
              (messagesMulti params arities a.commitments a.points a.values a.proof j)) k t').mapIdx
          fun j msg => P.read j msg c)
        (P.read k (viewMulti m params shape arities
          (messagesMulti params arities a.commitments a.points a.values a.proof k)) c)
        (spongeChalTensorMultiCast P W M bits chal)
    rw [extractPcsTensorMulti_mapIdx_eq a c k t' hmsgs']
    congr 1
    cases k with
    | zero =>
      subst hmsg_eq
      have hbfn := extractBatchFnMulti_mapIdx_eq m params shape arities wf hpos hsum a c
        P.batches le_rfl t' hmsgs'
      have hread0 : spongeStepReadMulti m params shape arities wf hpos hsum P.batches
          (spongeMessagesMulti params shape arities a P.batches) c =
          { batchFn := fun _ _ _ _ => 0
            claims := fun r cl =>
              ⟨0, (viewMulti m params shape arities
                    (spongeMessagesMulti params shape arities a P.batches)).point r cl.val,
                  (viewMulti m params shape arities
                    (spongeMessagesMulti params shape arities a P.batches)).value r cl.val⟩
            word := 0 } := by
        unfold spongeStepReadMulti
        dsimp only
        rw [dite_eq_right (lt_irrefl _), ite_eq_left rfl]
      have hexts : extsIn m (spongeMessagesMulti params shape arities a P.batches) =
          extsIn m (messagesMulti params arities a.commitments a.points a.values a.proof 0) := by
        have hs : spongeMessagesMulti params shape arities a P.batches =
            a.points.toList.map .ext ++ a.values.toList.map .ext := by
          change spongeMessagesMulti params shape arities a shape.length = _
          unfold spongeMessagesMulti
          rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl]
        have hm0 : messagesMulti params arities a.commitments a.points a.values a.proof 0 =
            firstMessage (F := F) a.commitments a.points a.values := rfl
        have hext_append : ∀ l₁ l₂ : List (Observation F EF D),
            extsIn m (l₁ ++ l₂) = extsIn m l₁ ++ extsIn m l₂ := fun l₁ l₂ => by
          simp [extsIn, List.filterMap_append]
        have hdigs : extsIn m (a.commitments.toList.map (Observation.digest (F := F) (EF := EF))) = [] := by
          unfold extsIn; induction a.commitments.toList <;> simp [*]
        rw [hs, hm0, firstMessage, hext_append, hext_append, hext_append, hdigs, List.nil_append]
      have hfirst : ∀ b : Fin P.batches,
          (viewMulti m params shape arities
            (messagesMulti params arities a.commitments a.points a.values a.proof 0)).inputRoots b =
            a.commitments.getD b.val default := by
        intro b
        have hm0 : messagesMulti params arities a.commitments a.points a.values a.proof 0 =
            firstMessage (F := F) a.commitments a.points a.values := rfl
        change (digestsIn (messagesMulti params arities a.commitments a.points a.values a.proof 0)).getD
          b.val default = a.commitments.getD b.val default
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
      rw [Nat.add_zero, hread0]
      unfold extractStepPcsMsgMulti MultiParams.read
      simp only [↓reduceIte]
      congr 1
      funext r cl
      dsimp only [MultiParams.claims]
      congr 1
      · congr 1
        funext idx
        rw [hbfn (P.slot r cl).batch.val (P.slot r cl).batch.isLt, hfirst (P.slot r cl).batch]
      · simp [Compiled.Msg.point, viewMulti, hexts]
      · simp [Compiled.Msg.value, viewMulti, hexts]
    | succ k' =>
      subst hmsg_eq
      have hgt : ¬ (P.batches + (k' + 1) < P.batches) := by omega
      have hne : P.batches + (k' + 1) ≠ P.batches := by omega
      have hsub : P.batches + (k' + 1) - P.batches = k' + 1 := Nat.add_sub_cancel_left _ _
      have hmsg' : spongeMessagesMulti params shape arities a (P.batches + (k' + 1)) =
          messagesMulti params arities a.commitments a.points a.values a.proof (k' + 1) := by
        unfold spongeMessagesMulti
        have hb : P.batches = shape.length := rfl
        rw [hb, ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
      rw [hmsg']
      unfold spongeStepReadMulti extractStepPcsMsgMulti MultiParams.read
      dsimp only
      rw [dite_eq_right hgt, ite_eq_right hne, hsub]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      congr 1

/-- **Generic incremental sponge soundness (`c = 3 / 2`) for executable
`Fri.verifyTensorWithSchedule`** with arbitrary variable per-round arity schedule `arities`. -/
theorem soundnessTensorMulti_sponge (s₀ : D) {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      Tensor2DMCA (((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain j).image
          ((modelParamsMulti m params shape arities wf hpos hsum).shift * ·))
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.degree j)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) θ (εα j))
    (hε₀ : ∀ j ≤ (modelParamsMulti m params shape arities wf hpos hsum).rounds, εα j ≤ ε₀)
    (hstep : ∀ i < (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      StepMCAArity (2 ^ (modelParamsMulti m params shape arities wf hpos hsum).logArity i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.zeta i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain i)
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.domain (i + 1))
        ((modelParamsMulti m params shape arities wf hpos hsum).ldt.degree (i + 1)) θ (εβ i))
    (hα : ε₀ ≤ εmax)
    (hβ : ∀ i < (modelParamsMulti m params shape arities wf hpos hsum).rounds,
      εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti m params shape arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift θ
          (P.claims (viewMulti m params shape arities
            (firstMessage (attempt res.1).commitments (attempt res.1).points
              (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti m params shape arities wf hpos hsum s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * Fintype.card D) := by
  intro P
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let bits := powBitsMulti params arities
  have hε0 : 0 ≤ εmax := (div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq
  have hε : ∀ i < P.batches + (P.rounds + 2),
      (if i < P.batches then 0
        else roundErrorTensor P.rounds ε₀ εβ θ P.queries (i - P.batches) /
          2 ^ bits (i - P.batches)) ≤ εmax := by
    intro i hi
    split_ifs with hlt
    · exact hε0
    · rcases hsub : i - P.batches with _ | k
      · rw [PcsRbr.roundErrorTensor_zero, show bits 0 = 0 from powBitsMulti_zero params arities,
          pow_zero, div_one]
        exact hα
      · by_cases hk : k < P.rounds
        · rw [PcsRbr.roundErrorTensor_succ_of_lt hk,
            show bits (k + 1) = params.commitPowBits from powBitsMulti_succ_of_lt params arities hk]
          exact hβ k hk
        · obtain rfl : k = P.rounds := by omega
          rw [PcsRbr.roundErrorTensor_last,
            show bits (P.rounds + 1) = params.queryPowBits from powBitsMulti_last params arities]
          exact hq
  have hnd : ∀ t : Oracle.Transcript (PcsRbr.Msg K P.numClaims)
      (GrindChal bits (ChalTensorMulti P.ldt W M P.queries)) (P.rounds + 2),
      PowPasses t → ClaimsFailMulti P.ldt P.shift θ (PcsRbr.claimsOf (ungrind t)) →
        AcceptsTensorMulti P.ldt P.shift (tensorCoordMulti params shape arities) (ungrind t) →
          ¬ PcsRbr.grindDoomed bits (PcsRbr.doomedTensorMulti P.ldt P.shift
              (tensorCoordMulti params shape arities) θ P.queries) (P.rounds + 2) t :=
    fun t => PcsRbr.not_grindDoomedTensorMulti_of_accepts t
  have hbound := prob_spongeExperiment_bind_committedRow_le (s₀ := s₀)
    (r := P.batches + (P.rounds + 2))
    (rbrSound_spongeTensorMulti P W M (tensorCoordMulti params shape arities)
      (fun j _ => tensorCoordMulti_injective params shape arities j) bits hθ hmca hε₀ hstep)
    hε hε0 (spongeDoomedTensorMulti_nil P W M (tensorCoordMulti params shape arities) bits θ)
    (stepDigestsOf := spongeStepDigestsMulti (F := F) (EF := EF) P) (M := 1) (by decide)
    (fun i _ msg => length_spongeStepDigestsMulti_le_one P i msg)
    (read := spongeStepReadMulti m params shape arities wf hpos hsum)
    (fun j msg c c' hc => spongeStepReadMulti_congr m params shape arities wf hpos hsum j msg c c' hc)
    hadv (fun a => spongeMessagesMulti params shape arities (attempt a))
    (rest := fun out =>
      (spongeVerifyTensorMulti m params shape arities wf hpos hsum (attempt out.1) out.2).bind
        fun b => .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (queryBound_spongeVerifyTensorMulti m params shape arities wf hpos hsum
        (attempt out.1) out.2).bind (m := 0) fun _ => queryBound_pure _ _)
    (E := fun res l =>
      (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          spongeAcceptsTensorMulti m params shape arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
      ClaimsFailMulti P.ldt P.shift θ
        (P.claims (viewMulti m params shape arities (firstMessage (attempt res.1).commitments
          (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
    fun out l res l' hexp hrun ⟨⟨f, hf, hacc⟩, hfail⟩ hno => by
      obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
      obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
      have hcomm : (attempt out.1).commitments.size = shape.length := by
        unfold spongeAcceptsTensorMulti Fri.verifyTensorWithSchedule Fri.shapeOkMultiArity at hacc
        simp only [Bool.and_eq_true, beq_iff_eq] at hacc
        exact hacc.1.1.1.1.1.1.1.1.1.1.2
      have hacc_free := acceptsTensorMulti_liftSpongeOracle_of_spongeAcceptsTensorMulti
        m params shape arities wf hpos hsum s₀ f (attempt out.1) hacc
      have hmodel_true : (P.verifyGrindViewTensor W M (tensorCoordMulti params shape arities) bits
          (viewMulti m params shape arities) (modelProofMulti m params shape (attempt out.1).proof)
          (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))).run
          (liftSpongeOracleTensorMulti P W M bits s₀ f) = true :=
        run_model_of_acceptsTensorMulti m params shape arities wf hpos hsum
          (liftSpongeOracleTensorMulti P W M bits s₀ f) (attempt out.1) hacc_free
      have hts : out.2 = spongeTranscript f s₀
          (spongeMessagesMulti params shape arities (attempt out.1))
          (P.batches + (P.rounds + 2)) := by
        have h1 := eq_spongeTranscript_of_outcome_spongeExperiment hexp hver.prefix f
        rwa [toFun_eq_self hf] at h1
      let tg := spongeToGrindTranscriptTensorMulti (P := P) (W := W) (M := M) (bits := bits)
        (M' := Compiled.Msg K D P.batches)
        (fun j => viewMulti m params shape arities
          (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
            (attempt out.1).values (attempt out.1).proof j))
        (P.rounds + 2) out.2.1
      have htg_eq : tg = (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
          (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
            (attempt out.1).values (attempt out.1).proof) (P.rounds + 2)).mapIdx
          (fun _ msg => (viewMulti m params shape arities msg : Compiled.Msg K D P.batches)) := by
        dsimp only [tg]
        rw [hts]
        exact spongeToGrindTranscriptTensorMulti_eq_fsTranscript m params shape arities wf hpos hsum
          s₀ f (attempt out.1) hcomm (P.rounds + 2)
      have hb_true : b = true := by
        have hrun_f : (spongeVerifyTensorMulti m params shape arities wf hpos hsum
            (attempt out.1) out.2).run f = b := by
          have := hver.run_toFun f
          rwa [toFun_eq_self hf] at this
        rw [← hrun_f]
        unfold spongeVerifyTensorMulti
        dsimp only
        obtain ⟨hpow_fs, hvw⟩ :=
          (P.run_verifyGrindViewTensor W M (tensorCoordMulti params shape arities) bits
            (viewMulti m params shape arities)
            (liftSpongeOracleTensorMulti P W M bits s₀ f) _ _).mp hmodel_true
        have hpow_tg : PowPasses tg := by
          rw [htg_eq]
          exact (PcsRbr.powPasses_mapIdx _ _).mpr hpow_fs
        change (@ite _ (PowPasses tg) (Classical.propDecidable _)
            (mapHashToSponge (M := RawMsg F EF D) (C := SpongeChalTensorMulti P W M bits)
              (P.verifyWithTensor (M' := Empty) (C := fun _ => PUnit) W M
                (tensorCoordMulti params shape arities)
                (modelProofMulti m params shape (attempt out.1).proof) (Compiled.msgAt (ungrind tg))
                (tensorOfMulti (ungrind tg)) (betasOfTensorMulti (ungrind tg))
                (fun k => P.indexOf (queriesOfTensorMulti (ungrind tg) k))))
            (.pure false)).run f = true
        rw [ite_eq_left hpow_tg, run_mapHashToSponge]
        have hrun_vw := P.run_verifyWithTensor W M (tensorCoordMulti params shape arities)
          (projHashFun f) (modelProofMulti m params shape (attempt out.1).proof)
          (Compiled.msgAt (ungrind tg)) (tensorOfMulti (ungrind tg))
          (betasOfTensorMulti (ungrind tg))
          (fun k => P.indexOf (queriesOfTensorMulti (ungrind tg) k))
        have hrun_fs := P.run_verifyWithTensor W M (tensorCoordMulti params shape arities)
          (liftSpongeOracleTensorMulti P W M bits s₀ f)
          (modelProofMulti m params shape (attempt out.1).proof)
          (fun j => viewMulti m params shape arities (Compiled.msgAt (ungrind (fsTranscript
            (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) j))
          (tensorOfMulti (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))))
          (betasOfTensorMulti (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))))
          (fun k => P.indexOf (queriesOfTensorMulti (ungrind (fsTranscript
            (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) k))
        rw [hrun_vw]
        rw [hrun_fs] at hvw
        have hhash_eq : hasherOf (projHashFun f) =
            hasherOf (liftSpongeOracleTensorMulti P W M bits s₀ f) := rfl
        let vP : RawMsg F EF D → Compiled.Msg K D P.batches := viewMulti m params shape arities
        have htu_eq : ungrind tg = (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
            (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
              (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))).mapIdx
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
              (liftSpongeOracleTensorMulti P W M bits s₀ f)
              (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
                (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) j) := by
          funext j
          rw [htu_eq]
          exact hmsgAt_map _ vP j
        have ht_eq : tensorOfMulti (ungrind tg) =
            tensorOfMulti (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
              (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
                (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.tensorOfMulti_mapIdx _ _
        have hβ_eq : betasOfTensorMulti (ungrind tg) =
            betasOfTensorMulti (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
              (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
                (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.betasOfTensorMulti_mapIdx _ _
        have hq_eq : queriesOfTensorMulti (ungrind tg) =
            queriesOfTensorMulti (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
              (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
                (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))) := by
          rw [htu_eq]
          exact PcsRbr.queriesOfTensorMulti_mapIdx _ _
        rw [hhash_eq, hmsg_eq, ht_eq, hβ_eq, hq_eq]
        exact hvw
      subst hb_true
      unfold spongeVerifyTensorMulti at hver
      dsimp only at hver
      split at hver
      · next hpow_tg =>
        have hproj_out := outcome_projHashLog hver
        have hnocol_proj : ¬ LogCollision hashObs (projHashLog l') := fun hc =>
          not_logCollision_sponge_of_not_jointHit hno (logCollision_projHashLog_iff.mp hc)
        have hacc_pcs := P.acceptsTensorMulti_of_outcome_verifyWithTensor_view id (ungrind tg)
          hproj_out hnocol_proj
        rw [committedRow_projHashLog] at hacc_pcs
        obtain ⟨_, -, hder⟩ := outcome_spongeExperiment hexp
        obtain ⟨_, hmsgs⟩ := outcome_spongeDerive_supports hder
        have hextr : extractPcsTensorMulti P W M bits (P.rounds + 2)
            (out.2.1.mapIdx fun j msg =>
              spongeStepReadMulti m params shape arities wf hpos hsum j msg (spongeCommittedRow l')) =
            tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          extractPcsTensorMulti_mapIdx_eq m params shape arities wf hpos hsum (attempt out.1)
            (spongeCommittedRow l') (P.rounds + 2) out.2.1 hmsgs
        rw [spongeDoomedTensorMulti_add_succ P W M (tensorCoordMulti params shape arities) bits θ
            (P.rounds + 1), hextr]
        have hungrind_tg : ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l')) =
            (ungrind tg).mapIdx fun j msg => P.read j msg (spongeCommittedRow l') :=
          PcsRbr.ungrind_mapIdx _ tg
        refine hnd _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow_tg) ?_ ?_
        · let vP : RawMsg F EF D → Compiled.Msg K D P.batches := viewMulti m params shape arities
          have h0 : (ungrind tg).msgs[0]? =
              some (vP (messagesMulti params arities (attempt out.1).commitments
                (attempt out.1).points (attempt out.1).values (attempt out.1).proof 0)) := by
            have hu : ungrind tg = (ungrind (fsTranscript (liftSpongeOracleTensorMulti P W M bits s₀ f)
                (messagesMulti params arities (attempt out.1).commitments (attempt out.1).points
                  (attempt out.1).values (attempt out.1).proof) (P.rounds + 2))).mapIdx
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
          change ClaimsFailMulti P.ldt P.shift θ
            (PcsRbr.claimsOf (ungrind (tg.mapIdx fun j msg => P.read j msg (spongeCommittedRow l'))))
          rw [hungrind_tg, PcsRbr.claimsOf_mapIdx _ (ungrind tg) h0]
          exact hfail
        · exact Eq.mpr
            (congrArg (fun u =>
              AcceptsTensorMulti P.ldt P.shift (tensorCoordMulti params shape arities) u)
              hungrind_tg)
            hacc_pcs
      · exact absurd (outcome_pure.mp hver).1 (by simp)
  have hcast : ((Q : ℝ) + ((P.batches + (P.rounds + 2) : ℕ) : ℝ) + P.verifierQueries) =
      (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    push_cast; ring
  rw [hcast] at hbound
  exact hbound

/-! ## 3. Unconditional Unique-Decoding & Johnson-Regime Multi-Arity Sponge Theorems -/

/-- **Unconditional unique-decoding incremental-sponge soundness (`c = 3 / 2`) for
executable `Fri.verifyTensorWithSchedule`** with ANY variable arity schedule `arities`!
Error is completely independent of the per-round fold factors `2 ^ a`. -/
theorem soundnessTensorMulti_sponge_uniqueDecoding (s₀ : D)
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti m params shape arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift (1 - δ)
          (P.claims (viewMulti m params shape arities
            (firstMessage (attempt res.1).commitments (attempt res.1).points
              (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti m params shape arities wf hpos hsum s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * Fintype.card D) := by
  intro P
  have hθ : 0 ≤ 1 - δ := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hcard_mul : ∀ j ≤ P.rounds,
      (P.ldt.domain j).card = 2 ^ params.logBlowup * P.ldt.degree j := fun j hj => by
    rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_degree,
      card_twoAdicDomain P.prim (P.cum_le_n j)]
    show 2 ^ (P.n - P.cum j) =
      2 ^ params.logBlowup * (2 ^ (arities.sum - P.cum j) * 2 ^ params.logFinalPolyLen)
    have hcle : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
    rw [← pow_add, ← pow_add]
    congr 1
    show logMaxHeight params.logBlowup shape - cumLogArity arities j =
      params.logBlowup + (arities.sum - cumLogArity arities j + params.logFinalPolyLen)
    unfold FriParams.logFinalHeight at hsum_eq
    omega
  have hdist_dom : ∀ j ≤ P.rounds,
      2 * (δ * (P.ldt.domain j).card) + P.ldt.degree j ≤ (P.ldt.domain j).card := fun j hj => by
    have hinv : (2 : ℝ) ^ params.logBlowup * (1 / 2 : ℝ) ^ params.logBlowup = 1 := by
      rw [← mul_pow]; norm_num
    have hdeg : (P.ldt.degree j : ℝ) = (1 / 2 : ℝ) ^ params.logBlowup * (P.ldt.domain j).card := by
      rw [hcard_mul j hj]; push_cast
      linear_combination -(P.ldt.degree j : ℝ) * hinv
    rw [hdeg]
    nlinarith [Nat.cast_nonneg (α := ℝ) (P.ldt.domain j).card]
  have hcard_le : ∀ j ≤ P.rounds, ((P.ldt.domain j).card : ℝ) ≤ (2 : ℝ) ^ P.n := fun j _ => by
    rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n (P.cum j))
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) (1 - δ)
        (((tensorNumChallenges (maxWidth shape) +
            tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
          (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K)) := by
    intro j hj
    refine tensor2DMCA_ud _ _ _ _ hδ ?_
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
    exact hdist_dom j hj
  have hε₀ : ∀ j ≤ P.rounds,
      ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        (((1 + δ) * ((P.ldt.domain j).image (P.shift * ·)).card) / Fintype.card K) ≤
      ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K := by
    intro j hj
    rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne), ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hcard_le j hj) (by linarith))
        (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) (1 - δ)
        (((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K) := by
    intro i hi
    have hps : PowStep (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1)) := by
      rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_domain,
        Compiled.MultiParams.ldt_zeta, P.cum_succ hi]
      exact powStep_twoAdicDomain P.prim (P.logArity_pos hi) (P.cum_succ hi ▸ P.cum_le_n (i + 1))
    have hbase := stepMCAArity_ud hps (P.ldt.degree (i + 1)) hδ (hdist_dom (i + 1) hi)
    intro ro f
    obtain ⟨bad, hbad, hgood⟩ := hbase ro f
    refine ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcard_le i hi.le) (by linarith)) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)), hgood⟩
  exact soundnessTensorMulti_sponge m params shape arities wf hpos hsum s₀ hθ hmca hε₀ hstep
    hα (fun _ _ => hβ) hq hadv attempt

/-- **Johnson-regime incremental sponge soundness (`c = 3 / 2`) for multi-arity
`Fri.verifyTensorWithSchedule`** from `CurveListCA K T` alone!
Because `m = 2 ^ a` cancels against BOTH `d' = d_src / m` (in `curveListThreshold ≤ m * Cd * d'`)
and `|D'| = |D_src| / m` (in `m * L_J * (1 - θ) * |D'|`), the folding round error is
`(cT + L_J * (1 - θ) * 2 ^ H) / |K| / 2 ^ commitPowBits` — completely independent of `m = 2 ^ a`! -/
theorem soundnessTensorMulti_sponge_johnson_of_curveListCA (s₀ : D) {T : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hca : CurveListCA K T)
    (hsum_eq : arities.sum + params.logFinalHeight = logMaxHeight params.logBlowup shape)
    {θ cT : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hgap : (1 / 2 : ℝ) ^ params.logBlowup < θ ^ 2)
    (hcT0 : 0 ≤ cT)
    (hT_batch : ∀ j ≤ arities.length,
      (T (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j))
        (2 ^ (arities.sum - cumLogArity arities j) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities j)⌉₊ 2 : ℝ) ≤ cT)
    (hT_fold : ∀ i < arities.length,
      (T (2 ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1)))
        (2 ^ (arities.sum - cumLogArity arities (i + 1)) * 2 ^ params.logFinalPolyLen)
        ⌈θ * (2 : ℝ) ^ (logMaxHeight params.logBlowup shape - cumLogArity arities (i + 1))⌉₊
        (2 ^ arities.getD i 1 + 1) : ℝ) ≤ cT)
    {εmax : ℝ}
    (hα : ((2 ^ (tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)) : ℕ) : ℝ) *
        (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) / Fintype.card K ≤ εmax)
    (hβ : (cT + ((θ - (1 / 2 : ℝ) ^ params.logBlowup) /
            (θ ^ 2 - (1 / 2 : ℝ) ^ params.logBlowup)) *
          ((1 - θ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape)) /
        Fintype.card K / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    let P := modelParamsMulti m params shape arities wf hpos hsum
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) m params shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti m params shape arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift θ
          (P.claims (viewMulti m params shape arities
            (firstMessage (attempt res.1).commitments (attempt res.1).points
              (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti m params shape arities wf hpos hsum s₀ adv attempt) [] ≤
      (Q + (P.batches + (P.rounds + 2)) + P.verifierQueries) * εmax +
        3 * ((Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries) ^ 2 /
          (2 * Fintype.card D) := by
  intro P
  set ρ : ℝ := (1 / 2 : ℝ) ^ params.logBlowup
  set W := maxWidth shape
  set M := maxOpeningsPerHeight params.logBlowup shape
  have hcard_mul : ∀ j ≤ P.rounds,
      (P.ldt.domain j).card = 2 ^ params.logBlowup * P.ldt.degree j := fun j hj => by
    rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_degree,
      card_twoAdicDomain P.prim (P.cum_le_n j)]
    show 2 ^ (P.n - P.cum j) =
      2 ^ params.logBlowup * (2 ^ (arities.sum - P.cum j) * 2 ^ params.logFinalPolyLen)
    have hcle : cumLogArity arities j ≤ arities.sum := cumLogArity_le_sum arities j
    rw [← pow_add, ← pow_add]
    congr 1
    show logMaxHeight params.logBlowup shape - cumLogArity arities j =
      params.logBlowup + (arities.sum - cumLogArity arities j + params.logFinalPolyLen)
    unfold FriParams.logFinalHeight at hsum_eq
    omega
  have hrate : ∀ j ≤ P.rounds, (P.ldt.degree j : ℝ) ≤ ρ * (P.ldt.domain j).card := fun j hj => by
    have hinv : (2 : ℝ) ^ params.logBlowup * ρ = 1 := by
      dsimp only [ρ]; rw [← mul_pow]; norm_num
    rw [hcard_mul j hj]; push_cast
    have : ρ * ((2 : ℝ) ^ params.logBlowup * (P.ldt.degree j : ℝ)) = (P.ldt.degree j : ℝ) := by
      linear_combination (P.ldt.degree j : ℝ) * hinv
    exact le_of_eq this.symm
  have hLJ_nn : 0 ≤ (θ - ρ) / (θ ^ 2 - ρ) := by
    have hnum : 0 ≤ θ - ρ := by nlinarith
    have hden : 0 < θ ^ 2 - ρ := sub_pos.mpr hgap
    exact div_nonneg hnum hden.le
  have hcard_le : ∀ j ≤ P.rounds, ((P.ldt.domain j).card : ℝ) ≤ (2 : ℝ) ^ P.n := fun j _ => by
    rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    exact_mod_cast Nat.pow_le_pow_right two_pos (Nat.sub_le P.n (P.cum j))
  let εLine : ℝ := (cT + ((θ - ρ) / (θ ^ 2 - ρ)) * ((1 - θ) * (2 : ℝ) ^ P.n)) / Fintype.card K
  have hεLine_nn : 0 ≤ εLine := by
    dsimp only [εLine]
    have : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
    positivity
  have hpow_ge : ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) ≤
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le _ 1
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) W M θ
        (((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) * εLine) := by
    intro j hj
    have hcard_img : ((P.ldt.domain j).image (P.shift * ·)).card =
        2 ^ (P.n - P.cum j) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne),
        Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n j)]
    have hdeg_img : (P.ldt.degree j : ℝ) ≤ ρ * ((P.ldt.domain j).image (P.shift * ·)).card := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact hrate j hj
    have hTj : (T ((P.ldt.domain j).image (P.shift * ·)).card (P.ldt.degree j)
        ⌈θ * (((P.ldt.domain j).image (P.shift * ·)).card : ℝ)⌉₊ 2 : ℝ) ≤ cT := by
      rw [hcard_img]
      have hcast : ((2 ^ (P.n - P.cum j) : ℕ) : ℝ) = (2 : ℝ) ^ (P.n - P.cum j) := by push_cast; rfl
      rw [hcast]
      exact hT_batch j hj
    have hcm := curveMCA_of_curveListCA_rel hca ((P.ldt.domain j).image (P.shift * ·))
      (P.ldt.degree j) 2 hθ0 hθ1 hdeg_img hgap hcT0 hTj
    have hcm' : CurveMCA ((P.ldt.domain j).image (P.shift * ·)) (P.ldt.degree j) 2 θ εLine := by
      refine ProximityGap.curveMCA_mono hcm le_rfl ?_
      rw [show ((2 - 1 : ℕ) : ℝ) = 1 by norm_num, mul_one,
        Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcard_le j hj) (sub_nonneg.mpr hθ1)) hLJ_nn))
        (Nat.cast_nonneg _)
    exact tensor2DMCA_of_curveMCA_two hcm'
  have hε₀ : ∀ j ≤ P.rounds,
      ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) - 1 : ℕ) : ℝ) * εLine ≤
        ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) * εLine :=
    fun _ _ => mul_le_mul_of_nonneg_right hpow_ge hεLine_nn
  have hstep : ∀ i < P.rounds,
      StepMCAArity (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1))
        (P.ldt.degree (i + 1)) θ εLine := by
    intro i hi
    have hps : PowStep (2 ^ P.logArity i) (P.ldt.zeta i) (P.ldt.domain i) (P.ldt.domain (i + 1)) := by
      rw [Compiled.MultiParams.ldt_domain, Compiled.MultiParams.ldt_domain,
        Compiled.MultiParams.ldt_zeta, P.cum_succ hi]
      exact powStep_twoAdicDomain P.prim (P.logArity_pos hi) (P.cum_succ hi ▸ P.cum_le_n (i + 1))
    have hcard_dst : (P.ldt.domain (i + 1)).card = 2 ^ (P.n - P.cum (i + 1)) := by
      rw [Compiled.MultiParams.ldt_domain, card_twoAdicDomain P.prim (P.cum_le_n (i + 1))]
    have hi_ar : i < arities.length := hi
    have ha_eq : arities.getD i 1 = P.logArity i := by
      simp only [P, modelParamsMulti, Compiled.MultiParams.logArity,
        List.getD_eq_getElem _ _ hi_ar]
    have hTi : (T (P.ldt.domain (i + 1)).card (P.ldt.degree (i + 1))
        ⌈θ * ((P.ldt.domain (i + 1)).card : ℝ)⌉₊ (2 ^ P.logArity i + 1) : ℝ) ≤ cT := by
      rw [hcard_dst, ← ha_eq]
      have hcast : ((2 ^ (P.n - P.cum (i + 1)) : ℕ) : ℝ) = (2 : ℝ) ^ (P.n - P.cum (i + 1)) := by
        push_cast; rfl
      rw [hcast]
      exact hT_fold i hi_ar
    have hbase := stepMCAArity_of_curveListCA_rel hca hps (P.ldt.degree (i + 1)) hθ0 hθ1
      (hrate (i + 1) hi) hgap hcT0 hTi
    intro ro f
    obtain ⟨bad, hbad, hgood⟩ := hbase ro f
    refine ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcard_le i hi.le) (sub_nonneg.mpr hθ1)) hLJ_nn))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)), hgood⟩
  have hα' : ((2 ^ (tensorNumChallenges W + tensorNumChallenges M) : ℕ) : ℝ) * εLine ≤ εmax := by
    dsimp only [εLine]
    rwa [← mul_div_assoc]
  exact soundnessTensorMulti_sponge m params shape arities wf hpos hsum s₀ hθ0.le hmca hε₀ hstep
    hα' (fun _ _ => hβ) hq hadv attempt

end ExecSpongeTensorMulti

end CertiFri.Exec

/-! ## 4. Unconditional 128-Bit `GoldilocksExt3` Multi-Arity Theorems (`compact400KBBalanced` & `ultraCompact400KBZk`) -/

namespace CertiFri.P3.Exec

open CertiFri CertiFri.Fri CertiFri.Exec CertiFri.Oracle CertiFri.Oracle.OracleComp CertiFri.Sponge
  CertiFri.Compiled
open CertiFri.PcsRbr (ClaimsFailMulti)

/-! ### Query-Soundness Arithmetic for `compact400KBBalanced` and `ultraCompact400KBZk` -/

/-- Query-phase soundness for `FriParams.compact400KBBalanced`
(`lb = 4, q ≥ 58, queryPow ≥ 28`, `θ = 35 / 128`, `136.5` query bits):
`(35 / 128) ^ q / 2 ^ pow ≤ (3 / 4) / 2 ^ 128`. -/
theorem johnson_35_128_compact400KB_le {q pow : ℕ} (hq : 58 ≤ q) (hpow : 28 ≤ pow) :
    ((35 / 128 : ℝ) ^ q) / (2 : ℝ) ^ pow ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have h20 : (2 : ℝ) ^ 20 ≤ (2 : ℝ) ^ pow := by
    exact_mod_cast Nat.pow_le_pow_right two_pos (show 20 ≤ pow by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) h20).trans
    (johnson_35_128_ge_58_pow20_le_three_quarters_128 hq)

/-- Query-phase soundness for `FriParams.ultraCompact400KBZk`
(`lb = 4, q ≥ 55, queryPow ≥ 30`, `θ = 35 / 128`, `132.9` query bits):
`(35 / 128) ^ q / 2 ^ pow ≤ (3 / 4) / 2 ^ 128`. -/
theorem johnson_35_128_ultraCompact400KB_le {q pow : ℕ} (hq : 55 ≤ q) (hpow : 30 ≤ pow) :
    ((35 / 128 : ℝ) ^ q) / (2 : ℝ) ^ pow ≤ (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
  have hmono_q : (35 / 128 : ℝ) ^ q ≤ (35 / 128 : ℝ) ^ 55 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hq
  have hmono_p : (2 : ℝ) ^ 30 ≤ (2 : ℝ) ^ pow := by
    exact_mod_cast Nat.pow_le_pow_right two_pos hpow
  have hstep1 : ((35 / 128 : ℝ) ^ q) / (2 : ℝ) ^ pow ≤ ((35 / 128 : ℝ) ^ 55) / (2 : ℝ) ^ 30 :=
    (div_le_div_of_nonneg_right hmono_q (by positivity)).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hmono_p)
  -- `(35 / 128)^55 / 2^30 ≤ (35 / 128)^58 / 2^20` because `128^3 = 2,097,152 ≤ 43,904,000 = 35^3 * 2^10`.
  have hcmp : ((35 / 128 : ℝ) ^ 55) / (2 : ℝ) ^ 30 ≤ ((35 / 128 : ℝ) ^ 58) / (2 : ℝ) ^ 20 := by
    rw [show (58 : ℕ) = 55 + 3 by decide, pow_add, show (30 : ℕ) = 20 + 10 by decide, pow_add,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hnum : (1 : ℝ) ≤ (35 / 128 : ℝ) ^ 3 * (2 : ℝ) ^ 10 := by norm_num
    have hpos : (0 : ℝ) < (35 / 128 : ℝ) ^ 55 * (2 : ℝ) ^ 20 := by positivity
    nlinarith
  exact hstep1.trans (hcmp.trans (johnson_35_128_ge_58_pow20_le_three_quarters_128 le_rfl))

/-! ### Master Unconditional Multi-Arity Johnson Profile Schema over `GoldilocksExt3` -/

/-- Shared arithmetic core for 100% unconditional Johnson-regime multi-arity
`Fri.verifyTensorWithSchedule` soundness over `GoldilocksExt3` (discharging
`CurveListCA` internally via `curveListCA_fp3`, ZERO unproven proximity assumptions!).
Works for ANY variable per-round arity schedule `arities : List ℕ` (including 2/4/8-ary). -/
private theorem goldilocksExt3_soundnessTensorMulti_sponge_johnson_of_profile_aux
    (D : Type) [Fintype D] [Nonempty D] [DecidableEq D] [Inhabited D]
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + params.logFinalHeight = Fri.logMaxHeight params.logBlowup shape)
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
    (hHmax : Hmax + PowExp ≤ 63)
    (s₀ : D) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := D) goldilocksExt3_fieldModel params shape
      arities (goldilocksExt3_wellFormed params shape (hmax.trans hmax32)) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 D) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let hsum : arities.sum ≤ Fri.logMaxHeight params.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := D) goldilocksExt3_fieldModel params shape
            arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
              s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift ((p : ℝ) / q)
          (P.claims (viewMulti goldilocksExt3_fieldModel params shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
        s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * Fintype.card D) := by
  intro wf hsum P N
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
  -- Core linear-in-`d` bound on `curveListThreshold` at ANY cumulative level `c ≤ arities.sum`.
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
      unfold FriParams.logFinalHeight at hsum_eq
      rw [hbl] at hsum_eq
      omega
    have hnc_eq : nc = B * dc := by
      dsimp only [nc, dc, B]
      rw [← pow_add, ← pow_add]
      congr 1; omega
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
        field_simp [hq_r.ne'] at this
        linarith
      exact_mod_cast h2
    have hAc_hi : q * (Ac - 1) < p * nc := by
      have h1 : (Ac : ℝ) < ((p : ℝ) / q) * (nc : ℝ) + 1 := Nat.ceil_lt_add_one hprod_pos.le
      have hq_r : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pos
      have h2 : (q : ℝ) * ((Ac - 1 : ℕ) : ℝ) < (p : ℝ) * (nc : ℝ) := by
        rw [Nat.cast_sub hAc_pos, Nat.cast_one]
        have hsub : (Ac : ℝ) - 1 < ((p : ℝ) / q) * (nc : ℝ) := by linarith
        have := mul_lt_mul_of_pos_left hsub hq_r
        field_simp [hq_r.ne'] at this
        linarith
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
      dsimp only [B]
      rw [← pow_add, ← pow_add]
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
  -- Exact `m = 2 ^ a` cancellation on EVERY multi-arity folding round:
  -- `((2^a + 1) - 1) * d_{i+1} = 2^a * d_{i+1} = d_i ≤ 2^H / B`!
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
      rw [← mul_assoc, ← pow_add]
      congr 2; omega
    have hdj_le : B * (2 ^ (arities.sum - cumLogArity arities i) * 2 ^ params.logFinalPolyLen) ≤
        2 ^ H := by
      have hH_eq : H = arities.sum + lb + params.logFinalPolyLen := by
        unfold FriParams.logFinalHeight at hsum_eq; rw [hbl] at hsum_eq; omega
      dsimp only [B]
      rw [← pow_add, ← pow_add]
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
  have hεβ : (cT + (((p : ℝ) / q - (1 / 2 : ℝ) ^ params.logBlowup) /
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
  have hmain := soundnessTensorMulti_sponge_johnson_of_curveListCA goldilocksExt3_fieldModel
    params shape arities wf hpos hsum s₀ curveListCA_fp3 hsum_eq hθ0 hθ1 hgap hcT0
    hT_batch hT_fold (εmax := (3 / 4 : ℝ) / (2 : ℝ) ^ 128) hεα hεβ hq hadv attempt
  dsimp only at hmain
  have hNcast : (N : ℝ) = (Q : ℝ) + (P.batches + (P.rounds + 2)) + P.verifierQueries := by
    dsimp only [N]; push_cast; ring
  rwa [← hNcast] at hmain

/-- **Master Unconditional 128-Bit Multi-Arity Johnson Soundness Schema (`Digest64`,
RFC 7693 `BLAKE2b-512`):** literal `≤ N / 2 ^ 128` for ANY variable arity schedule `arities`,
discharging `CurveListCA` internally via `curveListCA_fp3` (ZERO unproven assumptions!). -/
theorem goldilocksExt3_soundnessTensorMulti_sponge_blake2b512_johnson_of_profile
    (lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp : ℕ)
    (params : FriParams) (shape : ClaimShape) (arities : List ℕ)
    (hbl : params.logBlowup = lb) (hlb : 1 ≤ lb)
    (hmax : Fri.logMaxHeight params.logBlowup shape ≤ Hmax) (hmax32 : Hmax ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + params.logFinalHeight = Fri.logMaxHeight params.logBlowup shape)
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
    (hHmax : Hmax + PowExp ≤ 63)
    (s₀ : Digest64) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel
      params shape arities (goldilocksExt3_wellFormed params shape (hmax.trans hmax32)) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q)
    (hN : Q + ((modelParamsMulti goldilocksExt3_fieldModel params shape arities
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32)) hpos (by omega)).batches +
      ((modelParamsMulti goldilocksExt3_fieldModel params shape arities
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32)) hpos (by omega)).rounds + 2)) +
      (modelParamsMulti goldilocksExt3_fieldModel params shape arities
        (goldilocksExt3_wellFormed params shape (hmax.trans hmax32)) hpos
        (by omega)).verifierQueries ≤ 2 ^ 128)
    (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest64) :
    let wf := goldilocksExt3_wellFormed params shape (hmax.trans hmax32)
    let hsum : arities.sum ≤ Fri.logMaxHeight params.logBlowup shape := by omega
    let P := modelParamsMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := Digest64) goldilocksExt3_fieldModel params
            shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
              s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift ((p : ℝ) / q)
          (P.claims (viewMulti goldilocksExt3_fieldModel params shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel params shape arities wf hpos hsum
        s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  intro wf hsum P N
  have hmain := goldilocksExt3_soundnessTensorMulti_sponge_johnson_of_profile_aux Digest64
    lb p q Rmax Lmax LJ_ub PowExp Hmax ClaimExp params shape arities hbl hlb hmax hmax32 hpos
    hsum_eq htensor hq hq_pos hpq hgap_nat hR hL hLJ hCd hClaimExp hHmax s₀ hadv attempt
  dsimp only at hmain
  have hcol := digest64_sponge_collision_le_quarter_128 (N := N) hN
  refine hmain.trans ?_
  calc (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * Fintype.card Digest64)
      ≤ (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + (N : ℝ) / (4 * (2 : ℝ) ^ 128) :=
        add_le_add le_rfl hcol
    _ = (N : ℝ) / (2 : ℝ) ^ 128 := by ring

/-! ### Concrete 128-Bit Theorems: `FriParams.compact400KBBalanced` & `FriParams.ultraCompact400KBZk` -/

/-- **100% Unconditional 128-Bit Johnson Soundness (`BLAKE3-256`, `Digest`) for
`FriParams.compact400KBBalanced`** (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8,
numQueries = 58, queryPowBits = 28`, 8-ary folding) for ANY valid schedule `arities`
(including `Fri.scheduleOfShape FriParams.compact400KBBalanced shape`), ZERO unproven
assumptions! -/
theorem goldilocksExt3_compact400KBBalanced_sponge_blake3
    (shape : ClaimShape) (arities : List ℕ)
    (hmax : Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.compact400KBBalanced.logFinalHeight =
      Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight
          FriParams.compact400KBBalanced.logBlowup shape)) *
        2 ^ Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := Digest) goldilocksExt3_fieldModel
      FriParams.compact400KBBalanced shape arities
      (goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed FriParams.compact400KBBalanced shape hmax
    let hsum : arities.sum ≤ Fri.logMaxHeight FriParams.compact400KBBalanced.logBlowup shape := by
      omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape arities
      wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := Digest) goldilocksExt3_fieldModel
            FriParams.compact400KBBalanced shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
              arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256) := by
  have hcardD : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 256 := by
    rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Nat.cast_ofNat, hcardD] using
    goldilocksExt3_soundnessTensorMulti_sponge_johnson_of_profile_aux Digest
      4 35 128 11 58 13 30 32 33 FriParams.compact400KBBalanced shape arities rfl (by decide)
      hmax le_rfl hpos hsum_eq htensor (johnson_35_128_compact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv attempt

/-- **100% Unconditional Literal `≤ N / 2 ^ 128` Johnson Soundness (`BLAKE2b-512`, `Digest64`)
for `FriParams.compact400KBBalanced`** (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8,
numQueries = 58, queryPowBits = 28`, 8-ary folding) for ANY valid schedule `arities` and
`N ≤ 2 ^ 128`, ZERO unproven assumptions! -/
theorem goldilocksExt3_compact400KBBalanced_sponge_blake2b512
    (shape : ClaimShape) (arities : List ℕ)
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
        ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.compact400KBBalanced shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensorMulti_sponge_blake2b512_johnson_of_profile
      4 35 128 11 58 13 30 32 33 FriParams.compact400KBBalanced shape arities rfl (by decide)
      hmax le_rfl hpos hsum_eq htensor (johnson_35_128_compact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

/-- **100% Unconditional 128-Bit Johnson Soundness (`BLAKE3-256`, `Digest`) for
`FriParams.ultraCompact400KBZk`** (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8,
numQueries = 55, queryPowBits = 30`, 8-ary folding) for ANY valid schedule `arities`,
ZERO unproven assumptions! -/
theorem goldilocksExt3_ultraCompact400KBZk_sponge_blake3
    (shape : ClaimShape) (arities : List ℕ)
    (hmax : Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 32)
    (hpos : ∀ a ∈ arities, 0 < a)
    (hsum_eq : arities.sum + FriParams.ultraCompact400KBZk.logFinalHeight =
      Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape)
    (htensor : 2 ^ (Fri.tensorNumChallenges (Fri.maxWidth shape) +
        Fri.tensorNumChallenges (Fri.maxOpeningsPerHeight
          FriParams.ultraCompact400KBZk.logBlowup shape)) *
        2 ^ Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape ≤ 2 ^ 33)
    (s₀ : Digest) {A : Type*}
    {adv : OracleComp (SpongeTensorMultiOracleAnswer (D := Digest) goldilocksExt3_fieldModel
      FriParams.ultraCompact400KBZk shape arities
      (goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax) hpos
      (by omega)) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (attempt : A → Attempt Goldilocks GoldilocksExt3 Digest) :
    let wf := goldilocksExt3_wellFormed FriParams.ultraCompact400KBZk shape hmax
    let hsum : arities.sum ≤ Fri.logMaxHeight FriParams.ultraCompact400KBZk.logBlowup shape := by
      omega
    let P := modelParamsMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape arities
      wf hpos hsum
    let N : ℕ := Q + (P.batches + (P.rounds + 2)) + P.verifierQueries
    prob (fun res l =>
        (∃ f : ∀ x, SpongeTensorMultiOracleAnswer (D := Digest) goldilocksExt3_fieldModel
            FriParams.ultraCompact400KBZk shape arities wf hpos hsum x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            spongeAcceptsTensorMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
              arities wf hpos hsum s₀ f (attempt res.1) = true) ∧
        ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) * ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) + 3 * (N : ℝ) ^ 2 / (2 * (2 : ℝ) ^ 256) := by
  have hcardD : (Fintype.card Digest : ℝ) = (2 : ℝ) ^ 256 := by
    rw [card_digest, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Nat.cast_ofNat, hcardD] using
    goldilocksExt3_soundnessTensorMulti_sponge_johnson_of_profile_aux Digest
      4 35 128 11 58 13 30 32 33 FriParams.ultraCompact400KBZk shape arities rfl (by decide)
      hmax le_rfl hpos hsum_eq htensor (johnson_35_128_ultraCompact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv attempt

/-- **100% Unconditional Literal `≤ N / 2 ^ 128` Johnson Soundness (`BLAKE2b-512`, `Digest64`)
for `FriParams.ultraCompact400KBZk`** (`logBlowup = 4, maxLogArity = 3, logFinalPolyLen = 8,
numQueries = 55, queryPowBits = 30`, 8-ary folding) for ANY valid schedule `arities` and
`N ≤ 2 ^ 128`, ZERO unproven assumptions! -/
theorem goldilocksExt3_ultraCompact400KBZk_sponge_blake2b512
    (shape : ClaimShape) (arities : List ℕ)
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
        ClaimsFailMulti P.ldt P.shift (35 / 128)
          (P.claims (viewMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape arities
            (Fri.firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (spongeCommittedRow l)))
      (spongeExperimentTensorMulti goldilocksExt3_fieldModel FriParams.ultraCompact400KBZk shape
        arities wf hpos hsum s₀ adv attempt) [] ≤
      (N : ℝ) / (2 : ℝ) ^ 128 := by
  simpa only [Nat.cast_ofNat] using
    goldilocksExt3_soundnessTensorMulti_sponge_blake2b512_johnson_of_profile
      4 35 128 11 58 13 30 32 33 FriParams.ultraCompact400KBZk shape arities rfl (by decide)
      hmax le_rfl hpos hsum_eq htensor (johnson_35_128_ultraCompact400KB_le le_rfl le_rfl)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by norm_num) (by decide) (by decide) (by decide) s₀ hadv hN attempt

end CertiFri.P3.Exec
