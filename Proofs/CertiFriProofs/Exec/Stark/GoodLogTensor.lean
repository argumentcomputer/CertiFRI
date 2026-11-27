import CertiFriProofs.Exec.Stark.StateTensor

/-!
# The random oracle of the tensor-batched STARK experiment, and good logs

Tensor-batched counterpart of `Exec/Stark/GoodLog.lean`. Defines `STAns`,
`interpTensor`, `GoodLogTensor`, `settles_interpTensor`,
`sdoomedTensor_of_goodLogTensor`, and `prob_not_goodLogTensor_le`.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Oracle CertiFri.PcsRbr OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {fslots slots width : ℕ}

/-- The answer types of the oracle of the tensor-batched STARK experiment:
a multi-slot uniform answer to a challenge query, a digest to a hash query. -/
abbrev STAns (F EF D K : Type) (fslots slots width : ℕ) :=
  MerkleAnswer (RawMsg F EF D) (UTensorChal K fslots slots width) K D

/-- A raw message of round `j`, read against the log `l`: with the rows `l`
commits its first digests to, in a round below `r`. -/
noncomputable def interpTensor (B : Bounds) (r : ℕ) (l : Log (STAns F EF D K fslots slots width))
    (j : ℕ) (m : RawMsg F EF D) : IMsg F EF D K :=
  readMsg B m (if j < r then committedRow l else fun _ _ _ _ => none)

variable (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D) (θ : ℝ) (B : Bounds)
  (r : ℕ)

/-- A log without luck for the tensor-batched STARK: no challenge entry flips
`sdoomedTensor`, and no hash entry hits a digest in play. -/
def GoodLogTensor (l : Log (STAns F EF D K fslots slots width)) : Prop :=
  ¬ HasBad (InterpFlips r (sdoomedTensor M sys V θ B) (interpTensor B r)) l ∧
    ¬ HasBad (Hit (fun _ => digestsOf B) r) l

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
/-- The log interpretation `interpTensor` settles on committed Merkle rows up to a hit. -/
theorem settles_interpTensor :
    Settles (fun (l : Log (STAns F EF D K fslots slots width)) j m => interpTensor B r l j m)
      (Hit (fun _ => digestsOf B) r) := by
  refine settles_of_committedRow (fun _ => digestsOf B) r
    (fun j m c => readMsg B m (if j < r then c else fun _ _ _ _ => none)) ?_ ?_
  · intro j m c c' hj hc
    simp only [hj, ↓reduceIte, readMsg]
    refine congrArg (Prod.mk m) (funext fun root => ?_)
    by_cases hroot : root ∈ digestsOf B m
    · simp only [hroot, ↓reduceIte, hc root hroot]
    · simp only [hroot, ↓reduceIte]
  · intro j m c c' hj
    simp only [Nat.not_lt.mpr hj, ↓reduceIte]

variable {M sys V θ B r}

/-- In a good log, every answered chain of at most `r` rounds is doomed. -/
theorem sdoomedTensor_of_goodLogTensor {l : Log (STAns F EF D K fslots slots width)}
    (hgood : GoodLogTensor M sys V θ B r l) {i : ℕ}
    (t : Transcript (RawMsg F EF D) (UTensorChal K fslots slots width) i) (hi : i ≤ r)
    (hs : Supports l t) :
    sdoomedTensor M sys V θ B i (t.mapIdx (interpTensor B r l)) :=
  doomed_mapIdx_of_supports (settles_interpTensor B r) hgood.1 hgood.2
    (sdoomedTensor_nil M sys V θ B) t hi hs

/-- **Probability of a bad log in the tensor-batched STARK experiment.** -/
theorem prob_not_goodLogTensor_le [Fintype K] [Fintype D] {εpcs εmax : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hfslots : fslotsBound sys M.extData.d ≤ fslots)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomedTensor hs.params.ldt hs.params.shift (starkTensorCoord M sys hs)
            θ hs.params.queries))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {α : Type}
    {c : OracleComp (STAns F EF D K fslots slots width) α} {N : ℕ} (hc : c.QueryBound N) :
    prob (fun _ l => ¬ GoodLogTensor M sys V θ B r l) c []
      ≤ N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * Fintype.card D) := by
  have hflip := prob_hasBad_interpFlips_le (interp := interpTensor B r)
    (rbrSound_sdoomedTensor M sys V θ B hεpcs htwo hfslots hslots hcommit hquery hwidth hpcs r)
    (fun i _ => hε i) h0 hc
  have hhit_pot := prob_hasBad_hit_le_potential
    (digestsOf := fun _ => digestsOf (F := F) (EF := EF) B) (r := r)
    (M := (B.shards + 1) * r) (fun x => by
      unfold chalDigests
      refine (MerkleRO.length_flatMap_zipIdx_le (fun _ => digestsOf B) (fun _ => B.shards + 1)
        (fun _ m => by unfold digestsOf; exact List.length_take_le _ _) _ 0).trans ?_
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (List.length_take_le _ _)) hc
  have hhit : prob (fun _ l => HasBad (Hit (fun _ => digestsOf B) r) l) c []
      ≤ (((B.shards + 1) * r + 3 : ℝ) * N * (N - 1)) / (2 * Fintype.card D) := by
    refine hhit_pot.trans ?_
    have hle := MerkleRO.hitPotential_zero_le_choose ((B.shards + 1) * r) N
    have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hdiv := div_le_div_of_nonneg_right hle hD
    push_cast at hdiv
    simpa only [div_div, mul_comm (2 : ℝ)] using hdiv
  refine le_trans (prob_le_add_of_outcome fun _ l _ hbad => ?_) (add_le_add hflip hhit)
  by_contra hno
  exact hbad ⟨fun h => hno (.inl h), fun h => hno (.inr h)⟩

end CertiFri.Exec.Stark
