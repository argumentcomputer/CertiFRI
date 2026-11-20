import CertiFriProofs.Exec.Stark.State

/-!
# The random oracle of the STARK experiment, and the logs without luck

The STARK is analysed with one random oracle that answers the challenge
queries of every chain (a query holds the raw messages and the challenges of a
transcript so far, and the new raw message; the answer is a uniform `UAns`) and
the hash queries of the Merkle trees.

A log of queries is *good* when no challenge entry flips the state function of
`Exec/Stark/State.lean`, read against the rows the log commits to, and no hash
entry hits a digest already in play. This file bounds the probability that a
computation leaves a log that is not good, and shows that in a good log every
chain the log answers is doomed.

## Contents

* `SAns`: the answer types of the oracle.
* `interp B r l`: a raw message of a round below `r`, read with the rows the
  log `l` commits its first digests to.
* `GoodLog`: no flip and no hit.
* `prob_not_goodLog_le`: a computation with at most `N` queries leaves a log
  that is not good with probability at most
  `N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, where `εmax`
  bounds the error of every round.
* `sdoomed_of_goodLog`: in a good log, a transcript of at most `r` rounds whose
  challenges the log answers is doomed.

## Assumptions

Those of `rbrSound_sdoomed`. The random-oracle model: challenges and digests
are independent uniform answers of one oracle.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Oracle CertiFri.PcsRbr OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ}

/-- The answer types of the oracle of the STARK experiment: a uniform answer
to a challenge query, a digest to a hash query. -/
abbrev SAns (F EF D K : Type) (slots width : ℕ) :=
  MerkleAnswer (RawMsg F EF D) (UChal K slots width) K D

/-- A raw message of round `j`, read against the log `l`: with the rows `l`
commits its first digests to, in a round below `r`. -/
noncomputable def interp (B : Bounds) (r : ℕ) (l : Log (SAns F EF D K slots width)) (j : ℕ)
    (m : RawMsg F EF D) : IMsg F EF D K :=
  readMsg B m (if j < r then committedRow l else fun _ _ _ _ => none)

variable (M : StarkModel F EF K) (sys : System F D) (V : Variant F EF D) (θ : ℝ) (B : Bounds)
  (r : ℕ)

/-- A log without luck: no challenge entry flips the state function, read
against the log, and no hash entry hits a digest in play. -/
def GoodLog (l : Log (SAns F EF D K slots width)) : Prop :=
  ¬ HasBad (InterpFlips r (sdoomed M sys V θ B) (interp B r)) l ∧
    ¬ HasBad (Hit (digestsOf B) r) l

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [Inhabited D] in
/-- The reading of the messages is settled by the challenge queries, up to a
hit. -/
theorem settles_interp :
    Settles (fun (l : Log (SAns F EF D K slots width)) j m => interp B r l j m)
      (Hit (digestsOf B) r) := by
  refine settles_of_committedRow (digestsOf B) r
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

/-- **In a good log every answered chain is doomed.** A transcript of at most
`r` rounds whose chain of challenge queries a good log answers is doomed, when
its messages are read against that log. -/
theorem sdoomed_of_goodLog {l : Log (SAns F EF D K slots width)} (hgood : GoodLog M sys V θ B r l)
    {i : ℕ} (t : Transcript (RawMsg F EF D) (UChal K slots width) i) (hi : i ≤ r)
    (hs : Supports l t) : sdoomed M sys V θ B i (t.mapIdx (interp B r l)) :=
  doomed_mapIdx_of_supports (settles_interp B r) hgood.1 hgood.2 (sdoomed_nil M sys V θ B) t hi hs

/-- **The probability of a log that is not good.** Under the hypotheses of
`rbrSound_sdoomed`, with every round error at most `εmax`, a computation that
makes at most `N` queries from the empty log leaves a log that is not good with
probability at most
`N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`. -/
theorem prob_not_goodLog_le [Fintype K] [Fintype D] {εpcs εmax : ℝ} (hεpcs : 0 ≤ εpcs)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width)
    (hpcs : ∀ (v : ShardView F EF D K) (hs : Supported M sys θ v),
      RbrSound (hs.params.rounds + 2)
        (grindDoomed (powBits sys.fri (v.shape M sys))
          (PcsRbr.doomed hs.params.ldt hs.params.shift θ hs.params.queries
            (m := hs.params.numClaims)))
        fun _ => εpcs)
    (hε : ∀ i, roundErr M sys B εpcs i ≤ εmax) (h0 : 0 ≤ εmax) {α : Type}
    {c : OracleComp (SAns F EF D K slots width) α} {N : ℕ} (hc : c.QueryBound N) :
    prob (fun _ l => ¬ GoodLog M sys V θ B r l) c []
      ≤ N * εmax + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * Fintype.card D) := by
  have hflip := prob_hasBad_interpFlips_le (interp := interp B r)
    (rbrSound_sdoomed M sys V θ B hεpcs htwo hslots hcommit hquery hwidth hpcs r)
    (fun i _ => hε i) h0 hc
  have hhit := prob_hasBad_hit_le (digestsOf := digestsOf (F := F) (EF := EF) B) (r := r)
    (K := B.shards + 1) (fun m => by
      unfold digestsOf
      exact (List.length_take_le _ _)) hc
  push_cast at hhit
  refine le_trans (prob_le_add_of_outcome fun _ l _ hbad => ?_) (add_le_add hflip hhit)
  by_contra hno
  exact hbad ⟨fun h => hno (.inl h), fun h => hno (.inr h)⟩

end CertiFri.Exec.Stark
