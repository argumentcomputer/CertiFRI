import CertiFriProofs.Exec.Stark.Lookups
import CertiFriProofs.Exec.Stark.PcsSound

/-!
# Soundness of the STARK verifier with no hypothesis about the opening protocol

`soundness_verify` and `soundness_verifyBatch` take the round-by-round
soundness of the opening protocol as a hypothesis (`hpcs`).
`Exec/Stark/PcsSound.lean` proves it at the unique-decoding radius. This file
puts the two together: the soundness of `Stark.verify` and of
`Stark.verifyBatch` at agreement `1 - δ`, for any `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup < 1`, with an explicit error. The condition is on
the blowup alone, and the theorems are about every accepted proof within the
size bounds: nothing is assumed about the shape of the proof or the heights of
its traces.

## Contents

* `starkErr M sys B δ`: the largest error of a round. It is the largest of
  * `2 * itemBound / |K|` and `2 * itemBound * lenBound / |K|`, for the two
    lookup challenges;
  * `(constraintBound - 1) / |K|`, for the constraint challenge;
  * `(zetaBound + cosetBound) / |K|`, for the out-of-domain point: the check at
    the point passes by chance (`zetaBound`), or the point or its successor on
    a trace domain lies in a coset a column is committed on (`cosetBound`);
  * `pcsErr`, for the rounds of the opening protocol (batching, folding with
    its proof of work, queries with their proof of work).
* `soundness_verify_ud`, `soundness_verifyBatch_ud`: the two soundness
  theorems, with the bound
  `N * starkErr + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`.
* `soundness_verify_lookups_ud`, `soundness_verifyBatch_lookups_ud`: the same
  bound for the event that the lookup messages of an accepted proof within the
  size bounds are not balanced (`Exec/Stark/Lookups.lean`), for a system whose
  lookups read only the fixed and main traces and the row selectors
  (`Circuit.LookupsPlain`).

## Assumptions

Those of `soundness_verify` other than `hpcs` and `hθ`: the random-oracle model
with the idealised challenger and Merkle trees over the oracle, a `StarkModel`
of the fields, a system fixed before the adversary runs, none of whose fixed
traces is taller than the largest trace it supports (`sys.HeightOk`), and the
size bounds of `Covered` (of `BatchCovered`, for a batch). The event of each
theorem is: the verifier accepts, the attempt is within the size bounds, and
the conclusion fails. Nothing is assumed about the shape of the proof: that its
first domain exists in the field, that no column is shorter than the final
height, and that the first domain is no larger than the largest trace the
system supports, times the blowup, follow from acceptance.

`hrate : 2 * δ + (1 / 2) ^ logBlowup < 1`: the distance `δ` is strictly inside
the unique-decoding radius of a code of rate `2 ^ (-logBlowup)`. It gives the
round-by-round soundness of the opening protocol (`rbrSound_pcs_ud`, which
needs `≤` only) and the margin of unique decoding on the coset of every
committed matrix, whatever its height (`strictMargin_coset`, which needs `<`).

The two theorems about lookups also assume a characteristic other than two and
that the lookups of every circuit of the system are plain
(`Circuit.LookupsPlain`): their multiplicities and their arguments read only
the fixed trace, the main trace and the row selectors. The zeros may read
anything, the lookup trace and the public values included: a system with
extension constraints is covered, as long as the nodes its lookups refer to
come before the first node that reads the lookup trace or a public value.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Oracle OracleComp

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF]
  {slots width : ℕ} [Fintype K] (M : StarkModel F EF K) (sys : System F D) (B : Bounds) (δ : ℝ)

/-- **The largest error of a round of the STARK**, at agreement `1 - δ`: that
of the two lookup challenges, of the constraint challenge, of the out-of-domain
point, and of the opening protocol. -/
noncomputable def starkErr : ℝ :=
  max (max (roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) 0)
      (roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) 1))
    (max (max (roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) 2)
        (roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) 3))
      (pcsErr (K := K) sys M.extData.d δ))

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The error of every round is at most `starkErr`. -/
theorem roundErr_le_starkErr (i : ℕ) :
    roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) i ≤ starkErr M sys B δ := by
  by_cases h0 : i = 0
  · subst h0
    exact le_max_of_le_left (le_max_left _ _)
  by_cases h1 : i = 1
  · subst h1
    exact le_max_of_le_left (le_max_right _ _)
  by_cases h2 : i = 2
  · subst h2
    exact le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
  by_cases h3 : i = 3
  · subst h3
    exact le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
  have hi : roundErr M sys B (pcsErr (K := K) sys M.extData.d δ) i =
      pcsErr (K := K) sys M.extData.d δ := by
    simp only [roundErr, h0, h1, h2, h3, ↓reduceIte]
  rw [hi]
  exact le_max_of_le_right (le_max_right _ _)

omit [DecidableEq K] [Inhabited D] [DecidableEq D] [DecidableEq F] [DecidableEq EF] in
/-- The largest error is not negative. -/
theorem starkErr_nonneg {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ starkErr M sys B δ :=
  (pcsErr_nonneg (K := K) sys M.extData.d hδ).trans (le_max_of_le_right (le_max_right _ _))

variable {δ}

/-- **Soundness of `Stark.verify`, with no hypothesis about the opening
protocol.** For `δ ≥ 0` with `2 * δ + (1 / 2) ^ logBlowup < 1`, the probability
that some answer function that agrees with the final log makes `Stark.verify`
accept an attempt, with public claims within the size bounds (`Covered`), one
of whose constraints fails, at agreement `1 - δ`, is at most
`N * starkErr + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, with
`N = Q + shardQueries sys twoAdicity` and `r = maxRounds F`. No fixed trace of
the system is taller than the largest trace it supports (`hheightOk`). -/
theorem soundness_verify_ud [Fintype D] (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          Violates M sys (1 - δ) l f (attempt out.1))
      (experiment M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErr M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verify M sys (1 - δ) B hfixed hheightOk hshards hN hcast (by linarith)
    (pcsErr_nonneg (K := K) sys M.extData.d hδ) htwo hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcs_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErr M sys B δ) (starkErr_nonneg M sys B hδ) hadv attempt

/-- **Soundness of `Stark.verifyBatch`, with no hypothesis about the opening
protocol.** For `δ ≥ 0` with `2 * δ + (1 / 2) ^ logBlowup < 1`, the probability
that some answer function that agrees with the final log makes
`Stark.verifyBatch` accept a batch, with a preamble within the size bounds
(`BatchCovered`), one of whose shards has a failing constraint, at agreement
`1 - δ`, is at most
`N * starkErr + ((B.shards + 1) * r + 3) * N * (N - 1) / (2 * |D|)`, with
`N = Q + B.shards * shardQueries sys twoAdicity` and `r = maxRounds F`. No
fixed trace of the system is taller than the largest trace it supports
(`hheightOk`). -/
theorem soundness_verifyBatch_ud [Fintype D] (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          BatchViolates M sys (1 - δ) l f (attempt out.1))
      (batchExperiment M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErr M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatch M sys (1 - δ) B hfixed hheightOk hN hcast (by linarith)
    (pcsErr_nonneg (K := K) sys M.extData.d hδ) htwo hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcs_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErr M sys B δ) (starkErr_nonneg M sys B hδ) hadv attempt

/-- **`Stark.verify` only accepts balanced lookups, with no hypothesis about
the opening protocol.** For a system whose lookups are plain (its zeros may
read anything) over a field of characteristic not two and `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup < 1`, the probability that some answer function
that agrees with the final log makes `Stark.verify` accept an attempt, with
public claims within the size bounds (`Covered`), whose lookup messages are not
balanced, at agreement `1 - δ`, is at most the bound of `soundness_verify_ud`.
No fixed trace of the system is taller than the largest trace it supports
(`hheightOk`). -/
theorem soundness_verify_lookups_ud [Fintype D] (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → SAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts M sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ¬ LookupsBalanced M sys (1 - δ) B l (attempt out.1))
      (experiment M sys adv attempt) [] ≤
      (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) * starkErr M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verify_lookups M sys (1 - δ) B hplain h2 hfixed hheightOk hshards hN hcast
    (by linarith)
    (pcsErr_nonneg (K := K) sys M.extData.d hδ) htwo hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcs_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErr M sys B δ) (starkErr_nonneg M sys B hδ) hadv attempt

/-- **`Stark.verifyBatch` only accepts balanced lookups, with no hypothesis
about the opening protocol.** For a system whose lookups are plain (its zeros
may read anything) over a field of characteristic not two and `δ ≥ 0` with
`2 * δ + (1 / 2) ^ logBlowup < 1`, the probability that some answer function
that agrees with the final log makes `Stark.verifyBatch` accept a batch, with a
preamble within the size bounds (`BatchCovered`), whose lookup messages are not
balanced, at agreement `1 - δ`, is at most the bound of
`soundness_verifyBatch_ud`. No fixed trace of the system is taller than the
largest trace it supports (`hheightOk`). -/
theorem soundness_verifyBatch_lookups_ud [Fintype D] (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (h2 : (2 : K) ≠ 0) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N)
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : TwoAdicOps.twoAdicity (F := F) ≤ width) {A : Type}
    {adv : OracleComp (SAns F EF D K slots width) A} {Q : ℕ} (hadv : adv.QueryBound Q)
    (attempt : A → BAttempt F EF D) :
    prob (fun out l => ∃ f : ∀ x, SAns F EF D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts M sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalanced M sys (1 - δ) B l (attempt out.1))
      (batchExperiment M sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          starkErr M sys B δ +
        ((B.shards + 1) * maxRounds F + 3) *
          (Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) *
          ((Q + B.shards * shardQueries sys (TwoAdicOps.twoAdicity (F := F)) : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatch_lookups M sys (1 - δ) B hplain h2 hfixed hheightOk hN hcast
    (by linarith)
    (pcsErr_nonneg (K := K) sys M.extData.d hδ) htwo hslots hcommit hquery hwidth
    (fun v hs => rbrSound_pcs_ud M sys hδ hrate.le v hs.active hs)
    (roundErr_le_starkErr M sys B δ) (starkErr_nonneg M sys B hδ) hadv attempt

end CertiFri.Exec.Stark
