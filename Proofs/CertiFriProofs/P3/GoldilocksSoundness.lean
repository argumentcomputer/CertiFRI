import CertiFriProofs.P3.GoldilocksModel
import CertiFriProofs.Exec.Stark.Unconditional

/-!
# The soundness theorems, over Goldilocks

The theorems about the STARK verifier (`Exec/Stark/Unconditional.lean`) hold
for any executable fields with a `StarkModel`. Here they are stated for the
fields the verifier is run with: Goldilocks and its quadratic extension
(`CertiFriP3`), whose model is `Goldilocks.starkModel`
(`P3/GoldilocksModel.lean`). The model field `Goldilocks.K` has `p ^ 2`
elements, with `p = 2^64 - 2^32 + 1` (`Goldilocks.card_K`).

## Contents

* `Goldilocks.fieldModel`, `Goldilocks.wellFormed`: the model and the
  conditions on the two-adic structure that the theorems about the opening
  proof assume (`FieldModel`, `WellFormed` of `Exec/Setup.lean`), for any shape
  whose first domain has at most `2 ^ 32` points.
* `Goldilocks.soundness_verify`, `Goldilocks.soundness_verifyBatch`: soundness
  of `Stark.verify` and `Stark.verifyBatch` over Goldilocks, with an explicit
  error.
* `Goldilocks.soundness_verify_lookups`,
  `Goldilocks.soundness_verifyBatch_lookups`: accepted proofs have balanced
  lookups.

## Assumptions

Those of `Exec/Stark/Unconditional.lean` that are not about the fields: the
random-oracle model with the idealised challenger and Merkle trees, a system
fixed before the adversary runs, `System.FixedOk` and `System.HeightOk`, traces
of at most `2 ^ 32` rows, and size bounds below the order of the field
(`hNp`). Nothing is assumed about the arithmetic of the fields.
-/

namespace CertiFri.P3.Goldilocks

open CertiFri.Stark CertiFri.Fri CertiFri.Exec CertiFri.Exec.Stark CertiFri.Oracle OracleComp

/-- The model of Goldilocks and its quadratic extension, for the theorems
about the opening proof. -/
noncomputable def fieldModel : FieldModel Goldilocks GoldilocksExt K :=
  starkModel.toFieldModel

/-- The conditions of the opening proof on the two-adic structure hold for
every shape whose first domain has at most `2 ^ 32` points. -/
theorem wellFormed (params : FriParams) (shape : ClaimShape)
    (h : logMaxHeight params.logBlowup shape ≤ 32) : WellFormed fieldModel params shape :=
  starkModel.wellFormed params shape h

/-- Natural numbers of at most `N < p` are different in the model field. -/
theorem natCast_inj_le {N : ℕ} (hNp : N < order) (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (h : (a : K) = (b : K)) : a = b :=
  natCast_inj (lt_of_le_of_lt ha hNp) (lt_of_le_of_lt hb hNp) h

/-- Two is not zero in the model field. -/
theorem two_ne_zero : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = ((0 : ℕ) : K) := by simpa using h
  have := natCast_inj (a := 2) (b := 0) (by decide) (by decide) h'
  omega

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {slots width : ℕ}
  (sys : System Goldilocks D) (B : Bounds) {δ : ℝ}

/-- **Soundness of `Stark.verify` over Goldilocks.** The statement of
`soundness_verify_ud` for the fields of `CertiFriP3`, with nothing assumed
about their arithmetic: the size bounds are below the order of the field
(`hNp`) and the traces have at most `2 ^ 32` rows (`htwo`). -/
theorem soundness_verify (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < order) (htwo : sys.maxLogDegree ≤ 32)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt D K slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts starkModel sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          Violates starkModel sys (1 - δ) l f (attempt out.1))
      (experiment starkModel sys adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErr starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verify_ud starkModel sys B hδ hrate hfixed hheightOk hshards hN
    (natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

/-- **Soundness of `Stark.verifyBatch` over Goldilocks.** The statement of
`soundness_verifyBatch_ud` for the fields of `CertiFriP3`, with nothing assumed
about their arithmetic. -/
theorem soundness_verifyBatch (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < order)
    (htwo : sys.maxLogDegree ≤ 32) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt D K slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts starkModel sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          BatchViolates starkModel sys (1 - δ) l f (attempt out.1))
      (batchExperiment starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErr starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatch_ud starkModel sys B hδ hrate hfixed hheightOk hN
    (natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

/-- **`Stark.verify` over Goldilocks only accepts balanced lookups.** The
statement of `soundness_verify_lookups_ud` for the fields of `CertiFriP3`, with
nothing assumed about their arithmetic. -/
theorem soundness_verify_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < order) (htwo : sys.maxLogDegree ≤ 32)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt D K slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts starkModel sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ¬ LookupsBalanced starkModel sys (1 - δ) B l (attempt out.1))
      (experiment starkModel sys adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErr starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verify_lookups_ud starkModel sys B hδ hrate hplain two_ne_zero hfixed hheightOk
    hshards hN (natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

/-- **`Stark.verifyBatch` over Goldilocks only accepts balanced lookups.** The
statement of `soundness_verifyBatch_lookups_ud` for the fields of `CertiFriP3`,
with nothing assumed about their arithmetic. -/
theorem soundness_verifyBatch_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < order)
    (htwo : sys.maxLogDegree ≤ 32) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt D K slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt D K slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          batchAccepts starkModel sys f (attempt out.1) = true ∧
          BatchCovered B (attempt out.1) ∧
          ¬ BatchLookupsBalanced starkModel sys (1 - δ) B l (attempt out.1))
      (batchExperiment starkModel sys B adv attempt) [] ≤
      (Q + B.shards * shardQueries sys 32 : ℕ) * starkErr starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + B.shards * shardQueries sys 32 : ℕ) *
          ((Q + B.shards * shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verifyBatch_lookups_ud starkModel sys B hδ hrate hplain two_ne_zero hfixed
    hheightOk hN (natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

end CertiFri.P3.Goldilocks
