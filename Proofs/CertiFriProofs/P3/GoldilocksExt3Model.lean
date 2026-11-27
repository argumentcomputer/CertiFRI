import CertiFriProofs.P3.GoldilocksExt3
import CertiFriProofs.Exec.Stark.Model
import CertiFriProofs.Exec.Stark.Unconditional

/-!
# Goldilocks and its cubic trinomial extension `Fp3` as a `StarkModel`

Constructs `GoldilocksExt3.starkModel : Exec.Stark.StarkModel Goldilocks GoldilocksExt3 Fp3Model`
for the Protocol `v6` cubic trinomial extension `Fp3Model ≃+* GF(p)[Y] / (Y^3 - Y - 1)` of order
`p ^ 3 = (2^64 - 2^32 + 1)^3 ≈ 2^192`, and instantiates the unconditional STARK soundness theorems
over `Goldilocks` / `GoldilocksExt3` with zero field-model or proximity assumptions.

## Contents

* `Fp3Model.extData`: degree-`3` extension basis `(1, Y, Y^2)` and coordinates `(c0, c1, c2)`.
* `Fp3Model.natCast_inj`, `Fp3Model.natCast_inj_le`, `Fp3Model.two_ne_zero`: natural-number cast
  injectivity below `p` and characteristic-not-two in `Fp3Model`.
* `GoldilocksExt3.starkModel`: complete `Exec.Stark.StarkModel` over `Fp3Model`.
* `GoldilocksExt3.soundness_verify`, `GoldilocksExt3.soundness_verifyBatch`,
  `GoldilocksExt3.soundness_verify_lookups`, `GoldilocksExt3.soundness_verifyBatch_lookups`:
  unconditional Horner-FRI STARK soundness theorems instantiated over `Fp3Model`.
  (Tensor-batched `FriBatching::Tensor` STARK soundness over `Fp3Model` — both unpruned and
  with `CertiFri.P3.prunedMmcs` — is instantiated in `P3/GoldilocksExt3Soundness.lean`.)
-/

namespace CertiFri.P3

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Exec CertiFri.Exec.Stark
  CertiFri.Oracle OracleComp

namespace Fp3Model

/-- The basis `(1, Y, Y^2)` of the cubic trinomial extension `Fp[Y] / (Y^3 - Y - 1)`. -/
def basis (k : ℕ) : Fp3Model :=
  match k with
  | 0 => 1
  | 1 => xElem
  | 2 => xElem * xElem
  | _ => 0

/-- The embedded base-field coordinates of an element of `Fp3Model` in basis `(1, Y, Y^2)`. -/
def coord (y : Fp3Model) (k : ℕ) : Fp3Model :=
  match k with
  | 0 => embed y.c0
  | 1 => embed y.c1
  | 2 => embed y.c2
  | _ => 0

/-- `ExtData` for the cubic trinomial extension `Fp3Model`. -/
def extData : ExtData Fp3Model where
  d := 3
  basis := basis
  coord := coord
  d_pos := by decide
  basis_zero := rfl
  sum_coord y := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ext <;> simp [basis, coord, embed, xElem]

/-- Natural numbers embed into `Fp3Model` via the base-field embedding `embedHom`. -/
theorem natCast_eq_embedHom (n : ℕ) : (n : Fp3Model) = embedHom (n : GoldilocksField) := by
  induction n with
  | zero => exact (map_zero embedHom).symm
  | succ n ih => rw [Nat.cast_succ, Nat.cast_succ, map_add, map_one, ih]

/-- Natural numbers below `Goldilocks.order` are distinct in `Fp3Model`. -/
theorem natCast_inj {a b : ℕ} (ha : a < Goldilocks.order) (hb : b < Goldilocks.order)
    (h : (a : Fp3Model) = (b : Fp3Model)) : a = b := by
  rw [natCast_eq_embedHom, natCast_eq_embedHom] at h
  have hbase : (a : GoldilocksField) = (b : GoldilocksField) := embedHom_injective h
  have hval := congrArg ZMod.val hbase
  rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hval

/-- Natural numbers of at most `N < Goldilocks.order` are distinct in `Fp3Model`. -/
theorem natCast_inj_le {N : ℕ} (hNp : N < Goldilocks.order) (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (h : (a : Fp3Model) = (b : Fp3Model)) : a = b :=
  natCast_inj (lt_of_le_of_lt ha hNp) (lt_of_le_of_lt hb hNp) h

/-- Two is not zero in `Fp3Model`. -/
theorem two_ne_zero : (2 : Fp3Model) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : Fp3Model) = ((0 : ℕ) : Fp3Model) := by simpa using h
  have := natCast_inj (a := 2) (b := 0) (by unfold Goldilocks.order; decide)
    (by unfold Goldilocks.order; decide) h'
  omega

end Fp3Model

namespace GoldilocksExt3

/-- **Complete `Exec.Stark.StarkModel` for `Goldilocks` and its cubic trinomial extension
`GoldilocksExt3` over `Fp3Model` (`|Fp3Model| = p ^ 3 ≈ 2 ^ 192`).** -/
def starkModel : StarkModel Goldilocks GoldilocksExt3 Fp3Model where
  toFieldModel := goldilocksExt3_fieldModel
  extData := Fp3Model.extData
  degree_eq := rfl
  toBasis_size _ := rfl
  toBasis x k hk := by
    change k < 3 at hk
    interval_cases k <;> rfl
  ofBasis a ha := by
    change GoldilocksExt3.toModel (ExtensionOps.ofBasis a) =
      ∑ k ∈ Finset.range 3,
        goldilocksExt3_fieldModel.base.toModel (a.getD k 0) * Fp3Model.extData.basis k
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    change GoldilocksExt3.toModel
        ⟨a[0]?.getD Goldilocks.zero, a[1]?.getD Goldilocks.zero, a[2]?.getD Goldilocks.zero⟩ =
      Fp3Model.embedHom (Goldilocks.toZMod (a.getD 0 0)) * Fp3Model.basis 0 +
      Fp3Model.embedHom (Goldilocks.toZMod (a.getD 1 0)) * Fp3Model.basis 1 +
      Fp3Model.embedHom (Goldilocks.toZMod (a.getD 2 0)) * Fp3Model.basis 2
    have h0 : a.getD 0 0 = a[0]?.getD Goldilocks.zero := Array.getD_eq_getD_getElem?
    have h1 : a.getD 1 0 = a[1]?.getD Goldilocks.zero := Array.getD_eq_getD_getElem?
    have h2 : a.getD 2 0 = a[2]?.getD Goldilocks.zero := Array.getD_eq_getD_getElem?
    rw [h0, h1, h2]
    ext <;> simp [GoldilocksExt3.toModel, Fp3Model.basis, Fp3Model.embed, Fp3Model.xElem]
  generator k hk :=
    (goldilocks_twoAdicGenerator_isPrimitiveRoot k hk).map_of_injective Fp3Model.embedHom_injective
  generator_sq k hk := by
    change Fp3Model.embedHom (Goldilocks.toZMod (Goldilocks.twoAdicGenerator (k + 1))) ^ 2 =
      Fp3Model.embedHom (Goldilocks.toZMod (Goldilocks.twoAdicGenerator k))
    rw [← map_pow, goldilocks_twoAdicGenerator_sq k hk]
  shift_ne := fun h => by
    change Fp3Model.embedHom Goldilocks.generator.toZMod = 0 at h
    exact goldilocks_cosetShift_ne_zero
      (Fp3Model.embedHom_injective (h.trans (map_zero Fp3Model.embedHom).symm))

/-- The underlying `FieldModel` of `GoldilocksExt3.starkModel` is `goldilocksExt3_fieldModel`. -/
@[simp] theorem starkModel_toFieldModel :
    starkModel.toFieldModel = goldilocksExt3_fieldModel := rfl

/-- The extension degree of `GoldilocksExt3.starkModel` is `3`. -/
@[simp] theorem starkModel_extData_d : starkModel.extData.d = 3 := rfl

section HornerSoundness

variable {D : Type} [Inhabited D] [DecidableEq D] [Fintype D] {slots width : ℕ}
  (sys : System Goldilocks D) (B : Bounds) {δ : ℝ}

/-- **Soundness of `Stark.verify` (Horner FRI) over Goldilocks cubic extension `Fp3Model`.** -/
theorem soundness_verify (hδ : 0 ≤ δ) (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hfixed : sys.FixedOk) (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ}
    (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt3 D Fp3Model slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt3 D Fp3Model slots width x,
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
    (Fp3Model.natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

/-- **Soundness of `Stark.verifyBatch` (Horner FRI) over Goldilocks cubic extension `Fp3Model`.** -/
theorem soundness_verifyBatch (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt3 D Fp3Model slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt3 D Fp3Model slots width x,
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
    (Fp3Model.natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

/-- **`Stark.verify` (Horner FRI) over `Fp3Model` only accepts balanced lookups.** -/
theorem soundness_verify_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) (hshards : 1 ≤ B.shards) {N : ℕ} (hN : BoundsLE sys B N)
    (hNp : N < Goldilocks.order) (htwo : sys.maxLogDegree ≤ 32)
    (hslots : sys.fri.numQueries + 1 ≤ slots) (hcommit : sys.fri.commitPowBits ≤ width)
    (hquery : sys.fri.queryPowBits ≤ width) (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt3 D Fp3Model slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → SAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt3 D Fp3Model slots width x,
        (∀ x y, l.dlookup x = some y → f x = y) ∧
          verifyAccepts starkModel sys f (attempt out.1) = true ∧
          Covered B (attempt out.1) ∧
          ¬ LookupsBalanced starkModel sys (1 - δ) B l (attempt out.1))
      (experiment starkModel sys adv attempt) [] ≤
      (Q + shardQueries sys 32 : ℕ) * starkErr starkModel sys B δ +
        ((B.shards + 1) * maxRounds Goldilocks + 3) *
          (Q + shardQueries sys 32 : ℕ) * ((Q + shardQueries sys 32 : ℕ) - 1) /
            (2 * Fintype.card D) :=
  soundness_verify_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero hfixed
    hheightOk hshards hN (Fp3Model.natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv
    attempt

/-- **`Stark.verifyBatch` (Horner FRI) over `Fp3Model` only accepts balanced lookups.** -/
theorem soundness_verifyBatch_lookups (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ sys.fri.logBlowup < 1)
    (hplain : ∀ c ∈ sys.circuits, c.LookupsPlain) (hfixed : sys.FixedOk)
    (hheightOk : sys.HeightOk) {N : ℕ} (hN : BoundsLE sys B N) (hNp : N < Goldilocks.order)
    (htwo : sys.maxLogDegree ≤ 32) (hslots : sys.fri.numQueries + 1 ≤ slots)
    (hcommit : sys.fri.commitPowBits ≤ width) (hquery : sys.fri.queryPowBits ≤ width)
    (hwidth : 32 ≤ width) {A : Type}
    {adv : OracleComp (SAns Goldilocks GoldilocksExt3 D Fp3Model slots width) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → BAttempt Goldilocks GoldilocksExt3 D) :
    prob (fun out l => ∃ f : ∀ x, SAns Goldilocks GoldilocksExt3 D Fp3Model slots width x,
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
  soundness_verifyBatch_lookups_ud starkModel sys B hδ hrate hplain Fp3Model.two_ne_zero hfixed
    hheightOk hN (Fp3Model.natCast_inj_le hNp) htwo hslots hcommit hquery hwidth hadv attempt

end HornerSoundness

end GoldilocksExt3

end CertiFri.P3
