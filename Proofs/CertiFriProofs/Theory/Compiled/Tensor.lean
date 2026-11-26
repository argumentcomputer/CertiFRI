import CertiFriProofs.Theory.Compiled.SoundnessView
import CertiFriProofs.Theory.PcsRbrTensor

/-!
# Compiled tensor-batched FRI verifier and soundness

Tensor-batched counterpart of `Theory/Compiled/{Verifier,Accepts,SoundnessView}.lean`.
Reuses `Compiled.Params`, `Compiled.Msg`, `Compiled.Proof`, `Params.read`,
`Params.inputChecks`, `Params.foldChain`, `Params.round_of_opens`, and
`Oracle.prob_fsExperiment_bind_committedRow_le` verbatim, replacing only the
round-0 reduced-opening combination (`Params.reducedTensor`) and challenge type
(`PcsRbr.ChalTensor`).

## Main results

* `Params.verifyWithTensor` / `Params.verifyGrindViewTensor`: compiled verifier
  for `FriBatching::Tensor`, making at most `P.verifierQueries` oracle queries
  (`Params.queryBound_verifyWithTensor`).
* `Params.acceptsTensor_of_outcome_verifyWithTensor_view`: an accepting run
  against a collision-free log implies oracle-model acceptance `AcceptsTensor`.
* `Params.soundness_grind_view_tensor_of_imp`: soundness in the chained random
  oracle model for any event (such as executable `Fri.verifyTensor` acceptance)
  that implies compiled-verifier acceptance.
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (TensorChal tensorCoordWeight reducedOpeningTensor pcsInputTensor
  ChalTensor tensorOf betasOfTensor queriesOfTensor claimsOf wordsOf
  ClaimsFail AcceptsTensor GrindChal PowPasses ungrind roundErrorTensor)

variable {F D : Type}

/-! ## Arithmetic of tensor-batched reduced openings and fold chain -/

section TensorArith

variable [Field F]

namespace Params

variable (P : Params F)

/-- Tensor-batched reduced opening of level `j` at query index `index` from the
opened values, using the 2D slot map `coord j : Fin (P.numClaims j) → Fin M × Fin W`. -/
def reducedTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (msg : Msg F D P.batches) (opened : ∀ j, Fin (P.numClaims j) → F)
    (r : TensorChal F W M) (index j : ℕ) : F :=
  ∑ k : Fin (P.numClaims j),
    tensorCoordWeight r (coord j k) *
      ((msg.value j k - opened j k) /
        (msg.point j k - P.shift * pointOfIndex P.ω P.n (P.n - j) (index >>> j)))

/-- Fold chain value of query `t` after `i` rounds under tensor batching. -/
def foldedTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) : F :=
  P.foldChain (P.reducedTensor W M coord msg₀ (P.opened pf t) r index)
    (fun i => pf.siblings i t) β index i

/-- Reconstructed folding-round row of query `t` at round `i` under tensor batching. -/
def commitRowTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) : F × F :=
  placeRow (P.foldedTensor W M coord pf msg₀ r β index t i) (pf.siblings i t) (index >>> i)

theorem foldedTensor_zero (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) :
    P.foldedTensor W M coord pf msg₀ r β index t 0 =
      P.reducedTensor W M coord msg₀ (P.opened pf t) r index 0 := rfl

theorem foldedTensor_succ (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg₀ : Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : ℕ) (t : Fin P.queries) (i : ℕ) :
    P.foldedTensor W M coord pf msg₀ r β index t (i + 1) =
      foldRow (β i) (pointOfIndex P.ω P.n (P.n - i) (2 * (index >>> (i + 1))))
          (P.commitRowTensor W M coord pf msg₀ r β index t i).1
          (P.commitRowTensor W M coord pf msg₀ r β index t i).2 +
        β i ^ 2 * P.reducedTensor W M coord msg₀ (P.opened pf t) r index (i + 1) := rfl

end Params

end TensorArith

/-! ## Compiled tensor verifier -/

section TensorVerifier

variable [Field F] [DecidableEq F] [DecidableEq D]

namespace Params

variable (P : Params F)

/-- Merkle checks of the folding rounds under tensor batching. -/
def commitChecksTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    List (OracleComp (MerkleAnswer M' C F D) Bool) :=
  (List.range P.rounds).map fun i =>
    verifyOpeningsM (msg (i + 1)).commitRoot (P.commitDims i)
      (Array.ofFn fun t => index t >>> (i + 1))
      (Array.ofFn fun t => #[#[(P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).1,
        (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).2]])
      (Array.ofFn (pf.commitPaths i))

/-- Final polynomial comparison under tensor batching. -/
def FinalCheckTensor (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) : Prop :=
  ∀ t, P.foldedTensor W M coord pf (msg 0) r β (index t) t P.rounds =
    hornerEval ((msg (P.rounds + 1)).finalCoeffs.take P.finalDegree)
      (pointOfIndex P.ω P.n (P.n - P.rounds) (index t >>> P.rounds))

instance (W M : ℕ) (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    Decidable (P.FinalCheckTensor W M coord pf msg r β index) := by
  unfold FinalCheckTensor
  infer_instance

/-- **Compiled tensor verifier**, on the messages, tensor schedule, folding
challenges, and query indices read off a transcript. Makes only hash queries. -/
def verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    OracleComp (MerkleAnswer M' C F D) Bool :=
  (allM (P.inputChecks pf (msg 0) index)).bind fun ok =>
    if ok && decide (P.FinalCheckTensor W M coord pf msg r β index) then
      allM (P.commitChecksTensor W M coord pf msg r β index)
    else .pure false

/-- Query bound of `verifyWithTensor`: identical to `P.verifierQueries`. -/
theorem queryBound_verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    (P.verifyWithTensor (M' := M') (C := C) W M coord pf msg r β index).QueryBound
      P.verifierQueries := by
  have hin : (allM (P.inputChecks (M := M') (C := C) pf (msg 0) index)).QueryBound
      (P.batches * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.inputChecks (M := M') (C := C) pf (msg 0) index) fun c hc => by
        obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        exact Nat.mul_le_mul_left _ (by have := P.height_le b; omega)
    rwa [inputChecks, List.length_map, List.length_finRange] at h
  have hcommit : (allM (P.commitChecksTensor (M' := M') (C := C) W M coord pf msg r β index)).QueryBound
      (P.rounds * (P.queries * (3 * P.n + 1))) := by
    have h := queryBound_allM (n := P.queries * (3 * P.n + 1))
      (P.commitChecksTensor (M' := M') (C := C) W M coord pf msg r β index) fun c hc => by
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
        refine (queryBound_verifyOpeningsM _ _ _ _ _).mono ?_
        rw [Array.size_ofFn]
        refine Nat.mul_le_mul_left _ ?_
        have : Merkle.maxLogHeight (P.commitDims i).toList ≤ P.n := by
          simp only [commitDims, List.toList_toArray, Merkle.maxLogHeight]
          omega
        omega
    rwa [commitChecksTensor, List.length_map, List.length_range] at h
  refine QueryBound.mono (hin.bind fun ok => ?_) (by rw [verifierQueries, Nat.add_mul])
  split
  · exact hcommit
  · exact queryBound_pure _ _

/-- Execution of `verifyWithTensor` against a total answer function `f`. -/
theorem run_verifyWithTensor {M' : Type} {C : ℕ → Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (f : ∀ x : FSQuery M' C (HashQuery F D), MerkleAnswer M' C F D x)
    (pf : Proof F D P.batches P.queries) (msg : ℕ → Msg F D P.batches)
    (r : TensorChal F W M) (β : ℕ → F) (index : Fin P.queries → ℕ) :
    (P.verifyWithTensor W M coord pf msg r β index).run f =
      (((List.finRange P.batches).all fun b =>
          Merkle.verifyOpenings (hasherOf f) ((msg 0).inputRoots b) (P.dims b)
            (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
            (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
        decide (P.FinalCheckTensor W M coord pf msg r β index) &&
        (List.range P.rounds).all fun i =>
          Merkle.verifyOpenings (hasherOf f) (msg (i + 1)).commitRoot (P.commitDims i)
            (Array.ofFn fun t => index t >>> (i + 1))
            (Array.ofFn fun t => #[#[(P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).1,
              (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).2]])
            (Array.ofFn (pf.commitPaths i))) := by
  rw [verifyWithTensor, run_bind, run_allM, inputChecks, List.all_map]
  simp only [Function.comp_def, run_verifyOpeningsM]
  split
  · next h =>
    rw [run_allM, commitChecksTensor, List.all_map]
    simp only [Function.comp_def, run_verifyOpeningsM]
    rw [h, Bool.true_and]
  · next h =>
    rw [run_pure, (Bool.not_eq_true _).mp h, Bool.false_and]

/-- Compiled tensor verifier with proof-of-work checks on a transcript of raw messages. -/
noncomputable def verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) (pf : Proof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2)) :
    OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) Bool :=
  @ite _ (PowPasses t) (Classical.propDecidable _)
    (P.verifyWithTensor W M coord pf (fun j => view (msgAt (ungrind t) j))
      (tensorOf (ungrind t)) (betasOfTensor (ungrind t))
      (fun k => P.indexOf (queriesOfTensor (ungrind t) k)))
    (.pure false)

theorem queryBound_verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) (pf : Proof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2)) :
    (P.verifyGrindViewTensor W M coord bits view pf t).QueryBound P.verifierQueries := by
  unfold verifyGrindViewTensor
  split
  · exact P.queryBound_verifyWithTensor W M coord pf _ _ _ _
  · exact queryBound_pure _ _

theorem run_verifyGrindViewTensor {M' : Type} (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches)
    (f : ∀ x, MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D x)
    (pf : Proof F D P.batches P.queries)
    (t : Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2)) :
    (P.verifyGrindViewTensor W M coord bits view pf t).run f = true ↔
      PowPasses t ∧
        (P.verifyWithTensor (M' := M') (C := GrindChal bits (ChalTensor P.ldt W M P.queries))
          W M coord pf (fun j => view (msgAt (ungrind t) j)) (tensorOf (ungrind t))
          (betasOfTensor (ungrind t))
          (fun k => P.indexOf (queriesOfTensor (ungrind t) k))).run f = true := by
  unfold verifyGrindViewTensor
  split
  · next h => exact ⟨fun hr => ⟨h, hr⟩, fun hr => hr.2⟩
  · next h => exact ⟨fun hr => absurd hr (by simp), fun hr => absurd hr.1 h⟩

end Params

end TensorVerifier

/-! ## Accepting run implies oracle-model acceptance (`AcceptsTensor`) -/

section TensorAccepts

variable [Field F] [DecidableEq F] [DecidableEq D]

omit [DecidableEq F] in
/-- Query points of a full tensor-batched transcript lie in the first domain. -/
theorem queriesOfTensor_mem {M' : Type} {S : LdtInstance F} {W M q : ℕ}
    (t : Transcript M' (ChalTensor S W M q) (S.rounds + 2)) (k : Fin q) :
    queriesOfTensor t k ∈ S.domain 0 := by
  cases t with
  | snoc t m c =>
    rw [PcsRbr.queriesOfTensor_snoc, PcsRbr.ChalTensor.points_of_not_le (Nat.not_succ_le_self _)]
    exact (PcsRbr.chalTensorQuery _ c k).2

namespace Params

variable (P : Params F) {M' : Type} {C : ℕ → Type}
  [DecidableEq (FSQuery M' C (HashQuery F D))]
  {W M : ℕ} {coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W}
  {pf : Proof F D P.batches P.queries} {msg : ℕ → Msg F D P.batches}
  {r : TensorChal F W M} {β : ℕ → F} {index : Fin P.queries → ℕ}
  {l l' : Log (MerkleAnswer M' C F D)}

theorem outcome_verifyWithTensor
    (h : Outcome (P.verifyWithTensor W M coord pf msg r β index) l true l') :
    (∀ b t, Opens l' ((msg 0).inputRoots b) (P.dims b)
        (index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t)) ∧
      P.FinalCheckTensor W M coord pf msg r β index ∧
      ∀ i < P.rounds, ∀ t, Opens l' (msg (i + 1)).commitRoot (P.commitDims i)
        (index t >>> (i + 1))
        #[#[(P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).1,
          (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).2]] := by
  obtain ⟨ok, l₁, hin, hrest⟩ := outcome_bind.mp h
  split at hrest
  · next hcond =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    obtain ⟨rfl, hfinal⟩ := hcond
    refine ⟨fun b t => ?_, hfinal, fun i hi t => ?_⟩
    · obtain ⟨la, lb, hrun, hpre⟩ := outcome_allM hin _
        (List.mem_map.mpr ⟨b, List.mem_finRange b, rfl⟩)
      exact ((opens_of_outcome_ofFn hrun t).of_prefix hpre).of_prefix hrest.prefix
    · obtain ⟨la, lb, hrun, hpre⟩ := outcome_allM hrest _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      exact (opens_of_outcome_ofFn hrun t).of_prefix hpre
  · exact absurd hrest.1 (by simp)

omit [DecidableEq D] in
theorem pcsInputTensor_eq_reducedTensor (hl : ¬ LogCollision hashObs l')
    {idx : ℕ} {t : Fin P.queries}
    (hopen : ∀ b, Opens l' ((msg 0).inputRoots b) (P.dims b)
      (idx >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t))
    (hidx : idx < 2 ^ P.n) {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r j
        (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) =
      P.reducedTensor W M coord (msg 0) (P.opened pf t) r idx j := by
  have hjn : j ≤ P.n := hj.trans P.rounds_le
  unfold pcsInputTensor reducedOpeningTensor Params.reducedTensor quotientAt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn)]
  obtain ⟨d, hd, hdh, -⟩ := P.slot_dims j hj k
  have hmem : d ∈ (P.dims (P.slot j k).batch).toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hd)
  have hle := Merkle.le_maxLogHeight hmem
  have hH := P.height_le (P.slot j k).batch
  have hrow := committedRow_of_opens hl (hopen (P.slot j k).batch) hd
  rw [← Nat.shiftRight_add, show P.n - Merkle.maxLogHeight (P.dims (P.slot j k).batch).toList +
    (Merkle.maxLogHeight (P.dims (P.slot j k).batch).toList - d.logHeight) = j by omega] at hrow
  rw [hrow]
  rfl

theorem queryAccepts_of_outcome_tensor
    (hrun : Outcome (P.verifyWithTensor W M coord pf msg r β index) l true l')
    (hl : ¬ LogCollision hashObs l') (t : Fin P.queries) (hindex : index t < 2 ^ P.n)
    (words : ℕ → F → F)
    (hwords : ∀ i ≤ P.rounds, words i = (P.read (i + 1) (msg (i + 1)) (committedRow l')).word) :
    QueryAccepts P.rounds (pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r)
      words β (pointOfIndex P.ω P.n P.n (index t)) := by
  obtain ⟨hin, hfinal, hcommit⟩ := P.outcome_verifyWithTensor hrun
  have hpow : ∀ j ≤ P.n, pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ j =
      pointOfIndex P.ω P.n (P.n - j) (index t >>> j) := fun j hj =>
    pointOfIndex_pow_two_pow P.prim le_rfl hj (index t)
  have hro : ∀ j ≤ P.rounds,
      pcsInputTensor P.shift coord (P.claims (msg 0) (committedRow l')) r j
          (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ j) =
        P.reducedTensor W M coord (msg 0) (P.opened pf t) r (index t) j := fun j hj => by
    rw [hpow j (hj.trans P.rounds_le)]
    exact P.pcsInputTensor_eq_reducedTensor hl (fun b => hin b t) hindex hj
  have hround : ∀ i < P.rounds,
      words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
          P.foldedTensor W M coord pf (msg 0) r β (index t) t i ∧
        foldAt (words i) (β i) (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
          foldRow (β i) (pointOfIndex P.ω P.n (P.n - i) (2 * (index t >>> (i + 1))))
            (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).1
            (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).2 := fun i hi => by
    have hin' : i < P.n := lt_of_lt_of_le hi P.rounds_le
    obtain ⟨hval, hfold⟩ := P.round_of_opens hl hin' hindex (hcommit i hi t) (β i)
    rw [hpow i hin'.le, hwords i hi.le, P.read_word_of_lt hi]
    exact ⟨hval.trans (placeRow_self _ _ _), hfold⟩
  have hlast : words P.rounds (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.rounds) =
      P.foldedTensor W M coord pf (msg 0) r β (index t) t P.rounds := by
    rw [hpow _ P.rounds_le, hwords _ le_rfl, P.read_word_last, hfinal t, hornerEval_eq_eval]
    rfl
  have hword : ∀ i ≤ P.rounds, words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
      P.foldedTensor W M coord pf (msg 0) r β (index t) t i := fun i hi => by
    rcases Nat.lt_or_ge i P.rounds with hlt | hge
    · exact (hround i hlt).1
    · obtain rfl : i = P.rounds := le_antisymm hi hge
      exact hlast
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := hword 0 (Nat.zero_le _)
    have hro0 := hro 0 (Nat.zero_le _)
    rw [pow_zero, pow_one] at h0 hro0
    rw [h0, hro0, P.foldedTensor_zero]
  · rw [hword (i + 1) hi, (hround i hi).2, hro (i + 1) hi, P.foldedTensor_succ]

/-- An accepted tensor-batched transcript of raw messages against a collision-free
log is accepted by the oracle-model tensor protocol. -/
theorem acceptsTensor_of_outcome_verifyWithTensor_view {M'' : Type}
    (view : M'' → Msg F D P.batches)
    (t : Transcript M'' (ChalTensor P.ldt W M P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWithTensor (M' := M') (C := C) W M coord pf
      (fun j => view (msgAt t j)) (tensorOf t) (betasOfTensor t)
      fun k => P.indexOf (queriesOfTensor t k)) l true l')
    (hl : ¬ LogCollision hashObs l') :
    AcceptsTensor P.ldt P.shift coord (t.mapIdx fun j m => P.read j (view m) (committedRow l')) := by
  have hwords : ∀ i ≤ P.rounds,
      wordsOf (t.mapIdx fun j m => P.read j (view m) (committedRow l')) i =
        (P.read (i + 1) (view (msgAt t (i + 1))) (committedRow l')).word := fun i hi =>
    PcsRbr.wordsOf_mapIdx _ t (getElem?_msgs t (by omega))
  have hclaims : claimsOf (t.mapIdx fun j m => P.read j (view m) (committedRow l')) =
      P.claims (view (msgAt t 0)) (committedRow l') :=
    PcsRbr.claimsOf_mapIdx _ t (getElem?_msgs t (Nat.zero_le _))
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (view (msgAt t (P.rounds + 1))).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOfTensor t k ∈ twoAdicDomain P.ω P.n 0 := queriesOfTensor_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.tensorOf_mapIdx, PcsRbr.betasOfTensor_mapIdx,
      PcsRbr.queriesOfTensor_mapIdx, ← P.pointOfIndex_indexOf hx]
    exact P.queryAccepts_of_outcome_tensor hrun hl k (P.indexOf_lt _) _ hwords

theorem acceptsTensor_of_outcome_verifyGrindViewTensor {M'' : Type} {bits : ℕ → ℕ}
    [DecidableEq (FSQuery M'' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (HashQuery F D))]
    {view : M'' → Msg F D P.batches}
    {t : Transcript M'' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2)}
    {l l' : Log (MerkleAnswer M'' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)}
    (hrun : Outcome (P.verifyGrindViewTensor W M coord bits view pf t) l true l')
    {digests : ℕ → M'' → List D} {r : ℕ}
    (hno : ¬ HasBad (Hit digests r) l') :
    PowPasses t ∧
      AcceptsTensor P.ldt P.shift coord
        ((ungrind t).mapIdx fun j m => P.read j (view m) (committedRow l')) := by
  unfold verifyGrindViewTensor at hrun
  split at hrun
  · next hpow =>
    exact ⟨hpow, P.acceptsTensor_of_outcome_verifyWithTensor_view view (ungrind t) hrun
      (not_logCollision_of_not_hasBad_hit hno)⟩
  · exact absurd hrun.1 (by simp)

end Params

end TensorAccepts

/-! ## Soundness in the chained random-oracle model -/

section TensorSoundness

variable [Field F] [Fintype F] [DecidableEq F] [Fintype D] [Nonempty D] [DecidableEq D]

namespace Params

variable (P : Params F)

/-- Soundness experiment with proof of work on raw messages for tensor-batched FRI. -/
noncomputable def experimentGrindViewTensor {M' : Type} [DecidableEq M'] (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (bits : ℕ → ℕ)
    (view : M' → Msg F D P.batches) {A : Type*}
    (adv : OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) A)
    (msgs : A → ℕ → M') (proofOf : A → Proof F D P.batches P.queries) :
    OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) (A × Bool) :=
  (fsExperiment (P.rounds + 2) adv msgs).bind fun out =>
    (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2).bind fun b =>
      .pure (out.1, b)

omit [Fintype F] [Fintype D] [Nonempty D] in
theorem run_verifyGrindViewTensor_of_outcome {M' : Type} [DecidableEq M'] {W M : ℕ}
    {coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W} {bits : ℕ → ℕ}
    {view : M' → Msg F D P.batches} {A : Type*}
    {adv : OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) A}
    {msgs : A → ℕ → M'} {pf : Proof F D P.batches P.queries}
    {out : A × Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2)}
    {l₀ l l' : Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)}
    {b : Bool}
    (hexp : Outcome (fsExperiment (P.rounds + 2) adv msgs) l₀ out l)
    (hver : Outcome (P.verifyGrindViewTensor W M coord bits view pf out.2) l b l')
    (f : ∀ x, MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D x) :
    (P.verifyGrindViewTensor W M coord bits view pf
      (fsTranscript (l'.toFun f) (msgs out.1) (P.rounds + 2))).run (l'.toFun f) = b := by
  rw [← eq_fsTranscript_of_outcome_fsExperiment hexp hver.prefix f]
  exact hver.run_toFun f

/-- **Soundness of compiled tensor-batched FRI (chained ROM) for any event implying
oracle-model acceptance.** -/
theorem soundness_grind_view_tensor_of_accepts {M' : Type} [DecidableEq M'] (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (hinj : ∀ j ≤ P.rounds, Function.Injective (coord j))
    (bits : ℕ → ℕ) (view : M' → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ)
    {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) W M θ (εα j))
    (hε₀ : ∀ j ≤ P.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : ε₀ / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*} {B : Type*}
    {adv : OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (msgs : A → ℕ → M')
    {rest : A × Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2) →
      OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) B}
    {R : ℕ} (hrest : ∀ out, (rest out).QueryBound R)
    {E : B → Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) → Prop}
    (hE : ∀ (out : A × Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)) (b : B)
      (l' : Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l → Outcome (rest out) l b l' →
      E b l' → ¬ HasBad (Hit (fun j m => digestsOfAt P.rounds j (view m)) (P.rounds + 2)) l' →
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs out.1 0)) (committedRow l')) ∧
        PowPasses out.2 ∧
        AcceptsTensor P.ldt P.shift coord
          ((ungrind out.2).mapIdx fun j m => P.read j (view m) (committedRow l'))) :
    prob E ((fsExperiment (P.rounds + 2) adv msgs).bind rest) [] ≤
      (Q + (P.rounds + 2) + R) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + R) ^ 2 /
          (4 * Fintype.card D) := by
  have : ∀ i, Nonempty (ChalTensor P.ldt W M P.queries i) :=
    PcsRbr.ChalTensor.nonempty P.domain_zero_nonempty W M P.queries
  have hε : ∀ i < P.rounds + 2,
      roundErrorTensor P.rounds ε₀ εβ θ P.queries i / 2 ^ bits i ≤ εmax := by
    intro i hi
    rcases i with _ | k
    · exact hα
    · by_cases hk : k < P.rounds
      · rw [PcsRbr.roundErrorTensor_succ_of_lt hk]
        exact hβ k hk
      · obtain rfl : k = P.rounds := by omega
        rw [PcsRbr.roundErrorTensor_last]
        exact hq
  have hnd : ∀ t : Transcript (PcsRbr.Msg F P.numClaims)
      (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2),
      PowPasses t → ClaimsFail P.ldt P.shift θ (claimsOf (ungrind t)) →
        AcceptsTensor P.ldt P.shift coord (ungrind t) →
          ¬ PcsRbr.grindDoomed bits (PcsRbr.doomedTensor P.ldt P.shift coord θ P.queries)
              (P.rounds + 2) t :=
    fun t => PcsRbr.not_grindDoomedTensor_of_accepts t
  have h := prob_fsExperiment_bind_committedRow_le (r := P.rounds + 2)
    (PcsRbr.rbrSound_grind_tensor P.ldt P.shift_ne coord hinj hθ P.queries bits hmca hε₀ hstep) hε
    ((div_nonneg (pow_nonneg hθ _) (by positivity)).trans hq)
    (PcsRbr.grindDoomedTensor_nil bits)
    (digestsOf := fun j m => digestsOfAt P.rounds j (view m)) (M := P.batches + P.rounds)
    (fun x => length_chalDigests_le P.rounds view x)
    (read := fun j m c => P.read j (view m) c)
    (fun j m c c' hc => P.read_congr j (view m) c c' hc)
    hadv msgs hrest (E := E)
    (fun out l b l' hexp hrun hb hno => by
      obtain ⟨hfail, hpow, hacc⟩ := hE out l b l' hexp hrun hb hno
      refine hnd _ ((PcsRbr.powPasses_mapIdx _ _).mpr hpow) ?_ ?_
      · have h0 : (ungrind out.2).msgs[0]? = some (msgs out.1 0) := by
          rw [msgs_ungrind, msgs_of_outcome_fsExperiment hexp, List.getElem?_map,
            List.getElem?_range (Nat.succ_pos _)]
          rfl
        rw [PcsRbr.ungrind_mapIdx, PcsRbr.claimsOf_mapIdx _ (ungrind out.2) h0]
        exact hfail
      · rw [PcsRbr.ungrind_mapIdx]
        exact hacc)
  rwa [show ((P.rounds + 2 : ℕ) : ℝ) = (P.rounds : ℝ) + 2 by push_cast; rfl] at h

/-- **Soundness of compiled tensor-batched FRI (chained ROM) for any event implying
compiled verifier acceptance.** -/
theorem soundness_grind_view_tensor_of_imp {M' : Type} [DecidableEq M'] (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W)
    (hinj : ∀ j ≤ P.rounds, Function.Injective (coord j))
    (bits : ℕ → ℕ) (view : M' → Msg F D P.batches) {θ : ℝ} (hθ : 0 ≤ θ)
    {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ P.rounds, Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
      (2 ^ (P.rounds - j) * P.finalDegree) W M θ (εα j))
    (hε₀ : ∀ j ≤ P.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < P.rounds, StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
      (2 ^ (P.rounds - (i + 1)) * P.finalDegree) θ (εβ i))
    (hα : ε₀ / 2 ^ bits 0 ≤ εmax)
    (hβ : ∀ i < P.rounds, εβ i / 2 ^ bits (i + 1) ≤ εmax)
    (hq : θ ^ P.queries / 2 ^ bits (P.rounds + 1) ≤ εmax) {A : Type*}
    {adv : OracleComp (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) A}
    {Q : ℕ} (hadv : adv.QueryBound Q) (msgs : A → ℕ → M')
    (proofOf : A → Proof F D P.batches P.queries)
    (E : A → Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D) → Prop)
    (hE : ∀ (out : A × Transcript M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) (P.rounds + 2))
      (l : Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)) (b : Bool)
      (l' : Log (MerkleAnswer M' (GrindChal bits (ChalTensor P.ldt W M P.queries)) F D)),
      Outcome (fsExperiment (P.rounds + 2) adv msgs) [] out l →
      Outcome (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2) l b l' →
      E out.1 l' → b = true) :
    prob (fun res l => E res.1 l ∧
        ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
      (P.experimentGrindViewTensor W M coord bits view adv msgs proofOf) [] ≤
      (Q + (P.rounds + 2) + P.verifierQueries) * εmax +
        ((max (P.batches + P.rounds) 3 + 3 : ℕ) : ℝ) * (Q + (P.rounds + 2) + P.verifierQueries) ^ 2 /
          (4 * Fintype.card D) := by
  refine P.soundness_grind_view_tensor_of_accepts W M coord hinj bits view hθ hmca hε₀ hstep
    hα hβ hq hadv msgs
    (rest := fun out =>
      (P.verifyGrindViewTensor W M coord bits view (proofOf out.1) out.2).bind fun b =>
        .pure (out.1, b))
    (R := P.verifierQueries)
    (fun out => (P.queryBound_verifyGrindViewTensor W M coord bits view _ _).bind (m := 0) fun _ =>
      queryBound_pure _ _)
    (E := fun res l => E res.1 l ∧
      ClaimsFail P.ldt P.shift θ (P.claims (view (msgs res.1 0)) (committedRow l)))
    fun out l res l' hexp hrun hres hno => ?_
  obtain ⟨b, l₁, hver, hpure⟩ := outcome_bind.mp hrun
  obtain ⟨rfl, rfl⟩ := outcome_pure.mp hpure
  obtain rfl : b = true := hE out l b _ hexp hver hres.1
  exact ⟨hres.2, P.acceptsTensor_of_outcome_verifyGrindViewTensor hver hno⟩

end Params

end TensorSoundness

end CertiFri.Compiled
