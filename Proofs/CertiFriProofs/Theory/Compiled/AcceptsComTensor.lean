import CertiFriProofs.Theory.Compiled.Tensor

/-!
# Tensor-batched oracle acceptance for claims read from base-field committed rows

Tensor-batched counterpart of `Theory/Compiled/AcceptsCom.lean`. Proves that a
tensor-batched transcript accepted by `Params.verifyWithTensor` against a
collision-free log is accepted in the oracle model (`PcsRbr.AcceptsTensor`)
when the round-`0` claims are read from any committed-row map `c` agreeing with
`committedRow l'` at the rows opened by the queries (in particular
`M.baseRows (comOf ...)`).
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (TensorChal ChalTensor tensorOf betasOfTensor queriesOfTensor claimsOf wordsOf
  AcceptsTensor pcsInputTensor reducedOpeningTensor)

variable {F D : Type} [Field F]

/-- `QueryAccepts` reads the level-`j` reduced opening only at `x ^ (2 ^ j)`. -/
private theorem queryAccepts_of_input_eq_tensor {r : ℕ} {ro ro' words : ℕ → F → F} {β : ℕ → F}
    {x : F} (h : ∀ j ≤ r, ro' j (x ^ 2 ^ j) = ro j (x ^ 2 ^ j))
    (hq : QueryAccepts r ro words β x) :
    QueryAccepts r ro' words β x := by
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := h 0 (Nat.zero_le _)
    rw [pow_zero, pow_one] at h0
    rw [h0]
    exact hq.1
  · rw [h (i + 1) hi]
    exact hq.2 i hi

variable [DecidableEq F] [DecidableEq D]

namespace Params

variable (P : Params F)

omit [DecidableEq D] in
/-- The tensor-batched input of level `j ≤ rounds` at the query point of `idx`
reads only the opened rows at `idx >>> (P.n - d.logHeight)`. -/
private theorem pcsInputTensor_congr_of_rows {W M : ℕ}
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (msg : Msg F D P.batches)
    (r : TensorChal F W M) {c c' : Committed F D} {idx : ℕ} (hidx : idx < 2 ^ P.n)
    (hc : ∀ (b : Fin P.batches) (mi : ℕ) (d : Dimensions), (P.dims b)[mi]? = some d →
      c (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)) =
        c' (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)))
    {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInputTensor P.shift coord (P.claims msg c) r j
        (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) =
      pcsInputTensor P.shift coord (P.claims msg c') r j
        (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) := by
  have hjn : j ≤ P.n := hj.trans P.rounds_le
  unfold pcsInputTensor reducedOpeningTensor quotientAt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn),
    P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn)]
  obtain ⟨d, hd, hdh, -⟩ := P.slot_dims j hj k
  have hrow := hc (P.slot j k).batch (P.slot j k).matrix d hd
  rw [show P.n - d.logHeight = j by omega] at hrow
  rw [hrow]
  rfl

variable {M' M'' : Type} {C : ℕ → Type} [DecidableEq (FSQuery M' C (HashQuery F D))]
  {W M : ℕ} {coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W}
  {pf : Proof F D P.batches P.queries} {l l' : Log (MerkleAnswer M' C F D)}

/-- **An accepted tensor-batched transcript is accepted in the oracle model,
for claims read from committed rows `c` agreeing with `committedRow l'` where
the queries open.** -/
theorem acceptsTensor_of_outcome_verifyWithTensor_view_com (view : M'' → Msg F D P.batches)
    (t : Transcript M'' (ChalTensor P.ldt W M P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWithTensor (M' := M') (C := C) W M coord pf
      (fun j => view (msgAt t j)) (tensorOf t) (betasOfTensor t)
      fun k => P.indexOf (queriesOfTensor t k)) l true l')
    (hl : ¬ LogCollision hashObs l') (c : Committed F D)
    (hc : ∀ (b : Fin P.batches) (k : Fin P.queries) (mi : ℕ) (d : Dimensions),
      (P.dims b)[mi]? = some d →
      c ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOfTensor t k) >>> (P.n - d.logHeight)) =
        committedRow l' ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOfTensor t k) >>> (P.n - d.logHeight))) :
    AcceptsTensor P.ldt P.shift coord
      (t.mapIdx fun j m =>
        if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) := by
  have hwords : ∀ i ≤ P.rounds,
      wordsOf (t.mapIdx fun j m =>
          if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) i =
        (P.read (i + 1) (view (msgAt t (i + 1))) (committedRow l')).word := fun i hi => by
    rw [PcsRbr.wordsOf_mapIdx _ t (getElem?_msgs t (by omega)), ite_eq_right (Nat.succ_ne_zero i)]
  have hclaims : claimsOf (t.mapIdx fun j m =>
        if j = 0 then P.read 0 (view m) c else P.read j (view m) (committedRow l')) =
      P.claims (view (msgAt t 0)) c := by
    rw [PcsRbr.claimsOf_mapIdx _ t (getElem?_msgs t (Nat.zero_le _)), ite_eq_left rfl,
      P.read_claims_zero]
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (view (msgAt t (P.rounds + 1))).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOfTensor t k ∈ twoAdicDomain P.ω P.n 0 :=
      queriesOfTensor_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.tensorOf_mapIdx, PcsRbr.betasOfTensor_mapIdx,
      PcsRbr.queriesOfTensor_mapIdx, ← P.pointOfIndex_indexOf hx]
    refine queryAccepts_of_input_eq_tensor (fun j hj => ?_)
      (P.queryAccepts_of_outcome_tensor hrun hl k (P.indexOf_lt _) _ hwords)
    rw [pointOfIndex_pow_two_pow P.prim le_rfl (hj.trans P.rounds_le)]
    exact P.pcsInputTensor_congr_of_rows coord _ _ (P.indexOf_lt _)
      (fun b mi d hd => hc b k mi d hd) hj

end Params

end CertiFri.Compiled
