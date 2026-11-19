import CertiFriProofs.Exec.Setup
import CertiFriProofs.Exec.Field

/-!
# The arithmetic of one query, on both sides

For one query, the executable verifier (`Fri.checkQuery`) computes the reduced
opening of every level, walks the fold chain, and compares its end with the
final polynomial. This file shows that, under the abstraction maps of the two
fields, these are the values the model verifier computes: `Params.reduced`,
`Params.folded`, `Params.commitRow`, and the two sides of `Params.FinalCheck`.

* `toModel_domainPoint`, `toModel_cosetPoint`: the points the executable
  verifier computes from the two-adic generator are the points `pointOfIndex`
  of the model, times the coset shift for the cosets.
* `point_msg_zero`, `value_msg_zero`, `opened_modelProof`,
  `take_finalCoeffs_msg_last`: the opening points, the claimed values, the
  opened values and the final polynomial of the model are the entries of the
  executable statement and proof.
* `toModel_reducedOpenings`: the reduced openings.
* `toModel_foldChain_fst`, `toModel_foldChain_row`: the fold chain and its
  rows.
* `finalCheck_of_queryResult`, `rows_queryResult`: what `Exec.queryResult`
  yields. A query whose checks pass satisfies the comparison with the final
  polynomial of the model, and the rows it returns are the rows of the model.

## Assumptions

The fields are related by a `FieldModel` and the two-adic structure is
`WellFormed`. The statement and the proof pass `Fri.shapeOk`; of it, only two
facts are used: there is one opening point per `pointRefs` entry, and the final
polynomial has the configured length. The messages and challenges of the model
are those of the executable run (`Agrees`).

## Not covered

The Merkle checks, the transcript, and the two other conjuncts of
`Fri.checkQuery` (no opening point is a query point; the last reduced opening
is zero for a constant final polynomial): the model verifier has no counterpart
of these two, and nothing here depends on them.
-/

namespace CertiFri.Exec

open Fri

/-! ## The claims of a level -/

section Levels

namespace Arith

/-- Up to the last round, the claims `Fri.verifyWith` hands to a query for a
level are the claims of the level. -/
theorem levelsOf_eq (params : FriParams) (shape : ClaimShape) {j : ℕ}
    (hj : j ≤ numRounds params shape) :
    levelsOf params shape j =
      levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j := by
  have h : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  simp [levelsOf, h]

variable {lb : ℕ} {shape : ClaimShape} {n j : ℕ} {c : ClaimRef}

/-- The opening point of a claim of a level is one of the opening points of the
shape. -/
theorem pointIdx_lt_of_mem_levelClaims (h : c ∈ levelClaims lb shape n j) :
    c.pointIdx < (pointRefs lb shape).length := by
  obtain ⟨p, hp, -⟩ := mem_claimRefs (mem_claimRefs_of_mem_levelClaims h)
  exact (List.getElem?_eq_some_iff.mp hp).1

/-- The claimed value of a claim of a level is one of the claimed values of the
shape. -/
theorem valueIdx_lt_of_mem_levelClaims (h : c ∈ levelClaims lb shape n j) :
    c.valueIdx < (claimRefs lb shape).length :=
  (List.getElem?_eq_some_iff.mp
    (getElem?_claimRefs_valueIdx (mem_claimRefs_of_mem_levelClaims h))).1

end Arith

end Levels

/-! ## What the shape checks give -/

section Shape

variable {F EF D : Type} [FieldOps F] [TwoAdicOps F] {InputProof CommitProof : Type}
  {params : FriParams} {shape : ClaimShape} {commitments : Array D} {points values : Array EF}
  {proof : FriProof F EF D InputProof CommitProof}

namespace Arith

/-- A statement that passes the shape checks has one opening point per opening
point of the shape. -/
theorem size_points
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) :
    points.size = (pointRefs params.logBlowup shape).length := by
  simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
  exact hshape.1.1.1.1.1.1.1.1.2

/-- A proof that passes the shape checks has a final polynomial of the
configured length. -/
theorem size_finalPoly
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) :
    proof.finalPoly.size = params.finalPolyLen := by
  simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
  exact hshape.1.1.2

end Arith

end Shape

/-! ## Raw messages, rows and folds under the abstraction maps -/

section Messages

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)

namespace Arith

/-- The extension-field elements of a concatenation. -/
theorem extsIn_append (a b : RawMsg F EF D) : extsIn m (a ++ b) = extsIn m a ++ extsIn m b :=
  List.filterMap_append

/-- The extension-field elements of a list of extension-field elements. -/
theorem extsIn_map_ext (l : List EF) :
    extsIn m (l.map (Observation.ext (F := F) (D := D))) = l.map m.ext.toModel := by
  simp [extsIn, List.filterMap_map]

/-- A list of digests has no extension-field element. -/
theorem extsIn_map_digest (l : List D) :
    extsIn m (l.map (Observation.digest (F := F) (EF := EF))) = [] := by
  simp [extsIn, List.filterMap_map]

/-- A list of copies of a base-field element has no extension-field element. -/
theorem extsIn_replicate_base (n : ℕ) (a : F) :
    extsIn m (List.replicate n (Observation.base (EF := EF) (D := D) a)) = [] := by
  simp [extsIn]

/-- The extension-field elements of the statement: the opening points, then the
claimed values. -/
theorem extsIn_firstMessage (commitments : Array D) (points values : Array EF) :
    extsIn m (firstMessage (F := F) commitments points values) =
      points.toList.map m.ext.toModel ++ values.toList.map m.ext.toModel := by
  rw [firstMessage, extsIn_append, extsIn_append, extsIn_map_digest, extsIn_map_ext,
    extsIn_map_ext, List.nil_append]

/-- The extension-field elements of the last raw message of a run: the
coefficients of the final polynomial. -/
theorem extsIn_messages_last [Inhabited D] {InputProof CommitProof : Type}
    (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D InputProof CommitProof) :
    extsIn m (messages params shape commitments points values proof (numRounds params shape + 1)) =
      proof.finalPoly.toList.map m.ext.toModel := by
  have htail : extsIn m (if params.queryPowBits = 0 then []
      else [Observation.base (EF := EF) (D := D) proof.queryPowWitness]) = [] := by
    split <;> rfl
  rw [messages, ite_eq_right (Nat.succ_ne_zero _), ite_eq_right (Nat.not_succ_le_self _),
    finalMessage, extsIn_append, extsIn_append, extsIn_map_ext, extsIn_replicate_base, htail,
    List.append_nil, List.append_nil]

/-- The opening point of a claim of a level up to the last round, in a raw
message read through `view`: the extension-field element at the position
`pointIdx` of the claim. -/
theorem view_point [Inhabited D] (raw : RawMsg F EF D) {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length) :
    (view m params shape raw).point j k = (extsIn m raw).getD
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k).pointIdx
      0 := by
  have h : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  simp [Compiled.Msg.point, view, List.getD_eq_getElem?_getD, h]

/-- The claimed value of a claim of a level up to the last round, in a raw
message read through `view`: the extension-field element at the position
`valueIdx` of the claim, after the opening points. -/
theorem view_value [Inhabited D] (raw : RawMsg F EF D) {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length) :
    (view m params shape raw).value j k = (extsIn m raw).getD
      ((pointRefs params.logBlowup shape).length +
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).valueIdx) 0 := by
  have h : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  simp [Compiled.Msg.value, view, List.getD_eq_getElem?_getD, h]

/-- An entry of the rows of one batch, read in the model: the image of the
entry of the executable rows, with zero for a missing row or a missing column. -/
theorem entry_map {F : Type} [FieldOps F] (r : Refines F K) (rows : Array (Array F))
    (i col : ℕ) :
    Compiled.entry ((rows.map (·.map r.toModel))[i]?) col =
      r.toModel ((rows.getD i #[]).getD col 0) := by
  rw [Compiled.entry, Array.getElem?_map, Array.getD_eq_getD_getElem? (xs := rows)]
  cases rows[i]? with
  | none => simp [r.map_zero]
  | some row => exact toModel_getD_array_map r row col

/-- The executable fold of a row is the fold of the model: multiplying by the
inverse is dividing. -/
theorem toModel_foldRow (beta : EF) (x : F) (e0 e1 : EF) :
    m.ext.toModel (Fri.foldRow beta x e0 e1) =
      Compiled.foldRow (m.ext.toModel beta) (m.base.toModel x) (m.ext.toModel e0)
        (m.ext.toModel e1) := by
  rw [Fri.foldRow, Compiled.foldRow, m.ext.map_add, m.ext.map_mul, m.ext.map_mul, m.ext.map_inv,
    m.ext.map_sub, m.ext.map_sub, m.embed, m.embed, m.base.map_sub, m.base.map_neg,
    div_eq_mul_inv]

/-- The executable row of a folding round is the row of the model. -/
theorem toModel_placeRow (a b : EF) (index : ℕ) :
    (m.ext.toModel (Fri.placeRow a b index).1, m.ext.toModel (Fri.placeRow a b index).2) =
      Compiled.placeRow (m.ext.toModel a) (m.ext.toModel b) index := by
  unfold Fri.placeRow Compiled.placeRow
  split <;> rfl

end Arith

end Messages

/-! ## The rows of the executable fold chain -/

section Rows

variable {F EF : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  (n : ℕ) (ros : Array EF) (sib : ℕ → EF) (betas : Array EF) (idx : ℕ)

namespace Arith

/-- After `i` rounds the fold chain holds `i` rows. -/
theorem length_foldChain_snd (i : ℕ) :
    (Fri.foldChain (F := F) n ros sib betas idx i).2.length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Fri.foldChain, List.length_append, ih, List.length_singleton]

/-- The row of round `i'` in the fold chain after `i > i'` rounds: the value
after `i'` rounds and the sibling value of round `i'`, placed by the low bit of
the index of that round. -/
theorem getElem?_foldChain_snd {i' i : ℕ} (h : i' < i) :
    (Fri.foldChain (F := F) n ros sib betas idx i).2[i']? =
      some (Fri.placeRow (Fri.foldChain (F := F) n ros sib betas idx i').1 (sib i')
        (idx >>> i')) := by
  induction i with
  | zero => cases h
  | succ i ih =>
    simp only [Fri.foldChain]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hlt | rfl
    · rw [List.getElem?_append_left (by rw [length_foldChain_snd]; exact hlt), ih hlt]
    · rw [List.getElem?_append_right (by rw [length_foldChain_snd]), length_foldChain_snd,
        Nat.sub_self]
      rfl

end Arith

end Rows

section Query

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-! ## Domain points -/

/-- The point of an index in the domain of level `j`, as the executable
verifier computes it, is the point of the index at log-height `n - j` in the
model. -/
theorem toModel_domainPoint {j : ℕ} (hj : j ≤ logMaxHeight params.logBlowup shape) (index : ℕ) :
    m.base.toModel (domainPoint (F := F) (logMaxHeight params.logBlowup shape) j index) =
      pointOfIndex (modelParams m params shape wf).ω (logMaxHeight params.logBlowup shape)
        (logMaxHeight params.logBlowup shape - j) index := by
  rw [domainPoint, toModel_fieldPow, toModel_fieldPow, pointOfIndex, Nat.sub_sub_self hj]
  rfl

/-- The point of an index in the coset of level `j`, as the executable verifier
computes it, is the coset shift of the model times the point of the index at
log-height `n - j`. -/
theorem toModel_cosetPoint {j : ℕ} (hj : j ≤ logMaxHeight params.logBlowup shape) (index : ℕ) :
    m.ext.toModel (cosetPoint (F := F) (logMaxHeight params.logBlowup shape) j index) =
      (modelParams m params shape wf).shift *
        pointOfIndex (modelParams m params shape wf).ω (logMaxHeight params.logBlowup shape)
          (logMaxHeight params.logBlowup shape - j) index := by
  rw [cosetPoint, m.embed, m.base.map_mul, toModel_domainPoint m params shape wf hj]
  rfl

/-! ## The claims of the model -/

namespace Arith

/-- A level of the model has as many claims as the level of the shape. -/
theorem numClaims_modelParams (j : ℕ) :
    (modelParams m params shape wf).numClaims j =
      (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length :=
  rfl

/-- Claim `k` of level `j` of the model is about the batch, the matrix and the
column of the `k`-th claim of the level of the shape. -/
theorem slot_modelParams (j : ℕ) (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (((modelParams m params shape wf).slot j k).batch : ℕ) =
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).batch ∧
      ((modelParams m params shape wf).slot j k).matrix =
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).matrix ∧
      ((modelParams m params shape wf).slot j k).col =
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k).col :=
  ⟨rfl, rfl, rfl⟩

/-- The executable fold chain is the fold chain of the model, for any reduced
openings, sibling values and folding challenges that agree up to round `R`. -/
theorem toModel_foldChain (ros : Array EF) (sib : ℕ → EF) (betas : Array EF) (ro β : ℕ → K)
    (idx : ℕ) {R : ℕ} (hR : R ≤ logMaxHeight params.logBlowup shape)
    (hro : ∀ j ≤ R, m.ext.toModel (ros.getD j 0) = ro j)
    (hβ : ∀ i < R, β i = m.ext.toModel (betas.getD i 0)) {i : ℕ} (hi : i ≤ R) :
    m.ext.toModel (Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape) ros sib betas
        idx i).1 =
      (modelParams m params shape wf).foldChain ro (fun i => m.ext.toModel (sib i)) β idx i := by
  induction i with
  | zero => exact hro 0 (Nat.zero_le _)
  | succ i ih =>
    have ih := ih (Nat.le_of_succ_le hi)
    have hrow := toModel_placeRow m
      (Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape) ros sib betas idx i).1
      (sib i) (idx >>> i)
    rw [ih] at hrow
    simp only [Fri.foldChain, Compiled.Params.foldChain, m.ext.map_add, m.ext.map_mul,
      toModel_foldRow, hro (i + 1) hi,
      toModel_domainPoint m params shape wf (show i ≤ _ by omega),
      ← hβ i (Nat.lt_of_succ_le hi), pow_two]
    rw [← hrow]
    rfl

end Arith

variable {commitments : Array D} {points values : Array EF}
  {proof : FriProof F EF D (Array (List D)) (Array (List D))}

/-! ## The statement and the proof, read by the model -/

/-- The opened value of a claim in the model is the entry the executable
verifier reads from the opened rows of the query. -/
theorem opened_modelProof (t : Fin params.numQueries) (j : ℕ)
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (modelParams m params shape wf).opened (modelProof m params shape proof) t j k =
      m.base.toModel (openedEntry (queryRows proof t.val)
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get k)) :=
  Arith.entry_map m.base _ _ _

variable [Inhabited D] {ch : Challenges EF} {msg : ℕ → Compiled.Msg K D shape.length} {α : K}
  {β : ℕ → K} {index : Fin params.numQueries → ℕ}

/-- The opening point of a claim in the first message of the model is the entry
of `points` the claim refers to. -/
theorem point_msg_zero
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (msg 0).point j k = m.ext.toModel (points.getD
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
        k).pointIdx 0) := by
  have hk : ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
      k).pointIdx < (points.toList.map m.ext.toModel).length := by
    rw [List.length_map, Array.length_toList, Arith.size_points hshape]
    exact Arith.pointIdx_lt_of_mem_levelClaims (List.get_mem _ k)
  rw [hag.msg 0 (Nat.zero_le _), messages, ite_eq_left rfl, Arith.view_point m params shape _ hj k,
    Arith.extsIn_firstMessage, List.getD_append _ _ _ _ hk, toModel_getD_toList_map]

/-- The claimed value of a claim in the first message of the model is the entry
of `values` the claim refers to. -/
theorem value_msg_zero
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    {j : ℕ} (hj : j ≤ numRounds params shape)
    (k : Fin ((modelParams m params shape wf).numClaims j)) :
    (msg 0).value j k = m.ext.toModel (values.getD
      ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
        k).valueIdx 0) := by
  have hlen : (points.toList.map m.ext.toModel).length =
      (pointRefs params.logBlowup shape).length := by
    rw [List.length_map, Array.length_toList, Arith.size_points hshape]
  rw [hag.msg 0 (Nat.zero_le _), messages, ite_eq_left rfl, Arith.view_value m params shape _ hj k,
    Arith.extsIn_firstMessage, ← hlen, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, toModel_getD_toList_map]

/-- The coefficients in the last message of the model are the coefficients of
the final polynomial of the proof. -/
theorem finalCoeffs_msg_last
    (hag : Agrees m params shape commitments points values proof ch msg α β index) :
    (msg ((modelParams m params shape wf).rounds + 1)).finalCoeffs =
      proof.finalPoly.toList.map m.ext.toModel := by
  rw [show (modelParams m params shape wf).rounds = numRounds params shape from rfl,
    hag.msg _ le_rfl]
  exact Arith.extsIn_messages_last m params shape commitments points values proof

/-- The final polynomial the model evaluates, the first `finalDegree`
coefficients of its last message, is the whole final polynomial of the proof. -/
theorem take_finalCoeffs_msg_last
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index) :
    (msg ((modelParams m params shape wf).rounds + 1)).finalCoeffs.take
        (modelParams m params shape wf).finalDegree =
      proof.finalPoly.toList.map m.ext.toModel := by
  rw [finalCoeffs_msg_last m params shape wf hag]
  refine List.take_of_length_le ?_
  rw [List.length_map, Array.length_toList, Arith.size_finalPoly hshape]
  exact le_rfl

/-! ## Reduced openings -/

/-- **The reduced openings.** The reduced opening of a level up to the last
round, as the executable verifier computes it for the query `t` at the index
`idx`, is the reduced opening of the model. -/
theorem toModel_reducedOpenings
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    {j : ℕ} (hj : j ≤ numRounds params shape) (t : Fin params.numQueries) (idx : ℕ) :
    m.ext.toModel ((reducedOpenings (F := F) (logMaxHeight params.logBlowup shape)
        (numRounds params shape) (levelsOf params shape) ch.alpha points values
        (queryRows proof t.val) idx).getD j 0) =
      (modelParams m params shape wf).reduced (msg 0)
        ((modelParams m params shape wf).opened (modelProof m params shape proof) t) α idx j := by
  have hlt : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  have hjn : j ≤ logMaxHeight params.logBlowup shape := hj.trans (Nat.sub_le _ _)
  have hget : (reducedOpenings (F := F) (logMaxHeight params.logBlowup shape)
      (numRounds params shape) (levelsOf params shape) ch.alpha points values
      (queryRows proof t.val) idx).getD j 0 =
      Fri.reducedOpening ch.alpha
        (cosetPoint (F := F) (logMaxHeight params.logBlowup shape) j (idx >>> j)) points values
        (queryRows proof t.val)
        (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j) := by
    simp [reducedOpenings, hlt, Arith.levelsOf_eq params shape hj]
  rw [hget, Fri.reducedOpening, toModel_foldl_powers, m.ext.map_zero, m.ext.map_one, zero_add,
    one_mul]
  unfold Compiled.Params.reduced
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [m.ext.map_mul, m.ext.map_sub, m.ext.map_inv, m.ext.map_sub, m.embed, ← div_eq_mul_inv,
    toModel_cosetPoint m params shape wf hjn, ← hag.alpha,
    ← point_msg_zero m params shape wf hshape hag hj k,
    ← value_msg_zero m params shape wf hshape hag hj k,
    ← opened_modelProof m params shape wf t j k]
  rfl

/-! ## The fold chain -/

/-- **The fold chain.** The value of the executable fold chain of the query `t`
at the index `idx` after `i` rounds is the value of the fold chain of the
model. -/
theorem toModel_foldChain_fst
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (t : Fin params.numQueries) (idx : ℕ) {i : ℕ} (hi : i ≤ numRounds params shape) :
    m.ext.toModel (Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpenings (F := F) (logMaxHeight params.logBlowup shape) (numRounds params shape)
          (levelsOf params shape) ch.alpha points values (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).1 =
      (modelParams m params shape wf).folded (modelProof m params shape proof) (msg 0) α β idx t
        i :=
  Arith.toModel_foldChain m params shape wf _ _ _ _ β idx (Nat.sub_le _ _)
    (fun _ hj => toModel_reducedOpenings m params shape wf hshape hag hj t idx) hag.beta hi

/-- **The rows of the fold chain.** The row of round `i'` that the executable
fold chain of the query `t` at the index `idx` holds after `i > i'` rounds is
the row of the model. -/
theorem toModel_foldChain_row
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (t : Fin params.numQueries) (idx : ℕ) {i' i : ℕ} (hi' : i' < i)
    (hi : i ≤ numRounds params shape) :
    (m.ext.toModel (((Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpenings (F := F) (logMaxHeight params.logBlowup shape) (numRounds params shape)
          (levelsOf params shape) ch.alpha points values (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).2.getD i' (0, 0)).1),
      m.ext.toModel (((Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpenings (F := F) (logMaxHeight params.logBlowup shape) (numRounds params shape)
          (levelsOf params shape) ch.alpha points values (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).2.getD i' (0, 0)).2)) =
      (modelParams m params shape wf).commitRow (modelProof m params shape proof) (msg 0) α β idx t
        i' := by
  rw [List.getD_eq_getElem?_getD, Arith.getElem?_foldChain_snd _ _ _ _ _ hi', Option.getD_some,
    Arith.toModel_placeRow,
    toModel_foldChain_fst m params shape wf hshape hag t idx (hi'.le.trans hi)]
  rfl

/-! ## The results of one query -/

/-- **The comparison with the final polynomial.** If the checks of the query
`t` pass in the executable verifier, the fold chain of the model for that query
ends at the value of the final polynomial of the model: the query satisfies
`Compiled.Params.FinalCheck`. -/
theorem finalCheck_of_queryResult
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (t : Fin params.numQueries)
    (hok : (queryResult (F := F) params shape points values proof ch t.val).ok = true) :
    (modelParams m params shape wf).folded (modelProof m params shape proof) (msg 0) α β (index t) t
        (modelParams m params shape wf).rounds =
      Compiled.hornerEval
        ((msg ((modelParams m params shape wf).rounds + 1)).finalCoeffs.take
          (modelParams m params shape wf).finalDegree)
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - (modelParams m params shape wf).rounds)
          (index t >>> (modelParams m params shape wf).rounds)) := by
  simp only [queryResult, checkQuery, Bool.and_eq_true] at hok
  have hfinal := hok.2
  rw [m.ext.beq_iff, toModel_foldChain_fst m params shape wf hshape hag t _ le_rfl,
    m.ext.horner_eq_eval, m.embed,
    toModel_domainPoint m params shape wf (j := numRounds params shape) (Nat.sub_le _ _),
    ← Compiled.hornerEval_eq_eval, ← take_finalCoeffs_msg_last m params shape wf hshape hag,
    ← hag.index t] at hfinal
  exact hfinal

/-- If the checks of every query pass in the executable verifier, the model's
comparison with the final polynomial holds. -/
theorem finalCheck_of_forall_queryResult
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (hok : ∀ t : Fin params.numQueries,
      (queryResult (F := F) params shape points values proof ch t.val).ok = true) :
    (modelParams m params shape wf).FinalCheck (modelProof m params shape proof) msg α β index :=
  fun t => finalCheck_of_queryResult m params shape wf hshape hag t (hok t)

/-- **The rows of a query.** The row of folding round `i` that the executable
verifier reconstructs for the query `t` is the row of the model. -/
theorem rows_queryResult
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : Agrees m params shape commitments points values proof ch msg α β index)
    (t : Fin params.numQueries) {i : ℕ} (hi : i < numRounds params shape) :
    (m.ext.toModel (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
        (0, 0)).1),
      m.ext.toModel (((queryResult (F := F) params shape points values proof ch t.val).rows.getD i
        (0, 0)).2)) =
    (modelParams m params shape wf).commitRow (modelProof m params shape proof) (msg 0) α β
      (index t) t i := by
  rw [hag.index t]
  exact toModel_foldChain_row m params shape wf hshape hag t _ hi le_rfl

end Query

end CertiFri.Exec
