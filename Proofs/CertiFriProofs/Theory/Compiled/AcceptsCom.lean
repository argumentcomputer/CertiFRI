import CertiFriProofs.Theory.Compiled.Accepts

/-!
# Acceptance for claims read from other committed rows

`Compiled/Accepts.lean` shows that a transcript the model verifier accepts is
accepted in the oracle model, when every message is read from the rows the
final log commits to. The verifier, however, only learns about the rows it
opens. This file proves the same statement when the claims are read from any
family of rows that agrees with the committed rows of the log at the rows the
queries open.

The use: a reading that drops the committed rows which the verifier could not
have opened (rows with an entry outside the base field), so that the functions
the claims are about are base-field valued everywhere.

* `Params.accepts_of_outcome_verifyWith_view_com`: the statement, for a
  transcript of raw messages read through a function `view`. The claims of
  round `0` are read from `c`; the words of the later rounds from the committed
  rows of the log.

## How the proof goes

`QueryAccepts` reads the input of level `j` only at the query point of level
`j`, and that value is computed from the row of the query index shifted by `j`
of the claimed matrices. So the inputs for the claims read from `c` and from the
log agree where the queries read them, and the statement follows from
`Params.queryAccepts_of_outcome`.

## Assumptions

No collision of the hash oracle in the final log, as in `Compiled/Accepts.lean`.
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (Chal alphaOf betasOf queriesOf claimsOf wordsOf Accepts)

variable {F D : Type} [Field F]

/-- **`QueryAccepts` reads the inputs at the query points only.** Two families
of inputs that agree at the point `x ^ 2 ^ j` of every level `j ≤ r` pass the
check of the query at `x` together. -/
private theorem queryAccepts_of_input_eq {r : ℕ} {ro ro' words : ℕ → F → F} {β : ℕ → F} {x : F}
    (h : ∀ j ≤ r, ro' j (x ^ 2 ^ j) = ro j (x ^ 2 ^ j)) (hq : QueryAccepts r ro words β x) :
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
/-- **The inputs at a query point read the rows the query opens.** Let two
families of committed rows agree at the row of the index `idx`, shifted to the
height of the matrix, of every matrix of every input batch. Then the inputs of
level `j ≤ rounds` of the low-degree test, for the claims read from the one and
from the other, agree at the point of `idx` shifted by `j`. -/
private theorem pcsInput_congr_of_rows (msg : Msg F D P.batches) (α : F) {c c' : Committed F D}
    {idx : ℕ} (hidx : idx < 2 ^ P.n)
    (hc : ∀ (b : Fin P.batches) (mi : ℕ) (d : Dimensions), (P.dims b)[mi]? = some d →
      c (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)) =
        c' (msg.inputRoots b) (P.dims b) mi (idx >>> (P.n - d.logHeight)))
    {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInput P.shift (P.claims msg c) α j (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) =
      pcsInput P.shift (P.claims msg c') α j (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) := by
  have hjn : j ≤ P.n := hj.trans P.rounds_le
  unfold pcsInput reducedOpening quotientAt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn),
    P.claims_f_apply _ _ k (shiftRight_lt_two_pow hidx hjn)]
  obtain ⟨d, hd, hdh, -⟩ := P.slot_dims j hj k
  have hrow := hc (P.slot j k).batch (P.slot j k).matrix d hd
  rw [show P.n - d.logHeight = j by omega] at hrow
  rw [hrow]
  rfl

variable {M M' : Type} {C : ℕ → Type} [DecidableEq (FSQuery M C (HashQuery F D))]
  {pf : Proof F D P.batches P.queries} {l l' : Log (MerkleAnswer M C F D)}

/-- **An accepted transcript is accepted in the oracle model, for claims read
from rows that agree with the log where the queries open.** Let the verifier,
run on the messages read through `view`, the challenges and the indices of the
query points of a transcript, accept and leave a log without a collision. Let
`c` be a family of committed rows that agrees with the committed rows of the
final log at every row of every matrix of every input batch that a query
opens. Then the transcript, with the claims of round `0` read from `c` and
every later message read from the rows the final log commits to, is accepted by
the oracle-model protocol. -/
theorem accepts_of_outcome_verifyWith_view_com (view : M' → Msg F D P.batches)
    (t : Transcript M' (Chal P.ldt P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWith (M := M) (C := C) pf (fun j => view (msgAt t j)) (alphaOf t)
      (betasOf t) fun k => P.indexOf (queriesOf t k)) l true l')
    (hl : ¬ LogCollision hashObs l') (c : Committed F D)
    (hc : ∀ (b : Fin P.batches) (k : Fin P.queries) (mi : ℕ) (d : Dimensions),
      (P.dims b)[mi]? = some d →
      c ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOf t k) >>> (P.n - d.logHeight)) =
        committedRow l' ((view (msgAt t 0)).inputRoots b) (P.dims b) mi
          (P.indexOf (queriesOf t k) >>> (P.n - d.logHeight))) :
    Accepts P.ldt P.shift
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
      P.read_claims]
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (view (msgAt t (P.rounds + 1))).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOf t k ∈ twoAdicDomain P.ω P.n 0 := queriesOf_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.alphaOf_mapIdx, PcsRbr.betasOf_mapIdx, PcsRbr.queriesOf_mapIdx,
      ← P.pointOfIndex_indexOf hx]
    refine queryAccepts_of_input_eq (fun j hj => ?_)
      (P.queryAccepts_of_outcome hrun hl k (P.indexOf_lt _) _ hwords)
    rw [pointOfIndex_pow_two_pow P.prim le_rfl (hj.trans P.rounds_le)]
    exact P.pcsInput_congr_of_rows _ _ (P.indexOf_lt _) (fun b mi d hd => hc b k mi d hd) hj

end Params

end CertiFri.Compiled
