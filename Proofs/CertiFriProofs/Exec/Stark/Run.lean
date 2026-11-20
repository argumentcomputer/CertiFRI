import CertiFriProofs.Exec.Stark.Free
import CertiFriProofs.Exec.Stark.Model
import CertiFriProofs.Exec.Soundness

/-!
# A run of the STARK verifier with the idealised challenger

The executable verifier derives its challenges from a challenger. With the
idealised challenger over an oracle `f` (`uChallenger`, `Exec/Stark/Free.lean`),
they are the answers of `f` along the Fiat–Shamir chain on the raw messages of
the run. This file proves that for the two parts of a run that every entry
point of the verifier shares.

## The raw messages of a chain

Round `0` holds the first message; round `1` the first lookup challenge,
absorbed back; round `2` the second lookup challenge followed by what the entry
point absorbs next (the position of the shard, in a batch) and by the
commitment to the lookup traces and the lookup sums; round `3` the commitment
to the quotients; round `4` the opened values; round `5 + i` the commitment of
folding round `i` of the opening proof, with its proof-of-work witness; the
last round the final polynomial, with its witness.

## Results

* `lookupChallenges_ufree`: the two lookup challenges are representations of
  the field elements of the answers of rounds `0` and `1`, and the state after
  them is in round `2` with the second challenge absorbed.
* `checkAfterChallenges_ufree`: if the checks that follow the lookup
  challenges pass, then the constraint challenge and the out-of-domain point
  represent the field elements of the answers of rounds `2` and `3`; the
  constraint checks pass for them; and the checks of the opening proof
  (`Fri.verifyWith`) pass for challenges that are read off the answers of the
  rounds from `4` on.
* `modelChecks_of_verifyWith`: checks of the opening proof that pass, with the
  Merkle schemes over the hash functions of `f`, make the model verifier of
  the opening protocol accept against `f`.

## Assumptions

`checkAfterChallenges_ufree` takes the shape check of the proof as a
hypothesis: it is what makes the list of opened values nonempty, so that
absorbing it starts round `4`. The proof has an active circuit, whose quotient
is opened in a row of `quotientDegree * d` values, and the degree `d` of the
extension is positive in a `StarkModel`.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle
open CertiFri.Exec.Transcript (answer)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [Inhabited D] {slots width : ℕ}

/-! ## The opened values of a proof -/

section Values

omit [FieldOps EF] [Inhabited D] in
/-- A value claimed at a point of a matrix of a commitment is one of the claimed
values of nested claims. -/
private theorem mem_claimValues {claims : Array (CommitmentOpening EF D)}
    {c : CommitmentOpening EF D} {m : MatrixOpening EF} {po : PointOpening EF} {x : EF}
    (hc : c ∈ claims.toList) (hm : m ∈ c.matrices.toList) (hpo : po ∈ m.points.toList)
    (hx : x ∈ po.values.toList) : x ∈ (claimValues claims).toList := by
  simp only [claimValues, List.mem_flatMap]
  exact ⟨c, hc, m, hm, po, hpo, hx⟩

omit [FieldOps EF] in
/-- The claims about a matrix opened at one point, whose one row passes `rowsOk`
for a positive width, hold a value. -/
private theorem exists_value_matrixOpening (k : ℕ) (ζ : EF) {rows : Array (Array EF)} {w : ℕ}
    (hw : 0 < w) (h : rowsOk rows 1 w = true) :
    ∃ po ∈ (matrixOpening k [ζ] rows).points.toList, ∃ x, x ∈ po.values.toList := by
  obtain ⟨rs⟩ := rows
  simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨hsize, hall⟩ := h
  cases rs with
  | nil => cases hsize
  | cons r rs =>
    have hr : r.size = w := hall r (Array.mem_toList_iff.mp List.mem_cons_self)
    exact ⟨⟨ζ, r⟩, List.mem_cons_self, r[0]'(by omega), Array.getElem_mem_toList _⟩

omit [Inhabited D] in
/-- **The opened values of a proof of the right shape are not empty.** The
proof has an active circuit, and the row opened for its quotient has
`quotientDegree * d` values, a positive number. -/
private theorem claimValues_openingClaims_ne_nil {InputProof CommitProof : Type}
    (sys : System F D) (proof : Proof F EF D InputProof CommitProof)
    (hshape : Stark.shapeOk sys proof = true) (hd : 0 < ExtensionOps.degree (F := F) (EF := EF))
    (ζ : EF) : (claimValues (openingClaims sys proof ζ)).toList ≠ [] := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true] at hshape
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hne⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := hshape
  cases hact : activeIndices proof.active with
  | nil =>
    rw [hact] at hne
    cases hne
  | cons ci rest =>
    have hp : (ci, 0) ∈ (activeIndices proof.active).zipIdx := by
      rw [hact, List.zipIdx_cons]
      exact List.mem_cons_self
    obtain ⟨-, hq⟩ := hall (ci, 0) hp
    obtain ⟨po, hpo, x, hx⟩ := exists_value_matrixOpening (proof.logDegrees.getD 0 0) ζ
      (Nat.mul_pos (Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)) hd) hq
    refine List.ne_nil_of_mem (mem_claimValues
      (c := ⟨proof.quotientCommit, ((activeIndices proof.active).zipIdx.map fun p : ℕ × ℕ =>
        matrixOpening (proof.logDegrees.getD p.2 0) [ζ]
          (proof.quotientOpened.getD p.2 #[])).toArray⟩) ?_ ?_ hpo hx)
    · simp only [openingClaims, Array.toList_append]
      exact List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_map.mpr ⟨(ci, 0), hp, rfl⟩

end Values

/-! ## The challenges of a run -/

section Challenges

variable (M : StarkModel F EF K)
  (f : ∀ x : FSQuery (RawMsg F EF D) (UChal K slots width) (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (UChal K slots width) K D x)

omit [DecidableEq K] [Inhabited D] in
/-- **The lookup challenges of a run.** From the initial state, after the first
message `m0`: if round `0` of the chain holds `m0` and round `1` holds the
first challenge, the two challenges represent the field elements of the answers
of rounds `0` and `1`, and the state is in round `2`, holding the second
challenge. -/
theorem lookupChallenges_ufree (m0 : RawMsg F EF D) {ms : ℕ → RawMsg F EF D} (h0 : ms 0 = m0)
    (h1 : ms 1 = [.ext (lookupChallenges (uChallenger f M.toFieldModel)
      ((uChallenger f M.toFieldModel).observeAll UState.init m0)).1]) :
    (lookupChallenges (uChallenger f M.toFieldModel)
        ((uChallenger f M.toFieldModel).observeAll UState.init m0)).1 =
        Function.surjInv M.surj (answer f ms 0).field ∧
      (lookupChallenges (uChallenger f M.toFieldModel)
        ((uChallenger f M.toFieldModel).observeAll UState.init m0)).2.1 =
        Function.surjInv M.surj (answer f ms 1).field ∧
      UAt ms (lookupChallenges (uChallenger f M.toFieldModel)
          ((uChallenger f M.toFieldModel).observeAll UState.init m0)).2.2 2
        [.ext (lookupChallenges (uChallenger f M.toFieldModel)
          ((uChallenger f M.toFieldModel).observeAll UState.init m0)).2.1] false 0 := by
  have a0 : UAt ms ((uChallenger f M.toFieldModel).observeAll UState.init m0) 0 (ms 0)
      false 0 := by
    rw [h0]
    exact (UAt.init (ms := ms)).observeAll f M.toFieldModel m0
  obtain ⟨hβ, a0'⟩ := a0.sampleExt f M.toFieldModel
  have a1 : UAt ms ((uChallenger f M.toFieldModel).observe
      ((uChallenger f M.toFieldModel).sampleExt
        ((uChallenger f M.toFieldModel).observeAll UState.init m0)).2
      (.ext (lookupChallenges (uChallenger f M.toFieldModel)
        ((uChallenger f M.toFieldModel).observeAll UState.init m0)).1)) 1 (ms 1) false 0 := by
    rw [h1]
    exact a0'.observe_next f M.toFieldModel _
  obtain ⟨hγ, a1'⟩ := a1.sampleExt f M.toFieldModel
  exact ⟨hβ, hγ, a1'.observe_next f M.toFieldModel _⟩

omit [DecidableEq K] in
/-- **The checks after the lookup challenges, in a run.** Let the state be in
round `2` of the chain, holding `cur`, and let the rounds from `2` on hold what
the verifier absorbs: the commitment to the lookup traces and the lookup sums
after `cur`, the commitment to the quotients, the opened values, and the
messages of the opening proof. Write `α` and `ζ` for the representations of the
field elements of the answers of rounds `2` and `3`. If the proof has the shape
the system fixes and the checks pass, then `ζ` is usable, the constraint checks
pass for `α` and `ζ`, and the checks of the opening proof pass for challenges
read off the answers of the rounds from `4` on. -/
theorem checkAfterChallenges_ufree (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (sys : System F D) (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof)
    (hshape : Stark.shapeOk sys proof = true) {ms : ℕ → RawMsg F EF D} {s : UState F EF D}
    {cur : RawMsg F EF D} (β γ acc : EF) (hs : UAt ms s 2 cur false 0)
    (h2 : ms 2 = cur ++ secondMessage proof) (h3 : ms 3 = [.digest proof.quotientCommit])
    (h4 : ms 4 = (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map .ext)
    (hC : ∀ i < numRounds sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field))),
      ms (5 + i) = .digest (proof.openingProof.commitPhaseCommits.getD i default) ::
        (if sys.fri.commitPowBits = 0 then []
          else [.base (proof.openingProof.commitPowWitnesses.getD i 0)]))
    (hF : ms (5 + numRounds sys.fri (claimShape (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field)))) =
      finalMessage (numRounds sys.fri (claimShape (openingClaims sys proof
          (Function.surjInv M.surj (answer f ms 3).field)))) proof.openingProof.finalPoly ++
        (if sys.fri.queryPowBits = 0 then [] else [.base proof.openingProof.queryPowWitness]))
    (h : checkAfterChallenges inputMmcs friMmcs (uChallenger f M.toFieldModel) sys proof s β γ
      acc = true) :
    zetaOk proof (Function.surjInv M.surj (answer f ms 3).field) = true ∧
      constraintsOk sys proof β γ acc (Function.surjInv M.surj (answer f ms 2).field)
        (Function.surjInv M.surj (answer f ms 3).field) = true ∧
      widthsUniform (openingClaims sys proof
        (Function.surjInv M.surj (answer f ms 3).field)) = true ∧
      Fri.shapeOk sys.fri
        (claimShape (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
        ((openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)).map
          (·.commitment))
        (claimPoints (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
        (claimValues (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
        proof.openingProof = true ∧
      ∃ ch : Challenges EF,
        verifyWith inputMmcs friMmcs sys.fri
          (claimShape (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
          ((openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)).map
            (·.commitment))
          (claimPoints (openingClaims sys proof
            (Function.surjInv M.surj (answer f ms 3).field)))
          (claimValues (openingClaims sys proof
            (Function.surjInv M.surj (answer f ms 3).field)))
          proof.openingProof ch = true ∧
        ch.alpha = Function.surjInv M.surj (answer f ms 4).field ∧
        ch.betas = ((List.range (numRounds sys.fri (claimShape (openingClaims sys proof
            (Function.surjInv M.surj (answer f ms 3).field))))).map fun i =>
          Function.surjInv M.surj (answer f ms (5 + i)).field).toArray ∧
        (ch.powOk = true →
          (sys.fri.commitPowBits ≠ 0 → ∀ i < numRounds sys.fri (claimShape (openingClaims sys
              proof (Function.surjInv M.surj (answer f ms 3).field))),
            (answer f ms (5 + i)).bits 0 sys.fri.commitPowBits = 0) ∧
          (sys.fri.queryPowBits ≠ 0 →
            (answer f ms (5 + numRounds sys.fri (claimShape (openingClaims sys proof
              (Function.surjInv M.surj (answer f ms 3).field))))).bits 0
                sys.fri.queryPowBits = 0)) ∧
        ch.indices = ((List.range sys.fri.numQueries).map fun t =>
          (answer f ms (5 + numRounds sys.fri (claimShape (openingClaims sys proof
            (Function.surjInv M.surj (answer f ms 3).field))))).bits
            (t + if sys.fri.queryPowBits = 0 then 0 else 1)
            (logMaxHeight sys.fri.logBlowup (claimShape (openingClaims sys proof
              (Function.surjInv M.surj (answer f ms 3).field))))).toArray := by
  -- Round 2: the commitment to the lookup traces and the lookup sums, then `α`.
  have a2 : UAt ms ((uChallenger f M.toFieldModel).observeAll s (secondMessage proof)) 2 (ms 2)
      false 0 := by
    rw [h2]
    exact hs.observeAll f M.toFieldModel _
  obtain ⟨hα, a2'⟩ := a2.sampleExt f M.toFieldModel
  -- Round 3: the commitment to the quotients, then `ζ`.
  have a3 : UAt ms ((uChallenger f M.toFieldModel).observe
      ((uChallenger f M.toFieldModel).sampleExt
        ((uChallenger f M.toFieldModel).observeAll s (secondMessage proof))).2
      (.digest proof.quotientCommit)) 3 (ms 3) false 0 := by
    rw [h3]
    exact a2'.observe_next f M.toFieldModel _
  obtain ⟨hζ, a3'⟩ := a3.sampleExt f M.toFieldModel
  -- The checks, with the two challenges rewritten.
  simp only [checkAfterChallenges, mainChallenges, Bool.and_eq_true] at h
  rw [hα, hζ] at h
  obtain ⟨⟨hz, hv⟩, hc⟩ := h
  rw [verifyClaimsFrom, Bool.and_eq_true] at hv
  obtain ⟨hu, hvf⟩ := hv
  rw [verifyFrom, Bool.and_eq_true] at hvf
  obtain ⟨hsh, hw⟩ := hvf
  -- Round 4: the opened values, which are not empty.
  have hne : (claimValues (openingClaims sys proof
      (Function.surjInv M.surj (answer f ms 3).field))).toList.map
        (Observation.ext (F := F) (D := D)) ≠ [] := fun h0 =>
    claimValues_openingClaims_ne_nil sys proof hshape (M.degree_eq ▸ M.extData.d_pos) _
      (List.map_eq_nil_iff.mp h0)
  have a4 := a3'.observeAll_next f M.toFieldModel hne
  have a4' : UAt ms _ 4 (ms 4) false 0 :=
    ⟨a4.round, a4.hist, a4.cur.trans h4.symm, a4.squeezed, a4.nbits⟩
  -- The rounds of the opening proof.
  have hfinal : proof.openingProof.finalPoly.size ≠ 0 := by
    have hsh' := hsh
    simp only [Fri.shapeOk, Bool.and_eq_true, beq_iff_eq] at hsh'
    rw [hsh'.1.1.2]
    exact (Nat.two_pow_pos _).ne'
  obtain ⟨tα, tβ, tpow, tidx⟩ := transcriptTail_ufree f M.toFieldModel sys.fri
    (claimShape (openingClaims sys proof (Function.surjInv M.surj (answer f ms 3).field)))
    proof.openingProof 4 a4' hC hF hfinal
  exact ⟨hz, hc, hu, hsh, _, hw, tα, tβ, tpow, tidx⟩

end Challenges

/-! ## The opening proof -/

section Pcs

variable [DecidableEq D] (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape) {Msg : Type} {Chal : ℕ → Type}
  (f : ∀ x : FSQuery Msg Chal (HashQuery K D), MerkleAnswer Msg Chal K D x)

/-- **Accepted checks of the opening proof make the model verifier accept.** If
the checks of the opening proof pass for the challenges `ch`, with the Merkle
commitment schemes over the hash functions of `f`, then every proof-of-work
check of `ch` passed, and the model verifier of the opening protocol accepts
against the hasher of `f`, on the messages of the run read through `view` and
the challenges `ch` as elements of the model field. -/
theorem modelChecks_of_verifyWith {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : Challenges EF}
    (hshape : Fri.shapeOk (F := F) params shape commitments points values proof = true)
    (h : verifyWith (merkleMmcs (inputHasher m (hasherOf f)))
      (merkleMmcs (friHasher m (hasherOf f))) params shape commitments points values proof
      ch = true) :
    ch.powOk = true ∧
      modelChecks (modelParams m params shape wf) (hasherOf f) (modelProof m params shape proof)
        (fun j => view m params shape (messages params shape commitments points values proof j))
        (m.ext.toModel ch.alpha) (fun i => m.ext.toModel (ch.betas.getD i 0))
        (fun t => ch.indices.getD t.val 0) = true := by
  have hag : Agrees m params shape commitments points values proof ch
      (fun j => view m params shape (messages params shape commitments points values proof j))
      (m.ext.toModel ch.alpha) (fun i => m.ext.toModel (ch.betas.getD i 0))
      (fun t => ch.indices.getD t.val 0) :=
    { msg := fun _ _ => rfl
      alpha := rfl
      beta := fun _ _ => rfl
      index := fun _ => rfl }
  exact modelChecks_of_verifyWith_aux m params shape wf (hasherOf f) hshape hag
    (fun t hok => finalCheck_of_queryResult m params shape wf hshape hag t hok)
    (fun t i hi => rows_queryResult m params shape wf hshape hag t hi) h

end Pcs

end CertiFri.Exec.Stark
