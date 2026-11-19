import CertiFriProofs.Theory.Compiled.Verifier

/-!
# The compiled protocol: an accepting verifier accepts in the oracle model

The link between the model verifier of `Compiled/Verifier.lean` and the
acceptance predicate `PcsRbr.Accepts` of the oracle-model protocol.

If the model verifier accepts, and the final log has no collision of the hash
oracle, then the transcript, with every message read from the rows the final
log commits its roots to (`Params.read` with `Oracle.committedRow`), is
accepted in the oracle model: the final word is a codeword, and every query
satisfies `QueryAccepts`.

## Results

* `Params.outcome_verifyWith`: what an accepting run of the verifier leaves
  behind. The final log holds an opening (`Oracle.Opens`) of the opened input
  rows of every batch and query and of the row of every folding round and
  query, and every fold chain ends at the value of the final polynomial.
* `Params.pcsInput_eq_reduced`: the reduced opening the verifier computes from
  the opened values is the input of the low-degree test at the query point.
* `Params.round_of_opens`: the row of a folding round holds the values of the
  committed codeword at the query point of that level and at its negation, and
  `fold_row` of the row is `foldAt` of the codeword.
* `Params.queryAccepts_of_outcome`: one query of an accepting run satisfies
  `QueryAccepts`.
* `Params.accepts_of_outcome_verify` and `Params.accepts_of_outcome_verifyGrind`:
  the statement for a transcript, without and with proof of work, for a final
  log without a hit (`Oracle.Hit`).

## How the proof goes

An accepted Merkle check leaves the opening in the log
(`opens_of_outcome_verifyOpeningsM`), and in a log without a collision an
opening shows the committed row (`committedRow_of_opens`). So the values the
verifier computes with are the values of the functions the messages are read
as. The index lemmas of `Theory/Domain.lean` identify the points: the query
point of level `j` is the point of the index shifted by `j`, and the two
entries of a row are the values at a point and its negation. The verifier's
arithmetic is then `QueryAccepts`, by `foldAt_eq_interpolate`.

## Assumptions

No collision of the hash oracle in the final log. There is no assumption on
the log the verifier starts from, nor on how the transcript was produced.

Not covered: probabilities. These are statements about every outcome of a run.
-/

namespace CertiFri.Compiled

open Polynomial Oracle OracleComp MerkleRO
open PcsRbr (Chal alphaOf betasOf queriesOf claimsOf wordsOf Accepts GrindChal PowPasses ungrind)

variable {F D : Type}

/-! ## Accepted Merkle checks -/

section Openings

variable [DecidableEq D] {M T : Type} {C : ℕ → Type} [DecidableEq (FSQuery M C (HashQuery T D))]
  {l₀ l : Log (MerkleAnswer M C T D)} {root : D} {dims : Array Dimensions}

/-- Each opening of an accepted check, when the indices, the rows and the paths
are given by query. -/
theorem opens_of_outcome_ofFn {q : ℕ} {indices : Fin q → ℕ} {rows : Fin q → Array (Array T)}
    {paths : Fin q → List D}
    (h : Outcome (verifyOpeningsM root dims (Array.ofFn indices) (Array.ofFn rows)
      (Array.ofFn paths)) l₀ true l) (t : Fin q) : Opens l root dims (indices t) (rows t) :=
  opens_of_outcome_verifyOpeningsM h (query := t) (by simp) (by simp)

omit [DecidableEq D] in
/-- In a log without a collision, an opening of a commitment to one matrix
shows the committed row at its index. -/
theorem committedRow_of_opens_single (hl : ¬ LogCollision hashObs l) {d : Dimensions} {index : ℕ}
    {row : Array T} (h : Opens l root #[d] index #[row]) :
    committedRow l root #[d] 0 index = some row := by
  have hrow := committedRow_of_opens hl h (m := 0) (d := d) rfl
  simpa [Merkle.maxLogHeight] using hrow

end Openings

/-! ## Index arithmetic -/

/-- Shifting an index below `2 ^ n` by `j ≤ n` gives an index below `2 ^ (n - j)`. -/
theorem shiftRight_lt_two_pow {index n j : ℕ} (h : index < 2 ^ n) (hj : j ≤ n) :
    index >>> j < 2 ^ (n - j) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
    Nat.sub_add_cancel hj]
  exact h

/-- The entry of a row at the position of the value folded so far is that
value. -/
theorem placeRow_self [Field F] (folded sibling : F) (index : ℕ) :
    (if index % 2 = 0 then (placeRow folded sibling index).1
      else (placeRow folded sibling index).2) = folded := by
  unfold placeRow
  split <;> rfl

/-- The query points of a full transcript lie in the first domain. -/
theorem queriesOf_mem [Field F] {M : Type} {S : LdtInstance F} {q : ℕ}
    (t : Transcript M (Chal S q) (S.rounds + 2)) (k : Fin q) : queriesOf t k ∈ S.domain 0 := by
  cases t with
  | snoc t m c =>
    rw [PcsRbr.queriesOf_snoc, PcsRbr.Chal.points_of_not_le (Nat.not_succ_le_self _)]
    exact (PcsRbr.chalQuery _ c k).2

/-! ## What an accepting run leaves behind -/

variable [Field F] [DecidableEq F] [DecidableEq D]

namespace Params

variable (P : Params F) {C : ℕ → Type} [DecidableEq (FSQuery (Msg F D P.batches) C (HashQuery F D))]
  {pf : Proof F D P.batches P.queries} {msg : ℕ → Msg F D P.batches} {α : F} {β : ℕ → F}
  {index : Fin P.queries → ℕ} {l l' : Log (MerkleAnswer (Msg F D P.batches) C F D)}

/-- **An accepting run of the verifier.** The final log holds an opening of the
opened rows of every input batch at every query, every fold chain ends at the
value of the final polynomial, and the final log holds an opening of the row of
every folding round at every query. -/
theorem outcome_verifyWith (h : Outcome (P.verifyWith pf msg α β index) l true l') :
    (∀ b t, Opens l' ((msg 0).inputRoots b) (P.dims b)
        (index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t)) ∧
      P.FinalCheck pf msg α β index ∧
      ∀ i < P.rounds, ∀ t, Opens l' (msg (i + 1)).commitRoot (P.commitDims i)
        (index t >>> (i + 1))
        #[#[(P.commitRow pf (msg 0) α β (index t) t i).1,
          (P.commitRow pf (msg 0) α β (index t) t i).2]] := by
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

/-! ## The values the verifier computes with -/

omit [DecidableEq D] in
/-- **The reduced openings.** In a log without a collision that holds the
openings of the input rows of a query, the reduced opening the verifier
computes for level `j` is the input of the low-degree test of level `j`, for
the claims read from the log, at the point of the query index shifted by `j`. -/
theorem pcsInput_eq_reduced (hl : ¬ LogCollision hashObs l') {idx : ℕ} {t : Fin P.queries}
    (hopen : ∀ b, Opens l' ((msg 0).inputRoots b) (P.dims b)
      (idx >>> (P.n - Merkle.maxLogHeight (P.dims b).toList)) (pf.inputRows b t))
    (hidx : idx < 2 ^ P.n) {j : ℕ} (hj : j ≤ P.rounds) :
    pcsInput P.shift (P.claims (msg 0) (committedRow l')) α j
        (pointOfIndex P.ω P.n (P.n - j) (idx >>> j)) =
      P.reduced (msg 0) (P.opened pf t) α idx j := by
  have hjn : j ≤ P.n := hj.trans P.rounds_le
  unfold pcsInput reducedOpening Params.reduced quotientAt
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

omit [DecidableEq D] in
/-- The two entries of a committed row of a folding round are the values of the
codeword at the points of the two children of the row index. -/
theorem commitWord_row (hl : ¬ LogCollision hashObs l') {i : ℕ} (hi : i < P.n) {p : ℕ}
    (hp : p < 2 ^ (P.n - (i + 1))) {root : D} {a b : F}
    (hopen : Opens l' root (P.commitDims i) p #[#[a, b]]) :
    P.commitWord i (committedRow l' root (P.commitDims i) 0)
        (pointOfIndex P.ω P.n (P.n - i) (2 * p)) = a ∧
      P.commitWord i (committedRow l' root (P.commitDims i) 0)
        (pointOfIndex P.ω P.n (P.n - i) (2 * p + 1)) = b := by
  have hrow : committedRow l' root (P.commitDims i) 0 p = some #[a, b] :=
    committedRow_of_opens_single hl hopen
  have hpow : 2 ^ (P.n - i) = 2 * 2 ^ (P.n - (i + 1)) := by
    rw [← pow_succ', show P.n - (i + 1) + 1 = P.n - i by omega]
  have h0 : 2 * p < 2 ^ (P.n - i) := by omega
  have h1 : 2 * p + 1 < 2 ^ (P.n - i) := by omega
  rw [P.commitWord_apply i _ h0, P.commitWord_apply i _ h1,
    show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega,
    show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega, hrow]
  exact entry_pair a b

omit [DecidableEq D] in
/-- **One folding round.** Let the log hold an opening of the row `[a, b]` of
round `i` at the query index shifted by `i + 1`, and have no collision. Then
the committed codeword of level `i` takes at the query point of level `i` the
entry of the row that the low bit of the index selects, and its fold is
`foldRow` of the row at the point of the first entry. -/
theorem round_of_opens (hl : ¬ LogCollision hashObs l') {i : ℕ} (hi : i < P.n) {idx : ℕ}
    (hidx : idx < 2 ^ P.n) {root : D} {a b : F}
    (hopen : Opens l' root (P.commitDims i) (idx >>> (i + 1)) #[#[a, b]]) (β : F) :
    P.commitWord i (committedRow l' root (P.commitDims i) 0)
        (pointOfIndex P.ω P.n (P.n - i) (idx >>> i)) = (if idx >>> i % 2 = 0 then a else b) ∧
      foldAt (P.commitWord i (committedRow l' root (P.commitDims i) 0)) β
          (pointOfIndex P.ω P.n (P.n - i) (idx >>> i)) =
        foldRow β (pointOfIndex P.ω P.n (P.n - i) (2 * (idx >>> (i + 1)))) a b := by
  have hdiv : idx >>> i / 2 = idx >>> (i + 1) := (Nat.shiftRight_succ idx i).symm
  generalize idx >>> (i + 1) = p at hopen hdiv ⊢
  have hplt : p < 2 ^ (P.n - (i + 1)) := by
    have := shiftRight_lt_two_pow hidx hi.le
    have hpow : 2 ^ (P.n - i) = 2 * 2 ^ (P.n - (i + 1)) := by
      rw [← pow_succ', show P.n - (i + 1) + 1 = P.n - i by omega]
    omega
  obtain ⟨ha, hb⟩ := P.commitWord_row hl hi hplt hopen
  have hneg : pointOfIndex P.ω P.n (P.n - i) (2 * p + 1) =
      -pointOfIndex P.ω P.n (P.n - i) (2 * p) := by
    have e : P.n - i = P.n - (i + 1) + 1 := by omega
    rw [e, pointOfIndex_two_mul_add_one P.prim (by omega), pointOfIndex_two_mul]
  have h2 : (2 : F) ≠ 0 := Domain.two_ne_zero_of_isPrimitiveRoot P.prim (by omega)
  have hx0 : pointOfIndex P.ω P.n (P.n - i) (2 * p) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (P.prim.ne_zero (by positivity)))
  have hfold : foldAt (P.commitWord i (committedRow l' root (P.commitDims i) 0)) β
      (pointOfIndex P.ω P.n (P.n - i) (2 * p)) =
        foldRow β (pointOfIndex P.ω P.n (P.n - i) (2 * p)) a b := by
    rw [foldAt_eq_interpolate h2 _ _ hx0, ← hneg, ha, hb, foldRow, hneg]
  rcases Nat.mod_two_eq_zero_or_one (idx >>> i) with h0 | h1
  · have e : idx >>> i = 2 * p := by omega
    rw [ite_eq_left h0, e]
    exact ⟨ha, hfold⟩
  · have e : idx >>> i = 2 * p + 1 := by omega
    rw [ite_eq_right (by omega), e, hneg, foldAt_neg, ← hneg]
    exact ⟨hb, hfold⟩

/-! ## One query -/

/-- **An accepted query satisfies `QueryAccepts`.** After an accepting run of
the verifier that leaves a log without a collision, let `words i` be the word of
the message of round `1 + i` as read from the final log, for `i ≤ rounds`. Then
the query `t` passes the check of the oracle-model protocol at the point of its
index, with the claims of the message of round `0` as read from the final log. -/
theorem queryAccepts_of_outcome (hrun : Outcome (P.verifyWith pf msg α β index) l true l')
    (hl : ¬ LogCollision hashObs l') (t : Fin P.queries) (hindex : index t < 2 ^ P.n)
    (words : ℕ → F → F)
    (hwords : ∀ i ≤ P.rounds, words i = (P.read (i + 1) (msg (i + 1)) (committedRow l')).word) :
    QueryAccepts P.rounds (pcsInput P.shift (P.claims (msg 0) (committedRow l')) α) words β
      (pointOfIndex P.ω P.n P.n (index t)) := by
  obtain ⟨hin, hfinal, hcommit⟩ := P.outcome_verifyWith hrun
  have hpow : ∀ j ≤ P.n, pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ j =
      pointOfIndex P.ω P.n (P.n - j) (index t >>> j) := fun j hj =>
    pointOfIndex_pow_two_pow P.prim le_rfl hj (index t)
  -- The inputs of the low-degree test at the query points.
  have hro : ∀ j ≤ P.rounds,
      pcsInput P.shift (P.claims (msg 0) (committedRow l')) α j
          (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ j) =
        P.reduced (msg 0) (P.opened pf t) α (index t) j := fun j hj => by
    rw [hpow j (hj.trans P.rounds_le)]
    exact P.pcsInput_eq_reduced hl (fun b => hin b t) hindex hj
  -- The committed codewords at the query points, and their folds.
  have hround : ∀ i < P.rounds,
      words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
          P.folded pf (msg 0) α β (index t) t i ∧
        foldAt (words i) (β i) (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
          foldRow (β i) (pointOfIndex P.ω P.n (P.n - i) (2 * (index t >>> (i + 1))))
            (P.commitRow pf (msg 0) α β (index t) t i).1
            (P.commitRow pf (msg 0) α β (index t) t i).2 := fun i hi => by
    have hin' : i < P.n := lt_of_lt_of_le hi P.rounds_le
    obtain ⟨hval, hfold⟩ := P.round_of_opens hl hin' hindex (hcommit i hi t) (β i)
    rw [hpow i hin'.le, hwords i hi.le, P.read_word_of_lt hi]
    exact ⟨hval.trans (placeRow_self _ _ _), hfold⟩
  -- The final word at the last query point.
  have hlast : words P.rounds (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ P.rounds) =
      P.folded pf (msg 0) α β (index t) t P.rounds := by
    rw [hpow _ P.rounds_le, hwords _ le_rfl, P.read_word_last, hfinal t, hornerEval_eq_eval]
    rfl
  have hword : ∀ i ≤ P.rounds, words i (pointOfIndex P.ω P.n P.n (index t) ^ 2 ^ i) =
      P.folded pf (msg 0) α β (index t) t i := fun i hi => by
    rcases Nat.lt_or_ge i P.rounds with hlt | hge
    · exact (hround i hlt).1
    · obtain rfl : i = P.rounds := le_antisymm hi hge
      exact hlast
  refine ⟨?_, fun i hi => ?_⟩
  · have h0 := hword 0 (Nat.zero_le _)
    have hro0 := hro 0 (Nat.zero_le _)
    rw [pow_zero, pow_one] at h0 hro0
    rw [h0, hro0, P.folded_zero]
  · rw [hword (i + 1) hi, (hround i hi).2, hro (i + 1) hi, P.folded_succ]

end Params

/-! ## A transcript -/

namespace Params

variable (P : Params F) {C : ℕ → Type} [DecidableEq (FSQuery (Msg F D P.batches) C (HashQuery F D))]
  {pf : Proof F D P.batches P.queries} {l l' : Log (MerkleAnswer (Msg F D P.batches) C F D)}

/-- **An accepted transcript is accepted in the oracle model.** Let the
verifier, run on the messages, the challenges and the indices of the query
points of a transcript, accept and leave a log without a collision. Then the
transcript, with every message read from the rows the final log commits to, is
accepted by the oracle-model protocol. The oracle of the run may have any
challenge types. -/
theorem accepts_of_outcome_verifyWith
    (t : Transcript (Msg F D P.batches) (Chal P.ldt P.queries) (P.rounds + 2))
    (hrun : Outcome (P.verifyWith (C := C) pf (msgAt t) (alphaOf t) (betasOf t)
      fun k => P.indexOf (queriesOf t k)) l true l')
    (hl : ¬ LogCollision hashObs l') :
    Accepts P.ldt P.shift (t.mapIdx fun j m => P.read j m (committedRow l')) := by
  have hwords : ∀ i ≤ P.rounds,
      wordsOf (t.mapIdx fun j m => P.read j m (committedRow l')) i =
        (P.read (i + 1) (msgAt t (i + 1)) (committedRow l')).word := fun i hi =>
    PcsRbr.wordsOf_mapIdx _ t (getElem?_msgs t (by omega))
  have hclaims : claimsOf (t.mapIdx fun j m => P.read j m (committedRow l')) =
      P.claims (msgAt t 0) (committedRow l') :=
    PcsRbr.claimsOf_mapIdx _ t (getElem?_msgs t (Nat.zero_le _))
  refine ⟨?_, fun k => ?_⟩
  · have h := P.isCodeword_finalWord (msgAt t (P.rounds + 1)).finalCoeffs
    rw [← P.read_word_last _ (committedRow l'), ← hwords _ le_rfl] at h
    exact h
  · have hx : queriesOf t k ∈ twoAdicDomain P.ω P.n 0 := queriesOf_mem (S := P.ldt) t k
    rw [hclaims, PcsRbr.alphaOf_mapIdx, PcsRbr.betasOf_mapIdx, PcsRbr.queriesOf_mapIdx,
      ← P.pointOfIndex_indexOf hx]
    exact P.queryAccepts_of_outcome hrun hl k (P.indexOf_lt _) _ hwords

end Params

namespace Params

variable (P : Params F)

/-- **The key lemma, without proof of work.** If the model verifier accepts a
transcript and the final log has no hit, the transcript, read from the rows the
final log commits to, is accepted by the oracle-model protocol. -/
theorem accepts_of_outcome_verify {pf : Proof F D P.batches P.queries}
    {t : Transcript (Msg F D P.batches) (Chal P.ldt P.queries) (P.rounds + 2)}
    {l l' : Log (MerkleAnswer (Msg F D P.batches) (Chal P.ldt P.queries) F D)}
    (hrun : Outcome (P.verify pf t) l true l') {r : ℕ}
    (hno : ¬ HasBad (Hit digestsOf r) l') :
    Accepts P.ldt P.shift (t.mapIdx fun j m => P.read j m (committedRow l')) :=
  P.accepts_of_outcome_verifyWith t hrun (not_logCollision_of_not_hasBad_hit hno)

/-- **The key lemma, with proof of work.** If the model verifier with proof of
work accepts a transcript and the final log has no hit, every proof-of-work
sample of the transcript is zero, and the transcript without the samples, read
from the rows the final log commits to, is accepted by the oracle-model
protocol. -/
theorem accepts_of_outcome_verifyGrind {bits : ℕ → ℕ} {pf : Proof F D P.batches P.queries}
    {t : Transcript (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) (P.rounds + 2)}
    {l l' : Log (MerkleAnswer (Msg F D P.batches) (GrindChal bits (Chal P.ldt P.queries)) F D)}
    (hrun : Outcome (P.verifyGrind bits pf t) l true l') {r : ℕ}
    (hno : ¬ HasBad (Hit digestsOf r) l') :
    PowPasses t ∧
      Accepts P.ldt P.shift ((ungrind t).mapIdx fun j m => P.read j m (committedRow l')) := by
  unfold verifyGrind at hrun
  split at hrun
  · next hpow =>
    exact ⟨hpow, P.accepts_of_outcome_verifyWith (ungrind t) hrun
      (not_logCollision_of_not_hasBad_hit hno)⟩
  · exact absurd hrun.1 (by simp)

end Params

end CertiFri.Compiled
