import CertiFriProofs.Exec.Stark.Shard

/-!
# A failing check at the out-of-domain point makes the opening claims fail

The security proof of the STARK follows the event `ZetaFail`
(`Exec/Stark/Shard.lean`): for the polynomials the committed columns decode to,
the check at `ζ` fails for some circuit. The verifier does not see these
polynomials; it runs its check on the values the prover opened. This file
connects the two: if the opened values pass the executable checks although
`ZetaFail` holds, and `ζ` is off the cosets of the proof (`OffCosets`), the
opened values are not the values of the decoded polynomials, so the opening
claims fail.

* `claimsFail_of_zetaFail`: the statement.

## The proof

By contradiction. Every opening point of the claims is `ζ` or the successor of
`ζ` on the trace domain of its matrix (`point_of_mem_openingClaims`), so for a
`ζ` off the cosets no opening point lies in the coset of a column it is claimed
for. If the opening claims do not fail, every claimed value is then the value
of the decoded polynomial of its column at its opening point
(`eval_colPoly_of_not_claimsFail`). The opening claims of a proof that passes
the shape check hold, for each active circuit, the rows opened on its main
trace, its lookup trace, its quotient and its fixed trace, so each opened row
lists the values of the columns of the circuit at `ζ` or at its successor. On
such rows the executable check of a circuit (`circuitOk_iff`) is the check at
`ζ` on the polynomials (`circuitCheck_iff_eval`), which `ZetaFail` denies for
some circuit.

## Assumptions

`System.FixedOk`: a circuit without a fixed trace has fixed-trace width zero.
The strict margin of unique decoding (`StrictMargin`) at the height of every
committed matrix, and a first domain that exists in the field.

`OffCosets` at `ζ` is a hypothesis: the verifier does not check it, and without
it the opening protocol says nothing about the committed words at the opening
points. `fractionLE_offCosets` (`Exec/Stark/Shard.lean`) bounds the fraction of
the `ζ` for which it fails.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle Polynomial

/-! ## Lists and arrays -/

section Lists

/-- The length of a `flatMap` over an indexed list, when the length of each
part depends on the element only. -/
private theorem length_flatMap_zipIdx {α β : Type} (f : α × ℕ → List β) (g : α → ℕ)
    (h : ∀ p, (f p).length = g p.1) (l : List α) (n : ℕ) :
    ((l.zipIdx n).flatMap f).length = (l.map g).sum := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, h, ih, List.map_cons,
      List.sum_cons]

/-- Entry `i` of a list mapped over its indexed elements. -/
private theorem getElem?_map_zipIdx {α β : Type} (f : α × ℕ → β) {l : List α} {a : α} {i : ℕ}
    (h : (a, i) ∈ l.zipIdx) : (l.zipIdx.map f).toArray[i]? = some (f (a, i)) := by
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx,
    List.mem_zipIdx_iff_getElem?.mp h, Option.map_some, Option.map_some, Nat.zero_add]

/-- In the list of the values of a partial function on a list, the value at
entry `i` is at the position that counts the earlier entries with a value. -/
private theorem getElem?_filterMap {α β : Type} (f : α → Option β) {l : List α} {i : ℕ} {a : α}
    {y : β} (ha : l[i]? = some a) (hy : f a = some y) :
    (l.filterMap f)[((l.take i).filter fun c => (f c).isSome).length]? = some y := by
  induction l generalizing i with
  | nil => cases ha
  | cons b l ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at ha
      rw [ha, List.filterMap_cons_some hy]
      rfl
    | succ i =>
      rw [List.getElem?_cons_succ] at ha
      rw [List.take_succ_cons]
      cases hb : f b with
      | none =>
        rw [List.filterMap_cons_none hb, List.filter_cons_of_neg (by rw [hb]; simp)]
        exact ih ha
      | some z =>
        rw [List.filterMap_cons_some hb, List.filter_cons_of_pos (by rw [hb]; rfl),
          List.length_cons, List.getElem?_cons_succ]
        exact ih ha

/-- The position of an element of a list without duplicates. -/
private theorem idxOf?_of_mem_zipIdx {l : List ℕ} (hl : l.Nodup) {a i : ℕ}
    (h : (a, i) ∈ l.zipIdx) : l.idxOf? a = some i := by
  have hi := List.mem_zipIdx_iff_getElem?.mp h
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.idxOf?, List.findIdx?_eq_some_iff_getElem]
  refine ⟨hlt, by simpa using hget, fun j hji => ?_⟩
  have hne : l[j] ≠ l[i] := fun e => by
    have := (List.Nodup.getElem_inj_iff hl).mp e
    omega
  simpa [hget] using hne

/-- `getElem?_filterMap` for a list of consecutive numbers, the entries with a
value counted with any test that tells them. -/
private theorem getElem?_filterMap_range {β : Type} (f : ℕ → Option β) (q : ℕ → Bool)
    (hq : ∀ c, (f c).isSome = q c) {n i : ℕ} (hi : i < n) {y : β} (hy : f i = some y) :
    ((List.range n).filterMap f)[((List.range i).filter q).length]? = some y := by
  have h := getElem?_filterMap f (List.getElem?_range hi) hy
  rwa [List.take_range, min_eq_left hi.le, show (fun c => (f c).isSome) = q from funext hq] at h

/-- An entry of an array of mapped arrays, with the empty array as default. -/
private theorem getD_map_map {α β : Type} (φ : α → β) (ms : Array (Array α)) (i : ℕ) :
    (ms.map fun row => row.map φ).getD i #[] = (ms.getD i #[]).map φ := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases ms[i]? with
  | none => exact Array.map_empty.symm
  | some a => rfl

end Lists

/-! ## Nested claims -/

section Claims

variable {EF D : Type}

/-- Nested claims have one opening point per point of their shape. -/
private theorem size_claimPoints (lb : ℕ) (claims : Array (CommitmentOpening EF D)) :
    (claimPoints claims).size = (pointRefs lb (claimShape claims)).length := by
  rw [pointRefs, length_flatMap_zipIdx _ (fun mats => (mats.map (·.numPoints)).sum)
    (fun p => length_flatMap_zipIdx _ (·.numPoints) (fun q => List.length_replicate) p.1 0)]
  simp only [claimPoints, claimShape, List.size_toArray, List.length_flatMap, List.map_map,
    List.length_map, Array.length_toList, Function.comp_def]

/-- A row of rows that pass `rowsOk`. -/
private theorem getElem?_of_rowsOk {rows : Array (Array EF)} {count width p : ℕ}
    (h : rowsOk rows count width = true) (hp : p < count) :
    ∃ row, rows[p]? = some row ∧ row.size = width := by
  rw [rowsOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  have hlt : p < rows.size := h.1 ▸ hp
  exact ⟨rows[p], Array.getElem?_eq_getElem hlt, by simpa using h.2 _ (Array.getElem_mem hlt)⟩

/-- The opening of a matrix at its point number `p`. -/
private theorem matrixOpening_points {k p : ℕ} {pts : List EF} {rows : Array (Array EF)} {x : EF}
    {row : Array EF} (hx : pts[p]? = some x) (hrow : rows[p]? = some row) :
    (matrixOpening k pts rows).points[p]? = some ⟨x, row⟩ := by
  rw [matrixOpening, List.getElem?_toArray, List.getElem?_map,
    (List.getElem?_zip_eq_some (z := (x, row))).mpr ⟨hx, by rw [Array.getElem?_toList, hrow]⟩]
  rfl

end Claims

/-! ## The opening claims of a proof -/

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] {M : StarkModel F EF K} {sys : System F D} {θ : ℝ}
  {com : Compiled.Committed K D}

/-- **A row of an opened matrix holds the values of the decoded columns.** Let
every claim of the shape of nested claims be the value of the decoded
polynomial of its column at its opening point. Then the row opened at the point
number `p` of a matrix, in the model, lists the values of the decoded
polynomials of the columns of that matrix at that point. -/
private theorem opened_row [Inhabited D] (M : StarkModel F EF K) (lb : ℕ) (θ : ℝ)
    (com : Compiled.Committed K D) {claims : Array (CommitmentOpening EF D)}
    (huni : widthsUniform claims = true)
    (heval : ∀ r ∈ claimRefs lb (claimShape claims),
      (M.colPoly lb θ com ((claims.map (·.commitment)).getD r.batch default)
          (batchDims lb ((claimShape claims).getD r.batch [])) r.matrix r.col r.logHeight).eval
          (M.ext.toModel ((claimPoints claims).getD r.pointIdx 0)) =
        M.ext.toModel ((claimValues claims).getD r.valueIdx 0))
    {b mi p k w : ℕ} {root : D} {ms : Array (MatrixOpening EF)} {pts : List EF}
    {rows : Array (Array EF)} {x : EF} (hb : claims[b]? = some ⟨root, ms⟩)
    (hm : ms[mi]? = some (matrixOpening k pts rows)) (hx : pts[p]? = some x)
    (hrows : rowsOk rows pts.length w = true) :
    (rows.map fun row => row.map M.ext.toModel).getD p #[] =
      Array.ofFn (n := w) fun j =>
        (M.colPoly lb θ com root (batchDims lb ((claimShape claims).getD b [])) mi j.val
          (k + lb)).eval (M.ext.toModel x) := by
  obtain ⟨row, hrow, hsize⟩ := getElem?_of_rowsOk hrows (List.getElem?_eq_some_iff.mp hx).1
  have hpo := matrixOpening_points (k := k) hx hrow
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hrow, Option.map_some, Option.getD_some]
  refine Array.ext (by rw [Array.size_map, Array.size_ofFn, hsize]) fun j h₁ h₂ => ?_
  have hj : j < row.size := by rwa [Array.size_map] at h₁
  obtain ⟨r, hr, hrb, hrm, hrc, hrh, hrp, hrv⟩ :=
    @exists_claimRef _ _ ⟨0⟩ lb claims huni _ _ _ _ _ _ _ hb hm hpo hj
  have hrh' : r.logHeight = k + lb := hrh
  have hrp' : (claimPoints claims).getD r.pointIdx 0 = x := hrp
  have hrv' : (claimValues claims).getD r.valueIdx 0 = row[j] := by
    rw [show (claimValues claims).getD r.valueIdx 0 = row.getD j 0 from hrv,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some]
  have hcom : (claims.map (·.commitment)).getD b default = root := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hb, Option.map_some, Option.getD_some]
  have h := heval r hr
  rw [hrb, hrm, hrc, hrh', hrp', hrv', hcom] at h
  rw [Array.getElem_map, Array.getElem_ofFn, h]

omit [TwoAdicOps F] in
/-- **What the shape check says of an active circuit**: it is a circuit of the
system, it has no fixed trace if the system has no commitment to fixed traces,
and its opened rows have the numbers and the widths of its matrices. -/
private theorem shapeOk_active {InputProof CommitProof : Type}
    {proof : Proof F EF D InputProof CommitProof} (h : shapeOk sys proof = true) {ci pos : ℕ}
    (hp : (ci, pos) ∈ (activeIndices proof.active).zipIdx) :
    ci < sys.circuits.size ∧
      (sys.preprocessedCommit = none → sys.preprocessedIndices.getD ci none = none) ∧
      rowsOk (proof.stage1Opened.getD pos #[]) 2
        (sys.circuits.getD ci default).mainWidth = true ∧
      rowsOk (proof.stage2Opened.getD pos #[]) 2
        (sys.circuits.getD ci default).stage2Width = true ∧
      (sys.preprocessedIndices.getD ci none ≠ none →
        rowsOk (preprocessedRows sys proof ci) 2
          (sys.circuits.getD ci default).preprocessedWidth = true) ∧
      rowsOk (proof.quotientOpened.getD pos #[]) 1
        ((sys.circuits.getD ci default).quotientDegree *
          ExtensionOps.degree (F := F) (EF := EF)) = true := by
  rw [Stark.shapeOk] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hsize⟩, -⟩, -⟩, hcommit⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hact⟩ := h
  have hact' := List.all_eq_true.mp hact (ci, pos) hp
  simp only [Bool.and_eq_true] at hact'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h1⟩, h2⟩, hpre⟩, hq⟩ := hact'
  refine ⟨?_, fun hnone => ?_, h1, h2, fun hsome => ?_, hq⟩
  · have hmem : ci ∈ activeIndices proof.active :=
      List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
    rw [← beq_iff_eq.mp hsize]
    exact List.mem_range.mp (List.mem_filter.mp hmem).1
  · rw [hnone] at hcommit
    have hlen : (List.filter Option.isSome sys.preprocessedIndices.toList).length = 0 := by
      simpa using hcommit
    rw [Array.getD_eq_getD_getElem?]
    rcases hget : sys.preprocessedIndices[ci]? with _ | a
    · rfl
    · have ha := List.filter_eq_nil_iff.mp (List.eq_nil_of_length_eq_zero hlen) a
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget))
      rw [Option.getD_some]
      simpa using ha
  · rcases (Bool.or_eq_true _ _).mp hpre with hn | hr
    · exact absurd (Option.isNone_iff_eq_none.mp hn) hsome
    · exact hr

/-- **The claims about the traces of an active circuit.** At the position of an
active circuit, the first three commitments of the opening claims are those to
the main traces, the lookup traces and the quotients, with the opened rows of
the circuit: the traces at `ζ` and its successor, the quotient at `ζ`. -/
private theorem openingClaims_traces {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) {ci pos : ℕ}
    (hp : (ci, pos) ∈ (activeIndices proof.active).zipIdx) :
    (∃ ms, (openingClaims sys proof ζ)[0]? = some ⟨proof.stage1Commit, ms⟩ ∧
        ms[pos]? = some (matrixOpening (proof.logDegrees.getD pos 0)
          [ζ, nextPoint (F := F) (proof.logDegrees.getD pos 0) ζ]
          (proof.stage1Opened.getD pos #[]))) ∧
      (∃ ms, (openingClaims sys proof ζ)[1]? = some ⟨proof.stage2Commit, ms⟩ ∧
        ms[pos]? = some (matrixOpening (proof.logDegrees.getD pos 0)
          [ζ, nextPoint (F := F) (proof.logDegrees.getD pos 0) ζ]
          (proof.stage2Opened.getD pos #[]))) ∧
      ∃ ms, (openingClaims sys proof ζ)[2]? = some ⟨proof.quotientCommit, ms⟩ ∧
        ms[pos]? = some (matrixOpening (proof.logDegrees.getD pos 0) [ζ]
          (proof.quotientOpened.getD pos #[])) :=
  ⟨⟨_, (Array.getElem?_append_left (show 0 < 3 by omega)).trans rfl, getElem?_map_zipIdx _ hp⟩,
    ⟨_, (Array.getElem?_append_left (show 1 < 3 by omega)).trans rfl, getElem?_map_zipIdx _ hp⟩,
    ⟨_, (Array.getElem?_append_left (show 2 < 3 by omega)).trans rfl, getElem?_map_zipIdx _ hp⟩⟩

/-- **The claims about the fixed trace of an active circuit.** If the system
has a commitment to fixed traces and the active circuit `ci` has a fixed trace,
the fourth commitment of the opening claims is that commitment, and its matrix
at the position `fixedRank sys ci` holds the rows opened on the fixed trace of
`ci`, at `ζ` and its successor. -/
private theorem openingClaims_fixed {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) {root : D}
    (hroot : sys.preprocessedCommit = some root) {ci pos : ℕ}
    (hp : (ci, pos) ∈ (activeIndices proof.active).zipIdx) (hci : ci < sys.circuits.size)
    (hsome : sys.preprocessedIndices.getD ci none ≠ none) :
    ∃ ms, (openingClaims sys proof ζ)[3]? = some ⟨root, ms⟩ ∧
      ms[fixedRank sys ci]? = some (matrixOpening (proof.logDegrees.getD pos 0)
        [ζ, nextPoint (F := F) (proof.logDegrees.getD pos 0) ζ]
        (preprocessedRows sys proof ci)) := by
  have hidx : (activeIndices proof.active).idxOf? ci = some pos :=
    idxOf?_of_mem_zipIdx (List.Nodup.filter _ List.nodup_range) hp
  have key : ∀ a b c d : CommitmentOpening EF D, (#[a, b, c] ++ #[d])[3]? = some d :=
    fun _ _ _ _ => rfl
  simp only [openingClaims, hroot]
  refine ⟨_, key _ _ _ _, ?_⟩
  · rw [List.getElem?_toArray]
    refine getElem?_filterMap_range _ _ (fun c => ?_) hci ?_
    · rcases sys.preprocessedIndices.getD c none with _ | slot
      · rfl
      · cases List.idxOf? c (activeIndices proof.active) <;> rfl
    · rw [ite_eq_right (by rw [Option.isNone_iff_eq_none]; exact hsome), hidx]

/-! ## The statement -/

/-- **A failing check at `ζ` and passing executable checks make the opening
claims fail.** Let a proof pass the shape check, and the executable constraint
checks pass on its opened values for the challenges `β`, `γ`, `α`, `ζ` and the
entering lookup sum `acc0`, with `ζ` usable. Let the first domain of the
opening exist in the field, the strict margin of unique decoding hold at the
height of every committed matrix, and `ζ` be off the cosets of the proof. If,
for the polynomials the committed columns decode to, the check at `ζ` fails for
some circuit, then the opening claims of the proof, read from the committed
rows `com`, fail. -/
theorem claimsFail_of_zetaFail [Inhabited D] {InputProof CommitProof : Type} (hfixed : sys.FixedOk)
    (proof : Proof F EF D InputProof CommitProof) (hshape : shapeOk sys proof = true)
    (β γ acc0 α ζ : EF)
    (hcheck : constraintsOk sys proof β γ acc0 α ζ = true) (hzeta : zetaOk proof ζ = true)
    (htwo : logMaxHeight sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees) ≤
        TwoAdicOps.twoAdicity (F := F))
    (hfinal : ∀ m ∈ (starkShape sys M.extData.d proof.active proof.logDegrees).flatten,
      sys.fri.logFinalHeight ≤ m.logDegree + sys.fri.logBlowup)
    (hmargin : ∀ m ∈ (starkShape sys M.extData.d proof.active proof.logDegrees).flatten,
      StrictMargin (M.coset (m.logDegree + sys.fri.logBlowup)) (2 ^ m.logDegree) θ)
    (hoff : OffCosets M sys proof.active proof.logDegrees (M.ext.toModel ζ))
    (hfail : ZetaFail M sys θ com proof.active proof.logDegrees proof.stage1Commit
      proof.stage2Commit proof.quotientCommit (M.ext.toModel β) (M.ext.toModel γ)
      (M.ext.toModel acc0) (proof.intermediateAccumulators.map M.ext.toModel) (M.ext.toModel α)
      (M.ext.toModel ζ)) :
    PcsRbr.ClaimsFail
      (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).ldt
      (modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).shift θ
      ((modelParams M.toFieldModel sys.fri
        (starkShape sys M.extData.d proof.active proof.logDegrees)
        (M.wellFormed sys.fri _ htwo)).claims
        (view M.toFieldModel sys.fri (starkShape sys M.extData.d proof.active proof.logDegrees)
          (firstMessage ((openingClaims sys proof ζ).map (·.commitment))
            (claimPoints (openingClaims sys proof ζ)) (claimValues (openingClaims sys proof ζ))))
        com) := by
  by_contra hnf
  -- Every claim of the shape is the value of the decoded polynomial of its column.
  have hsh : claimShape (openingClaims sys proof ζ) =
      starkShape sys M.extData.d proof.active proof.logDegrees := by
    rw [claimShape_openingClaims sys proof hshape ζ, M.degree_eq]
  have huni := widthsUniform_openingClaims sys proof hshape ζ
  -- No opening point lies in the coset of a column it is claimed for.
  have hpoint : ∀ r ∈ claimRefs sys.fri.logBlowup
      (starkShape sys M.extData.d proof.active proof.logDegrees),
      M.ext.toModel ((claimPoints (openingClaims sys proof ζ)).getD r.pointIdx 0) ∉
        M.coset r.logHeight := by
    intro r hr
    rw [← hsh] at hr
    obtain ⟨c, hc, m, hm, po, hpo, hh, hpt⟩ :=
      exists_point_of_mem_claimRefs sys.fri.logBlowup (openingClaims sys proof ζ) hr 0
    have hmem : (⟨m.logDegree, claimedWidth m, m.points.size⟩ : MatrixShape) ∈
        (starkShape sys M.extData.d proof.active proof.logDegrees).flatten := by
      rw [← hsh]
      exact List.mem_flatten.mpr ⟨_, List.mem_map_of_mem (Array.mem_toList_iff.mpr hc),
        List.mem_map_of_mem (Array.mem_toList_iff.mpr hm)⟩
    have hm' := hoff _ hmem
    rw [hpt, hh]
    rcases point_of_mem_openingClaims sys proof ζ hc hm hpo with h | h
    · rw [h]
      exact hm'.1
    · rw [h, nextPoint, M.ext.map_mul, M.embed]
      exact hm'.2
  have heval : ∀ r ∈ claimRefs sys.fri.logBlowup (claimShape (openingClaims sys proof ζ)),
      (M.colPoly sys.fri.logBlowup θ com
          (((openingClaims sys proof ζ).map (·.commitment)).getD r.batch default)
          (batchDims sys.fri.logBlowup ((claimShape (openingClaims sys proof ζ)).getD r.batch []))
          r.matrix r.col r.logHeight).eval
          (M.ext.toModel ((claimPoints (openingClaims sys proof ζ)).getD r.pointIdx 0)) =
        M.ext.toModel ((claimValues (openingClaims sys proof ζ)).getD r.valueIdx 0) := by
    rw [hsh]
    intro r hr
    exact eval_colPoly_of_not_claimsFail M sys.fri _ htwo _ _ _ com
      (by rw [← hsh]; exact size_claimPoints _ _) hfinal hmargin hpoint hnf hr
  -- The circuit whose check at `ζ` fails.
  obtain ⟨⟨ci, pos⟩, hp, hne⟩ := hfail
  refine hne ?_
  dsimp only
  set k := proof.logDegrees.getD pos 0
  set c := sys.circuits.getD ci default
  set cols := shardCols M sys θ com proof.active proof.logDegrees proof.stage1Commit
    proof.stage2Commit proof.quotientCommit pos ci with hcols
  obtain ⟨hci, hnoCommit, hrows1, hrows2, hrowsPre, hrowsQ⟩ := shapeOk_active hshape hp
  obtain ⟨⟨ms0, hb0, hm0⟩, ⟨ms1, hb1, hm1⟩, ms2, hb2, hm2⟩ := openingClaims_traces sys proof ζ hp
  have hpos : pos < (activeIndices proof.active).length :=
    (List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hp)).1
  -- The generator of the trace domain.
  have hktwo : k ≤ TwoAdicOps.twoAdicity (F := F) := by
    have hmem : (⟨k, c.mainWidth, 2⟩ : MatrixShape) ∈
        (starkShape sys M.extData.d proof.active proof.logDegrees).flatten := by
      rw [starkShape, List.flatten_append, List.flatten_cons]
      exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_map.mpr ⟨(ci, pos), hp, rfl⟩))
    have h : k + sys.fri.logBlowup ≤ _ := CertiFri.Exec.le_logMaxHeight hmem
    exact (Nat.le_add_right _ _).trans (h.trans htwo)
  have hprim := M.generator k hktwo
  have hnext : M.ext.toModel (nextPoint (F := F) k ζ) = M.ext.toModel ζ * M.gen k := by
    rw [nextPoint, M.ext.map_mul, M.embed]
    rfl
  -- The opened rows are the values of the columns at `ζ` and at its successor.
  have hmain : ∀ (p : ℕ) (x : EF), [ζ, nextPoint (F := F) k ζ][p]? = some x →
      ((proof.stage1Opened.getD pos #[]).map fun row => row.map M.ext.toModel).getD p #[] =
        Array.ofFn (n := c.mainWidth) fun j => (cols.main j.val).eval (M.ext.toModel x) := by
    intro p x hx
    have h := opened_row M sys.fri.logBlowup θ com huni heval hb0 hm0 hx hrows1
    rwa [hsh] at h
  have hs2 : ∀ (p : ℕ) (x : EF), [ζ, nextPoint (F := F) k ζ][p]? = some x →
      ((proof.stage2Opened.getD pos #[]).map fun row => row.map M.ext.toModel).getD p #[] =
        Array.ofFn (n := c.stage2Width) fun j => (cols.stage2 j.val).eval (M.ext.toModel x) := by
    intro p x hx
    have h := opened_row M sys.fri.logBlowup θ com huni heval hb1 hm1 hx hrows2
    rwa [hsh] at h
  have hpre : ∀ (p : ℕ) (x : EF), [ζ, nextPoint (F := F) k ζ][p]? = some x →
      ((preprocessedRows sys proof ci).map fun row => row.map M.ext.toModel).getD p #[] =
        Array.ofFn (n := c.preprocessedWidth) fun j =>
          (cols.pre j.val).eval (M.ext.toModel x) := by
    intro p x hx
    by_cases hnone : sys.preprocessedIndices.getD ci none = none
    · have hw : c.preprocessedWidth = 0 := hfixed ci (by rw [hnone]; rfl)
      have hrows : preprocessedRows sys proof ci = #[] := by rw [preprocessedRows, hnone]
      rw [hrows, getD_map_map, Array.getD_eq_getD_getElem?, Array.getElem?_empty,
        Option.getD_none, Array.map_empty]
      exact Array.ext (by rw [Array.size_ofFn, hw]; rfl) fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)
    · rcases hroot : sys.preprocessedCommit with _ | root
      · exact absurd (hnoCommit hroot) hnone
      · obtain ⟨ms3, hb3, hm3⟩ := openingClaims_fixed sys proof ζ hroot hp hci hnone
        have h := opened_row M sys.fri.logBlowup θ com huni heval hb3 hm3 hx (hrowsPre hnone)
        rw [hsh] at h
        rw [h, hcols]
        simp only [shardCols, hroot]
        rfl
  have hquot : ∀ i < c.quotientDegree * M.extData.d,
      (((proof.quotientOpened.getD pos #[]).getD 0 #[]).map M.ext.toModel).getD i 0 =
        (cols.quotient i).eval (M.ext.toModel ζ) := by
    intro i hi
    have h := opened_row M sys.fri.logBlowup θ com huni heval hb2 hm2 (p := 0) (x := ζ)
      (w := c.quotientDegree * M.extData.d) rfl (by rw [M.degree_eq]; exact hrowsQ)
    rw [hsh, getD_map_map] at h
    rw [h, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hi]
    rfl
  -- The executable check is the check on these values.
  have hcirc := (circuitOk_iff M _ _ _ _ _ _ _ _ _ _ _ _).mp
    (List.all_eq_true.mp hcheck (ci, pos) hp)
  have key := (circuitCheck_iff_eval M.base.toModel M.extData c hprim.pow_eq_one
    (hprim.ne_zero (pow_ne_zero _ two_ne_zero)) _ _ _ _ _
    ((zetaOk_model M proof ζ hzeta).2 pos hpos) cols (hpre 0 ζ rfl)
    (by have h := hpre 1 _ rfl; rwa [hnext] at h) (hmain 0 ζ rfl)
    (by have h := hmain 1 _ rfl; rwa [hnext] at h) (hs2 0 ζ rfl)
    (by have h := hs2 1 _ rfl; rwa [hnext] at h) hquot).mp hcirc
  have hpub : shardPublics M (M.ext.toModel β) (M.ext.toModel γ) (M.ext.toModel acc0)
      (proof.intermediateAccumulators.map M.ext.toModel) pos =
      M.extData.publics (M.ext.toModel β) (M.ext.toModel γ)
        (M.ext.toModel (if pos = 0 then acc0 else proof.intermediateAccumulators.getD (pos - 1) 0))
        (M.ext.toModel (proof.intermediateAccumulators.getD pos 0)) := by
    rw [shardPublics, accIn, accOut, toModel_getD_array_map, toModel_getD_array_map,
      apply_ite M.ext.toModel]
  rw [hpub]
  exact key

end CertiFri.Exec.Stark
