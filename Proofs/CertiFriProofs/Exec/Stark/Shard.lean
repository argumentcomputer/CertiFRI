import CertiFriProofs.Exec.Stark.Arith
import CertiFriProofs.Exec.Stark.Columns

/-!
# One proof of the STARK: its columns, its constraints, and the two bounds

Everything here is about one proof (one shard of a batch): the shape of its
opening claims, the polynomials its committed columns decode to, and the three
events the security proof follows through the rounds of the protocol.

## Contents

* `starkShape`: the shape of the opening claims of a proof, from the system,
  the activation bitmap and the trace heights. `claimShape_openingClaims`: it
  is the shape of `openingClaims` for a proof that passes `shapeOk`.
  `widthsUniform_openingClaims`: these claims give as many values at every
  point of a matrix as at its first.
* `exists_claimRef`: every value of nested opening claims is named by a
  `ClaimRef` of their shape.
* `shardCols`: the columns of an active circuit, as the polynomials its
  committed columns decode to. `accIn`, `accOut`: the lookup sums entering and
  leaving a circuit.
* `rowVals`: the constraint values of an active circuit at a point.
* `ConstraintFail`: some constraint value of some active circuit is not zero
  on some row of its trace domain. `AlphaFail`: the constraints of some active
  circuit, folded with `α`, are not zero on some row. `ZetaFail`: for some
  active circuit, the folded constraints at `ζ` are not the vanishing
  polynomial times the quotient at `ζ`.
* `constraintBound`, `zetaBound`: the numbers in the two error terms.
* `fractionLE_alphaFail`: if `ConstraintFail`, then `AlphaFail` for all but a
  fraction `(constraintBound - 1) / |K|` of the `α`.
* `fractionLE_zetaFail`: if `AlphaFail`, then `ZetaFail` for all but a fraction
  `zetaBound / |K|` of the `ζ`.

`Exec/Stark/Link.lean` relates `ZetaFail` to the opening claims.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri CertiFri.Oracle Polynomial

/-! ## Shapes -/

section Shape

variable {F D : Type}

/-- The shapes of the matrices of one commitment to traces: one per active
circuit, of the height of its trace. -/
def traceShapes (act : List ℕ) (logDegrees : Array ℕ) (width : ℕ → ℕ) (numPoints : ℕ) :
    List MatrixShape :=
  act.zipIdx.map fun p => ⟨logDegrees.getD p.2 0, width p.1, numPoints⟩

/-- The shapes of the fixed traces: one per circuit that has one, opened at two
points for an active circuit and at one for an inactive one. -/
def fixedShapes (sys : System F D) (act : List ℕ) (logDegrees : Array ℕ) : List MatrixShape :=
  (List.range sys.circuits.size).filterMap fun ci =>
    if (sys.preprocessedIndices.getD ci none).isNone then none
    else
      match act.idxOf? ci with
      | some pos =>
        some ⟨logDegrees.getD pos 0, (sys.circuits.getD ci default).preprocessedWidth, 2⟩
      | none =>
        some ⟨Nat.log2 (sys.circuits.getD ci default).preprocessedHeight,
          (sys.circuits.getD ci default).preprocessedWidth, 1⟩

/-- **The shape of the opening claims of a proof**, for an extension of degree
`d`: the main traces, the lookup traces and the quotients of the active
circuits, then the fixed traces if the system has any. -/
def starkShape (sys : System F D) (d : ℕ) (active : Array Bool) (logDegrees : Array ℕ) :
    ClaimShape :=
  [traceShapes (activeIndices active) logDegrees
      (fun ci => (sys.circuits.getD ci default).mainWidth) 2,
    traceShapes (activeIndices active) logDegrees
      (fun ci => (sys.circuits.getD ci default).stage2Width) 2,
    traceShapes (activeIndices active) logDegrees
      (fun ci => (sys.circuits.getD ci default).quotientDegree * d) 1]
    ++ match sys.preprocessedCommit with
      | some _ => [fixedShapes sys (activeIndices active) logDegrees]
      | none => []

/-- The position of the fixed trace of circuit `ci` among the fixed traces: the
number of circuits before it that have one. -/
def fixedRank (sys : System F D) (ci : ℕ) : ℕ :=
  ((List.range ci).filter fun c => (sys.preprocessedIndices.getD c none).isSome).length

/-- A circuit without a fixed trace has fixed-trace width zero. -/
def _root_.CertiFri.Stark.System.FixedOk (sys : System F D) : Prop :=
  ∀ ci, (sys.preprocessedIndices.getD ci none).isNone →
    (sys.circuits.getD ci default).preprocessedWidth = 0

/-- An entry of a list of numbers is at most their maximum. -/
private theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

/-- An active circuit of a bitmap no longer than the system is a circuit of
the system. -/
private theorem getD_mem_circuits {sys : System F D} {active : Array Bool}
    (hact : active.size ≤ sys.circuits.size) {p : ℕ × ℕ}
    (hp : p ∈ (activeIndices active).zipIdx) :
    sys.circuits.getD p.1 default ∈ sys.circuits.toList := by
  have hmem : p.1 ∈ activeIndices active :=
    List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hp)
  simp only [activeIndices, List.mem_filter, List.mem_range] at hmem
  have hlt : p.1 < sys.circuits.size := lt_of_lt_of_le hmem.1 hact
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some]
  exact Array.getElem_mem_toList hlt

end Shape

/-! ## The rows of a proof and the claims about one matrix -/

section Rows

variable {EF : Type}

/-- The claims about a matrix whose rows pass `rowsOk` for the number of its
opening points have the log-height, the width and the number of points of the
check. -/
private theorem shape_matrixOpening (k : ℕ) {points : List EF} {rows : Array (Array EF)} {w : ℕ}
    (hpts : points ≠ []) (h : rowsOk rows points.length w = true) :
    (⟨(matrixOpening k points rows).logDegree, claimedWidth (matrixOpening k points rows),
      (matrixOpening k points rows).points.size⟩ : MatrixShape) = ⟨k, w, points.length⟩ := by
  obtain ⟨rs⟩ := rows
  simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨hsize, hall⟩ := h
  cases points with
  | nil => exact absurd rfl hpts
  | cons p ps =>
    cases rs with
    | nil => simp at hsize
    | cons r rs =>
      have hr : r.size = w := hall r (by simp)
      have hlen : rs.length = ps.length := by simpa using hsize
      simp [matrixOpening, claimedWidth, hr, hlen]

/-- In the claims about a matrix whose rows pass `rowsOk`, every opening point
has as many values as the first. -/
private theorem uniform_matrixOpening (k : ℕ) (points : List EF) {rows : Array (Array EF)}
    {count w : ℕ} (h : rowsOk rows count w = true) :
    (matrixOpening k points rows).points.all
      (fun p => p.values.size == claimedWidth (matrixOpening k points rows)) = true := by
  simp only [rowsOk, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem] at h
  have hw : ∀ p ∈ (matrixOpening k points rows).points, p.values.size = w := by
    intro p hp
    simp only [matrixOpening, List.mem_toArray, List.mem_map] at hp
    obtain ⟨⟨x, row⟩, hmem, rfl⟩ := hp
    exact h.2 row (Array.mem_toList_iff.mp (List.of_mem_zip hmem).2)
  rw [Array.all_eq_true_iff_forall_mem]
  intro p hp
  obtain ⟨i, hi⟩ := Array.getElem?_of_mem hp
  have h0 : 0 < (matrixOpening k points rows).points.size := by
    have := (Array.getElem?_eq_some_iff.mp hi).1
    omega
  have hc : claimedWidth (matrixOpening k points rows) = w := by
    rw [claimedWidth, Array.getElem?_eq_getElem h0]
    exact hw _ (Array.getElem_mem h0)
  rw [hc, hw p hp]
  exact beq_self_eq_true w

/-- A circuit found among the active circuits is at the position it is found
at. -/
private theorem mem_zipIdx_of_idxOf? {act : List ℕ} {ci pos : ℕ}
    (h : act.idxOf? ci = some pos) : (ci, pos) ∈ act.zipIdx := by
  obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.mp h
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hlt, heq]

/-- The shapes of the claims about one commitment to traces of the active
circuits, each opened at `n` points. -/
private theorem map_shape_traces (act : List ℕ) (logDegrees : Array ℕ)
    (opened : Array (Array (Array EF))) (points : ℕ → List EF) (width : ℕ → ℕ) (n : ℕ)
    (hpts : ∀ k, points k ≠ [] ∧ (points k).length = n)
    (h : ∀ p ∈ act.zipIdx, rowsOk (opened.getD p.2 #[]) n (width p.1) = true) :
    (act.zipIdx.map fun p =>
        matrixOpening (logDegrees.getD p.2 0) (points (logDegrees.getD p.2 0))
          (opened.getD p.2 #[])).map
      (fun m => (⟨m.logDegree, claimedWidth m, m.points.size⟩ : MatrixShape)) =
      traceShapes act logDegrees width n := by
  rw [List.map_map, traceShapes]
  refine List.map_congr_left fun p hp => ?_
  have hs := shape_matrixOpening (logDegrees.getD p.2 0) (hpts (logDegrees.getD p.2 0)).1
    (rows := opened.getD p.2 #[]) (w := width p.1) (by rw [(hpts _).2]; exact h p hp)
  rw [(hpts _).2] at hs
  exact hs

end Rows

/-! ## Nested claims and the claims of their shape -/

section Flat

variable {EF D : Type}

/-- The element at position `k` of block `i` of a `flatMap` is at position `k`
after the blocks before block `i`. -/
private theorem getElem?_flatMap_add {α β : Type} (f : α → List β) {l : List α} {i k : ℕ}
    {a : α} {x : β} (hi : l[i]? = some a) (hk : (f a)[k]? = some x) :
    (l.flatMap f)[((l.take i).flatMap f).length + k]? = some x := by
  induction l generalizing i with
  | nil => cases hi
  | cons b l ih =>
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      rw [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add, List.flatMap_cons,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1]
      exact hk
    | succ i =>
      rw [List.getElem?_cons_succ] at hi
      rw [List.take_succ_cons, List.flatMap_cons, List.flatMap_cons, List.length_append,
        Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      exact ih hi

/-- The number of elements in the first blocks of a `flatMap` over indexed
elements, when the length of a block does not depend on the index. -/
private theorem length_flatMap_take_zipIdx {α β : Type} (f : α × ℕ → List β) (w : α → ℕ)
    (hf : ∀ x, (f x).length = w x.1) (l : List α) (i k : ℕ) :
    (((l.zipIdx k).take i).flatMap f).length = ((l.take i).map w).sum := by
  induction l generalizing i k with
  | nil => rw [List.zipIdx_nil, List.take_nil, List.take_nil, List.flatMap_nil, List.map_nil]; rfl
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.zipIdx_cons, List.take_succ_cons, List.take_succ_cons, List.flatMap_cons,
        List.length_append, List.map_cons, List.sum_cons, hf, ih]

/-- A `flatMap` over indexed elements that does not read the index. -/
private theorem flatMap_zipIdx_fst {α β : Type} (f : α → List β) (l : List α) (k : ℕ) :
    ((l.zipIdx k).flatMap fun x => f x.1) = l.flatMap f := by
  rw [← List.flatMap_map Prod.fst f, List.zipIdx_map_fst]

/-- Column `j` of the opening point at position `P` of a shape is a claim of
the shape, at the position after the columns of the points before. -/
private theorem mem_claimRefs_of_getElem? {lb : ℕ} {shape : ClaimShape} {P j : ℕ}
    {pr : PointRef} (hP : (pointRefs lb shape)[P]? = some pr) (hj : j < pr.width) :
    (⟨pr.batch, pr.matrix, j, pr.logHeight, P,
      (((pointRefs lb shape).take P).map (·.width)).sum + j⟩ : ClaimRef) ∈
      claimRefs lb shape := by
  have hget := getElem?_flatMap_add
    (fun x : PointRef × ℕ => (List.range x.1.width).map fun col => (x.1, x.2, col))
    (l := (pointRefs lb shape).zipIdx) (i := P) (a := (pr, P)) (k := j) (x := (pr, P, j))
    (by rw [List.getElem?_zipIdx, hP, Nat.zero_add]; rfl)
    (by rw [List.getElem?_map, List.getElem?_range hj]; rfl)
  rw [length_flatMap_take_zipIdx _ (·.width)
    (fun x => by rw [List.length_map, List.length_range])] at hget
  simp only [claimRefs, List.mem_map, List.mem_zipIdx_iff_getElem?]
  exact ⟨((pr, P, j), (((pointRefs lb shape).take P).map (·.width)).sum + j), hget, rfl⟩

/-- The opening points of nested claims, in the order batch, matrix, point,
each with the opening point of the shape of the claims at the same position. -/
private def pointPairs (lb : ℕ) (claims : Array (CommitmentOpening EF D)) :
    List (PointRef × PointOpening EF) :=
  claims.toList.zipIdx.flatMap fun c => c.1.matrices.toList.zipIdx.flatMap fun m =>
    m.1.points.toList.map fun po => (⟨c.2, m.2, m.1.logDegree + lb, claimedWidth m.1⟩, po)

/-- The first components of `pointPairs` are the opening points of the shape
of the claims. -/
private theorem map_fst_pointPairs (lb : ℕ) (claims : Array (CommitmentOpening EF D)) :
    (pointPairs lb claims).map Prod.fst = pointRefs lb (claimShape claims) := by
  rw [pointPairs, pointRefs, claimShape, List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr ?_
  rintro ⟨c, b⟩ -
  simp only [Prod.map_apply, id]
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr ?_
  rintro ⟨m, mi⟩ -
  simp only [Prod.map_apply, id, List.map_map]
  rw [← Array.length_toList, ← List.map_const']
  rfl

/-- A `flatMap` over the second components of `pointPairs` is one over the
opening points of the claims. -/
private theorem flatMap_snd_pointPairs {β : Type} (lb : ℕ)
    (claims : Array (CommitmentOpening EF D)) (g : PointOpening EF → List β) :
    ((pointPairs lb claims).flatMap fun x => g x.2) =
      claims.toList.flatMap fun c => c.matrices.toList.flatMap fun m =>
        m.points.toList.flatMap g := by
  rw [pointPairs, List.flatMap_assoc, ← flatMap_zipIdx_fst
    (fun c : CommitmentOpening EF D => c.matrices.toList.flatMap fun m =>
      m.points.toList.flatMap g) claims.toList 0]
  refine List.flatMap_congr fun c _ => ?_
  rw [List.flatMap_assoc, ← flatMap_zipIdx_fst
    (fun m : MatrixOpening EF => m.points.toList.flatMap g) c.1.matrices.toList 0]
  refine List.flatMap_congr fun m _ => ?_
  rw [List.flatMap_map]

/-- The opening points of nested claims are those of `pointPairs`. -/
private theorem claimPoints_eq (lb : ℕ) (claims : Array (CommitmentOpening EF D)) :
    claimPoints claims = ((pointPairs lb claims).map fun x => x.2.point).toArray := by
  rw [claimPoints, List.map_eq_flatMap, flatMap_snd_pointPairs lb claims fun po => [po.point]]
  simp only [List.map_eq_flatMap]

/-- The claimed values of nested claims are those of `pointPairs`. -/
private theorem claimValues_eq (lb : ℕ) (claims : Array (CommitmentOpening EF D)) :
    claimValues claims = ((pointPairs lb claims).flatMap fun x => x.2.values.toList).toArray := by
  rw [claimValues, flatMap_snd_pointPairs lb claims fun po => po.values.toList]

/-- With uniform widths, an opening point of the shape of nested claims has the
width of the values claimed at it. -/
private theorem width_of_mem_pointPairs (lb : ℕ) {claims : Array (CommitmentOpening EF D)}
    (huni : widthsUniform claims = true) {x : PointRef × PointOpening EF}
    (hx : x ∈ pointPairs lb claims) : x.1.width = x.2.values.size := by
  simp only [pointPairs, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨⟨c, b⟩, hc, ⟨m, mi⟩, hm, po, hpo, rfl⟩ := hx
  simp only [widthsUniform, Array.all_eq_true_iff_forall_mem, beq_iff_eq] at huni
  exact (huni c
    (Array.mem_toList_iff.mp (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hc))) m
    (Array.mem_toList_iff.mp (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hm))) po
    (Array.mem_toList_iff.mp hpo)).symm

/-- Point `p` of matrix `mi` of commitment `b` of nested claims is in
`pointPairs`, with the opening point of the shape for that matrix. -/
private theorem mem_pointPairs (lb : ℕ) {claims : Array (CommitmentOpening EF D)} {b mi p : ℕ}
    {c : CommitmentOpening EF D} {m : MatrixOpening EF} {po : PointOpening EF}
    (hb : claims[b]? = some c) (hm : c.matrices[mi]? = some m) (hp : m.points[p]? = some po) :
    (⟨b, mi, m.logDegree + lb, claimedWidth m⟩, po) ∈ pointPairs lb claims := by
  simp only [pointPairs, List.mem_flatMap, List.mem_map]
  exact ⟨(c, b), List.mem_zipIdx_iff_getElem?.mpr (by rw [Array.getElem?_toList]; exact hb),
    (m, mi), List.mem_zipIdx_iff_getElem?.mpr (by rw [Array.getElem?_toList]; exact hm), po,
    Array.mem_toList_iff.mpr (Array.mem_of_getElem? hp), rfl⟩

end Flat

section Claims

variable {F EF D : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]

omit [TwoAdicOps F] in
/-- What the shape check says about the rows opened for an active circuit:
two rows of the main trace and of the lookup trace, one of the quotient, and
two of the fixed trace if the circuit has one, each of the width of its
matrix. -/
private theorem rowsOk_of_shapeOk {InputProof CommitProof : Type} {sys : System F D}
    {proof : Proof F EF D InputProof CommitProof} (h : Stark.shapeOk sys proof = true)
    {p : ℕ × ℕ} (hp : p ∈ (activeIndices proof.active).zipIdx) :
    rowsOk (proof.stage1Opened.getD p.2 #[]) 2 (sys.circuits.getD p.1 default).mainWidth = true ∧
      rowsOk (proof.stage2Opened.getD p.2 #[]) 2
        (sys.circuits.getD p.1 default).stage2Width = true ∧
      rowsOk (proof.quotientOpened.getD p.2 #[]) 1
        ((sys.circuits.getD p.1 default).quotientDegree *
          ExtensionOps.degree (F := F) (EF := EF)) = true ∧
      ((sys.preprocessedIndices.getD p.1 none).isNone = false →
        rowsOk (preprocessedRows sys proof p.1) 2
          (sys.circuits.getD p.1 default).preprocessedWidth = true) := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true] at h
  have hp' := h.2 p hp
  simp only [Bool.or_eq_true] at hp'
  obtain ⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩ := hp'
  refine ⟨h1, h2, h4, fun hn => ?_⟩
  rcases h3 with h3 | h3
  · rw [hn] at h3
    cases h3
  · exact h3

omit [TwoAdicOps F] in
/-- What the shape check says about the rows opened for the fixed trace of an
inactive circuit: one row of the width of the fixed trace. -/
private theorem rowsOk_fixed_of_shapeOk {InputProof CommitProof : Type} {sys : System F D}
    {proof : Proof F EF D InputProof CommitProof} (h : Stark.shapeOk sys proof = true)
    {ci : ℕ} (hci : ci < sys.circuits.size) (hact : ci ∉ activeIndices proof.active)
    (hn : (sys.preprocessedIndices.getD ci none).isNone = false) :
    rowsOk (preprocessedRows sys proof ci) 1
      (sys.circuits.getD ci default).preprocessedWidth = true := by
  simp only [Stark.shapeOk, Bool.and_eq_true, List.all_eq_true] at h
  have hc := h.1.2 ci (List.mem_range.mpr hci)
  simp only [Bool.or_eq_true] at hc
  rcases hc with (hc | hc) | hc
  · refine absurd ?_ hact
    simp only [activeIndices, List.mem_filter, List.mem_range]
    refine ⟨?_, hc⟩
    by_contra hlt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hc
    cases hc
  · rw [hn] at hc
    cases hc
  · exact hc

/-- The opening claims of a proof that passes the shape check have the shape
`starkShape`. -/
theorem claimShape_openingClaims {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (h : shapeOk sys proof = true) (ζ : EF) :
    claimShape (openingClaims sys proof ζ) =
      starkShape sys (ExtensionOps.degree (F := F) (EF := EF)) proof.active proof.logDegrees := by
  have h1 := map_shape_traces (activeIndices proof.active) proof.logDegrees proof.stage1Opened
    (fun k => [ζ, nextPoint (F := F) k ζ]) (fun ci => (sys.circuits.getD ci default).mainWidth) 2
    (fun _ => ⟨List.cons_ne_nil _ _, rfl⟩) fun p hp => (rowsOk_of_shapeOk h hp).1
  have h2 := map_shape_traces (activeIndices proof.active) proof.logDegrees proof.stage2Opened
    (fun k => [ζ, nextPoint (F := F) k ζ]) (fun ci => (sys.circuits.getD ci default).stage2Width)
    2 (fun _ => ⟨List.cons_ne_nil _ _, rfl⟩) fun p hp => (rowsOk_of_shapeOk h hp).2.1
  have h3 := map_shape_traces (activeIndices proof.active) proof.logDegrees proof.quotientOpened
    (fun _ => [ζ])
    (fun ci => (sys.circuits.getD ci default).quotientDegree *
      ExtensionOps.degree (F := F) (EF := EF)) 1
    (fun _ => ⟨List.cons_ne_nil _ _, rfl⟩) fun p hp => (rowsOk_of_shapeOk h hp).2.2.1
  simp only [openingClaims, claimShape, starkShape]
  cases sys.preprocessedCommit with
  | none =>
    simp only [Array.append_empty, List.append_nil, List.map_cons, List.map_nil]
    rw [h1, h2, h3]
  | some c =>
    simp only [Array.toList_append, List.map_append, List.map_cons, List.map_nil]
    rw [h1, h2, h3, List.map_filterMap, fixedShapes]
    refine congrArg (fun x => _ ++ [x]) (List.filterMap_congr fun ci hci => ?_)
    by_cases hn : (sys.preprocessedIndices.getD ci none).isNone = true
    · rw [ite_eq_left hn, ite_eq_left hn]
      rfl
    · rw [ite_eq_right hn, ite_eq_right hn]
      rw [Bool.not_eq_true] at hn
      cases hidx : (activeIndices proof.active).idxOf? ci with
      | some pos =>
        exact congrArg some (shape_matrixOpening _ (List.cons_ne_nil _ _)
          ((rowsOk_of_shapeOk h (mem_zipIdx_of_idxOf? hidx)).2.2.2 hn))
      | none =>
        exact congrArg some (shape_matrixOpening _ (List.cons_ne_nil _ _)
          (rowsOk_fixed_of_shapeOk h (List.mem_range.mp hci)
            (List.idxOf?_eq_none_iff.mp hidx) hn))

/-- Every matrix of the opening claims of a proof that passes the shape check
is given by rows that pass `rowsOk`. -/
private theorem exists_rowsOk_of_mem_openingClaims {InputProof CommitProof : Type}
    {sys : System F D} {proof : Proof F EF D InputProof CommitProof}
    (h : Stark.shapeOk sys proof = true) {ζ : EF} {c : CommitmentOpening EF D}
    (hc : c ∈ openingClaims sys proof ζ) {m : MatrixOpening EF} (hm : m ∈ c.matrices) :
    ∃ k points rows count w, m = matrixOpening k points rows ∧ rowsOk rows count w = true := by
  simp only [openingClaims, Array.mem_append, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with (rfl | rfl | rfl) | hc
  · simp only [List.mem_toArray, List.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact ⟨_, _, _, _, _, rfl, (rowsOk_of_shapeOk h hp).1⟩
  · simp only [List.mem_toArray, List.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact ⟨_, _, _, _, _, rfl, (rowsOk_of_shapeOk h hp).2.1⟩
  · simp only [List.mem_toArray, List.mem_map] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    exact ⟨_, _, _, _, _, rfl, (rowsOk_of_shapeOk h hp).2.2.1⟩
  · split at hc
    · simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp only [List.mem_toArray, List.mem_filterMap, List.mem_range] at hm
      obtain ⟨ci, hci, hm⟩ := hm
      by_cases hn : (sys.preprocessedIndices.getD ci none).isNone = true
      · rw [ite_eq_left hn] at hm
        cases hm
      · rw [ite_eq_right hn] at hm
        rw [Bool.not_eq_true] at hn
        cases hidx : (activeIndices proof.active).idxOf? ci with
        | some pos =>
          rw [hidx, Option.some.injEq] at hm
          exact ⟨_, _, _, _, _, hm.symm,
            (rowsOk_of_shapeOk h (mem_zipIdx_of_idxOf? hidx)).2.2.2 hn⟩
        | none =>
          rw [hidx, Option.some.injEq] at hm
          exact ⟨_, _, _, _, _, hm.symm,
            rowsOk_fixed_of_shapeOk h hci (List.idxOf?_eq_none_iff.mp hidx) hn⟩
    · exact absurd hc (Array.not_mem_empty c)

/-- The opening claims of a proof that passes the shape check have as many
values at every point of a matrix as at its first. -/
theorem widthsUniform_openingClaims {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (h : shapeOk sys proof = true) (ζ : EF) :
    widthsUniform (openingClaims sys proof ζ) = true := by
  rw [widthsUniform, Array.all_eq_true_iff_forall_mem]
  intro c hc
  rw [Array.all_eq_true_iff_forall_mem]
  intro m hm
  obtain ⟨k, points, rows, count, w, rfl, hrows⟩ := exists_rowsOk_of_mem_openingClaims h hc hm
  exact uniform_matrixOpening k points hrows

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] in
/-- **Every value of nested claims is named by a claim of their shape.** For
value `j` at point `p` of matrix `mi` of commitment `b`, there is a `ClaimRef`
of the shape of the claims with that batch, matrix and column, whose opening
point and claimed value, read in the flat lists of points and values, are that
point and that value. -/
theorem exists_claimRef [Inhabited EF] (lb : ℕ) (claims : Array (CommitmentOpening EF D))
    (huni : widthsUniform claims = true) {b mi p j : ℕ} {c : CommitmentOpening EF D}
    {m : MatrixOpening EF} {po : PointOpening EF} (hb : claims[b]? = some c)
    (hm : c.matrices[mi]? = some m) (hp : m.points[p]? = some po) (hj : j < po.values.size) :
    ∃ r ∈ claimRefs lb (claimShape claims), r.batch = b ∧ r.matrix = mi ∧ r.col = j ∧
      r.logHeight = m.logDegree + lb ∧
      (claimPoints claims).getD r.pointIdx default = po.point ∧
      (claimValues claims).getD r.valueIdx default = po.values.getD j default := by
  have hmem := mem_pointPairs lb hb hm hp
  obtain ⟨P, hP⟩ := List.getElem?_of_mem hmem
  have hpr : (pointRefs lb (claimShape claims))[P]? =
      some ⟨b, mi, m.logDegree + lb, claimedWidth m⟩ := by
    rw [← map_fst_pointPairs, List.getElem?_map, hP]
    rfl
  have hjw : j < claimedWidth m := by
    rw [show claimedWidth m = po.values.size from width_of_mem_pointPairs lb huni hmem]
    exact hj
  -- The values before the point: as many as the columns of the points before.
  have hsum : (((pointRefs lb (claimShape claims)).take P).map (·.width)).sum =
      (((pointPairs lb claims).take P).flatMap fun x => x.2.values.toList).length := by
    rw [← map_fst_pointPairs, List.length_flatMap, ← List.map_take, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
    rw [Array.length_toList]
    exact width_of_mem_pointPairs lb huni (List.mem_of_mem_take hx)
  refine ⟨_, mem_claimRefs_of_getElem? hpr hjw, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [claimPoints_eq lb, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      hP]
    rfl
  · rw [claimValues_eq lb, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hsum,
      getElem?_flatMap_add _ hP (x := po.values[j])
        (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hj]),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]

end Claims

/-! ## The columns and the constraints of one proof -/

section Shard

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] (M : StarkModel F EF K) (sys : System F D) (θ : ℝ)
  (com : Compiled.Committed K D)

/-- The columns of the active circuit `ci`, at position `pos` among the active
circuits: the polynomials that its columns decode to under the commitments to
the main traces, the lookup traces, the quotients and the fixed traces. -/
noncomputable def shardCols (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (pos ci : ℕ) : Columns K where
  main := fun j => M.colPoly sys.fri.logBlowup θ com stage1
    (batchDims sys.fri.logBlowup ((starkShape sys M.extData.d active logDegrees).getD 0 []))
    pos j (logDegrees.getD pos 0 + sys.fri.logBlowup)
  stage2 := fun j => M.colPoly sys.fri.logBlowup θ com stage2
    (batchDims sys.fri.logBlowup ((starkShape sys M.extData.d active logDegrees).getD 1 []))
    pos j (logDegrees.getD pos 0 + sys.fri.logBlowup)
  quotient := fun j => M.colPoly sys.fri.logBlowup θ com quot
    (batchDims sys.fri.logBlowup ((starkShape sys M.extData.d active logDegrees).getD 2 []))
    pos j (logDegrees.getD pos 0 + sys.fri.logBlowup)
  pre := fun j =>
    match sys.preprocessedCommit with
    | some root => M.colPoly sys.fri.logBlowup θ com root
        (batchDims sys.fri.logBlowup ((starkShape sys M.extData.d active logDegrees).getD 3 []))
        (fixedRank sys ci) j (logDegrees.getD pos 0 + sys.fri.logBlowup)
    | none => 0

/-- The lookup sum entering the circuit at position `pos`: `acc0` for the first
circuit, the sum leaving the previous circuit for the others. -/
def accIn (acc0 : K) (accs : Array K) (pos : ℕ) : K :=
  if pos = 0 then acc0 else accs.getD (pos - 1) 0

/-- The lookup sum leaving the circuit at position `pos`. -/
def accOut (accs : Array K) (pos : ℕ) : K := accs.getD pos 0

/-- The public values of the circuit at position `pos`. -/
def shardPublics (β γ acc0 : K) (accs : Array K) (pos : ℕ) : Array K :=
  M.extData.publics β γ (accIn acc0 accs pos) (accOut accs pos)

/-- The constraint values of the active circuit `ci`, at position `pos`, at the
point `x`: the zeros of its graph and its lookup constraints, on the values of
its columns at `x` and at the successor of `x`. -/
noncomputable def rowVals (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (β γ acc0 : K) (accs : Array K) (pos ci : ℕ) (x : K) : Array K :=
  constraintVals M.base.toModel M.extData.d M.extData.table (sys.circuits.getD ci default)
    (pointRow (sys.circuits.getD ci default) (2 ^ logDegrees.getD pos 0)
      (M.gen (logDegrees.getD pos 0))
      (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci)
      (shardPublics M β γ acc0 accs pos) x)
    (deltaScaled M.extData.d (2 ^ logDegrees.getD pos 0) (M.gen (logDegrees.getD pos 0))
      (shardPublics M β γ acc0 accs pos))

/-- Some constraint value of some active circuit is not zero on some row of its
trace domain. -/
def ConstraintFail (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (β γ acc0 : K) (accs : Array K) : Prop :=
  ∃ p ∈ (activeIndices active).zipIdx, ∃ r < 2 ^ logDegrees.getD p.2 0, ∃ idx,
    (rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs p.2 p.1
      (M.gen (logDegrees.getD p.2 0) ^ r)).getD idx 0 ≠ 0

/-- The constraints of some active circuit, folded with `α`, are not zero on
some row of its trace domain. -/
def AlphaFail (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (β γ acc0 : K) (accs : Array K) (α : K) : Prop :=
  ∃ p ∈ (activeIndices active).zipIdx, ∃ r < 2 ^ logDegrees.getD p.2 0,
    foldAlpha α (rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs p.2 p.1
      (M.gen (logDegrees.getD p.2 0) ^ r)) ≠ 0

/-- For some active circuit, the folded constraints at `ζ` are not the
vanishing polynomial of the trace domain times the quotient at `ζ`. -/
def ZetaFail (active : Array Bool) (logDegrees : Array ℕ) (stage1 stage2 quot : D)
    (β γ acc0 : K) (accs : Array K) (α ζ : K) : Prop :=
  ∃ p ∈ (activeIndices active).zipIdx,
    (compPoly M.base.toModel M.extData.d M.extData.table (sys.circuits.getD p.1 default)
        (2 ^ logDegrees.getD p.2 0) (M.gen (logDegrees.getD p.2 0))
        (shardCols M sys θ com active logDegrees stage1 stage2 quot p.2 p.1)
        (shardPublics M β γ acc0 accs p.2)
        (deltaScaled M.extData.d (2 ^ logDegrees.getD p.2 0) (M.gen (logDegrees.getD p.2 0))
          (shardPublics M β γ acc0 accs p.2)) α).eval ζ ≠
      (ζ ^ 2 ^ logDegrees.getD p.2 0 - 1) *
        (quotientPoly M.extData.basis M.extData.d (2 ^ logDegrees.getD p.2 0)
          (sys.circuits.getD p.1 default).quotientDegree
          (shardCols M sys θ com active logDegrees stage1 stage2 quot p.2 p.1)).eval ζ

/-- The largest number of constraint values of a circuit of the system, for an
extension of degree `d`. -/
def constraintBound (sys : System F D) (d : ℕ) : ℕ :=
  (sys.circuits.toList.map fun c =>
    c.graph.zeros.size + lookupGroups c.graph.lookups.size c.lookupGroupSize * d).foldr max 0

/-- The largest degree of the polynomial the check at `ζ` is about, over the
circuits of the system and the supported trace heights. -/
def zetaBound (sys : System F D) : ℕ :=
  (sys.circuits.toList.map fun c =>
    ((List.range (sys.maxLogDegree + 1)).map fun k => c.zetaDegree (2 ^ k) (2 ^ k)).foldr max
      0).foldr max 0

/-- The columns of an active circuit have degree at most the height of its
trace. -/
private theorem degLE_shardCols (active : Array Bool) (logDegrees : Array ℕ)
    (stage1 stage2 quot : D) (pos ci : ℕ) :
    (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci).DegLE
      (2 ^ logDegrees.getD pos 0) := by
  have hcol : ∀ root dims mi col,
      (M.colPoly sys.fri.logBlowup θ com root dims mi col
        (logDegrees.getD pos 0 + sys.fri.logBlowup)).natDegree ≤ 2 ^ logDegrees.getD pos 0 := by
    intro root dims mi col
    have h := M.natDegree_colPoly_le sys.fri.logBlowup θ com root dims mi col
      (logDegrees.getD pos 0 + sys.fri.logBlowup)
    rwa [Nat.add_sub_cancel] at h
  refine ⟨fun j => ?_, fun j => hcol _ _ _ _, fun j => hcol _ _ _ _, fun j => hcol _ _ _ _⟩
  rw [shardCols]
  split
  · exact hcol _ _ _ _
  · rw [natDegree_zero]
    exact Nat.zero_le _

variable {M sys θ com}

/-- **The constraint challenge.** If some constraint fails on some row, then
for all but a fraction `(constraintBound - 1) / |K|` of the challenges `α` the
folded constraints of some circuit are not zero on some row. -/
theorem fractionLE_alphaFail [Fintype K] {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} {β γ acc0 : K} {accs : Array K}
    (hact : active.size ≤ sys.circuits.size)
    (h : ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs) :
    FractionLE
      (fun α : K => ¬ AlphaFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs α)
      ((constraintBound sys M.extData.d - 1 : ℕ) / Fintype.card K) := by
  obtain ⟨p, hp, r, hr, idx, hne⟩ := h
  refine ((fractionLE_foldAlpha _ ⟨idx, hne⟩).mono_left fun α hα => ?_).mono_right ?_
  · by_contra hfold
    exact hα ⟨p, hp, r, hr, hfold⟩
  · refine div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_right ?_ 1))
      (Nat.cast_nonneg _)
    rw [rowVals, size_constraintVals]
    exact le_foldr_max (List.mem_map_of_mem
      (f := fun c : Circuit F =>
        c.graph.zeros.size + lookupGroups c.graph.lookups.size c.lookupGroupSize * M.extData.d)
      (getD_mem_circuits hact hp))

/-- **The out-of-domain point.** If the folded constraints of some circuit are
not zero on some row, then for all but a fraction `zetaBound / |K|` of the
points `ζ` the check at `ζ` fails for some circuit. -/
theorem fractionLE_zetaFail [Fintype K] {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} {β γ acc0 : K} {accs : Array K} {α : K}
    (hact : active.size ≤ sys.circuits.size)
    (hdeg : ∀ pos, logDegrees.getD pos 0 ≤ sys.maxLogDegree)
    (htwo : sys.maxLogDegree ≤ TwoAdicOps.twoAdicity (F := F))
    (h : AlphaFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs α) :
    FractionLE
      (fun ζ : K =>
        ¬ ZetaFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs α ζ)
      (zetaBound sys / Fintype.card K) := by
  obtain ⟨p, hp, r, -, hne⟩ := h
  have hk := hdeg p.2
  have hprim : IsPrimitiveRoot (M.gen (logDegrees.getD p.2 0)) (2 ^ logDegrees.getD p.2 0) :=
    M.generator _ (hk.trans htwo)
  refine ((fractionLE_zeta (n := 2 ^ logDegrees.getD p.2 0) M.base.toModel M.extData.basis
    M.extData.d M.extData.table (sys.circuits.getD p.1 default) (M.gen (logDegrees.getD p.2 0))
    (degLE_shardCols M sys θ com active logDegrees stage1 stage2 quot p.2 p.1)
    (shardPublics M β γ acc0 accs p.2)
    (deltaScaled M.extData.d (2 ^ logDegrees.getD p.2 0) (M.gen (logDegrees.getD p.2 0))
      (shardPublics M β γ acc0 accs p.2)) α
    ⟨M.gen (logDegrees.getD p.2 0) ^ r, ?_, ?_⟩).mono_left fun ζ hζ => ?_).mono_right ?_
  · rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
  · rw [eval_compPoly]
    exact hne
  · by_contra hfail
    exact hζ ⟨p, hp, hfail⟩
  · refine div_le_div_of_nonneg_right (Nat.cast_le.mpr ?_) (Nat.cast_nonneg _)
    exact (le_foldr_max (List.mem_map_of_mem
      (f := fun k => (sys.circuits.getD p.1 default).zetaDegree (2 ^ k) (2 ^ k))
      (List.mem_range.mpr (Nat.lt_succ_of_le hk)))).trans
      (le_foldr_max (List.mem_map_of_mem
        (f := fun c : Circuit F =>
          ((List.range (sys.maxLogDegree + 1)).map fun k =>
            c.zetaDegree (2 ^ k) (2 ^ k)).foldr max 0)
        (getD_mem_circuits hact hp)))

end Shard

end CertiFri.Exec.Stark
