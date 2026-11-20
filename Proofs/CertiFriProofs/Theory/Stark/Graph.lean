import Mathlib
import CertiFri.Stark.Graph

/-!
# Constraint graphs over a commutative ring

The executable verifier evaluates a constraint graph on the values of two
adjacent rows (`Graph.sweep`, `CertiFri/Stark/Graph.lean`), over an executable
field. Here the same computation is defined over any commutative ring `R`, with
a map `ι : F → R` for the constants of the graph. Three rings are used:

* the model field `K`, for the values the verifier computes at the
  out-of-domain point and for the values on a row of a trace;
* the polynomial ring `K[X]`, where a column is a polynomial and the value of a
  node is the polynomial the constraint is as a function of the row.

A ring homomorphism commutes with the computation (`map_sweep`), which relates
the two: evaluating the polynomial of a node at a point gives the value of the
node on the evaluations of the columns.

## Contents

* `mapRow`, `varVal`, `nodeVal`, `sweep`: the computation, written as in the
  executable code. A read outside an array gives zero.
* `size_sweep`: there is one value per node.
* `map_sweep`: a ring homomorphism commutes with `sweep`.
* `Node.Plain`, `RowAgree`, `getD_sweep_congr_of_plain`: the values of a prefix
  of nodes that read neither the lookup trace nor the public values depend
  only on the fixed trace, the main trace and the selectors.
* `nodeDeg`, `sweepDeg`, `natDegree_sweep_le`: for polynomial rows, a bound on
  the degree of every node, computed by the same sweep over the natural
  numbers with `max` for sums and `+` for products.

Nothing here is about a protocol.
-/

namespace CertiFri.Stark.Model

open Polynomial

variable {F R S : Type}

/-- Apply a function to every value of a row. -/
def mapRow (φ : R → S) (v : RowValues R) : RowValues S where
  preprocessed := v.preprocessed.map φ
  preprocessedNext := v.preprocessedNext.map φ
  main := v.main.map φ
  mainNext := v.mainNext.map φ
  stage2 := v.stage2.map φ
  stage2Next := v.stage2Next.map φ
  publics := v.publics.map φ
  isFirstRow := φ v.isFirstRow
  isLastRow := φ v.isLastRow
  isTransition := φ v.isTransition

section Ring

variable [CommRing R] [CommRing S]

/-- The value of a column variable; zero if the row has no such column. -/
def varVal (v : RowValues R) (col : ColRef) : R :=
  (match col.source, col.next with
    | .preprocessed, false => v.preprocessed
    | .preprocessed, true => v.preprocessedNext
    | .main, false => v.main
    | .main, true => v.mainNext
    | .stage2, false => v.stage2
    | .stage2, true => v.stage2Next).getD col.index 0

/-- The value of one node, given the values `buf` of the nodes before it. The
constants of the graph are read through `ι`. -/
def nodeVal (ι : F → R) (v : RowValues R) (buf : Array R) : Node F → R
  | .const c => ι c
  | .var col => varVal v col
  | .pub index => v.publics.getD index 0
  | .isFirstRow => v.isFirstRow
  | .isLastRow => v.isLastRow
  | .isTransition => v.isTransition
  | .add a b => buf.getD a 0 + buf.getD b 0
  | .sub a b => buf.getD a 0 - buf.getD b 0
  | .mul a b => buf.getD a 0 * buf.getD b 0
  | .neg a => -buf.getD a 0

/-- The values of all nodes, first to last. -/
def sweep (ι : F → R) (nodes : Array (Node F)) (v : RowValues R) : Array R :=
  nodes.foldl (fun buf node => buf.push (nodeVal ι v buf node)) #[]

/-- A read of a buffer after a push: the pushed value at the old size, the old
read elsewhere. -/
private theorem getD_push {α : Type} (buf : Array α) (x d : α) (i : ℕ) :
    (buf.push x).getD i d = if i = buf.size then x else buf.getD i d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split <;> rfl

/-- A fold that pushes one value per element adds as many values as there are
elements. -/
private theorem size_foldl_push {α β : Type} (g : Array β → α → β) (l : List α)
    (buf : Array β) :
    (l.foldl (fun buf x => buf.push (g buf x)) buf).size = buf.size + l.length := by
  induction l generalizing buf with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, ih, Array.size_push, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

/-- There is one value per node. -/
theorem size_sweep (ι : F → R) (nodes : Array (Node F)) (v : RowValues R) :
    (sweep ι nodes v).size = nodes.size := by
  rw [sweep, ← Array.foldl_toList, size_foldl_push, Array.size_empty, Nat.zero_add,
    Array.length_toList]

/-- A read of a mapped buffer is the image of the read: the map sends zero to
zero. -/
private theorem getD_map_zero (φ : R →+* S) (buf : Array R) (i : ℕ) :
    (buf.map φ).getD i 0 = φ (buf.getD i 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases buf[i]? with
  | none => exact (map_zero φ).symm
  | some x => rfl

/-- The value of a column variable of a mapped row is the image of its value. -/
theorem varVal_mapRow (φ : R →+* S) (v : RowValues R) (col : ColRef) :
    varVal (mapRow φ v) col = φ (varVal v col) := by
  obtain ⟨source, next, index⟩ := col
  cases source <;> cases next <;> exact getD_map_zero φ _ index

/-- The value of a node on the image of a row, given the images of the values
before it, is the image of its value. -/
private theorem nodeVal_mapRow (φ : R →+* S) (ι : F → R) (v : RowValues R) (buf : Array R)
    (node : Node F) :
    nodeVal (fun c => φ (ι c)) (mapRow φ v) (buf.map φ) node = φ (nodeVal ι v buf node) := by
  cases node with
  | const c => rfl
  | var col => exact varVal_mapRow φ v col
  | pub index => exact getD_map_zero φ v.publics index
  | isFirstRow => rfl
  | isLastRow => rfl
  | isTransition => rfl
  | add a b => simp only [nodeVal, getD_map_zero, map_add]
  | sub a b => simp only [nodeVal, getD_map_zero, map_sub]
  | mul a b => simp only [nodeVal, getD_map_zero, map_mul]
  | neg a => simp only [nodeVal, getD_map_zero, map_neg]

/-- `map_sweep`, for the fold over a list of nodes from any buffer. -/
private theorem map_foldl_nodeVal (φ : R →+* S) (ι : F → R) (v : RowValues R)
    (l : List (Node F)) (buf : Array R) :
    (l.foldl (fun buf node => buf.push (nodeVal ι v buf node)) buf).map φ =
      l.foldl (fun buf node => buf.push (nodeVal (fun c => φ (ι c)) (mapRow φ v) buf node))
        (buf.map φ) := by
  induction l generalizing buf with
  | nil => rfl
  | cons node l ih => rw [List.foldl_cons, List.foldl_cons, ih, Array.map_push, nodeVal_mapRow]

/-- A ring homomorphism commutes with the evaluation of a graph: the values of
the nodes on the image of a row are the images of the values on the row. -/
theorem map_sweep (φ : R →+* S) (ι : F → R) (nodes : Array (Node F)) (v : RowValues R) :
    (sweep ι nodes v).map φ = sweep (fun c => φ (ι c)) nodes (mapRow φ v) := by
  rw [sweep, sweep, ← Array.foldl_toList, ← Array.foldl_toList, map_foldl_nodeVal,
    Array.map_empty]

/-- `map_sweep`, for one node. -/
theorem getD_sweep_mapRow (φ : R →+* S) (ι : F → R) (nodes : Array (Node F)) (v : RowValues R)
    (i : ℕ) :
    (sweep (fun c => φ (ι c)) nodes (mapRow φ v)).getD i 0 = φ ((sweep ι nodes v).getD i 0) := by
  rw [← map_sweep, getD_map_zero]

/-! ## Nodes that do not read the lookup trace or the public values -/

/-- The node reads neither a column of the lookup trace nor a public value. -/
def _root_.CertiFri.Stark.Node.Plain : Node F → Prop
  | .var col => col.source ≠ .stage2
  | .pub _ => False
  | _ => True

/-- Two rows have the same fixed trace, main trace and selectors. They may
differ in the lookup trace and in the public values. -/
structure RowAgree (v v' : RowValues R) : Prop where
  /-- The fixed trace. -/
  preprocessed : v.preprocessed = v'.preprocessed
  /-- The fixed trace, next row. -/
  preprocessedNext : v.preprocessedNext = v'.preprocessedNext
  /-- The main trace. -/
  main : v.main = v'.main
  /-- The main trace, next row. -/
  mainNext : v.mainNext = v'.mainNext
  /-- The first-row selector. -/
  isFirstRow : v.isFirstRow = v'.isFirstRow
  /-- The last-row selector. -/
  isLastRow : v.isLastRow = v'.isLastRow
  /-- The transition selector. -/
  isTransition : v.isTransition = v'.isTransition

/-- A column variable outside the lookup trace has the same value on two rows
that agree. -/
private theorem varVal_congr_of_agree {v v' : RowValues R} (h : RowAgree v v') {col : ColRef}
    (hcol : col.source ≠ .stage2) : varVal v col = varVal v' col := by
  obtain ⟨source, next, index⟩ := col
  cases source with
  | preprocessed =>
    cases next with
    | false => exact congrArg (fun row => row.getD index 0) h.preprocessed
    | true => exact congrArg (fun row => row.getD index 0) h.preprocessedNext
  | main =>
    cases next with
    | false => exact congrArg (fun row => row.getD index 0) h.main
    | true => exact congrArg (fun row => row.getD index 0) h.mainNext
  | stage2 => exact absurd rfl hcol

/-- A plain node has the same value on two rows that agree, given buffers with
the same reads. -/
private theorem nodeVal_congr_of_plain (ι : F → R) {v v' : RowValues R} (h : RowAgree v v')
    {buf buf' : Array R} (hbuf : ∀ i, buf.getD i 0 = buf'.getD i 0) {node : Node F}
    (hnode : node.Plain) : nodeVal ι v buf node = nodeVal ι v' buf' node := by
  cases node with
  | const c => rfl
  | var col => exact varVal_congr_of_agree h hnode
  | pub index => exact hnode.elim
  | isFirstRow => exact h.isFirstRow
  | isLastRow => exact h.isLastRow
  | isTransition => exact h.isTransition
  | add a b => simp only [nodeVal, hbuf]
  | sub a b => simp only [nodeVal, hbuf]
  | mul a b => simp only [nodeVal, hbuf]
  | neg a => simp only [nodeVal, hbuf]

/-- `getD_sweep_congr_of_plain`, for the fold over a list of nodes from two
buffers of the same size that agree below `k`. The node at position `j` of the
list is the node `buf.size + j` of the graph. -/
private theorem getD_foldl_congr_of_plain (ι : F → R) {v v' : RowValues R} (h : RowAgree v v')
    (k : ℕ) (l : List (Node F)) (buf buf' : Array R) (hsize : buf.size = buf'.size)
    (hbuf : ∀ i < k, buf.getD i 0 = buf'.getD i 0)
    (hplain : ∀ j, buf.size + j < k → ∀ node, l[j]? = some node → node.Plain) {i : ℕ}
    (hi : i < k) :
    (l.foldl (fun buf node => buf.push (nodeVal ι v buf node)) buf).getD i 0 =
      (l.foldl (fun buf node => buf.push (nodeVal ι v' buf node)) buf').getD i 0 := by
  induction l generalizing buf buf' with
  | nil => exact hbuf i hi
  | cons node l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_ ?_
    · rw [Array.size_push, Array.size_push, hsize]
    · intro j hj
      rw [getD_push, getD_push, ← hsize]
      split
      · next hjs =>
        -- The node is the node `buf.size < k` of the graph. Below `k` the
        -- buffers agree, and from `k` on both reads are outside the buffers.
        refine nodeVal_congr_of_plain ι h (fun a => ?_)
          (hplain 0 (by omega) node List.getElem?_cons_zero)
        by_cases ha : a < k
        · exact hbuf a ha
        · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
            Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
      · exact hbuf j hj
    · intro j hj node' hnode'
      rw [Array.size_push] at hj
      refine hplain (j + 1) (by omega) node' ?_
      rw [List.getElem?_cons_succ]
      exact hnode'

/-- If the first `k` nodes of a graph are plain, their values depend only on
the fixed trace, the main trace and the selectors. A node only reads nodes
before itself: a reference to a later node reads zero. -/
theorem getD_sweep_congr_of_plain (ι : F → R) (nodes : Array (Node F)) (k : ℕ)
    (hplain : ∀ i < k, ∀ node, nodes[i]? = some node → node.Plain) {v v' : RowValues R}
    (h : RowAgree v v') {i : ℕ} (hi : i < k) :
    (sweep ι nodes v).getD i 0 = (sweep ι nodes v').getD i 0 := by
  rw [sweep, sweep, ← Array.foldl_toList, ← Array.foldl_toList]
  refine getD_foldl_congr_of_plain ι h k nodes.toList #[] #[] rfl (fun _ _ => rfl) ?_ hi
  intro j hj node hnode
  rw [Array.size_empty, Nat.zero_add] at hj
  rw [Array.getElem?_toList] at hnode
  exact hplain j hj node hnode

/-! ## Degrees -/

/-- A bound on the degree of one node, given bounds `buf` for the nodes before
it: `dcol` for a column, `dsel` for the selectors of the first and of the last
row, `1` for the transition selector, `0` for a constant or a public value. -/
def nodeDeg (dcol dsel : ℕ) (buf : Array ℕ) : Node F → ℕ
  | .const _ => 0
  | .var _ => dcol
  | .pub _ => 0
  | .isFirstRow => dsel
  | .isLastRow => dsel
  | .isTransition => 1
  | .add a b => max (buf.getD a 0) (buf.getD b 0)
  | .sub a b => max (buf.getD a 0) (buf.getD b 0)
  | .mul a b => buf.getD a 0 + buf.getD b 0
  | .neg a => buf.getD a 0

/-- The degree bounds of all nodes, first to last. -/
def sweepDeg (dcol dsel : ℕ) (nodes : Array (Node F)) : Array ℕ :=
  nodes.foldl (fun buf node => buf.push (nodeDeg dcol dsel buf node)) #[]

/-- The largest degree bound of a node of the graph. -/
def maxNodeDeg (dcol dsel : ℕ) (nodes : Array (Node F)) : ℕ :=
  (sweepDeg dcol dsel nodes).foldl max 0

/-- The entries of a row of polynomials have the degrees `dcol` (columns),
`dsel` (first-row and last-row selectors), `1` (transition selector) and `0`
(public values) at most. -/
structure RowDegLE (v : RowValues R[X]) (dcol dsel : ℕ) : Prop where
  /-- The columns of the fixed trace. -/
  preprocessed : ∀ i, (v.preprocessed.getD i 0).natDegree ≤ dcol
  /-- The columns of the fixed trace, next row. -/
  preprocessedNext : ∀ i, (v.preprocessedNext.getD i 0).natDegree ≤ dcol
  /-- The columns of the main trace. -/
  main : ∀ i, (v.main.getD i 0).natDegree ≤ dcol
  /-- The columns of the main trace, next row. -/
  mainNext : ∀ i, (v.mainNext.getD i 0).natDegree ≤ dcol
  /-- The columns of the lookup trace. -/
  stage2 : ∀ i, (v.stage2.getD i 0).natDegree ≤ dcol
  /-- The columns of the lookup trace, next row. -/
  stage2Next : ∀ i, (v.stage2Next.getD i 0).natDegree ≤ dcol
  /-- The public values are constants. -/
  publics : ∀ i, (v.publics.getD i 0).natDegree = 0
  /-- The first-row selector. -/
  isFirstRow : v.isFirstRow.natDegree ≤ dsel
  /-- The last-row selector. -/
  isLastRow : v.isLastRow.natDegree ≤ dsel
  /-- The transition selector. -/
  isTransition : v.isTransition.natDegree ≤ 1

/-- A column variable of a row of polynomials has degree at most `dcol`. -/
private theorem natDegree_varVal_le {v : RowValues R[X]} {dcol dsel : ℕ}
    (hv : RowDegLE v dcol dsel) (col : ColRef) : (varVal v col).natDegree ≤ dcol := by
  obtain ⟨source, next, index⟩ := col
  cases source with
  | preprocessed =>
    cases next with
    | false => exact hv.preprocessed index
    | true => exact hv.preprocessedNext index
  | main =>
    cases next with
    | false => exact hv.main index
    | true => exact hv.mainNext index
  | stage2 =>
    cases next with
    | false => exact hv.stage2 index
    | true => exact hv.stage2Next index

/-- On a row of polynomials, the degree of a node is at most the bound
`nodeDeg` computes from bounds for the values before it. -/
private theorem natDegree_nodeVal_le (ι : F → R[X]) (hι : ∀ c, (ι c).natDegree = 0)
    {v : RowValues R[X]} {dcol dsel : ℕ} (hv : RowDegLE v dcol dsel) {buf : Array R[X]}
    {deg : Array ℕ} (hbuf : ∀ i, (buf.getD i 0).natDegree ≤ deg.getD i 0) (node : Node F) :
    (nodeVal ι v buf node).natDegree ≤ nodeDeg dcol dsel deg node := by
  cases node with
  | const c => exact (hι c).le
  | var col => exact natDegree_varVal_le hv col
  | pub index => exact (hv.publics index).le
  | isFirstRow => exact hv.isFirstRow
  | isLastRow => exact hv.isLastRow
  | isTransition => exact hv.isTransition
  | add a b => exact (natDegree_add_le _ _).trans (max_le_max (hbuf a) (hbuf b))
  | sub a b => exact (natDegree_sub_le _ _).trans (max_le_max (hbuf a) (hbuf b))
  | mul a b => exact natDegree_mul_le.trans (Nat.add_le_add (hbuf a) (hbuf b))
  | neg a => exact (natDegree_neg _).le.trans (hbuf a)

/-- `natDegree_sweep_le`, for the two folds over a list of nodes from a buffer
and bounds for its values. -/
private theorem natDegree_foldl_le (ι : F → R[X]) (hι : ∀ c, (ι c).natDegree = 0)
    {v : RowValues R[X]} {dcol dsel : ℕ} (hv : RowDegLE v dcol dsel) (l : List (Node F))
    (buf : Array R[X]) (deg : Array ℕ) (hsize : buf.size = deg.size)
    (hbuf : ∀ i, (buf.getD i 0).natDegree ≤ deg.getD i 0) (i : ℕ) :
    ((l.foldl (fun buf node => buf.push (nodeVal ι v buf node)) buf).getD i 0).natDegree ≤
      (l.foldl (fun buf node => buf.push (nodeDeg dcol dsel buf node)) deg).getD i 0 := by
  induction l generalizing buf deg with
  | nil => exact hbuf i
  | cons node l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_ ?_
    · rw [Array.size_push, Array.size_push, hsize]
    · intro j
      rw [getD_push, getD_push, ← hsize]
      split
      · exact natDegree_nodeVal_le ι hι hv hbuf node
      · exact hbuf j

/-- On a row of polynomials, the degree of every node is at most the bound
`sweepDeg` computes. The constants of the graph are constant polynomials. -/
theorem natDegree_sweep_le (ι : F → R[X]) (hι : ∀ c, (ι c).natDegree = 0)
    (nodes : Array (Node F)) {v : RowValues R[X]} {dcol dsel : ℕ} (hv : RowDegLE v dcol dsel)
    (i : ℕ) :
    ((sweep ι nodes v).getD i 0).natDegree ≤ (sweepDeg dcol dsel nodes).getD i 0 := by
  rw [sweep, sweepDeg, ← Array.foldl_toList, ← Array.foldl_toList]
  exact natDegree_foldl_le ι hι hv nodes.toList #[] #[] rfl (fun j => by simp) i

/-- A left fold of `max` is at least its initial value and every element of the
list. -/
private theorem le_foldl_max (l : List ℕ) (init x : ℕ) (hx : x ≤ init ∨ x ∈ l) :
    x ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact hx.resolve_right List.not_mem_nil
  | cons y l ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    rcases hx with hx | hx
    · exact .inl (hx.trans (le_max_left _ _))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact .inl (le_max_right _ _)
      · exact .inr hx

/-- Every degree bound of a node is at most the largest one. -/
theorem getD_sweepDeg_le_maxNodeDeg (dcol dsel : ℕ) (nodes : Array (Node F)) (i : ℕ) :
    (sweepDeg dcol dsel nodes).getD i 0 ≤ maxNodeDeg dcol dsel nodes := by
  rw [maxNodeDeg, ← Array.foldl_toList, Array.getD_eq_getD_getElem?]
  by_cases hi : i < (sweepDeg dcol dsel nodes).size
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    exact le_foldl_max _ _ _ (.inr (Array.getElem_mem_toList hi))
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi)]
    exact Nat.zero_le _

/-- On a row of polynomials, the degree of every node is at most
`maxNodeDeg`. -/
theorem natDegree_sweep_le_max (ι : F → R[X]) (hι : ∀ c, (ι c).natDegree = 0)
    (nodes : Array (Node F)) {v : RowValues R[X]} {dcol dsel : ℕ} (hv : RowDegLE v dcol dsel)
    (i : ℕ) : ((sweep ι nodes v).getD i 0).natDegree ≤ maxNodeDeg dcol dsel nodes :=
  (natDegree_sweep_le ι hι nodes hv i).trans (getD_sweepDeg_le_maxNodeDeg dcol dsel nodes i)

end Ring

end CertiFri.Stark.Model
