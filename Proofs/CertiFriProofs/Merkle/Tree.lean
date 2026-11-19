import Mathlib.Data.Nat.Notation
import CertiFri.Merkle

/-!
# The Merkle tree, and that its openings verify

`CertiFri.Merkle` holds the verifying side of the Merkle commitment and its
binding theorem. This file holds the other side as a mathematical object: the
tree over a list of matrices (`node`, `root`), the rows it opens at an index
(`rowsAt`) and the authentication path of an index (`pathAt`). It proves that
the verifier accepts these openings: `verifyOpening_tree` for one index,
`verifyOpenings_tree` for several, and `merkleMmcs_verifyMultiBatch_tree` for
the commitment-scheme interface.

## The tree

The layout is the one the verifier checks, which is that of Plonky3's
`MerkleTreeMmcs` with a two-to-one compression function. With `top` the
log-height of the tallest matrix, the layer of log-height `h` has `2 ^ h`
nodes, for `h ≤ top`.

* Node `j` of the layer `top` is the hash of row `j` of the matrices of
  log-height `top`, concatenated in batch order (`node_top`).
* Node `j` of a layer `h < top` is the compression of nodes `2 * j` and
  `2 * j + 1` of the layer `h + 1`, compressed once more with the hash of row
  `j` of the matrices of log-height `h` if there are any (`node_of_lt`).
* The root is the one node of the layer `0`.

`CertiFriProofs.Merkle.TreeExamples` evaluates these definitions on a small
batch and compares them with the values Plonky3 computes.

## Assumptions

The theorems hold for every pair of hash functions; no property of them is
used. The batch must not be empty, row `i` of a matrix must have the width of
the matrix for every `i` below its height, and an opened index must address a
row of the tallest matrix. The verifier rejects an opening that fails any of
these.

## Not covered

No program that builds a tree is certified here: the tree is a function from
positions to digests, and nothing relates it to an array computed layer by
layer. Compression of more than two digests, heights that are not powers of
two, and commitments to a layer of several digests are not covered, as in
`CertiFri.Merkle`.
-/

namespace CertiFri.Merkle

variable {T D : Type}

/-- A matrix to commit to: `2 ^ logHeight` rows of `width` entries. `row i` is
row `i`; its values for `i ≥ 2 ^ logHeight` do not matter. -/
structure Matrix (T : Type) where
  /-- Log of the number of rows. -/
  logHeight : ℕ
  /-- Number of columns. -/
  width : ℕ
  /-- Row `i`, for `i < 2 ^ logHeight`. -/
  row : ℕ → Array T

/-! ## Dimensions -/

/-- The dimensions of the matrices, as the verifier takes them. -/
def dimsOf (ms : List (Matrix T)) : Array Dimensions :=
  (ms.map fun M => { width := M.width, logHeight := M.logHeight }).toArray

/-- The dimensions as a list: one per matrix, in batch order. -/
theorem toList_dimsOf (ms : List (Matrix T)) :
    (dimsOf ms).toList = ms.map fun M => { width := M.width, logHeight := M.logHeight } :=
  rfl

/-- There is one dimension per matrix. -/
@[simp]
theorem size_dimsOf (ms : List (Matrix T)) : (dimsOf ms).size = ms.length := by
  simp only [dimsOf, List.size_toArray, List.length_map]

/-- The `k`-th dimension is the width and the log-height of the `k`-th matrix. -/
theorem getElem?_dimsOf (ms : List (Matrix T)) (k : ℕ) :
    (dimsOf ms)[k]? = ms[k]?.map fun M => { width := M.width, logHeight := M.logHeight } := by
  simp only [dimsOf, List.getElem?_toArray, List.getElem?_map]

/-- The `k`-th dimension is the width and the log-height of the `k`-th matrix. -/
theorem getElem_dimsOf (ms : List (Matrix T)) (k : ℕ) (hk : k < ms.length) :
    (dimsOf ms)[k]'(by rw [size_dimsOf]; exact hk) =
      { width := ms[k].width, logHeight := ms[k].logHeight } := by
  simp only [dimsOf, List.getElem_toArray, List.getElem_map]

/-- The depth of the tree is the largest log-height of a matrix, and `0` for an
empty batch. -/
theorem maxLogHeight_dimsOf (ms : List (Matrix T)) :
    maxLogHeight (dimsOf ms).toList = (ms.map (·.logHeight)).foldr max 0 := by
  induction ms with
  | nil => rfl
  | cons M ms ih =>
    rw [toList_dimsOf] at ih
    simp only [toList_dimsOf, List.map_cons, maxLogHeight, List.foldr_cons, ih]

/-- No matrix is taller than the tree is deep. -/
theorem logHeight_le_maxLogHeight {ms : List (Matrix T)} {M : Matrix T} (hM : M ∈ ms) :
    M.logHeight ≤ maxLogHeight (dimsOf ms).toList :=
  le_maxLogHeight (d := { width := M.width, logHeight := M.logHeight })
    (List.mem_map.mpr ⟨M, hM, rfl⟩)

/-- Some matrix of a batch that is not empty is as tall as the tree is deep. -/
theorem exists_logHeight_eq_maxLogHeight {ms : List (Matrix T)} (hne : ms ≠ []) :
    ∃ M ∈ ms, M.logHeight = maxLogHeight (dimsOf ms).toList := by
  induction ms with
  | nil => exact absurd rfl hne
  | cons M ms ih =>
    have hcons : maxLogHeight (dimsOf (M :: ms)).toList =
        max M.logHeight (maxLogHeight (dimsOf ms).toList) := rfl
    rw [hcons]
    by_cases hms : ms = []
    · subst hms
      exact ⟨M, List.mem_cons_self, (Nat.max_eq_left (Nat.zero_le _)).symm⟩
    · obtain ⟨M', hM', hM'top⟩ := ih hms
      by_cases hle : maxLogHeight (dimsOf ms).toList ≤ M.logHeight
      · exact ⟨M, List.mem_cons_self, (Nat.max_eq_left hle).symm⟩
      · exact ⟨M', List.mem_cons_of_mem _ hM',
          hM'top.trans (Nat.max_eq_right (Nat.le_of_not_ge hle)).symm⟩

/-- The depth of the tree is the log-height that some matrix has and none
exceeds. -/
theorem maxLogHeight_dimsOf_eq {ms : List (Matrix T)} {h : ℕ}
    (hle : ∀ M ∈ ms, M.logHeight ≤ h) (hex : ∃ M ∈ ms, M.logHeight = h) :
    maxLogHeight (dimsOf ms).toList = h := by
  obtain ⟨M, hM, hMh⟩ := hex
  obtain ⟨M', hM', hM'top⟩ := exists_logHeight_eq_maxLogHeight (List.ne_nil_of_mem hM)
  exact Nat.le_antisymm (hM'top ▸ hle M' hM') (hMh ▸ logHeight_le_maxLogHeight hM)

/-- The tree over a single matrix is as deep as the matrix is tall. -/
@[simp]
theorem maxLogHeight_dimsOf_singleton (M : Matrix T) :
    maxLogHeight (dimsOf [M]).toList = M.logHeight :=
  Nat.max_eq_left (Nat.zero_le _)

/-! ## The tree -/

namespace Tree

/-- Row `j` of every matrix of log-height `h`, concatenated in batch order: the
entries the tree hashes at node `j` of the layer with `2 ^ h` nodes. -/
def groupAt (ms : List (Matrix T)) (h j : ℕ) : List T :=
  (ms.filter fun M => M.logHeight = h).flatMap fun M => (M.row j).toList

/-- Node `j` of the layer with `2 ^ h` nodes, from the compression `digest` of
its two children: if some matrix has log-height `h`, the digest is compressed
once more with the hash of row `j` of the matrices of that height. -/
def injectAt (H : MerkleHasher T D) (ms : List (Matrix T)) (h j : ℕ) (digest : D) : D :=
  if ms.any fun M => M.logHeight = h then
    H.compress digest (H.hashRows (groupAt ms h j).toArray)
  else digest

/-- Node `j` of the layer with `2 ^ h` nodes, in a tree whose leaves are `dist`
layers above that layer. -/
def nodeFrom (H : MerkleHasher T D) (ms : List (Matrix T)) : (dist h j : ℕ) → D
  | 0, h, j => H.hashRows (groupAt ms h j).toArray
  | dist + 1, h, j =>
    injectAt H ms h j
      (H.compress (nodeFrom H ms dist (h + 1) (2 * j)) (nodeFrom H ms dist (h + 1) (2 * j + 1)))

end Tree

/-- The digest of node `j` of the layer with `2 ^ h` nodes. The layers are those
with `h` at most the log-height of the tallest matrix. -/
def node (H : MerkleHasher T D) (ms : List (Matrix T)) (h j : ℕ) : D :=
  Tree.nodeFrom H ms (maxLogHeight (dimsOf ms).toList - h) h j

/-- The root: the one node of the layer with one node. -/
def root (H : MerkleHasher T D) (ms : List (Matrix T)) : D :=
  node H ms 0 0

/-- A leaf is the hash of the rows of the tallest matrices at its index. -/
theorem node_top (H : MerkleHasher T D) (ms : List (Matrix T)) (j : ℕ) :
    node H ms (maxLogHeight (dimsOf ms).toList) j =
      H.hashRows (Tree.groupAt ms (maxLogHeight (dimsOf ms).toList) j).toArray := by
  rw [node, Nat.sub_self, Tree.nodeFrom]

/-- A node below the leaves is the compression of its two children, with the
rows of the matrices of its layer injected. -/
theorem node_of_lt (H : MerkleHasher T D) {ms : List (Matrix T)} {h : ℕ}
    (hlt : h < maxLogHeight (dimsOf ms).toList) (j : ℕ) :
    node H ms h j =
      Tree.injectAt H ms h j
        (H.compress (node H ms (h + 1) (2 * j)) (node H ms (h + 1) (2 * j + 1))) := by
  have hdist : maxLogHeight (dimsOf ms).toList - h
      = maxLogHeight (dimsOf ms).toList - (h + 1) + 1 := by omega
  rw [node, hdist, Tree.nodeFrom, node, node]

/-! ## Openings -/

/-- The rows opened at `index`: for each matrix, its row at the index shifted
to its height. -/
def rowsAt (ms : List (Matrix T)) (index : ℕ) : Array (Array T) :=
  (ms.map fun M => M.row (index >>> (maxLogHeight (dimsOf ms).toList - M.logHeight))).toArray

/-- The opened rows as a list: one per matrix, in batch order. -/
theorem toList_rowsAt (ms : List (Matrix T)) (index : ℕ) :
    (rowsAt ms index).toList =
      ms.map fun M => M.row (index >>> (maxLogHeight (dimsOf ms).toList - M.logHeight)) :=
  rfl

/-- One row is opened per matrix. -/
@[simp]
theorem size_rowsAt (ms : List (Matrix T)) (index : ℕ) : (rowsAt ms index).size = ms.length := by
  simp only [rowsAt, List.size_toArray, List.length_map]

/-- The `k`-th opened row is the row of the `k`-th matrix at the index shifted
right by the difference between the depth of the tree and the log-height of
the matrix. -/
theorem getElem?_rowsAt (ms : List (Matrix T)) (index k : ℕ) :
    (rowsAt ms index)[k]? = ms[k]?.map fun M =>
      M.row (index >>> (maxLogHeight (dimsOf ms).toList - M.logHeight)) := by
  simp only [rowsAt, List.getElem?_toArray, List.getElem?_map]

/-- The `k`-th opened row is the row of the `k`-th matrix at the index shifted
right by the difference between the depth of the tree and the log-height of
the matrix. -/
theorem getElem_rowsAt (ms : List (Matrix T)) (index k : ℕ) (hk : k < ms.length) :
    (rowsAt ms index)[k]'(by rw [size_rowsAt]; exact hk) =
      ms[k].row (index >>> (maxLogHeight (dimsOf ms).toList - ms[k].logHeight)) := by
  simp only [rowsAt, List.getElem_toArray, List.getElem_map]

/-- The tree over a single matrix opens the row of the matrix at the index. -/
@[simp]
theorem rowsAt_singleton (M : Matrix T) (index : ℕ) : rowsAt [M] index = #[M.row index] := by
  rw [rowsAt, maxLogHeight_dimsOf_singleton, List.map_singleton, Nat.sub_self,
    Nat.shiftRight_zero]

/-- The authentication path of `index`: the sibling at each level, leaf level
first. At level `level` the path passes through node `index >>> level` of the
layer that many levels below the leaves, and the sibling is the node next to
it. -/
def pathAt (H : MerkleHasher T D) (ms : List (Matrix T)) (index : ℕ) : List D :=
  (List.range (maxLogHeight (dimsOf ms).toList)).map fun level =>
    node H ms (maxLogHeight (dimsOf ms).toList - level) ((index >>> level) ^^^ 1)

/-- A path has one sibling per level of the tree. -/
@[simp]
theorem length_pathAt (H : MerkleHasher T D) (ms : List (Matrix T)) (index : ℕ) :
    (pathAt H ms index).length = maxLogHeight (dimsOf ms).toList := by
  simp only [pathAt, List.length_map, List.length_range]

/-- The sibling at level `level` of the path of `index`. -/
theorem getElem_pathAt (H : MerkleHasher T D) (ms : List (Matrix T)) (index level : ℕ)
    (hlevel : level < maxLogHeight (dimsOf ms).toList) :
    (pathAt H ms index)[level]'(by rw [length_pathAt]; exact hlevel) =
      node H ms (maxLogHeight (dimsOf ms).toList - level) ((index >>> level) ^^^ 1) := by
  simp only [pathAt, List.getElem_map, List.getElem_range]

/-! ## The opened rows, as the verifier groups them -/

namespace Tree

/-- If every matrix of log-height `h` is opened at row `j`, the verifier's
concatenation of the opened rows of that height is what the tree hashes at
node `j` of the layer of that height. -/
private theorem groupRows_rows (f : Matrix T → ℕ) (h j : ℕ) :
    ∀ ms : List (Matrix T), (∀ M ∈ ms, M.logHeight = h → f M = j) →
      groupRows (ms.map fun M => ({ width := M.width, logHeight := M.logHeight } : Dimensions))
        (ms.map fun M => M.row (f M)) h = groupAt ms h j
  | [], _ => rfl
  | M :: ms, hf => by
    have ih := groupRows_rows f h j ms fun M' hM' => hf M' (List.mem_cons_of_mem _ hM')
    simp only [groupAt] at ih ⊢
    simp only [List.map_cons, groupRows, List.filter_cons]
    by_cases hM : M.logHeight = h
    · simp only [hM, ↓reduceIte, decide_true, List.flatMap_cons, ih, hf M List.mem_cons_self hM]
    · simp only [hM, ↓reduceIte, decide_false, Bool.false_eq_true, ih]

/-- Rows of the widths of their matrices pass the width check. -/
private theorem widthsMatch_rows (f : Matrix T → ℕ) :
    ∀ ms : List (Matrix T), (∀ M ∈ ms, (M.row (f M)).size = M.width) →
      widthsMatch (ms.map fun M => ({ width := M.width, logHeight := M.logHeight } : Dimensions))
        (ms.map fun M => M.row (f M)) = true
  | [], _ => rfl
  | M :: ms, hw => by
    simp only [List.map_cons, widthsMatch, Bool.and_eq_true, beq_iff_eq]
    exact ⟨hw M List.mem_cons_self,
      widthsMatch_rows f ms fun M' hM' => hw M' (List.mem_cons_of_mem _ hM')⟩

/-- An index of the tallest matrix, shifted to a shorter height, is an index
of that height. -/
private theorem shiftRight_lt {index top h : ℕ} (hindex : index < 2 ^ top) (hle : h ≤ top) :
    index >>> (top - h) < 2 ^ h := by
  have htop : h + (top - h) = top := by omega
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide)),
    ← Nat.pow_add, htop]
  exact hindex

end Tree

/-- The verifier's test for a matrix of log-height `h`, on the dimensions of
the batch. -/
theorem hasHeight_dimsOf (ms : List (Matrix T)) (h : ℕ) :
    hasHeight (dimsOf ms).toList h = ms.any fun M => M.logHeight = h := by
  simp only [hasHeight, toList_dimsOf, List.any_map, Function.comp_def]

/-- The opened rows of the matrices of log-height `h`, as the verifier
concatenates them, are the rows the tree hashes at the node the path of the
index passes through in the layer of that height. -/
theorem groupRows_rowsAt (ms : List (Matrix T)) (index h : ℕ) :
    groupRows (dimsOf ms).toList (rowsAt ms index).toList h =
      Tree.groupAt ms h (index >>> (maxLogHeight (dimsOf ms).toList - h)) :=
  Tree.groupRows_rows _ h _ ms fun _ _ hM => by rw [hM]

/-- The opened rows have the widths of their matrices, when the index addresses
a row of the tallest matrix. -/
theorem widthsMatch_rowsAt {ms : List (Matrix T)}
    (hwidth : ∀ M ∈ ms, ∀ i < 2 ^ M.logHeight, (M.row i).size = M.width) {index : ℕ}
    (hindex : index < 2 ^ maxLogHeight (dimsOf ms).toList) :
    widthsMatch (dimsOf ms).toList (rowsAt ms index).toList = true :=
  Tree.widthsMatch_rows _ ms fun M hM =>
    hwidth M hM _ (Tree.shiftRight_lt hindex (logHeight_le_maxLogHeight hM))

/-! ## Climbing the tree -/

namespace Tree

/-- A node and its sibling have the same parent. -/
private theorem xor_one_div_two (j : ℕ) : (j ^^^ 1) / 2 = j / 2 := by
  rw [Nat.xor_div_two, Nat.xor_zero]

/-- A node and its sibling are on opposite sides of their parent. -/
private theorem xor_one_mod_two (j : ℕ) : (j ^^^ 1) % 2 = 1 ↔ j % 2 ≠ 1 := by
  rw [Nat.xor_mod_two_eq_one]
  simp only [Nat.one_mod, iff_true]

/-- The parent of a node and its sibling is the compression of the two
children of the node below them, left child first. -/
private theorem parent_sibling (H : MerkleHasher T D) (ms : List (Matrix T)) (h j : ℕ) :
    parent H j (node H ms h j) (node H ms h (j ^^^ 1)) =
      H.compress (node H ms h (2 * (j / 2))) (node H ms h (2 * (j / 2) + 1)) := by
  have hdiv := xor_one_div_two j
  have hmod := xor_one_mod_two j
  unfold parent
  split
  · have hleft : 2 * (j / 2) = j := by omega
    have hright : 2 * (j / 2) + 1 = j ^^^ 1 := by omega
    rw [hright, hleft]
  · have hleft : 2 * (j / 2) = j ^^^ 1 := by omega
    have hright : 2 * (j / 2) + 1 = j := by omega
    rw [hright, hleft]

/-- The verifier's injection of the opened rows at a node on the path of the
index is the tree's injection at that node. -/
private theorem inject_rowsAt (H : MerkleHasher T D) (ms : List (Matrix T)) (index h : ℕ)
    (digest : D) :
    inject H (dimsOf ms).toList (rowsAt ms index).toList h digest =
      injectAt H ms h (index >>> (maxLogHeight (dimsOf ms).toList - h)) digest := by
  rw [inject, injectAt, groupDigest, hasHeight_dimsOf, groupRows_rowsAt]

/-- One step of the verifier's climb along the path of the index: from the node
of the layer `h + 1` on the path and its sibling to the node of the layer `h`
on the path. -/
private theorem inject_parent (H : MerkleHasher T D) {ms : List (Matrix T)} (index : ℕ) {h : ℕ}
    (hlt : h < maxLogHeight (dimsOf ms).toList) :
    inject H (dimsOf ms).toList (rowsAt ms index).toList h
        (parent H (index >>> (maxLogHeight (dimsOf ms).toList - (h + 1)))
          (node H ms (h + 1) (index >>> (maxLogHeight (dimsOf ms).toList - (h + 1))))
          (node H ms (h + 1) ((index >>> (maxLogHeight (dimsOf ms).toList - (h + 1))) ^^^ 1))) =
      node H ms h (index >>> (maxLogHeight (dimsOf ms).toList - h)) := by
  have hshift : maxLogHeight (dimsOf ms).toList - h
      = maxLogHeight (dimsOf ms).toList - (h + 1) + 1 := by omega
  rw [parent_sibling, inject_rowsAt, node_of_lt H hlt, hshift, Nat.shiftRight_succ]

/-- The verifier's climb from the node of the layer `h` on the path of the
index, along the siblings of the remaining levels, reaches the node of the
layer `0` on the path. -/
private theorem climb_tree (H : MerkleHasher T D) (ms : List (Matrix T)) (index : ℕ) :
    ∀ h, h ≤ maxLogHeight (dimsOf ms).toList →
      climb H (dimsOf ms).toList (rowsAt ms index).toList h
        (index >>> (maxLogHeight (dimsOf ms).toList - h))
        (node H ms h (index >>> (maxLogHeight (dimsOf ms).toList - h)))
        ((List.range' (maxLogHeight (dimsOf ms).toList - h) h).map fun level =>
          node H ms (maxLogHeight (dimsOf ms).toList - level) ((index >>> level) ^^^ 1)) =
      node H ms 0 (index >>> maxLogHeight (dimsOf ms).toList)
  | 0, _ => by rw [List.range'_zero, List.map_nil, climb, Nat.sub_zero]
  | h + 1, hle => by
    have hstart : maxLogHeight (dimsOf ms).toList - (h + 1) + 1
        = maxLogHeight (dimsOf ms).toList - h := by omega
    have hlayer : maxLogHeight (dimsOf ms).toList - (maxLogHeight (dimsOf ms).toList - (h + 1))
        = h + 1 := by omega
    rw [List.range'_succ, List.map_cons, climb, hlayer, Nat.add_sub_cancel,
      inject_parent H index (Nat.lt_of_succ_le hle), ← Nat.shiftRight_succ, hstart]
    exact climb_tree H ms index h (Nat.le_of_succ_le hle)

end Tree

/-! ## Openings verify -/

/-- **Openings of the tree verify.** The verifier accepts, under the root of
the tree, the rows and the path the tree gives at an index of the tallest
matrix. -/
theorem verifyOpening_tree [DecidableEq D] (H : MerkleHasher T D) {ms : List (Matrix T)}
    (hne : ms ≠ [])
    (hwidth : ∀ M ∈ ms, ∀ i < 2 ^ M.logHeight, (M.row i).size = M.width) {index : ℕ}
    (hindex : index < 2 ^ maxLogHeight (dimsOf ms).toList) :
    verifyOpening H (root H ms) (dimsOf ms) index (rowsAt ms index) (pathAt H ms index)
      = true := by
  have hclimb := Tree.climb_tree H ms index _ (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero, ← List.range_eq_range', node_top,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hindex] at hclimb
  simp only [verifyOpening, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, widthsMatch_rowsAt hwidth hindex⟩, length_pathAt H ms index⟩, hindex⟩, ?_⟩
  · rw [size_dimsOf]
    exact fun hlen => hne (List.eq_nil_of_length_eq_zero hlen)
  · rw [groupDigest, groupRows_rowsAt, Nat.sub_self, Nat.shiftRight_zero]
    exact hclimb

/-- **Openings at several indices verify.** The verifier accepts, under the
root of the tree, the rows and the paths the tree gives at any indices of the
tallest matrix. -/
theorem verifyOpenings_tree [DecidableEq D] (H : MerkleHasher T D) {ms : List (Matrix T)}
    (hne : ms ≠ [])
    (hwidth : ∀ M ∈ ms, ∀ i < 2 ^ M.logHeight, (M.row i).size = M.width) (indices : Array ℕ)
    (hindices : ∀ i ∈ indices, i < 2 ^ maxLogHeight (dimsOf ms).toList) :
    verifyOpenings H (root H ms) (dimsOf ms) indices (indices.map (rowsAt ms))
      (indices.map (pathAt H ms)) = true := by
  simp only [verifyOpenings, Array.size_map, beq_self_eq_true, Bool.true_and, List.all_eq_true,
    List.mem_range]
  intro query hquery
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem hquery, Option.map_some]
  exact verifyOpening_tree H hne hwidth (hindices _ (Array.getElem_mem hquery))

/-- **Openings verify through the commitment-scheme interface.** The Merkle
commitment scheme accepts, under the root of the tree, the rows and the paths
the tree gives at any indices of the tallest matrix. -/
theorem merkleMmcs_verifyMultiBatch_tree [DecidableEq D] (H : MerkleHasher T D)
    {ms : List (Matrix T)} (hne : ms ≠ [])
    (hwidth : ∀ M ∈ ms, ∀ i < 2 ^ M.logHeight, (M.row i).size = M.width) (indices : Array ℕ)
    (hindices : ∀ i ∈ indices, i < 2 ^ maxLogHeight (dimsOf ms).toList) :
    (merkleMmcs H).verifyMultiBatch (root H ms) (dimsOf ms) indices (indices.map (rowsAt ms))
      (indices.map (pathAt H ms)) = true :=
  verifyOpenings_tree H hne hwidth indices hindices

end CertiFri.Merkle
