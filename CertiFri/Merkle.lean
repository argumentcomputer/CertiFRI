import CertiFri.Mmcs

/-!
# Merkle commitments

The verifying side of a Merkle commitment to several matrices of different
heights, and the theorem that makes it a commitment: an accepted opening
determines the opened rows, unless the hash functions collide.

## The tree

The layout is that of Plonky3's `MerkleTreeMmcs` with a two-to-one compression
function, power-of-two heights and a single root.

* A leaf is the hash of the rows of the tallest matrices at one index,
  concatenated in batch order.
* A node is the compression of its two children.
* A shorter matrix is injected where the tree is as wide as the matrix is tall:
  the node there is compressed once more with the hash of the rows of the
  matrices of that height.

An index addresses a row of the tallest matrix. A matrix that is `2 ^ k` times
shorter is opened at the index shifted right by `k`.

Not covered: compression of more than two digests, heights that are not powers
of two, and commitments to a layer of several digests instead of one root.

## Openings

An opening at one index is the opened rows and the siblings along the path to
the root (`verifyOpening`). An opening at several indices carries one path per
index (`verifyOpenings`). A format that shares siblings between paths can be
unpacked into this one before it is checked; nothing has to be proved about the
unpacking, because every path is checked afterwards.

## Binding

`verifyOpening_binding`: two accepted openings under one root give the same row
of a matrix whenever they address the same row of it, or else one of the two
hash functions has a collision. The proofs use no axiom beyond `propext` and
`Quot.sound`, so the collision is one a program could compute from the two
openings; no such program is written here.
-/

namespace CertiFri

/-- `f` sends two different inputs to the same output. -/
def HasCollision {α β : Type} (f : α → β) : Prop :=
  ∃ a b, a ≠ b ∧ f a = f b

theorem eq_or_hasCollision {α β : Type} [DecidableEq α] (f : α → β) {a b : α}
    (h : f a = f b) : a = b ∨ HasCollision f :=
  if hab : a = b then .inl hab else .inr ⟨a, b, hab, h⟩

/-- The two functions a Merkle tree is built from, over entries `T` and digests `D`. -/
structure MerkleHasher (T D : Type) where
  /-- Hash the entries of a leaf or of an injection. -/
  hashRows : Array T → D
  /-- Compress two digests into one. -/
  compress : D → D → D

namespace MerkleHasher

variable {T D : Type}

/-- One of the two functions has a collision. -/
def Collides (H : MerkleHasher T D) : Prop :=
  HasCollision H.hashRows ∨ HasCollision fun pair : D × D => H.compress pair.1 pair.2

theorem hashRows_inj [DecidableEq T] (H : MerkleHasher T D) {xs ys : Array T}
    (h : H.hashRows xs = H.hashRows ys) : xs = ys ∨ H.Collides :=
  (eq_or_hasCollision H.hashRows h).imp id .inl

theorem compress_inj [DecidableEq D] (H : MerkleHasher T D) {a b a' b' : D}
    (h : H.compress a b = H.compress a' b') : (a = a' ∧ b = b') ∨ H.Collides :=
  (eq_or_hasCollision (fun pair : D × D => H.compress pair.1 pair.2)
    (a := (a, b)) (b := (a', b')) h).imp (fun heq => Prod.mk.inj heq) .inr

end MerkleHasher

namespace Merkle

variable {T D : Type}

/-! ## The shape of the tree -/

/-- Log-height of the tallest matrix: the depth of the tree. -/
def maxLogHeight : List Dimensions → Nat
  | [] => 0
  | d :: dims => max d.logHeight (maxLogHeight dims)

/-- Whether some matrix has log-height `h`. -/
def hasHeight (dims : List Dimensions) (h : Nat) : Bool :=
  dims.any fun d => decide (d.logHeight = h)

/-- The opened rows of the matrices of log-height `h`, concatenated in batch order. -/
def groupRows : List Dimensions → List (Array T) → Nat → List T
  | d :: dims, row :: rows, h =>
    if d.logHeight = h then row.toList ++ groupRows dims rows h else groupRows dims rows h
  | _, _, _ => []

/-- Whether there is one opened row per matrix, each of the width of its matrix. -/
def widthsMatch : List Dimensions → List (Array T) → Bool
  | [], [] => true
  | d :: dims, row :: rows => row.size == d.width && widthsMatch dims rows
  | _, _ => false

theorem le_maxLogHeight {d : Dimensions} :
    ∀ {dims : List Dimensions}, d ∈ dims → d.logHeight ≤ maxLogHeight dims
  | [], h => nomatch h
  | e :: dims, h => by
    simp only [maxLogHeight]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left ..
    · exact Nat.le_trans (le_maxLogHeight h) (Nat.le_max_right ..)

theorem hasHeight_of_mem {d : Dimensions} :
    ∀ {dims : List Dimensions}, d ∈ dims → hasHeight dims d.logHeight = true
  | [], h => nomatch h
  | e :: dims, h => by
    unfold hasHeight
    rw [List.any_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rw [decide_eq_true rfl, Bool.true_or]
    · rw [show dims.any (fun e => decide (e.logHeight = d.logHeight)) = true from
        hasHeight_of_mem h, Bool.or_true]

theorem widthsMatch_length :
    ∀ {dims : List Dimensions} {rows : List (Array T)},
      widthsMatch dims rows = true → rows.length = dims.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [widthsMatch, Bool.and_eq_true] at h
    simp only [List.length_cons, widthsMatch_length h.2]
  | [], _ :: _, h => by simp [widthsMatch] at h
  | _ :: _, [], h => by simp [widthsMatch] at h

/-- Rows of the right widths are determined by their concatenation. -/
theorem groupRows_inj :
    ∀ (dims : List Dimensions) (rows rows' : List (Array T)) (g : Nat),
      widthsMatch dims rows = true → widthsMatch dims rows' = true →
      groupRows dims rows g = groupRows dims rows' g →
      ∀ (m : Nat) (d : Dimensions), dims[m]? = some d → d.logHeight = g → rows[m]? = rows'[m]?
  | [], _, _, _, _, _, _, m, d, hd, _ => by simp at hd
  | _ :: _, [], _, _, hw, _, _, _, _, _, _ => by simp [widthsMatch] at hw
  | _ :: _, _ :: _, [], _, _, hw', _, _, _, _, _ => by simp [widthsMatch] at hw'
  | e :: dims, row :: rows, row' :: rows', g, hw, hw', heq, m, d, hd, hg => by
    simp only [widthsMatch, Bool.and_eq_true, beq_iff_eq] at hw hw'
    simp only [groupRows] at heq
    by_cases he : e.logHeight = g
    · simp only [he, ↓reduceIte] at heq
      have hlen : row.toList.length = row'.toList.length := by
        simp only [Array.length_toList, hw.1, hw'.1]
      obtain ⟨hrow, hrest⟩ := List.append_inj heq hlen
      cases m with
      | zero => simp only [List.getElem?_cons_zero, Array.toList_inj.mp hrow]
      | succ m =>
        simp only [List.getElem?_cons_succ] at hd ⊢
        exact groupRows_inj dims rows rows' g hw.2 hw'.2 hrest m d hd hg
    · simp only [he, ↓reduceIte] at heq
      cases m with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hd
        exact absurd (hd ▸ hg) he
      | succ m =>
        simp only [List.getElem?_cons_succ] at hd ⊢
        exact groupRows_inj dims rows rows' g hw.2 hw'.2 heq m d hd hg

/-! ## Climbing to the root -/

/-- Digest of the opened rows of the matrices of log-height `h`. -/
def groupDigest (H : MerkleHasher T D) (dims : List Dimensions) (rows : List (Array T))
    (h : Nat) : D :=
  H.hashRows (groupRows dims rows h).toArray

/-- Inject the matrices of log-height `h`, if there are any, into a node of the
layer of that height. -/
def inject (H : MerkleHasher T D) (dims : List Dimensions) (rows : List (Array T))
    (h : Nat) (digest : D) : D :=
  if hasHeight dims h then H.compress digest (groupDigest H dims rows h) else digest

/-- The parent of a node and its sibling. An even index is a left child. -/
def parent (H : MerkleHasher T D) (index : Nat) (digest sibling : D) : D :=
  if index % 2 = 0 then H.compress digest sibling else H.compress sibling digest

/-- Climb from node `index` of the layer of log-height `h`, whose digest is
`digest`, through one sibling per level. Returns the digest reached. -/
def climb (H : MerkleHasher T D) (dims : List Dimensions) (rows : List (Array T)) :
    (h index : Nat) → (digest : D) → (path : List D) → D
  | _, _, digest, [] => digest
  | h, index, digest, sibling :: path =>
    climb H dims rows (h - 1) (index / 2)
      (inject H dims rows (h - 1) (parent H index digest sibling)) path

section Binding

variable [DecidableEq D] {H : MerkleHasher T D} {dims : List Dimensions}
  {rows rows' : List (Array T)}

theorem parent_inj {index : Nat} {digest digest' sibling sibling' : D}
    (h : parent H index digest sibling = parent H index digest' sibling') :
    digest = digest' ∨ H.Collides := by
  unfold parent at h
  split at h
  · exact (H.compress_inj h).imp (·.1) id
  · exact (H.compress_inj h).imp (·.2) id

theorem inject_inj {g : Nat} {digest digest' : D}
    (h : inject H dims rows g digest = inject H dims rows' g digest') :
    digest = digest' ∨ H.Collides := by
  unfold inject at h
  split at h
  · exact (H.compress_inj h).imp (·.1) id
  · exact .inl h

omit [DecidableEq D] in
theorem groupDigest_inj [DecidableEq T] {g : Nat}
    (h : groupDigest H dims rows g = groupDigest H dims rows' g) :
    groupRows dims rows g = groupRows dims rows' g ∨ H.Collides :=
  (H.hashRows_inj h).imp List.toArray_inj id

theorem inject_group [DecidableEq T] {g : Nat} {digest digest' : D}
    (hg : hasHeight dims g = true)
    (h : inject H dims rows g digest = inject H dims rows' g digest') :
    groupRows dims rows g = groupRows dims rows' g ∨ H.Collides := by
  simp only [inject, hg, ↓reduceIte] at h
  rcases H.compress_inj h with ⟨_, hgroup⟩ | hcol
  · exact groupDigest_inj hgroup
  · exact .inr hcol

/-- Two climbs from the same node to the same digest start from the same digest. -/
theorem climb_inj :
    ∀ (path path' : List D) (h index : Nat) (digest digest' : D),
      path.length = path'.length →
      climb H dims rows h index digest path = climb H dims rows' h index digest' path' →
      digest = digest' ∨ H.Collides
  | [], [], _, _, _, _, _, heq => .inl heq
  | [], _ :: _, _, _, _, _, hlen, _ => absurd hlen.symm (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, _, _, hlen, _ => absurd hlen (Nat.succ_ne_zero _)
  | _ :: path, _ :: path', h, index, _, _, hlen, heq => by
    simp only [climb] at heq
    rcases climb_inj path path' (h - 1) (index / 2) _ _ (Nat.succ.inj hlen) heq
      with hinject | hcol
    · rcases inject_inj hinject with hparent | hcol
      · exact parent_inj hparent
      · exact .inr hcol
    · exact .inr hcol

/-- Two climbs to the same digest that pass through the same node of the layer
of log-height `g` inject the same rows there. -/
theorem climb_group [DecidableEq T] :
    ∀ (path path' : List D) (h index index' : Nat) (digest digest' : D) (g : Nat),
      path.length = h → path'.length = h → g < h → hasHeight dims g = true →
      index >>> (h - g) = index' >>> (h - g) →
      climb H dims rows h index digest path = climb H dims rows' h index' digest' path' →
      groupRows dims rows g = groupRows dims rows' g ∨ H.Collides
  | [], _, _, _, _, _, _, _, hlen, _, hg, _, _, _ =>
    absurd (hlen ▸ hg) (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, _, _, _, hlen, hlen', _, _, _, _ =>
    absurd (hlen.trans hlen'.symm) (Nat.succ_ne_zero _)
  | _ :: path, _ :: path', h, index, index', _, _, g, hlen, hlen', hg, hheight, hindex, heq => by
    simp only [climb] at heq
    have hpath : path.length = h - 1 := by rw [← hlen, List.length_cons, Nat.add_sub_cancel]
    have hpath' : path'.length = h - 1 := by rw [← hlen', List.length_cons, Nat.add_sub_cancel]
    by_cases hlast : g = h - 1
    · -- The two climbs meet at the parents, where the rows are injected.
      have hshift : h - g = 1 := by omega
      have hnode : index / 2 = index' / 2 := by
        simpa only [hshift, Nat.shiftRight_eq_div_pow, Nat.pow_one] using hindex
      rw [← hnode] at heq
      rcases climb_inj path path' (h - 1) (index / 2) _ _ (hpath.trans hpath'.symm) heq
        with hinject | hcol
      · exact inject_group (hlast ▸ hheight) (hlast ▸ hinject)
      · exact .inr hcol
    · have hbelow : g < h - 1 := Nat.lt_of_le_of_ne (Nat.le_sub_one_of_lt hg) hlast
      have hshift : h - g = 1 + (h - 1 - g) := by omega
      have hhalf : ∀ i : Nat, i >>> (h - g) = (i / 2) >>> (h - 1 - g) := fun i => by
        rw [hshift, Nat.shiftRight_add, Nat.shiftRight_eq_div_pow i 1, Nat.pow_one]
      have hnode : (index / 2) >>> (h - 1 - g) = (index' / 2) >>> (h - 1 - g) := by
        rw [← hhalf, ← hhalf, hindex]
      exact climb_group path path' (h - 1) (index / 2) (index' / 2) _ _ g
        hpath hpath' hbelow hheight hnode heq

end Binding

/-! ## Openings -/

/-- Check an opening at one index: `rows[m]` is claimed to be the row of matrix
`m` at `index` shifted right by the difference between the tallest log-height
and that of the matrix, and `path` holds the sibling at each level, leaf level
first. -/
def verifyOpening [DecidableEq D] (H : MerkleHasher T D) (root : D)
    (dims : Array Dimensions) (index : Nat) (rows : Array (Array T)) (path : List D) : Bool :=
  let top := maxLogHeight dims.toList
  dims.size != 0 && widthsMatch dims.toList rows.toList && path.length == top
    && decide (index < 2 ^ top)
    && climb H dims.toList rows.toList top index
        (groupDigest H dims.toList rows.toList top) path == root

/-- Check openings at several indices, one path per index. -/
def verifyOpenings [DecidableEq D] (H : MerkleHasher T D) (root : D)
    (dims : Array Dimensions) (indices : Array Nat) (openedRows : Array (Array (Array T)))
    (paths : Array (List D)) : Bool :=
  openedRows.size == indices.size && paths.size == indices.size
    && (List.range indices.size).all fun query =>
      match indices[query]?, openedRows[query]?, paths[query]? with
      | some index, some rows, some path => verifyOpening H root dims index rows path
      | _, _, _ => false

section Binding

variable [DecidableEq D] {H : MerkleHasher T D} {root : D} {dims : Array Dimensions}

theorem verifyOpening_eq_true {index : Nat} {rows : Array (Array T)} {path : List D}
    (h : verifyOpening H root dims index rows path = true) :
    widthsMatch dims.toList rows.toList = true ∧ path.length = maxLogHeight dims.toList
      ∧ climb H dims.toList rows.toList (maxLogHeight dims.toList) index
          (groupDigest H dims.toList rows.toList (maxLogHeight dims.toList)) path = root := by
  simp only [verifyOpening, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.2⟩

/-- **Binding.** Two accepted openings under one root that address the same row
of matrix `m` open the same row of it, or the hash functions collide. -/
theorem verifyOpening_binding [DecidableEq T] {index index' : Nat}
    {rows rows' : Array (Array T)} {path path' : List D}
    (h : verifyOpening H root dims index rows path = true)
    (h' : verifyOpening H root dims index' rows' path' = true)
    {m : Nat} {d : Dimensions} (hd : dims[m]? = some d)
    (hindex : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight)) :
    rows[m]? = rows'[m]? ∨ H.Collides := by
  obtain ⟨hw, hlen, hroot⟩ := verifyOpening_eq_true h
  obtain ⟨hw', hlen', hroot'⟩ := verifyOpening_eq_true h'
  have hd' : dims.toList[m]? = some d := by rw [Array.getElem?_toList]; exact hd
  have hmem : d ∈ dims.toList := List.mem_of_getElem? hd'
  have hle : d.logHeight ≤ maxLogHeight dims.toList := le_maxLogHeight hmem
  have hgroup : groupRows dims.toList rows.toList d.logHeight
      = groupRows dims.toList rows'.toList d.logHeight ∨ H.Collides := by
    rw [← hroot'] at hroot
    by_cases htop : d.logHeight = maxLogHeight dims.toList
    · -- A tallest matrix: its rows are in the leaf, and both openings start there.
      have hsame : index = index' := by
        simpa only [htop, Nat.sub_self, Nat.shiftRight_zero] using hindex
      rw [hsame] at hroot
      rcases climb_inj _ _ _ _ _ _ (hlen.trans hlen'.symm) hroot with hleaf | hcol
      · exact htop ▸ groupDigest_inj hleaf
      · exact .inr hcol
    · exact climb_group _ _ _ _ _ _ _ d.logHeight hlen hlen' (Nat.lt_of_le_of_ne hle htop)
        (hasHeight_of_mem hmem) hindex hroot
  rcases hgroup with hgroup | hcol
  · have := groupRows_inj _ _ _ _ hw hw' hgroup m d hd' rfl
    simp only [Array.getElem?_toList] at this
    exact .inl this
  · exact .inr hcol

/-- Lists of equal length agree if they agree at every position, where each
position may instead yield `C`. -/
private theorem list_eq_or {α : Type} [DecidableEq α] {C : Prop} :
    ∀ (l l' : List α), l.length = l'.length → (∀ m : Nat, l[m]? = l'[m]? ∨ C) → l = l' ∨ C
  | [], [], _, _ => .inl rfl
  | [], _ :: _, hlen, _ => absurd hlen.symm (Nat.succ_ne_zero _)
  | _ :: _, [], hlen, _ => absurd hlen (Nat.succ_ne_zero _)
  | a :: l, a' :: l', hlen, hall => by
    have hlen := Nat.succ.inj hlen
    rcases hall 0 with hhead | hc
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hhead
      rcases list_eq_or l l' hlen (fun m => by simpa using hall (m + 1)) with htail | hc
      · exact .inl (by rw [hhead, htail])
      · exact .inr hc
    · exact .inr hc

/-- Two accepted openings at the same index open the same rows of every matrix,
or the hash functions collide. -/
theorem verifyOpening_binding_index [DecidableEq T] {index : Nat}
    {rows rows' : Array (Array T)} {path path' : List D}
    (h : verifyOpening H root dims index rows path = true)
    (h' : verifyOpening H root dims index rows' path' = true) :
    rows = rows' ∨ H.Collides := by
  have hlen : rows.toList.length = rows'.toList.length := by
    rw [widthsMatch_length (verifyOpening_eq_true h).1,
      widthsMatch_length (verifyOpening_eq_true h').1]
  refine (list_eq_or rows.toList rows'.toList hlen fun m => ?_).imp Array.toList_inj.mp id
  simp only [Array.getElem?_toList]
  cases hd : dims[m]? with
  | none =>
    -- Past the last matrix neither opening has a row.
    have hm : dims.toList.length ≤ m := by
      simpa only [Array.getElem?_eq_none_iff, Array.length_toList] using hd
    have hrows : rows[m]? = none := by
      rw [Array.getElem?_eq_none_iff, ← Array.length_toList,
        widthsMatch_length (verifyOpening_eq_true h).1]
      exact hm
    have hrows' : rows'[m]? = none := by
      rw [Array.getElem?_eq_none_iff, ← Array.length_toList,
        widthsMatch_length (verifyOpening_eq_true h').1]
      exact hm
    exact .inl (hrows.trans hrows'.symm)
  | some d => exact verifyOpening_binding h h' hd rfl

/-- An accepted opening at several indices holds an accepted opening at each. -/
theorem verifyOpenings_query {indices : Array Nat} {openedRows : Array (Array (Array T))}
    {paths : Array (List D)} (h : verifyOpenings H root dims indices openedRows paths = true)
    {query index : Nat} {rows : Array (Array T)} (hindex : indices[query]? = some index)
    (hrows : openedRows[query]? = some rows) :
    ∃ path, verifyOpening H root dims index rows path = true := by
  simp only [verifyOpenings, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hquery : query < indices.size := (Array.getElem?_eq_some_iff.mp hindex).1
  have hall := h.2 query hquery
  rw [hindex, hrows] at hall
  cases hpath : paths[query]? with
  | none => simp [hpath] at hall
  | some path => exact ⟨path, by simpa only [hpath] using hall⟩

/-- **Binding of openings at several indices.** Two queries, of the same
accepted opening or of two different ones under one root, that address the same
row of matrix `m` open the same row of it, or the hash functions collide. This
is what lets a commitment stand for one matrix per position in the batch. -/
theorem verifyOpenings_binding [DecidableEq T] {indices indices' : Array Nat}
    {openedRows openedRows' : Array (Array (Array T))} {paths paths' : Array (List D)}
    (h : verifyOpenings H root dims indices openedRows paths = true)
    (h' : verifyOpenings H root dims indices' openedRows' paths' = true)
    {query query' index index' : Nat} {rows rows' : Array (Array T)}
    (hindex : indices[query]? = some index) (hrows : openedRows[query]? = some rows)
    (hindex' : indices'[query']? = some index') (hrows' : openedRows'[query']? = some rows')
    {m : Nat} {d : Dimensions} (hd : dims[m]? = some d)
    (hrow : index >>> (maxLogHeight dims.toList - d.logHeight)
      = index' >>> (maxLogHeight dims.toList - d.logHeight)) :
    rows[m]? = rows'[m]? ∨ H.Collides := by
  obtain ⟨_, hopen⟩ := verifyOpenings_query h hindex hrows
  obtain ⟨_, hopen'⟩ := verifyOpenings_query h' hindex' hrows'
  exact verifyOpening_binding hopen hopen' hd hrow

end Binding

end Merkle

/-- The Merkle commitment scheme over a hasher, as the interface the verifier
is written against. A commitment is a root; a proof is one path per query. -/
def merkleMmcs {T D : Type} [DecidableEq D] (H : MerkleHasher T D) : Mmcs T D where
  MultiProof := Array (List D)
  verifyMultiBatch := Merkle.verifyOpenings H

end CertiFri
