import Mathlib.Data.Nat.Notation
import CertiFri.Merkle

/-!
# The Merkle check under a map of the entries

A Merkle hasher over entries `T'` gives one over entries `T` for every map
`g : T → T'`: hash the image of the row. The opening check for that hasher on
rows over `T` is the opening check for the original hasher on the images of the
rows (`verifyOpenings_map`).

This is how a commitment scheme over an executable field is read as one over
the field it implements: the hasher of the executable scheme is the hasher of
the model applied to the modelled values of a row.

The steps of the check (`widthsMatch`, `groupRows`, `groupDigest`, `inject`,
`parent`, `climb`, `verifyOpening`) each have their statement in
`CertiFri.Exec.Checks`.

Nothing is assumed about `g` or about the hash functions. Binding of the mapped
scheme is not covered here.
-/

namespace CertiFri.Exec

namespace Checks

variable {T T' D : Type}

/-- Mapping the entries keeps the widths of the rows. -/
theorem widthsMatch_map (g : T → T') :
    ∀ (dims : List Dimensions) (rows : List (Array T)),
      Merkle.widthsMatch dims (rows.map fun row => row.map g) = Merkle.widthsMatch dims rows
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: dims, _ :: rows => by
    simp only [List.map_cons, Merkle.widthsMatch, Array.size_map, widthsMatch_map g dims rows]

/-- The rows of one height, concatenated, of the mapped rows are the image of
those of the rows. -/
theorem groupRows_map (g : T → T') :
    ∀ (dims : List Dimensions) (rows : List (Array T)) (h : ℕ),
      Merkle.groupRows dims (rows.map fun row => row.map g) h =
        (Merkle.groupRows dims rows h).map g
  | [], _, _ => by simp only [Merkle.groupRows, List.map_nil]
  | _ :: _, [], _ => by simp only [List.map_nil, Merkle.groupRows]
  | d :: dims, row :: rows, h => by
    simp only [List.map_cons, Merkle.groupRows]
    split
    · rw [List.map_append, groupRows_map g dims rows h, Array.toList_map]
    · exact groupRows_map g dims rows h

/-- The digest of the rows of one height, for the hasher that hashes the image
of a row. -/
theorem groupDigest_map (g : T → T') (H : MerkleHasher T' D) (dims : List Dimensions)
    (rows : List (Array T)) (h : ℕ) :
    Merkle.groupDigest ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims rows h =
      Merkle.groupDigest H dims (rows.map fun row => row.map g) h := by
  simp only [Merkle.groupDigest, groupRows_map, List.map_toArray]

/-- The injection of the rows of one height, for the hasher that hashes the
image of a row. -/
theorem inject_map (g : T → T') (H : MerkleHasher T' D) (dims : List Dimensions)
    (rows : List (Array T)) (h : ℕ) (digest : D) :
    Merkle.inject ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims rows h digest =
      Merkle.inject H dims (rows.map fun row => row.map g) h digest := by
  simp only [Merkle.inject, groupDigest_map]

/-- The parent of a node only depends on the compression function. -/
theorem parent_map (g : T → T') (H : MerkleHasher T' D) (index : ℕ) (digest sibling : D) :
    Merkle.parent ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ index digest sibling =
      Merkle.parent H index digest sibling :=
  rfl

/-- The climb to the root, for the hasher that hashes the image of a row. -/
theorem climb_map (g : T → T') (H : MerkleHasher T' D) (dims : List Dimensions)
    (rows : List (Array T)) :
    ∀ (path : List D) (h index : ℕ) (digest : D),
      Merkle.climb ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ dims rows h index digest path =
        Merkle.climb H dims (rows.map fun row => row.map g) h index digest path
  | [], _, _, _ => rfl
  | sibling :: path, h, index, digest => by
    simp only [Merkle.climb, inject_map, parent_map]
    exact climb_map g H dims rows path _ _ _

/-- The check of an opening at one index, for the hasher that hashes the image
of a row, is the check of the images of the rows. -/
theorem verifyOpening_map [DecidableEq D] (g : T → T') (H : MerkleHasher T' D) (root : D)
    (dims : Array Dimensions) (index : ℕ) (rows : Array (Array T)) (path : List D) :
    Merkle.verifyOpening ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ root dims index rows path =
      Merkle.verifyOpening H root dims index (rows.map fun row => row.map g) path := by
  simp only [Merkle.verifyOpening, Array.toList_map, widthsMatch_map, climb_map, groupDigest_map]

end Checks

variable {T T' D : Type} [DecidableEq D]

/-- **The Merkle check under a map of the entries.** For the hasher that hashes
the image under `g` of a row, the check of openings at several indices is the
check, for the hasher `H`, of the images under `g` of the opened rows. -/
theorem verifyOpenings_map (g : T → T') (H : MerkleHasher T' D) (root : D)
    (dims : Array Dimensions) (indices : Array ℕ) (rows : Array (Array (Array T)))
    (paths : Array (List D)) :
    Merkle.verifyOpenings ⟨fun xs => H.hashRows (xs.map g), H.compress⟩ root dims indices rows
        paths =
      Merkle.verifyOpenings H root dims indices (rows.map fun r => r.map fun row => row.map g)
        paths := by
  simp only [Merkle.verifyOpenings, Array.size_map, Array.getElem?_map]
  congr 1
  refine List.all_congr rfl fun query => ?_
  cases indices[query]? <;> cases rows[query]? <;> cases paths[query]? <;>
    simp only [Option.map_none, Option.map_some, Checks.verifyOpening_map]

end CertiFri.Exec
