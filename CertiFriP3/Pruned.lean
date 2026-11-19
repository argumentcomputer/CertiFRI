import CertiFri.Merkle

/-!
# Plonky3's pruned Merkle multi-openings

Plonky3's `MerkleTreeMmcs` proves an opening at several indices with one flat
list of digests, `PrunedMerklePaths` (`merkle-tree/src/pruning.rs`): the
siblings that the verifier cannot compute from the opened rows. This file
restores one full authentication path per query from such a proof
(`restorePaths`) and passes the paths to the certified check
`Merkle.verifyOpenings` (`prunedMmcs`).

## The format

The *frontier* of a layer is the set of its nodes that lie above a queried
leaf. The frontier of the leaf layer is the set of queried indices: neither the
order of the queries nor their repetitions change the proof. The verifier
computes the digest of every node of every frontier, layer by layer:

* a leaf of the frontier is the hash of the rows opened there;
* the nodes of a frontier are taken in ascending order of index. When both
  children of a parent are in the frontier, each is the sibling of the other
  and the proof holds nothing for them. Otherwise the sibling of the one child
  in the frontier is the next digest of the proof;
* where shorter matrices are injected, the rows are those opened by the query
  at the smallest index below the node, and by the first such query if several
  have that index.

So the proof lists the missing siblings level by level, leaf level first, and
by ascending node index within a level. The indices determine how many there
are: a proof with fewer or more digests is rejected.

The path of a query is read off this walk: at each level, the sibling of the
node above the queried leaf.

## What is and is not established

Nothing is proved about the restoration. `prunedMmcs` accepts only when the
restored paths pass `Merkle.verifyOpenings` (`prunedMmcs_accepts`), so
`Merkle.verifyOpenings_binding` applies to what it accepts, and a wrong
restoration can only cause a rejection. That it accepts Plonky3's proofs is
tested against vectors produced by Plonky3 (`CertiFriTest/P3/Pruned.lean`).

Covered: Plonky3's `verify_multi_batch` with two-to-one compression,
power-of-two heights and a single root (cap height 0), which is the tree of
`CertiFri.Merkle`. Not covered: compression of more than two digests, other
heights, a cap of several digests.

Plonky3 hashes the rows of one query per node of the frontier and compares the
rows of the other queries below that node with them. Here every query is
checked along its own restored path with its own rows. The two accept the same
openings unless a hash function collides: rows that differ from those Plonky3
hashed but hash alike are accepted here and rejected by Plonky3.
-/

namespace CertiFri.P3

variable {T D : Type}

/-- Plonky3's pruned multi-opening proof: the sibling digests the verifier
cannot compute itself, in Plonky3's order. Port of `PrunedMerklePaths`. -/
structure PrunedPaths (D : Type) where
  /-- The missing siblings: leaf level first, by ascending node index within a
  level. -/
  siblingHashes : Array D

namespace Pruned

/-- A node above a queried leaf, with what the walk knows about its subtree. -/
structure Node (T D : Type) where
  /-- Position of the node in its layer. -/
  index : Nat
  /-- Digest of the node, computed from the opened rows and the proof. -/
  digest : D
  /-- The rows opened by the query at the smallest index below the node. The
  nodes above it inject these rows. -/
  rows : List (Array T)
  /-- The queried indices below the node, in ascending order, each with the
  siblings found so far along its path, the latest first. -/
  below : List (Nat × List D)

/-- Record `sibling` as the next sibling on the path of every queried index. -/
def addSibling (sibling : D) (below : List (Nat × List D)) : List (Nat × List D) :=
  below.map fun (index, path) => (index, sibling :: path)

/-- The leaves of the frontier of a tree of depth `top`: one node per distinct
queried index, in ascending order. Queries at the same index are represented by
the first of them. -/
def leaves (H : MerkleHasher T D) (dims : List Dimensions) (top : Nat)
    (queries : List (Nat × List (Array T))) : List (Node T D) :=
  let ascending := queries.mergeSort fun a b => a.1 ≤ b.1
  (ascending.eraseRepsBy fun a b => a.1 == b.1).map fun (index, rows) =>
    { index, rows, digest := Merkle.groupDigest H dims rows top, below := [(index, [])] }

/-- The parent of `node`, in the layer of log-height `h`, from the digest of the
sibling of `node` and the queried indices below that sibling. -/
def Node.parent (H : MerkleHasher T D) (dims : List Dimensions) (h : Nat) (node : Node T D)
    (sibling : D) (belowSibling : List (Nat × List D)) : Node T D where
  index := node.index / 2
  digest := Merkle.inject H dims node.rows h (Merkle.parent H node.index node.digest sibling)
  rows := node.rows
  below := addSibling sibling node.below ++ belowSibling

/-- One level of the walk: from the frontier of a layer, in ascending order, to
the frontier of the layer above it, of log-height `h`. Two nodes with the same
parent are siblings of each other; any other node takes its sibling from the
front of `supplied`. Returns the parents and the digests left, or `none` if
`supplied` runs out. -/
def ascend (H : MerkleHasher T D) (dims : List Dimensions) (h : Nat) :
    List (Node T D) → List D → Option (List (Node T D) × List D)
  | [], supplied => some ([], supplied)
  | node :: nodes, supplied =>
    match nodes with
    | next :: rest =>
      if node.index / 2 = next.index / 2 then do
        let (parents, supplied) ← ascend H dims h rest supplied
        let below := addSibling node.digest next.below
        return (node.parent H dims h next.digest below :: parents, supplied)
      else do
        let sibling :: supplied := supplied | none
        let (parents, supplied) ← ascend H dims h nodes supplied
        return (node.parent H dims h sibling [] :: parents, supplied)
    | [] => do
      let sibling :: supplied := supplied | none
      return ([node.parent H dims h sibling []], supplied)

/-- Walk from the frontier of the layer of log-height `h` to the frontier of
the root layer. Returns it with the digests left, or `none` if `supplied` runs
out. -/
def walk (H : MerkleHasher T D) (dims : List Dimensions) :
    (h : Nat) → List (Node T D) → List D → Option (List (Node T D) × List D)
  | 0, nodes, supplied => some (nodes, supplied)
  | h + 1, nodes, supplied => do
    let (parents, supplied) ← ascend H dims h nodes supplied
    walk H dims h parents supplied

end Pruned

/-- Restore one full authentication path per query (leaf level first) from a
pruned proof and the opened rows: `openedRows[q]` holds the rows opened at
`indices[q]`. Returns `none` if the pruned proof does not have exactly the
digests the walk takes, if there is no matrix, or if there is not one set of
opened rows per index. -/
def restorePaths (H : MerkleHasher T D) (dims : Array Dimensions) (indices : Array Nat)
    (openedRows : Array (Array (Array T))) (proof : PrunedPaths D) : Option (Array (List D)) :=
  if dims.isEmpty || openedRows.size != indices.size then none
  else
    let top := Merkle.maxLogHeight dims.toList
    let queries := indices.toList.zip (openedRows.toList.map (·.toList))
    match Pruned.walk H dims.toList top (Pruned.leaves H dims.toList top queries)
        proof.siblingHashes.toList with
    | some (nodes, []) =>
      let found := nodes.flatMap (·.below)
      indices.mapM fun index => (found.lookup index).map List.reverse
    | _ => none

/-- The Merkle commitment scheme with Plonky3's pruned multi-opening proofs.
It accepts when the paths restored from the proof pass the certified check. -/
def prunedMmcs [DecidableEq D] (H : MerkleHasher T D) : Mmcs T D where
  MultiProof := PrunedPaths D
  verifyMultiBatch root dims indices openedRows proof :=
    match restorePaths H dims indices openedRows proof with
    | some paths => Merkle.verifyOpenings H root dims indices openedRows paths
    | none => false

/-- An opening that `prunedMmcs` accepts passes the certified check with the
restored paths, so it holds an accepted opening at every query. -/
theorem prunedMmcs_accepts [DecidableEq D] {H : MerkleHasher T D} {root : D}
    {dims : Array Dimensions} {indices : Array Nat} {openedRows : Array (Array (Array T))}
    {proof : PrunedPaths D}
    (h : (prunedMmcs H).verifyMultiBatch root dims indices openedRows proof = true) :
    ∃ paths, restorePaths H dims indices openedRows proof = some paths
      ∧ Merkle.verifyOpenings H root dims indices openedRows paths = true := by
  unfold prunedMmcs at h
  dsimp only at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · exact absurd h Bool.false_ne_true

end CertiFri.P3
