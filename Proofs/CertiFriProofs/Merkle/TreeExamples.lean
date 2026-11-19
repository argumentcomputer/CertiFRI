import CertiFriProofs.Merkle.Tree

/-!
# Examples of the Merkle tree

Checks, by evaluation in the kernel, that the tree of `CertiFri.Merkle` is the
intended one, independently of the proof that its openings verify.

The batch is the one of the verifier's tests (`CertiFriTest/Merkle.lean`): four
matrices of three heights, two of them injected below the leaves, one of those
at the root. Under the toy hasher of those tests, Plonky3's `MerkleTreeMmcs`
commits to it with the root and opens it with the paths pinned here
(`CertiFriTest/vectors/merkle_tree.rs` generates them). The examples check that
`root`, `rowsAt` and `pathAt` give exactly these values, that the verifier
accepts them, and that it rejects changed ones.

The hasher is a toy: it is not collision resistant, and nothing here depends on
it beyond telling the openings below apart.
-/

namespace CertiFri.Merkle.Tree.Examples

/-- A toy hasher over naturals: the one of the verifier's tests, with the fold
over the list of entries so that the kernel evaluates it. -/
def toy : MerkleHasher ℕ ℕ where
  hashRows xs := xs.toList.foldl (fun acc x => (acc * 1000003 + x + 1) % 4294967291) 7
  compress a b := (a * 2654435761 + b * 40503 + 12345) % 4294967291

/-- Matrix `m` of the batch: entry `j` of row `i` is `1000 * m + 10 * i + j`. -/
def matrix (m logHeight width : ℕ) : Matrix ℕ where
  logHeight := logHeight
  width := width
  row i := ((List.range width).map fun j => 1000 * m + 10 * i + j).toArray

/-- Two matrices of the tallest height, none of log-height 2, one of log-height
1 and one single row, which is injected at the root. -/
def batch : List (Matrix ℕ) :=
  [matrix 1 3 2, matrix 2 1 3, matrix 3 3 1, matrix 4 0 2]

/-- The root Plonky3 commits to. -/
def plonky3Root : ℕ := 111120707

/-- The rows and the path Plonky3 opens at each index, in index order. -/
def plonky3Openings : List (Array (Array ℕ) × List ℕ) := [
  (#[#[1000, 1001], #[2000, 2001, 2002], #[3000], #[4000, 4001]],
    [1194002756, 38512364, 2872480574]),
  (#[#[1010, 1011], #[2000, 2001, 2002], #[3010], #[4000, 4001]],
    [4102823365, 38512364, 2872480574]),
  (#[#[1020, 1021], #[2000, 2001, 2002], #[3020], #[4000, 4001]],
    [3966296120, 401543074, 2872480574]),
  (#[#[1030, 1031], #[2000, 2001, 2002], #[3030], #[4000, 4001]],
    [2580149438, 401543074, 2872480574]),
  (#[#[1040, 1041], #[2010, 2011, 2012], #[3040], #[4000, 4001]],
    [2443622193, 3607418235, 2203775664]),
  (#[#[1050, 1051], #[2010, 2011, 2012], #[3050], #[4000, 4001]],
    [1057475511, 3607418235, 2203775664]),
  (#[#[1060, 1061], #[2010, 2011, 2012], #[3060], #[4000, 4001]],
    [920948266, 3970448945, 2203775664]),
  (#[#[1070, 1071], #[2010, 2011, 2012], #[3070], #[4000, 4001]],
    [3829768875, 3970448945, 2203775664])]

/-! ## The tree is Plonky3's -/

example : dimsOf batch = #[⟨2, 3⟩, ⟨3, 1⟩, ⟨1, 3⟩, ⟨2, 0⟩] := by decide

example : maxLogHeight (dimsOf batch).toList = 3 := by decide

example : root toy batch = plonky3Root := by decide

example : (List.range 8).map (fun i => (rowsAt batch i, pathAt toy batch i)) = plonky3Openings := by
  decide

/-! ## The verifier accepts the openings of the tree -/

example : ((List.range 8).all fun i =>
    verifyOpening toy (root toy batch) (dimsOf batch) i (rowsAt batch i) (pathAt toy batch i))
      = true := by
  decide

-- Several indices at once, with a repeat.
example : verifyOpenings toy (root toy batch) (dimsOf batch) #[5, 0, 5, 7]
    #[rowsAt batch 5, rowsAt batch 0, rowsAt batch 5, rowsAt batch 7]
    #[pathAt toy batch 5, pathAt toy batch 0, pathAt toy batch 5, pathAt toy batch 7] = true := by
  decide

-- A single row: the tree is one leaf and the path is empty.
example : pathAt toy [matrix 1 0 3] 0 = [] := by decide

example : root toy [matrix 1 0 3] = toy.hashRows #[1000, 1001, 1002] := by decide

example : verifyOpening toy (root toy [matrix 1 0 3]) (dimsOf [matrix 1 0 3]) 0
    (rowsAt [matrix 1 0 3] 0) (pathAt toy [matrix 1 0 3] 0) = true := by
  decide

/-! ## The verifier rejects changed openings -/

-- The opening at index 3 that the examples below change.
example : rowsAt batch 3 = #[#[1030, 1031], #[2000, 2001, 2002], #[3030], #[4000, 4001]] := by
  decide

-- A changed entry in a row of a tallest matrix, which is hashed into the leaf.
example : verifyOpening toy (root toy batch) (dimsOf batch) 3
    #[#[1030, 1032], #[2000, 2001, 2002], #[3030], #[4000, 4001]] (pathAt toy batch 3)
      = false := by
  decide

-- A changed entry in the row of the matrix injected in the layer of two nodes.
example : verifyOpening toy (root toy batch) (dimsOf batch) 3
    #[#[1030, 1031], #[2000, 2001, 2003], #[3030], #[4000, 4001]] (pathAt toy batch 3)
      = false := by
  decide

-- A changed entry in the row of the matrix injected at the root.
example : verifyOpening toy (root toy batch) (dimsOf batch) 3
    #[#[1030, 1031], #[2000, 2001, 2002], #[3030], #[4001, 4001]] (pathAt toy batch 3)
      = false := by
  decide

-- The row of the injected matrix at another index.
example : verifyOpening toy (root toy batch) (dimsOf batch) 3
    #[#[1030, 1031], #[2010, 2011, 2012], #[3030], #[4000, 4001]] (pathAt toy batch 3)
      = false := by
  decide

-- An opening presented at another index.
example : verifyOpening toy (root toy batch) (dimsOf batch) 2 (rowsAt batch 3) (pathAt toy batch 3)
    = false := by
  decide

-- The path of another index.
example : verifyOpening toy (root toy batch) (dimsOf batch) 3 (rowsAt batch 3) (pathAt toy batch 5)
    = false := by
  decide

end CertiFri.Merkle.Tree.Examples
