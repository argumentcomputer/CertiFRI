import CertiFri.Merkle

/-!
# Tests of the Merkle verifier

A reference tree builder, written independently of the verifier: it computes
every layer bottom-up, where the verifier climbs one path. The tests check that
the verifier accepts every opening the builder produces and rejects tampered
ones.

The layout of the tree is checked against Plonky3: the same batch, committed
and opened by Plonky3's `MerkleTreeMmcs` under the same toy hasher, gives the
root and the paths pinned below, and the verifier accepts them.

The builder is test code. Nothing is proved about it, and the hasher is a toy.
-/

namespace CertiFriTest.Merkle

open CertiFri CertiFri.Merkle

/-- A toy hasher over naturals. It is not collision resistant; it only has to
tell the honest openings below from the tampered ones. -/
def toy : MerkleHasher Nat Nat where
  hashRows xs := xs.foldl (fun acc x => (acc * 1000003 + x + 1) % 4294967291) 7
  compress a b := (a * 2654435761 + b * 40503 + 12345) % 4294967291

/-- A matrix to commit to. It must have `2 ^ logHeight` rows of equal width. -/
structure Matrix where
  logHeight : Nat
  rows : Array (Array Nat)

def dimsOf (ms : Array Matrix) : Array Dimensions :=
  ms.map fun m => { width := (m.rows[0]?.getD #[]).size, logHeight := m.logHeight }

def topOf (ms : Array Matrix) : Nat :=
  ms.foldl (fun acc m => max acc m.logHeight) 0

/-- Row `i` of every matrix of log-height `h`, concatenated in batch order. -/
def groupAt (ms : Array Matrix) (h i : Nat) : Array Nat :=
  ms.foldl (fun acc m => if m.logHeight = h then acc ++ m.rows[i]?.getD #[] else acc) #[]

/-- The layer of log-height `h`, from the layer above it. -/
def layerBelow (ms : Array Matrix) (h : Nat) (above : Array Nat) : Array Nat :=
  Array.ofFn (n := 2 ^ h) fun j =>
    let node := toy.compress (above[2 * j.val]?.getD 0) (above[2 * j.val + 1]?.getD 0)
    if ms.any (·.logHeight == h) then toy.compress node (toy.hashRows (groupAt ms h j)) else node

/-- Every layer, leaves first. -/
def layers (ms : Array Matrix) : List (Array Nat) :=
  go (topOf ms) (Array.ofFn (n := 2 ^ topOf ms) fun i => toy.hashRows (groupAt ms (topOf ms) i))
where
  go : Nat → Array Nat → List (Array Nat)
    | 0, layer => [layer]
    | h + 1, layer => layer :: go h (layerBelow ms h layer)

def rootOf (ms : Array Matrix) : Nat :=
  ((layers ms).getLast?.getD #[])[0]?.getD 0

def rowsAt (ms : Array Matrix) (index : Nat) : Array (Array Nat) :=
  ms.map fun m => m.rows[index >>> (topOf ms - m.logHeight)]?.getD #[]

def pathAt (ms : Array Matrix) (index : Nat) : List Nat :=
  (List.range (topOf ms)).map fun level =>
    ((layers ms)[level]?.getD #[])[(index >>> level) ^^^ 1]?.getD 0

/-- Matrix `m` with `2 ^ logHeight` rows of the given width and distinct entries. -/
def matrix (m logHeight width : Nat) : Matrix where
  logHeight
  rows := Array.ofFn (n := 2 ^ logHeight) fun i =>
    Array.ofFn (n := width) fun j => 1000 * m + 10 * i.val + j.val

/-- Two matrices of the tallest height, none of log-height 2, one of log-height 1
and one single row, which is injected at the root. -/
def batch : Array Matrix :=
  #[matrix 1 3 2, matrix 2 1 3, matrix 3 3 1, matrix 4 0 2]

def dims : Array Dimensions := dimsOf batch
def root : Nat := rootOf batch

def accepts (index : Nat) (rows : Array (Array Nat)) (path : List Nat) : Bool :=
  verifyOpening toy root dims index rows path

/-- Add one to entry `j` of row `m`. -/
def bump (rows : Array (Array Nat)) (m j : Nat) : Array (Array Nat) :=
  rows.modify m fun row => row.modify j (· + 1)

def allIndices : List Nat := List.range 8

/-! ## Honest openings are accepted -/

#guard allIndices.all fun i => accepts i (rowsAt batch i) (pathAt batch i)

-- A single row: the tree is one leaf and the path is empty.
#guard verifyOpening toy (rootOf #[matrix 1 0 3]) (dimsOf #[matrix 1 0 3]) 0
  (rowsAt #[matrix 1 0 3] 0) []

-- One matrix, so nothing is injected.
#guard (List.range 4).all fun i =>
  verifyOpening toy (rootOf #[matrix 1 2 2]) (dimsOf #[matrix 1 2 2]) i
    (rowsAt #[matrix 1 2 2] i) (pathAt #[matrix 1 2 2] i)

-- Several indices at once, with a repeat, through the commitment-scheme interface.
#guard (merkleMmcs toy).verifyMultiBatch root dims #[5, 0, 5, 7]
  (#[5, 0, 5, 7].map (rowsAt batch)) (#[5, 0, 5, 7].map (pathAt batch))

/-! ## Plonky3's openings are accepted

The batch above, committed and opened at every index by Plonky3. Two revisions
give the same values: `3152b14a`, which the Rust prover pins, and `0d803737`,
which the `plonky3/` submodule pins. The generator is
`CertiFriTest/vectors/merkle_tree.rs`. -/

def plonky3Dims : Array Dimensions :=
  #[{ width := 2, logHeight := 3 }, { width := 3, logHeight := 1 },
    { width := 1, logHeight := 3 }, { width := 2, logHeight := 0 }]

def plonky3Root : Nat := 111120707

/-- The opened rows and the path at each index, in index order. -/
def plonky3Openings : List (Array (Array Nat) × List Nat) := [
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

-- The verifier accepts each of Plonky3's openings under Plonky3's root.
#guard plonky3Openings.length == 8
#guard (allIndices.zip plonky3Openings).all fun (i, rows, path) =>
  verifyOpening toy plonky3Root plonky3Dims i rows path

-- The reference builder computes the same dimensions, root, rows and paths.
#guard dims == plonky3Dims && root == plonky3Root
#guard (allIndices.zip plonky3Openings).all fun (i, rows, path) =>
  rowsAt batch i == rows && pathAt batch i == path

/-! ## Tampered openings are rejected -/

-- Any changed entry, in any matrix, at any index.
#guard allIndices.all fun i =>
  [(0, 0), (0, 1), (1, 0), (1, 2), (2, 0), (3, 0), (3, 1)].all fun (m, j) =>
    !accepts i (bump (rowsAt batch i) m j) (pathAt batch i)

-- Any changed sibling.
#guard allIndices.all fun i =>
  (List.range 3).all fun level =>
    !accepts i (rowsAt batch i) ((pathAt batch i).modify level (· + 1))

-- An opening presented at another index.
#guard allIndices.all fun i =>
  allIndices.all fun j => i == j || !accepts j (rowsAt batch i) (pathAt batch i)

-- An index past the last row, which would walk the same path.
#guard !accepts (3 + 8) (rowsAt batch 3) (pathAt batch 3)

-- A path that is too short or too long.
#guard !accepts 3 (rowsAt batch 3) ((pathAt batch 3).take 2)
#guard !accepts 3 (rowsAt batch 3) (pathAt batch 3 ++ [0])

-- A row of the wrong width, even when the concatenation is unchanged: the
-- first two matrices share a leaf, and an entry moves from one row to the next.
#guard !accepts 3 (((rowsAt batch 3).set! 0 #[1030]).set! 2 #[1031, 3030]) (pathAt batch 3)
#guard !accepts 3 ((rowsAt batch 3).modify 0 (·.push 0)) (pathAt batch 3)

-- A missing or an extra row.
#guard !accepts 3 (rowsAt batch 3).pop (pathAt batch 3)
#guard !accepts 3 ((rowsAt batch 3).push #[]) (pathAt batch 3)

-- An empty batch.
#guard !verifyOpening toy (toy.hashRows #[]) #[] 0 #[] []

-- Several indices: one bad query, or counts that do not line up.
#guard !verifyOpenings toy root dims #[5, 0]
  #[rowsAt batch 5, bump (rowsAt batch 0) 1 1] #[pathAt batch 5, pathAt batch 0]
#guard !verifyOpenings toy root dims #[5, 0] #[rowsAt batch 5] #[pathAt batch 5, pathAt batch 0]
#guard !verifyOpenings toy root dims #[5, 0] #[rowsAt batch 5, rowsAt batch 0] #[pathAt batch 5]

end CertiFriTest.Merkle
