import CertiFriP3.Pruned
import CertiFriTest.Merkle

/-!
# Tests of the pruned Merkle multi-openings

Plonky3 commits to five batches of matrices under the toy hasher of
`CertiFriTest.Merkle`, opens each at several lists of indices with
`open_multi_batch`, and accepts each opening with `verify_multi_batch`. The
values it computes are pinned below. The tests check that `prunedMmcs` accepts
every one of Plonky3's pruned proofs, that the paths it restores are those of
Plonky3's single-index openings, and that it rejects tampered openings.

The generator is `CertiFriTest/vectors/merkle_pruned.rs`. It prints the pinned
definitions as they stand here, and it asserts that Plonky3 rejects the tampered
openings that are rejected below.

The hasher is a toy, and nothing here is a proof.
-/

namespace CertiFriTest.P3.Pruned

open CertiFri CertiFri.P3
open CertiFriTest.Merkle (toy Matrix matrix dimsOf rootOf rowsAt pathAt plonky3Dims plonky3Root
  plonky3Openings)

/-- A batch committed by Plonky3, with its openings. -/
structure Batch where
  /-- Dimensions of the matrices. Matrix `m` holds `1000 * (m + 1) + 10 * row + column`. -/
  dims : Array Dimensions
  /-- The commitment. -/
  root : Nat
  /-- The single-index opening at every index: the opened rows and the path. -/
  single : Array (Array (Array Nat) × List Nat)
  /-- Multi-openings: the indices and the pruned proof. The opened rows are
  those of the single-index openings. -/
  multi : List (Array Nat × Array Nat)

/-! ## Values computed by Plonky3

Printed by the generator at revision `3152b14a`. Among the lists of indices of
each batch: a single index, two siblings, indices in different halves, every
index, repeated indices, unsorted indices, and the queries
`[37, 9, 33, 60, 8, 22]` of a domain of 64 points reduced to the height of the
batch. -/

/-- Two matrices of the tallest height, none of log-height 2, one of log-height 1 and
one single row: the batch of `CertiFriTest.Merkle`. -/
def mixed : Batch where
  dims := #[⟨2, 3⟩, ⟨3, 1⟩, ⟨1, 3⟩, ⟨2, 0⟩]
  root := 111120707
  single := #[
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
  multi := [
    (#[5], #[1057475511, 3607418235, 2203775664]),
    (#[2, 3], #[401543074, 2872480574]),
    (#[1, 6], #[4102823365, 920948266, 38512364, 3970448945]),
    (#[0, 1, 2, 3, 4, 5, 6, 7], #[]),
    (#[5, 0, 5, 7], #[1194002756, 1057475511, 3829768875, 38512364]),
    (#[6, 1, 4], #[4102823365, 2443622193, 920948266, 38512364]),
    (#[3, 3, 3], #[2580149438, 401543074, 2872480574]),
    (#[0, 1, 2], #[3966296120, 2872480574]),
    (#[4, 5, 6, 7], #[2203775664]),
    (#[7, 6, 5, 4, 3, 2, 1, 0], #[]),
    (#[4, 1, 4, 7, 1, 2], #[4102823365, 3966296120, 2443622193, 3829768875]),
    (#[], #[])]

/-- Two matrices of the tallest height and one injected at every level above. -/
def ladder : Batch where
  dims := #[⟨1, 4⟩, ⟨2, 3⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 1⟩, ⟨1, 0⟩]
  root := 2464277578
  single := #[
    (#[#[1000], #[2000, 2001], #[3000], #[4000, 4001], #[5000, 5001, 5002], #[6000]],
      [4193012754, 1929645730, 4039273190, 1213525703]),
    (#[#[1010], #[2000, 2001], #[3000], #[4010, 4011], #[5000, 5001, 5002], #[6000]],
      [2806866072, 1929645730, 4039273190, 1213525703]),
    (#[#[1020], #[2010, 2011], #[3000], #[4020, 4021], #[5000, 5001, 5002], #[6000]],
      [2670338827, 1840325027, 4039273190, 1213525703]),
    (#[#[1030], #[2010, 2011], #[3000], #[4030, 4031], #[5000, 5001, 5002], #[6000]],
      [1284192145, 1840325027, 4039273190, 1213525703]),
    (#[#[1040], #[2020, 2021], #[3010], #[4040, 4041], #[5000, 5001, 5002], #[6000]],
      [1147664900, 2108287136, 1163192499, 1213525703]),
    (#[#[1050], #[2020, 2021], #[3010], #[4050, 4051], #[5000, 5001, 5002], #[6000]],
      [4056485509, 2108287136, 1163192499, 1213525703]),
    (#[#[1060], #[2030, 2031], #[3010], #[4060, 4061], #[5000, 5001, 5002], #[6000]],
      [3919958264, 2018966433, 1163192499, 1213525703]),
    (#[#[1070], #[2030, 2031], #[3010], #[4070, 4071], #[5000, 5001, 5002], #[6000]],
      [2533811582, 2018966433, 1163192499, 1213525703]),
    (#[#[1080], #[2040, 2041], #[3020], #[4080, 4081], #[5010, 5011, 5012], #[6000]],
      [2397284337, 2286928542, 1201499990, 3481874849]),
    (#[#[1090], #[2040, 2041], #[3020], #[4090, 4091], #[5010, 5011, 5012], #[6000]],
      [1011137655, 2286928542, 1201499990, 3481874849]),
    (#[#[1100], #[2050, 2051], #[3020], #[4100, 4101], #[5010, 5011, 5012], #[6000]],
      [874610410, 2197607839, 1201499990, 3481874849]),
    (#[#[1110], #[2050, 2051], #[3020], #[4110, 4111], #[5010, 5011, 5012], #[6000]],
      [3783431019, 2197607839, 1201499990, 3481874849]),
    (#[#[1120], #[2060, 2061], #[3030], #[4120, 4121], #[5010, 5011, 5012], #[6000]],
      [3646903774, 2465569948, 2620386590, 3481874849]),
    (#[#[1130], #[2060, 2061], #[3030], #[4130, 4131], #[5010, 5011, 5012], #[6000]],
      [2260757092, 2465569948, 2620386590, 3481874849]),
    (#[#[1140], #[2070, 2071], #[3030], #[4140, 4141], #[5010, 5011, 5012], #[6000]],
      [2124229847, 2376249245, 2620386590, 3481874849]),
    (#[#[1150], #[2070, 2071], #[3030], #[4150, 4151], #[5010, 5011, 5012], #[6000]],
      [738083165, 2376249245, 2620386590, 3481874849])]
  multi := [
    (#[11], #[3783431019, 2197607839, 1201499990, 3481874849]),
    (#[6, 7], #[2018966433, 1163192499, 1213525703]),
    (#[2, 13], #[2670338827, 2260757092, 1840325027, 2465569948, 4039273190, 2620386590]),
    (#[0, 1, 2, 3, 12, 13, 14, 15], #[4039273190, 2620386590]),
    (#[9, 4, 9, 9, 4], #[1147664900, 1011137655, 2108287136, 2286928542, 1163192499, 1201499990]),
    (#[15, 0, 8],
      #[4193012754, 2397284337, 738083165, 1929645730, 2286928542, 2376249245, 4039273190]),
    (#[9, 2, 8, 15, 2, 5],
      #[2670338827, 4056485509, 738083165, 1840325027, 2108287136, 2286928542, 2376249245]),
    (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], #[])]

/-- One matrix: nothing is injected. -/
def plain : Batch where
  dims := #[⟨2, 2⟩]
  root := 3362107204
  single := #[
    (#[#[1000, 1001]], [256319778, 3678648953]),
    (#[#[1010, 1011]], [246319738, 3678648953]),
    (#[#[1020, 1021]], [276319858, 242313680]),
    (#[#[1030, 1031]], [266319818, 242313680])]
  multi := [
    (#[2], #[276319858, 242313680]),
    (#[0, 1], #[3678648953]),
    (#[1, 2], #[246319738, 276319858]),
    (#[3, 0, 3], #[256319778, 266319818]),
    (#[0, 1, 2, 3], #[]),
    (#[2, 0, 2, 3, 0, 1], #[])]

/-- Two leaves, and a row injected at the root. -/
def pair : Batch where
  dims := #[⟨1, 1⟩, ⟨2, 0⟩]
  root := 1017965728
  single := #[
    (#[#[1000], #[2000, 2001]], [7001032]),
    (#[#[1010], #[2000, 2001]], [7001022])]
  multi := [
    (#[0], #[7001032]),
    (#[1], #[7001022]),
    (#[0, 1], #[]),
    (#[1, 0, 1], #[]),
    (#[1, 0, 1, 1, 0, 0], #[])]

/-- The tallest matrix has one row: the tree is one leaf and every path is empty. -/
def oneRow : Batch where
  dims := #[⟨3, 0⟩, ⟨1, 0⟩]
  root := 1746228987
  single := #[
    (#[#[1000, 1001, 1002], #[2000]], [])]
  multi := [
    (#[0], #[]),
    (#[0, 0], #[]),
    (#[0, 0, 0, 0, 0, 0], #[])]

/-- `fingerprint` of the pruned proofs of `mixed` at `subsets 8`. -/
def mixedSubsetsFingerprint : Nat := 1978305711

/-- `fingerprint` of the pruned proofs of `ladder` at `drawnLists`. -/
def ladderListsFingerprint : Nat := 3346951561

/-! ## Plonky3's openings are accepted -/

namespace Batch

/-- Depth of the tree. -/
def depth (b : Batch) : Nat :=
  Merkle.maxLogHeight b.dims.toList

/-- The matrices of the batch, as the generator fills them. -/
def matrices (b : Batch) : Array Matrix :=
  b.dims.mapIdx fun m d => matrix (m + 1) d.logHeight d.width

/-- The rows the single-index openings give at `indices`. -/
def rows (b : Batch) (indices : Array Nat) : Array (Array (Array Nat)) :=
  indices.map fun index => b.single[index]!.1

/-- The paths the single-index openings give at `indices`. -/
def paths (b : Batch) (indices : Array Nat) : Array (List Nat) :=
  indices.map fun index => b.single[index]!.2

/-- Whether `prunedMmcs` accepts an opening under `root`. -/
def acceptsUnder (b : Batch) (root : Nat) (indices : Array Nat)
    (rows : Array (Array (Array Nat))) (proof : Array Nat) : Bool :=
  (prunedMmcs toy).verifyMultiBatch root b.dims indices rows (⟨proof⟩ : PrunedPaths Nat)

/-- Whether `prunedMmcs` accepts an opening under the root of the batch. -/
def accepts (b : Batch) : Array Nat → Array (Array (Array Nat)) → Array Nat → Bool :=
  b.acceptsUnder b.root

/-- The paths restored from the pruned proof of an opening of the rows at `indices`. -/
def restore (b : Batch) (indices : Array Nat) (proof : Array Nat) : Option (Array (List Nat)) :=
  restorePaths toy b.dims indices (b.rows indices) ⟨proof⟩

end Batch

/-- The batches pinned above. -/
def batches : List Batch := [mixed, ladder, plain, pair, oneRow]

/-- Every pinned multi-opening: the batch, the indices and the pruned proof. -/
def openings : List (Batch × Array Nat × Array Nat) :=
  batches.flatMap fun b => b.multi.map fun (indices, proof) => (b, indices, proof)

-- The certified check accepts every single-index opening, so their paths are
-- the full paths that the restored ones are compared with.
#guard batches.all fun b => b.single.size == 2 ^ b.depth &&
  (List.range b.single.size).all fun index =>
    Merkle.verifyOpening toy b.root b.dims index b.single[index]!.1 b.single[index]!.2

-- The reference builder of `CertiFriTest.Merkle` computes the same dimensions,
-- roots, rows and paths from the matrices, and `mixed` is the batch pinned there.
#guard batches.all fun b =>
  dimsOf b.matrices == b.dims && rootOf b.matrices == b.root &&
    (List.range b.single.size).all fun index =>
      b.single[index]! == (rowsAt b.matrices index, pathAt b.matrices index)
#guard mixed.dims == plonky3Dims && mixed.root == plonky3Root
  && mixed.single.toList == plonky3Openings

-- Each of Plonky3's pruned proofs is accepted under Plonky3's root.
#guard openings.length == 34
#guard openings.all fun (b, indices, proof) => b.accepts indices (b.rows indices) proof

-- The restored paths are those of Plonky3's single-index openings.
#guard openings.all fun (b, indices, proof) => b.restore indices proof == some (b.paths indices)

-- Every batch is opened at the reduced queries of one domain.
#guard batches.all fun b => b.multi.any fun (indices, _) =>
  indices == #[37, 9, 33, 60, 8, 22].map (· >>> (6 - b.depth))

/-! ## Tampered openings are rejected -/

/-- Every way to add one to one opened entry. -/
def bumpedRows (rows : Array (Array (Array Nat))) : List (Array (Array (Array Nat))) :=
  (List.range rows.size).flatMap fun query =>
    (List.range rows[query]!.size).flatMap fun m =>
      (List.range rows[query]![m]!.size).map fun j =>
        rows.modify query (·.modify m (·.modify j (· + 1)))

-- A changed opened entry, of any query, matrix and column.
#guard openings.all fun (b, indices, proof) =>
  (bumpedRows (b.rows indices)).all fun rows => !b.accepts indices rows proof

-- A changed sibling digest.
#guard openings.all fun (b, indices, proof) =>
  (List.range proof.size).all fun position =>
    !b.accepts indices (b.rows indices) (proof.modify position (· + 1))

-- A dropped digest: no path is restored.
#guard openings.all fun (b, indices, proof) =>
  (List.range proof.size).all fun position =>
    b.restore indices (proof.eraseIdxIfInBounds position) == none
      && !b.accepts indices (b.rows indices) (proof.eraseIdxIfInBounds position)

-- An extra digest, anywhere: no path is restored.
#guard openings.all fun (b, indices, proof) =>
  (List.range (proof.size + 1)).all fun position =>
    b.restore indices (proof.insertIdxIfInBounds position 12345) == none
      && !b.accepts indices (b.rows indices) (proof.insertIdxIfInBounds position 12345)

-- A changed index, in the tree or past its last leaf.
#guard openings.all fun (b, indices, proof) =>
  (List.range indices.size).all fun query =>
    (List.range (2 * b.single.size)).all fun index =>
      index == indices[query]! || !b.accepts (indices.set! query index) (b.rows indices) proof

-- A dropped or an extra index, with the rows unchanged.
#guard openings.all fun (b, indices, proof) =>
  ((List.range indices.size).all fun query =>
      !b.accepts (indices.eraseIdxIfInBounds query) (b.rows indices) proof)
    && (List.range b.single.size).all fun index =>
      !b.accepts (indices.push index) (b.rows indices) proof

-- Another root. With no query, nothing is compared with the root.
#guard openings.all fun (b, indices, proof) =>
  indices.isEmpty || !b.acceptsUnder (b.root + 1) indices (b.rows indices) proof

-- No matrix, even with nothing opened.
#guard !(prunedMmcs toy).verifyMultiBatch mixed.root #[] #[] #[] (⟨#[]⟩ : PrunedPaths Nat)

/-! ## Every set of indices

The pruned proof of an opening is determined by the single-index openings, and
`Batch.prune` computes it from them without walking the tree. Plonky3's pruned
proofs of many more openings are pinned by one hash of them all: they are the
proofs `Batch.prune` gives, and `prunedMmcs` accepts each. -/

/-- The pruned proof of the opening at `indices`, from the single-index
openings: level by level and by ascending node index, the digest of every node
that is not above a queried leaf while its sibling is. -/
def Batch.prune (b : Batch) (indices : Array Nat) : Array Nat :=
  (List.range b.depth).foldl (init := #[]) fun proof level =>
    let above := indices.map (· >>> level)
    (List.range (2 ^ (b.depth - level))).foldl (init := proof) fun proof node =>
      if !above.contains node && above.contains (node ^^^ 1) then
        -- The digest of `node` is the sibling at `level` of the leaves below its sibling.
        proof.push b.single[(node ^^^ 1) <<< level]!.2[level]!
      else proof

/-- Whether `prunedMmcs` accepts the opening at `indices` with the proof of
`Batch.prune`, and restores the paths of the single-index openings from it. -/
def Batch.opens (b : Batch) (indices : Array Nat) : Bool :=
  b.accepts indices (b.rows indices) (b.prune indices)
    && b.restore indices (b.prune indices) == some (b.paths indices)

/-- The toy hash of a sequence of pruned proofs, each preceded by its length. -/
def fingerprint (proofs : List (Array Nat)) : Nat :=
  toy.hashRows (proofs.foldl (fun stream proof => stream.push proof.size ++ proof) #[])

/-- The non-empty sets of indices below `n`, each in ascending order. -/
def subsets (n : Nat) : List (Array Nat) :=
  (List.range (2 ^ n)).tail.map fun mask => ((List.range n).filter mask.testBit).toArray

/-- The lists of indices the generator draws for `ladder`: 300 lists of 1 to 12
indices, unsorted and with repetitions. -/
def drawnLists : List (Array Nat) := Id.run do
  let next (state : Nat) := (state * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  let mut state := 1
  let mut lists := #[]
  for _ in [0:300] do
    state := next state
    let length := 1 + (state >>> 33) % 12
    let mut indices := #[]
    for _ in [0:length] do
      state := next state
      indices := indices.push ((state >>> 33) % 16)
    lists := lists.push indices
  return lists.toList

-- `Batch.prune` gives the pruned proofs pinned above.
#guard openings.all fun (b, indices, proof) => b.prune indices == proof

-- `mixed` at each of the 255 non-empty sets of indices.
#guard fingerprint ((subsets 8).map mixed.prune) == mixedSubsetsFingerprint
#guard (subsets 8).all mixed.opens

-- `ladder` at 300 lists of indices.
#guard fingerprint (drawnLists.map ladder.prune) == ladderListsFingerprint
#guard drawnLists.all ladder.opens

/-! ## Where Plonky3 is stricter

Plonky3 hashes the rows of one query per node and compares the rows of the other
queries below the node with them. `prunedMmcs` hashes the rows of every query.
So rows that differ but hash alike are rejected by Plonky3 and accepted here.
The toy hasher reduces entries modulo `4294967291`, which gives such rows; the
generator asserts that Plonky3 rejects the two openings below. -/

/-- The rows the single-index openings give at `indices`, with `4294967291`
added to the first entry of the row of matrix `m` of the second query. -/
def Batch.collidingRows (b : Batch) (indices : Array Nat) (m : Nat) : Array (Array (Array Nat)) :=
  (b.rows indices).modify 1 (·.modify m (·.modify 0 (· + 4294967291)))

-- Two queries at index 5 that open different rows of matrix 0.
#guard mixed.collidingRows #[5, 5] 0 != mixed.rows #[5, 5]
#guard mixed.accepts #[5, 5] (mixed.collidingRows #[5, 5] 0) (mixed.prune #[5, 5])

-- Queries at 4 and 5 that open different rows of matrix 1, where both address row 1.
#guard mixed.collidingRows #[4, 5] 1 != mixed.rows #[4, 5]
#guard mixed.accepts #[4, 5] (mixed.collidingRows #[4, 5] 1) (mixed.prune #[4, 5])

end CertiFriTest.P3.Pruned
