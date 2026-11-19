import CertiFriP3.Hashers

/-!
# Tests of the Merkle hashers

Checks of `CertiFriP3/Hashers.lean` against Plonky3 at revision `3152b14a`,
with the hashers of the BLAKE3 configuration:

* `SerializingHasher<Blake3>` on rows of Goldilocks elements;
* the same on rows of extension elements flattened by `flatten_to_base`, as
  `ExtensionMmcs` does;
* `CompressionFunctionFromHasher<Blake3, 2, 32>` on pairs of digests;
* the roots `MerkleTreeMmcs` and `ExtensionMmcs` commit to for matrices of two
  rows, which exercise the row hash and the compression together through the
  commitment schemes themselves.

The rows are generated from a seed: word `i` of the row with seed `s` is
`(s + i + 1) * 0x9E3779B97F4A7C15` modulo `2^64`, and an extension element
takes two consecutive words. The lengths cover the empty row, the boundaries
of a block (8 base elements) and of a chunk (128 base elements), and rows of
several chunks.

The hashers read a row as blocks of words; the tests also compare them with
BLAKE3 on the bytes of the row.
-/

namespace CertiFriTest.P3.Hashers

open CertiFri CertiFri.P3

/-- Word `i` of the row with seed `seed`. -/
def rowWord (seed : UInt64) (i : Nat) : UInt64 :=
  (seed + i.toUInt64 + 1) * 0x9E3779B97F4A7C15

/-- The row of `n` base elements with seed `seed`. -/
def baseRow (seed : UInt64) (n : Nat) : Array Goldilocks :=
  Array.ofFn (n := n) fun i => Goldilocks.ofUInt64 (rowWord seed i.val)

/-- The row of `n` extension elements with seed `seed`. -/
def extRow (seed : UInt64) (n : Nat) : Array GoldilocksExt :=
  Array.ofFn (n := n) fun i =>
    ⟨Goldilocks.ofUInt64 (rowWord seed (2 * i.val)),
      Goldilocks.ofUInt64 (rowWord seed (2 * i.val + 1))⟩

/-- The digest written in hexadecimal. -/
def digest (text : String) : Digest :=
  (Digest.ofHex? text).getD default

/-! ## Against Plonky3 -/

/-- `(seed, n, digest)`: `SerializingHasher<Blake3>` on the row of `n` base elements
with seed `seed`. -/
def baseRowVectors : Array (UInt64 × Nat × String) := #[
  (1000, 0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
  (2000, 1, "849ae156c11bfb0d5ee7587ed061eec04d24be0bc16f080d8a31c8519234fded"),
  (3000, 2, "6e2fb5d9af3de1412cd5706db9bb78dd7e7d8576082beb22d637022210e66c58"),
  (4000, 7, "9329e7b1f611d7f07a7b75b372714699b98417d071a44ac7e3b0e382fac36619"),
  (5000, 8, "c3fd00a5ff655aeea0f0b5cc4f82c6d14e8d0f96fbf12800502b9d6e14bb5034"),
  (6000, 9, "a7e50fd251de27f709119353dbf5642657310784bc58679b380c03b05b9b3dc5"),
  (7000, 16, "a9a3108649234e596936004da920a3785326602f1d98fa8d99963721120c90df"),
  (8000, 127, "a26b996fe6a354d5e932409514f0ac46d924a9082604fe6557297379caaca13a"),
  (9000, 128, "5827908202db8224e2ce599ae60ad40d50be305a155695801c9e57ba203fcfd1"),
  (10000, 129, "c10c546b77e33ea5c419512c6763061fb87b930ce8e36b2b54a6f3c58bebfa8e"),
  (11000, 255, "7f03f79ce312324e47ca030c8f3cae68fc40f3197717de27aaaaf503dfe0c70e"),
  (12000, 256, "7fc124107bbdd06459f776fb6b30e4fe21de19d62fe24d4a7eae6b467fcdb248"),
  (13000, 257, "46337d2b5e04909df260ea2e92763716f708c7be91eb55613d0e217a7434d85e"),
  (14000, 300, "8e8c552d538c616d72f8f1670aa550ffb60e52cc12f8d6884d00fd806aae7d56"),
  (15000, 513, "b9b33789e9155bfcecc3506814f5faddcb0cb63111c79f4c5f301318c4ff4ec8")]

/-- A row of words at the edges of the field, some of them not canonical, and its digest. -/
def edgeRowVector : Array UInt64 × String := (#[
  0x0000000000000000, 0x0000000000000001, 0xffffffff00000000, 0x00000000ffffffff,
  0x0000000100000000, 0x8000000000000000, 0xffffffff00000001, 0xffffffffffffffff,
  0x0123456789abcdef],
  "b3fe26af70ffe1a543fcdf662eab9dbd52c78376df97ef0776ffe6d63f69c5d3")

/-- `(seed, n, digest)`: the row of `n` extension elements with seed `seed`,
flattened as `ExtensionMmcs` does (`flatten_to_base`) and hashed by
`SerializingHasher<Blake3>`. -/
def extRowVectors : Array (UInt64 × Nat × String) := #[
  (77, 0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
  (154, 1, "78b7c23667397343edfdbca1519cc1d95513d3b3b29ae81eef4d0763f0799c04"),
  (231, 2, "86eab5c27d8d6ac541f9ee076939fb1425d6376d2bc840aa6655c8f5bac18516"),
  (308, 3, "efa5739818aeef978b73a9ab11f846735f8a4c5f74e9edaa1e8f60f062479d12"),
  (385, 4, "c3e83e8ce1e4255b0a6cd6dc47fd90d7e5833336f9752f33cd163c4790d9e11c"),
  (462, 5, "f5f9e696e7a0f663b1a2f5a7852157d445b2e0179c96b26273723dad8f81d6cd"),
  (539, 63, "318c393798a26ce02084285bda3af55e3089f231e8359d3e1579df491e5dac18"),
  (616, 64, "fe22ac4b1ec72993844607ed7ed6f806c5582f98cf4cf83b8a86dbc2f6a6ed04"),
  (693, 65, "4efc9df51c3a210abd3f48a63306bc7b0953dc08e40956b56787fe7a2a4291b2"),
  (770, 150, "99e9791327454d376365697e3b935a439d0c013ba0aa0a48c96f8b6d9be9c92d")]

/-- `(left, right, compress(left, right))`: `CompressionFunctionFromHasher<Blake3, 2, 32>`. -/
def compressVectors : Array (String × String × String) := #[
  ("0000000000000000000000000000000000000000000000000000000000000000",
    "ed8f01dbe4140b1d89a9817b8a6f46b301dd50d0a6e8eb9ccfc9ab66fb64a712",
    "78a2c4c63510e6a32cc6261d1dc45e14ccbac440697f088187808e06105e68f3"),
  ("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "9699b7caad8d6837074f1f093777dfa2b8fdbecb42eb9822169285dc210d83e3",
    "5c7150cb20f3bf1ca630afb6a9306d09125dd11f99436a6f7ade690a9bdef2ce"),
  ("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "7aee49c8e044b67d726b03a2b1a976e3cc7ad4d712b6ccb27f485c308f2d3eb6",
    "d7b35c4161299bd35069264ae9c10f4cd4969df122e5cdbff886a5cce18a13ff"),
  ("ed8f01dbe4140b1d89a9817b8a6f46b301dd50d0a6e8eb9ccfc9ab66fb64a712",
    "f4dc0f9d990fec7ac39f3493952204565c1cf0654e7ca6b7ea9382616a1284cc",
    "7a74b725fe81bc8ac6ab1db0da83140cadc316d4f30297084b0175a5c2b2a666"),
  ("9699b7caad8d6837074f1f093777dfa2b8fdbecb42eb9822169285dc210d83e3",
    "0000000000000000000000000000000000000000000000000000000000000000",
    "c6fc359220221fa1a214f6aa22ab95629b7753b9590f00b5466824507878db74"),
  ("7aee49c8e044b67d726b03a2b1a976e3cc7ad4d712b6ccb27f485c308f2d3eb6",
    "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    "516fba09157675d4f2d9a6bcf2a6c447ae980650fc78a016c5fd42959e6eb78a"),
  ("f4dc0f9d990fec7ac39f3493952204565c1cf0654e7ca6b7ea9382616a1284cc",
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
    "a34a001d7a0c2a98ba00527490d36e9c77e17a968867f09541689cab6010e5c7")]

/-- `(m, digest)`: the digests of the base row of length `n` with seed `n` and of the
extension row of length `n` with seed `n + 7`, for every `n ≤ m`, folded from the
zero digest by the compression, the row digest on the right. -/
def rowSweepVector : Nat × String :=
  (48, "3105cb638028a4f7bb6e0affadd40b297a5bd94ea3b0e4f375caaefa66bf4d1a")

/-- `(seed, width, root)`: the root `MerkleTreeMmcs` commits to for the matrix of two
rows of `width` base elements, the rows having seeds `seed` and `seed + 500`. -/
def baseRootVectors : Array (UInt64 × Nat × String) := #[
  (31, 1, "f8d2628239a9acf7d1be124b1855bd8949b04e4934f53336dd0c96c35a96b7f0"),
  (62, 3, "8ca4f9b2b5072ac4e72835367075e9a025282687590ba1dfb210141a8b0d9f49"),
  (93, 8, "42c6a8e565cba8041b808fb788f03eece666f8358ef1c2431ef432cbc015746c"),
  (124, 20, "4d0de0595348ed62b8e3021a5fbfa2a2c5bf650d5009f75b8a8ee7d079151c72"),
  (155, 130, "d63b4a8a883bcdee3b2ff34463d1daa205af4bee615203b02a81cfde096fdd80")]

/-- `(seed, width, root)`: the root `ExtensionMmcs` commits to for the matrix of two
rows of `width` extension elements, the rows having seeds `seed` and `seed + 500`. -/
def extRootVectors : Array (UInt64 × Nat × String) := #[
  (53, 1, "15568d67f5d402a8a54ced201fea47b4e802fb76d2a1a8b498d803bfa309f929"),
  (106, 2, "bd3f97e956c7568a4de830a98a5a816d9ebdd0534035e374a443df7c6bc6753b"),
  (159, 5, "d32d93177b738f4fa136ab500b7c1fdfcfb5051e429574716cda929aea2469dc"),
  (212, 70, "f777d5ab5e89e5f577807e79f88b6565a23dc85fc16cd8ec1fcd787643b8b051")]

#guard baseRowVectors.size = 15
#guard baseRowVectors.all fun (seed, n, expected) =>
  (baseHasher.hashRows (baseRow seed n)).toHex == expected

#guard (baseHasher.hashRows (edgeRowVector.1.map Goldilocks.ofUInt64)).toHex == edgeRowVector.2

#guard extRowVectors.size = 10
#guard extRowVectors.all fun (seed, n, expected) =>
  (extHasher.hashRows (extRow seed n)).toHex == expected

#guard compressVectors.size = 7
#guard compressVectors.all fun (left, right, expected) =>
  (baseHasher.compress (digest left) (digest right)).toHex == expected
    && (extHasher.compress (digest left) (digest right)).toHex == expected

-- Rows of every length up to 48.
#guard
  let zero := digest "0000000000000000000000000000000000000000000000000000000000000000"
  ((List.range (rowSweepVector.1 + 1)).foldl (fun acc n =>
    let acc := baseHasher.compress acc (baseHasher.hashRows (baseRow n.toUInt64 n))
    extHasher.compress acc (extHasher.hashRows (extRow (n.toUInt64 + 7) n))) zero).toHex
    == rowSweepVector.2

#guard baseRootVectors.size = 5
#guard baseRootVectors.all fun (seed, width, root) =>
  (baseHasher.compress (baseHasher.hashRows (baseRow seed width))
    (baseHasher.hashRows (baseRow (seed + 500) width))).toHex == root

#guard extRootVectors.size = 4
#guard extRootVectors.all fun (seed, width, root) =>
  (extHasher.compress (extHasher.hashRows (extRow seed width))
    (extHasher.hashRows (extRow (seed + 500) width))).toHex == root

/-! ## Against BLAKE3 on bytes -/

-- A row is hashed as its bytes are: eight bytes per base element.
#guard (Hashers.rowBytes (baseRow 1 3)).size = 24
#guard (Hashers.rowBytes #[Goldilocks.ofUInt64 0x0123456789ABCDEF, Goldilocks.ofUInt64 0xFF]).data
  = #[0xEF, 0xCD, 0xAB, 0x89, 0x67, 0x45, 0x23, 0x01, 0xFF, 0, 0, 0, 0, 0, 0, 0]
#guard (List.range 40 ++ [63, 64, 65, 127, 128, 129, 200, 256, 257, 384, 385]).all fun n =>
  baseHasher.hashRows (baseRow 5 n) == Blake3.hash (Hashers.rowBytes (baseRow 5 n))

-- An extension element is its two coordinates, `c0` first.
#guard (Hashers.extRowBytes (extRow 1 3)).size = 48
#guard Hashers.extRowBytes #[⟨Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2⟩]
  == Hashers.rowBytes #[Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2]
#guard (List.range 24 ++ [31, 32, 33, 63, 64, 65, 100, 128, 129, 192, 193]).all fun n =>
  extHasher.hashRows (extRow 9 n) == Blake3.hash (Hashers.extRowBytes (extRow 9 n))
    && extHasher.hashRows (extRow 9 n) == baseHasher.hashRows (baseRow 9 (2 * n))

-- The compression is the hash of the 64 bytes of the two digests.
#guard compressVectors.all fun (left, right, _) =>
  baseHasher.compress (digest left) (digest right)
    == Blake3.hash ((digest left).toBytes ++ (digest right).toBytes)

end CertiFriTest.P3.Hashers
