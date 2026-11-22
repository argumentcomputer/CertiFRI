import CertiFri.Merkle
import CertiFriP3.GoldilocksExt
import CertiFriP3.GoldilocksExt3
import CertiFriP3.Blake3

/-!
# The Merkle hashers of the BLAKE3 configuration

The two functions Plonky3's `MerkleTreeMmcs` builds its trees from when it is
instantiated with `SerializingHasher<Blake3>` and
`CompressionFunctionFromHasher<Blake3, 2, 32>`, as instances of
`MerkleHasher` with digests of 32 bytes.

* `baseHasher` hashes rows of Goldilocks elements. The hash of a row is the
  BLAKE3 digest of the concatenation of the elements, eight bytes each: the
  canonical word, least significant byte first
  (`symmetric/src/serializing_hasher.rs`, `F::into_byte_stream`). There is no
  length prefix, no padding and no separator between the rows of different
  matrices: the hasher sees one stream of elements.
* `extHasher` hashes rows of extension elements, as Plonky3's `ExtensionMmcs`
  over the same tree does (`commit/src/adapters/extension_mmcs.rs`): each
  element is replaced by its two coordinates, `c0` then `c1`, and the row of
  base elements is hashed as above.
* Both compress two digests into the BLAKE3 digest of their 64 bytes, left
  digest first (`symmetric/src/compression.rs`).

The hashers do not write the bytes: a block of 64 bytes is eight elements, and
each element gives two of the 16 words of the block. `Hashers.rowBytes` and
`Hashers.extRowBytes` write the same bytes, for reference and for the tests.

Nothing is proved here. The hashers are tested against Plonky3
(`CertiFriTest/P3/Hashers.lean`).

Not covered: digests of another size, and compression of more than two
digests.
-/

namespace CertiFri.P3

namespace Hashers

open Blake3 (Block)

/-- The bytes hashed for a row of base elements: eight bytes per element. -/
def rowBytes (row : Array Goldilocks) : ByteArray :=
  row.foldl Goldilocks.pushBytes (ByteArray.emptyWithCapacity (8 * row.size))

/-- The bytes hashed for a row of extension elements: 16 bytes per element,
the coordinate `c0` first. -/
def extRowBytes (row : Array GoldilocksExt) : ByteArray :=
  row.foldl (fun bytes e => Goldilocks.pushBytes (Goldilocks.pushBytes bytes e.c0) e.c1)
    (ByteArray.emptyWithCapacity (16 * row.size))

/-- The bytes hashed for a row of cubic-extension elements: 24 bytes per
element, coordinates `c0`, `c1`, `c2` in order. -/
def ext3RowBytes (row : Array GoldilocksExt3) : ByteArray :=
  row.foldl GoldilocksExt3.pushBytes (ByteArray.emptyWithCapacity (24 * row.size))

/-- The canonical word of element `i` of a row, or zero past the end. -/
@[inline] def wordOrZero (row : Array Goldilocks) (i : Nat) : UInt64 :=
  if h : i < row.size then row[i].val else 0

/-- The block of eight canonical words: each word gives its low half, then its
high half. -/
@[inline] def wordsBlock (e0 e1 e2 e3 e4 e5 e6 e7 : UInt64) : Block :=
  ⟨e0.toUInt32, (e0 >>> 32).toUInt32, e1.toUInt32, (e1 >>> 32).toUInt32,
    e2.toUInt32, (e2 >>> 32).toUInt32, e3.toUInt32, (e3 >>> 32).toUInt32,
    e4.toUInt32, (e4 >>> 32).toUInt32, e5.toUInt32, (e5 >>> 32).toUInt32,
    e6.toUInt32, (e6 >>> 32).toUInt32, e7.toUInt32, (e7 >>> 32).toUInt32⟩

/-- Block `i` of `rowBytes row`, padded with zeros: elements `8 * i` to
`8 * i + 7`. -/
def rowBlock (row : Array Goldilocks) (i : Nat) : Block :=
  let j := 8 * i
  wordsBlock (wordOrZero row j) (wordOrZero row (j + 1)) (wordOrZero row (j + 2))
    (wordOrZero row (j + 3)) (wordOrZero row (j + 4)) (wordOrZero row (j + 5))
    (wordOrZero row (j + 6)) (wordOrZero row (j + 7))

/-- Block `i` of `extRowBytes row`, padded with zeros: elements `4 * i` to
`4 * i + 3`. -/
def extRowBlock (row : Array GoldilocksExt) (i : Nat) : Block :=
  let j := 4 * i
  let e0 := row[j]?.getD default
  let e1 := row[j + 1]?.getD default
  let e2 := row[j + 2]?.getD default
  let e3 := row[j + 3]?.getD default
  wordsBlock e0.c0.val e0.c1.val e1.c0.val e1.c1.val e2.c0.val e2.c1.val e3.c0.val e3.c1.val

/-- The canonical word at base-coordinate index `k` of a cubic-extension row,
or zero past the end. -/
@[inline] def ext3WordOrZero (row : Array GoldilocksExt3) (k : Nat) : UInt64 :=
  let e := row[k / 3]?.getD default
  match k % 3 with
  | 0 => e.c0.val
  | 1 => e.c1.val
  | _ => e.c2.val

/-- Block `i` of `ext3RowBytes row`, padded with zeros: base coordinates
`8 * i` to `8 * i + 7`. -/
def ext3RowBlock (row : Array GoldilocksExt3) (i : Nat) : Block :=
  let j := 8 * i
  wordsBlock (ext3WordOrZero row j) (ext3WordOrZero row (j + 1)) (ext3WordOrZero row (j + 2))
    (ext3WordOrZero row (j + 3)) (ext3WordOrZero row (j + 4)) (ext3WordOrZero row (j + 5))
    (ext3WordOrZero row (j + 6)) (ext3WordOrZero row (j + 7))

end Hashers

/-- The hasher of Merkle trees over Goldilocks: `SerializingHasher<Blake3>` on
rows, `CompressionFunctionFromHasher<Blake3, 2, 32>` on pairs of digests. -/
def baseHasher : MerkleHasher Goldilocks Digest where
  hashRows row := Blake3.hashBlocks (8 * row.size) (Hashers.rowBlock row)
  compress := Blake3.hashPair

/-- The hasher of Merkle trees over the extension, as `ExtensionMmcs` over the
base tree hashes: rows are flattened to their base coordinates. -/
def extHasher : MerkleHasher GoldilocksExt Digest where
  hashRows row := Blake3.hashBlocks (16 * row.size) (Hashers.extRowBlock row)
  compress := Blake3.hashPair

/-- The hasher of Merkle trees over the cubic trinomial extension
`GoldilocksExt3`: rows are flattened to their three base coordinates. -/
def ext3Hasher : MerkleHasher GoldilocksExt3 Digest where
  hashRows row := Blake3.hashBlocks (24 * row.size) (Hashers.ext3RowBlock row)
  compress := Blake3.hashPair

end CertiFri.P3
