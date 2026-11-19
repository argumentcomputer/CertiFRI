import CertiFriP3.Digest

/-!
# BLAKE3

The BLAKE3 hash function in its plain mode (no key, no key derivation), with
an output of 32 bytes: `blake3`. This is what Plonky3's `Blake3` hasher
computes (`blake3/src/lib.rs`, which calls the `blake3` crate).

## The function

The input is cut into chunks of 1024 bytes, the last one possibly shorter (an
empty input is one empty chunk). A chunk is cut into blocks of 64 bytes, the
last one padded with zeros, and its blocks are compressed in a chain that
starts from the initialization vector; the compression is keyed by the index
of the chunk. The chaining values of the chunks are the leaves of a binary
tree, in which a parent is the compression of the two chaining values of its
children and the left subtree of a node holds the largest power of two of
chunks that leaves the right subtree nonempty. The digest is the output of the
last compression, the one of the root, which is flagged as such.

## This implementation

The tree is built with the stack of the reference implementation: the chaining
value of every chunk but the last is pushed, after merging it with the top of
the stack once for every factor two of the number of chunks seen so far; the
last chunk is then merged with what is left on the stack, top first.

The message is read through a function that gives the block at an index, as 16
little-endian words (`hashBlocks`). The Merkle hashers use this to hash field
elements and digests without first writing them as bytes.

Nothing is proved here. The function is tested against the vectors of the
BLAKE3 reference (`CertiFriTest/P3/Blake3.lean`).

Not covered: the keyed mode, key derivation, outputs longer than 32 bytes, and
hashing a message in several updates.
-/

namespace CertiFri.P3

namespace Blake3

/-- A message block of 64 bytes, as 16 little-endian 32-bit words: `mK` is
bytes `4 * K` to `4 * K + 3`. -/
structure Block where
  m0 : UInt32
  m1 : UInt32
  m2 : UInt32
  m3 : UInt32
  m4 : UInt32
  m5 : UInt32
  m6 : UInt32
  m7 : UInt32
  m8 : UInt32
  m9 : UInt32
  m10 : UInt32
  m11 : UInt32
  m12 : UInt32
  m13 : UInt32
  m14 : UInt32
  m15 : UInt32
  deriving Inhabited

/-- The 16 words of state of the compression function, `v0` to `v15`. -/
structure State where
  v0 : UInt32
  v1 : UInt32
  v2 : UInt32
  v3 : UInt32
  v4 : UInt32
  v5 : UInt32
  v6 : UInt32
  v7 : UInt32
  v8 : UInt32
  v9 : UInt32
  v10 : UInt32
  v11 : UInt32
  v12 : UInt32
  v13 : UInt32
  v14 : UInt32
  v15 : UInt32

/-- The initialization vector, which is the key of the plain mode. -/
def iv : Digest :=
  ⟨0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19⟩

/-- Flag of the first block of a chunk. -/
def flagChunkStart : UInt32 := 1

/-- Flag of the last block of a chunk. -/
def flagChunkEnd : UInt32 := 2

/-- Flag of the compression of a parent node. -/
def flagParent : UInt32 := 4

/-- Flag of the last compression of all. -/
def flagRoot : UInt32 := 8

/-- The quarter round: mixes two message words into four words of state. The
rotations are to the right by 16, 12, 8 and 7 bits. -/
@[inline] def quarter (a b c d x y : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b + x
  let d := d ^^^ a
  let d := (d >>> 16) ||| (d <<< 16)
  let c := c + d
  let b := b ^^^ c
  let b := (b >>> 12) ||| (b <<< 20)
  let a := a + b + y
  let d := d ^^^ a
  let d := (d >>> 8) ||| (d <<< 24)
  let c := c + d
  let b := b ^^^ c
  let b := (b >>> 7) ||| (b <<< 25)
  (a, b, c, d)

/-- One round: the quarter round on the four columns of the state, then on its
four diagonals. -/
def round (s : State) (m : Block) : State :=
  let (v0, v4, v8, v12) := quarter s.v0 s.v4 s.v8 s.v12 m.m0 m.m1
  let (v1, v5, v9, v13) := quarter s.v1 s.v5 s.v9 s.v13 m.m2 m.m3
  let (v2, v6, v10, v14) := quarter s.v2 s.v6 s.v10 s.v14 m.m4 m.m5
  let (v3, v7, v11, v15) := quarter s.v3 s.v7 s.v11 s.v15 m.m6 m.m7
  let (v0, v5, v10, v15) := quarter v0 v5 v10 v15 m.m8 m.m9
  let (v1, v6, v11, v12) := quarter v1 v6 v11 v12 m.m10 m.m11
  let (v2, v7, v8, v13) := quarter v2 v7 v8 v13 m.m12 m.m13
  let (v3, v4, v9, v14) := quarter v3 v4 v9 v14 m.m14 m.m15
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- The permutation of the message words between two rounds: word `i` of the
result is word `2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8` of the
block, for `i = 0, …, 15`. -/
def permute (m : Block) : Block :=
  ⟨m.m2, m.m6, m.m3, m.m10, m.m7, m.m0, m.m4, m.m13, m.m1, m.m11, m.m12, m.m5, m.m9, m.m14, m.m15,
    m.m8⟩

/-- `count` rounds, permuting the message words after each. -/
def rounds : (count : Nat) → State → Block → State
  | 0, s, _ => s
  | count + 1, s, m => rounds count (round s m) (permute m)

/-- The compression function, truncated to its first eight words of output:
the next chaining value, or the digest when `flags` has `flagRoot`.

`cv` is the chaining value so far, `m` the block, `counter` the index of the
chunk (zero for a parent node), `blockLen` the number of bytes of the block
before padding, and `flags` the flags of the block. -/
def compress (cv : Digest) (m : Block) (counter : UInt64) (blockLen flags : UInt32) : Digest :=
  let s := rounds 7
    ⟨cv.w0, cv.w1, cv.w2, cv.w3, cv.w4, cv.w5, cv.w6, cv.w7, iv.w0, iv.w1, iv.w2, iv.w3,
      counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags⟩ m
  ⟨s.v0 ^^^ s.v8, s.v1 ^^^ s.v9, s.v2 ^^^ s.v10, s.v3 ^^^ s.v11, s.v4 ^^^ s.v12, s.v5 ^^^ s.v13,
    s.v6 ^^^ s.v14, s.v7 ^^^ s.v15⟩

/-- The block whose 64 bytes are those of two digests, `a` first. -/
def pairBlock (a b : Digest) : Block :=
  ⟨a.w0, a.w1, a.w2, a.w3, a.w4, a.w5, a.w6, a.w7, b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7⟩

/-- A compression that has not been done yet, so that it can still be flagged
as the root: the last block of a chunk, or a parent node. -/
structure Node where
  /-- The chaining value that enters the compression. -/
  cv : Digest
  /-- The block. -/
  block : Block
  /-- The index of the chunk, or zero for a parent node. -/
  counter : UInt64
  /-- The number of bytes of the block before padding. -/
  blockLen : UInt32
  /-- The flags of the block, without `flagRoot`. -/
  flags : UInt32

/-- The chaining value of a node that is not the root. -/
def Node.chainingValue (n : Node) : Digest :=
  compress n.cv n.block n.counter n.blockLen n.flags

/-- The digest of the node that is the root. -/
def Node.rootDigest (n : Node) : Digest :=
  compress n.cv n.block n.counter n.blockLen (n.flags ||| flagRoot)

/-- The parent of two chaining values. -/
def parentNode (left right : Digest) : Node :=
  { cv := iv, block := pairBlock left right, counter := 0, blockLen := 64, flags := flagParent }

/-- Compress `count` full blocks of a chunk that are not its last, from block
`j` of the chunk on. `block` gives the blocks of the message, `first` is the
index in the message of the first block of the chunk, and `counter` the index
of the chunk. -/
def chainBlocks (block : Nat → Block) (first : Nat) (counter : UInt64) :
    (count j : Nat) → Digest → Digest
  | 0, _, cv => cv
  | count + 1, j, cv =>
    chainBlocks block first counter count (j + 1)
      (compress cv (block (first + j)) counter 64 (if j = 0 then flagChunkStart else 0))

/-- Chunk `chunk` of a message of `len` bytes whose blocks are given by
`block`, up to its last compression. -/
def chunkNode (len : Nat) (block : Nat → Block) (chunk : Nat) : Node :=
  let chunkLen := min 1024 (len - 1024 * chunk)
  let blocks := max 1 ((chunkLen + 63) / 64)
  let counter := chunk.toUInt64
  { cv := chainBlocks block (16 * chunk) counter (blocks - 1) 0 iv
    block := block (16 * chunk + (blocks - 1))
    counter := counter
    blockLen := (chunkLen - 64 * (blocks - 1)).toUInt32
    flags := if blocks = 1 then flagChunkStart ||| flagChunkEnd else flagChunkEnd }

/-- Push the chaining value of a chunk that is not the last on the stack of
subtrees. `total` is the number of chunks pushed so far, this one included:
the chunk completes one subtree for every factor two of `total`, and is merged
with the top of the stack as many times. -/
def pushChunk : (stack : List Digest) → (cv : Digest) → (total : Nat) → List Digest
  | [], cv, _ => [cv]
  | top :: stack, cv, total =>
    if total % 2 = 0 then pushChunk stack (parentNode top cv).chainingValue (total / 2)
    else cv :: top :: stack

/-- Push the chaining values of `count` chunks that are not the last, from
chunk `chunk` on. -/
def pushChunks (len : Nat) (block : Nat → Block) :
    (count chunk : Nat) → (stack : List Digest) → List Digest
  | 0, _, stack => stack
  | count + 1, chunk, stack =>
    pushChunks len block count (chunk + 1)
      (pushChunk stack (chunkNode len block chunk).chainingValue (chunk + 1))

/-- Merge the last node with the subtrees left on the stack, top first, and
flag the last compression as the root. -/
def finish : (stack : List Digest) → Node → Digest
  | [], node => node.rootDigest
  | top :: stack, node => finish stack (parentNode top node.chainingValue)

/-- The BLAKE3 digest of a message of `len` bytes, read through `block`:
`block i` must be bytes `64 * i` to `64 * i + 63` of the message as 16
little-endian words, with zeros past the end of the message. -/
def hashBlocks (len : Nat) (block : Nat → Block) : Digest :=
  let chunks := max 1 ((len + 1023) / 1024)
  finish (pushChunks len block (chunks - 1) 0 []) (chunkNode len block (chunks - 1))

/-- Block `i` of a message given as bytes, padded with zeros. -/
def bytesBlock (bytes : ByteArray) (i : Nat) : Block :=
  let word := fun (k : Nat) => LittleEndian.word32 bytes (64 * i + 4 * k)
  ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7, word 8, word 9, word 10,
    word 11, word 12, word 13, word 14, word 15⟩

/-- The BLAKE3 digest of a message. -/
def hash (bytes : ByteArray) : Digest :=
  hashBlocks bytes.size (bytesBlock bytes)

/-- The BLAKE3 digest of the 64 bytes of two digests, `a` first: one
compression, which is both the only block of the only chunk and the root. -/
def hashPair (a b : Digest) : Digest :=
  compress iv (pairBlock a b) 0 64 (flagChunkStart ||| flagChunkEnd ||| flagRoot)

end Blake3

/-- BLAKE3 in its plain mode: the 32-byte digest of a message of any length. -/
def blake3 (bytes : ByteArray) : ByteArray :=
  (Blake3.hash bytes).toBytes

end CertiFri.P3
