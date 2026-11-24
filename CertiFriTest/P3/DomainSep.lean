import CertiFriP3.DomainSep

/-!
# Tests of native BLAKE3 `derive_key` domain separation (`multi-stark` `v6` parity)

Checks of `CertiFriP3/DomainSep.lean` and `CertiFriP3/Blake3.lean`:

* Exact byte-for-byte parity with `multi-stark` `v6` (`p3_adapter/domain_blake3.rs`
  and `cuda/kernels.cu`) on context keys (`v6MerkleLeafKey`, `v6MerkleCompressKey`)
  and reference test vectors at 64, 512, 1024, 1025, and 4264 bytes (`MerkleLeaf`)
  and 64-byte internal Merkle pair compression (`MerkleCompress`).
* Identical 64-byte payloads hashed as a Merkle leaf (8 base elements), a
  Merkle 2-to-1 node (two 32-byte digests), and a Fiat–Shamir transcript buffer
  produce pairwise distinct digests, all distinct from plain BLAKE3.
* 1-block `deriveKeyPair` matches streaming `deriveKey` on 64 bytes; 2-block
  `deriveKeyPairXof48` matches streaming `deriveKeyXof48` on 96 bytes; and
  the first 32 bytes of `deriveKeyXof48` match `deriveKey` identically.
* `baseHasherSep`, `extHasherSep`, `ext3HasherSep`, `baseHasherSepXof48`,
  `ext3HasherSepXof48`, `challengerSep`, and `challenger3Sep` work consistently
  on Merkle openings and challenger transcripts.
-/

namespace CertiFriTest.P3.DomainSep

open CertiFri CertiFri.P3

/-! ## Exact `multi-stark` `v6` (`domain_blake3.rs` & `cuda/kernels.cu`) test vectors -/

def v6Pattern (len : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := len) fun i => ((i.val * 37 + 13) % 256).toUInt8)

-- Exact context keys shared with `cuda/kernels.cu` (`BLAKE3_V6_LEAF_CV`, `BLAKE3_V6_COMPRESS_CV`,
-- `BLAKE3_V6ZK_LEAF_CV`, `BLAKE3_V6ZK_COMPRESS_CV`).
#guard Blake3.deriveContextKey v6MerkleLeafContext == v6MerkleLeafKey
#guard Blake3.deriveContextKey v6MerkleCompressContext == v6MerkleCompressKey
#guard Blake3.deriveContextKey v6TranscriptSingleContext == v6TranscriptSingleKey
#guard Blake3.deriveContextKey v6TranscriptBatchContext == v6TranscriptBatchKey
#guard Blake3.deriveContextKey v6VkContext == v6VkKey
#guard Blake3.deriveContextKey v6ZkMerkleLeafContext == v6ZkMerkleLeafKey
#guard Blake3.deriveContextKey v6ZkMerkleCompressContext == v6ZkMerkleCompressKey
#guard Blake3.deriveContextKey v6ZkTranscriptSingleContext == v6ZkTranscriptSingleKey
#guard Blake3.deriveContextKey v6ZkTranscriptBatchContext == v6ZkTranscriptBatchKey
#guard Blake3.deriveContextKey v6ZkVkContext == v6ZkVkKey

-- Exact `domain_blake3.rs` `cuda_v6_blake3_and_ext3_vectors_match_rust` MerkleLeaf vectors
-- across single-block (64B), multi-block (512B), 1-chunk (1024B), and multi-chunk (1025B, 4264B).
#guard (Blake3Domain.merkleLeaf.hash (v6Pattern 64)).toHex
  == "4059736d0564475319baa815a76396039b1922ce8b8c51985ec1489f48e4581a"
#guard (Blake3Domain.merkleLeaf.hash (v6Pattern 512)).toHex
  == "58ec79936d612be378b23c2cfbb876f93179b825100d3ba77c2a8fd189deae51"
#guard (Blake3Domain.merkleLeaf.hash (v6Pattern 1024)).toHex
  == "0f237b3cbe5c88760fcf0305435c2b6d762142697aa21133b6508af2bd228e9c"
#guard (Blake3Domain.merkleLeaf.hash (v6Pattern 1025)).toHex
  == "1efbf193b24ebcabf1c230b0f7f2c30265d0a82272db4a19341767e688849358"
#guard (Blake3Domain.merkleLeaf.hash (v6Pattern 4264)).toHex
  == "bb19b2a12d999d55cc3bb2caf75c085e201c6b387519dfa2cb25eec6b9b54136"

-- Exact `domain_blake3.rs` MerkleCompress 64-byte pair vector (`(0..64u8)`).
def ramp64 : ByteArray := ByteArray.mk (Array.ofFn (n := 64) fun i => i.val.toUInt8)
def rampLeft : Digest := (Digest.ofBytes? (ramp64.extract 0 32)).getD default
def rampRight : Digest := (Digest.ofBytes? (ramp64.extract 32 64)).getD default

#guard (Blake3Domain.merkleCompress.hash ramp64).toHex
  == "8b14c7db6f612da11fa63c6fbec9783e35f74ab3dedf6f382fff8ace42e1b379"
-- 1-block `deriveKeyPair` matches general streaming `deriveKey` on 64 bytes.
#guard Blake3.deriveKeyPair v6MerkleCompressKey rampLeft rampRight
  == Blake3Domain.merkleCompress.hash ramp64
#guard baseHasherSep.compress rampLeft rampRight
  == Blake3Domain.merkleCompress.hash ramp64

/-! ## Pairwise separation across all 11 `Blake3Domain` modes (`plain` + 5 `v6` + 5 `v6-zk`) -/

def allDomains : List Blake3Domain :=
  [.plain, .merkleLeaf, .merkleCompress, .transcriptSingle, .transcriptBatch, .verifyingKey,
   .zkMerkleLeaf, .zkMerkleCompress, .zkTranscriptSingle, .zkTranscriptBatch, .zkVerifyingKey]

#guard
  let digests := allDomains.map fun d => d.hash ramp64
  digests.eraseDups.length == 11

#guard
  let digests := allDomains.map fun d => d.hash (v6Pattern 1025)
  digests.eraseDups.length == 11

-- `v6-zk` salted leaf hashing distinguishes distinct salts on the same row and stays distinct from `v6`.
#guard
  let row := #[Goldilocks.ofUInt64 10, Goldilocks.ofUInt64 20]
  let saltA : DomainSep.Salt16 := ⟨1, 2, 3, 4⟩
  let saltB : DomainSep.Salt16 := ⟨1, 2, 3, 5⟩
  hashSaltedRow row saltA != hashSaltedRow row saltB
    && hashSaltedRow row saltA != baseHasherSep.hashRows row
    && (hashSaltedRowXof48 row saltA).prefix32 == hashSaltedRow row saltA

/-! ## Role separation & Merkle/challenger integration -/

def d0 : Digest :=
  (Digest.ofHex? "0000000000000000000000000000000000000000000000000000000000000000").getD default

def d1 : Digest :=
  (Digest.ofHex? "0100000000000000020000000000000003000000000000000400000000000000").getD default

/-- A row of 8 canonical Goldilocks elements whose raw serialization equals
`d0.toBytes ++ d1.toBytes` (64 bytes). -/
def matchingRow : Array Goldilocks :=
  #[Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0,
    Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2, Goldilocks.ofUInt64 3, Goldilocks.ofUInt64 4]

-- Sanity: raw payload bytes are identical across all three roles (64 bytes).
#guard Hashers.rowBytes matchingRow == d0.toBytes ++ d1.toBytes

-- Stock Plonky3 BLAKE3 collides on identical 64-byte leaf, node, and transcript inputs.
#guard baseHasher.hashRows matchingRow == baseHasher.compress d0 d1
#guard (baseHasher.hashRows matchingRow).toBytes == blake3 (d0.toBytes ++ d1.toBytes)

-- Native `derive_key` BLAKE3 separates all three roles and differs from plain BLAKE3.
def sepLeaf : Digest := baseHasherSep.hashRows matchingRow
def sepNode : Digest := baseHasherSep.compress d0 d1
def sepTranscript : ByteArray := blake3Transcript .standard (d0.toBytes ++ d1.toBytes)
def plainDigest : Digest := baseHasher.hashRows matchingRow

#guard sepLeaf != sepNode
#guard sepLeaf.toBytes != sepTranscript
#guard sepNode.toBytes != sepTranscript
#guard sepLeaf != plainDigest
#guard sepNode != plainDigest
#guard sepTranscript != plainDigest.toBytes
-- Block-streaming `baseHasherSep.hashRows` matches byte-oriented `deriveKey`.
#guard sepLeaf == Blake3Domain.merkleLeaf.hash (Hashers.rowBytes matchingRow)

-- Extension hasher matches base hasher on flattened coordinates under `derive_key`.
def extMatchingRow : Array GoldilocksExt :=
  #[⟨Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0⟩,
    ⟨Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0⟩,
    ⟨Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2⟩,
    ⟨Goldilocks.ofUInt64 3, Goldilocks.ofUInt64 4⟩]

#guard extHasherSep.hashRows extMatchingRow == baseHasherSep.hashRows matchingRow
#guard extHasherSep.compress d0 d1 == baseHasherSep.compress d0 d1

-- Merkle opening check passes with `baseHasherSep` on a 2-leaf matrix and rejects tampered leaves.
#guard
  let h := baseHasherSep
  let row0 := #[Goldilocks.ofUInt64 10, Goldilocks.ofUInt64 20]
  let row1 := #[Goldilocks.ofUInt64 30, Goldilocks.ofUInt64 40]
  let leaf0 := h.hashRows row0
  let leaf1 := h.hashRows row1
  let root := h.compress leaf0 leaf1
  let dims := #[{ width := 2, logHeight := 1 : Dimensions }]
  Merkle.verifyOpening h root dims 0 #[row0] [leaf1]
    && Merkle.verifyOpening h root dims 1 #[row1] [leaf0]
    && !Merkle.verifyOpening h root dims 0 #[row1] [leaf1]
    && !Merkle.verifyOpening baseHasher root dims 0 #[row0] [leaf1]

-- Single vs batch `v6` challengers differ from each other and from plain challenger.
#guard
  let init := ChallengerState.new ByteArray.empty
  let sPlain := challenger.observe init (.digest d1)
  let sSingle := (challengerSep .v6Single).observe init (.digest d1)
  let sBatch := (challengerSep .v6Batch).observe init (.digest d1)
  (challenger.sampleExt sPlain).1 != ((challengerSep .v6Single).sampleExt sSingle).1
    && ((challengerSep .v6Single).sampleExt sSingle).1
        != ((challengerSep .v6Batch).sampleExt sBatch).1

/-! ## 48-byte (384-bit) BLAKE3 XOF checks -/

-- First 32 bytes of 48B XOF coincide with 32B digest across single- and multi-chunk inputs.
#guard (Blake3Domain.merkleLeaf.hashXof48 (v6Pattern 64)).prefix32
  == Blake3Domain.merkleLeaf.hash (v6Pattern 64)
#guard (Blake3Domain.merkleLeaf.hashXof48 (v6Pattern 4264)).prefix32
  == Blake3Domain.merkleLeaf.hash (v6Pattern 4264)

-- 2-block `deriveKeyPairXof48` matches streaming 96-byte `deriveKeyXof48` byte-for-byte.
#guard
  let a := Blake3Domain.merkleLeaf.hashXof48 (v6Pattern 64)
  let b := Blake3Domain.merkleLeaf.hashXof48 (v6Pattern 512)
  a.toBytes.size == 48 && b.toBytes.size == 48
    && Digest48.ofBytes? a.toBytes == some a
    && Digest48.ofHex? a.toHex == some a
    && Blake3.deriveKeyPairXof48 v6MerkleCompressKey a b
        == Blake3Domain.merkleCompress.hashXof48 (a.toBytes ++ b.toBytes)

-- 48-byte XOF Merkle opening verification passes and rejects tampered leaves.
#guard
  let h := baseHasherSepXof48
  let row0 := #[Goldilocks.ofUInt64 10, Goldilocks.ofUInt64 20]
  let row1 := #[Goldilocks.ofUInt64 30, Goldilocks.ofUInt64 40]
  let leaf0 := h.hashRows row0
  let leaf1 := h.hashRows row1
  let root := h.compress leaf0 leaf1
  let dims := #[{ width := 2, logHeight := 1 : Dimensions }]
  Merkle.verifyOpening h root dims 0 #[row0] [leaf1]
    && Merkle.verifyOpening h root dims 1 #[row1] [leaf0]
    && !Merkle.verifyOpening h root dims 0 #[row1] [leaf1]

/-! ## Certified 128-bit PQ RFC 7693 `BLAKE2b-512` (`Digest64`) checks -/

-- 1-block `Blake2b.hashPair64WithInit` matches streaming 128-byte `Blake2b512Domain.hash`.
#guard
  let a := Blake2b512Domain.merkleLeaf.hash (v6Pattern 64)
  let b := Blake2b512Domain.merkleLeaf.hash (v6Pattern 512)
  a.toBytes.size == 64 && b.toBytes.size == 64
    && Digest64.ofBytes? a.toBytes == some a
    && Digest64.ofHex? a.toHex == some a
    && Blake2b512Domain.merkleCompress.hashPair64 a b
        == Blake2b512Domain.merkleCompress.hash (a.toBytes ++ b.toBytes)
    && a != Blake2b512Domain.plain.hash (v6Pattern 64)
    && a != Blake2b512Domain.zkMerkleLeaf.hash (v6Pattern 64)

-- `baseHasherSepBlake2b512` and `ext3HasherSepBlake2b512` match `rowBytes`/`ext3RowBytes`
-- across single- and multi-block row widths (`< 16`, `= 16`, `> 16` elements).
#guard
  let r3 := #[Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2, Goldilocks.ofUInt64 3]
  let r16 := Array.ofFn (n := 16) (fun i => Goldilocks.ofUInt64 (i.val.toUInt64 + 100))
  let r25 := Array.ofFn (n := 25) (fun i => Goldilocks.ofUInt64 (i.val.toUInt64 + 1000))
  let hb := baseHasherSepBlake2b512
  hb.hashRows r3 == Blake2b512Domain.merkleLeaf.hash (Hashers.rowBytes r3)
    && hb.hashRows r16 == Blake2b512Domain.merkleLeaf.hash (Hashers.rowBytes r16)
    && hb.hashRows r25 == Blake2b512Domain.merkleLeaf.hash (Hashers.rowBytes r25)

#guard
  let e7 := Array.ofFn (n := 7) fun i =>
    ({ c0 := Goldilocks.ofUInt64 (3 * i.val.toUInt64 + 1),
       c1 := Goldilocks.ofUInt64 (3 * i.val.toUInt64 + 2),
       c2 := Goldilocks.ofUInt64 (3 * i.val.toUInt64 + 3) } : GoldilocksExt3)
  let he := ext3HasherSepBlake2b512
  he.hashRows e7 == Blake2b512Domain.merkleLeaf.hash (Hashers.ext3RowBytes e7)

-- `BLAKE2b-512` Merkle opening verification passes and rejects tampered leaves.
#guard
  let h := baseHasherSepBlake2b512
  let row0 := #[Goldilocks.ofUInt64 10, Goldilocks.ofUInt64 20]
  let row1 := #[Goldilocks.ofUInt64 30, Goldilocks.ofUInt64 40]
  let leaf0 := h.hashRows row0
  let leaf1 := h.hashRows row1
  let root := h.compress leaf0 leaf1
  let dims := #[{ width := 2, logHeight := 1 : Dimensions }]
  Merkle.verifyOpening h root dims 0 #[row0] [leaf1]
    && Merkle.verifyOpening h root dims 1 #[row1] [leaf0]
    && !Merkle.verifyOpening h root dims 0 #[row1] [leaf1]

-- `v6-zk` salted `BLAKE2b-512` leaf hash and `challenger3Blake2b512` domain separation.
#guard
  let row := #[Goldilocks.ofUInt64 7, Goldilocks.ofUInt64 11]
  let saltA : DomainSep.Salt16 := ⟨1, 2, 3, 4⟩
  let saltB : DomainSep.Salt16 := ⟨1, 2, 3, 5⟩
  let dA := hashSaltedRowBlake2b512 row saltA
  let dB := hashSaltedRowBlake2b512 row saltB
  let sV6 := (challenger3Blake2b512 .v6Single).observe (ChallengerState.new ByteArray.empty) (.digest dA)
  let sZk := challenger3V6ZkBlake2b512.observe (ChallengerState.new ByteArray.empty) (.digest dA)
  dA != dB
    && ((challenger3Blake2b512 .v6Single).sampleExt sV6).1
        != (challenger3V6ZkBlake2b512.sampleExt sZk).1

end CertiFriTest.P3.DomainSep
