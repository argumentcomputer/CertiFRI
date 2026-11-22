import CertiFriP3.DomainSep

/-!
# Tests of domain-separated BLAKE3 hashers and challenger

Checks of `CertiFriP3/DomainSep.lean`:

* Identical 64-byte payloads hashed as a Merkle leaf (8 base elements), a
  Merkle 2-to-1 node (two 32-byte digests), and a Fiat–Shamir transcript buffer
  produce three pairwise-distinct digests, all distinct from plain BLAKE3.
* `baseHasherSep`, `extHasherSep`, and `challengerSep` work consistently on
  Merkle openings and challenger transcripts, and custom `DomainSep` tags change
  outputs as expected.
-/

namespace CertiFriTest.P3.DomainSep

open CertiFri CertiFri.P3

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

-- Domain-separated BLAKE3 separates all three roles and differs from plain BLAKE3.
def sepLeaf : Digest := (baseHasherSep).hashRows matchingRow
def sepNode : Digest := (baseHasherSep).compress d0 d1
def sepTranscript : ByteArray := blake3Transcript .standard (d0.toBytes ++ d1.toBytes)
def plainDigest : Digest := baseHasher.hashRows matchingRow

#guard sepLeaf != sepNode
#guard sepLeaf.toBytes != sepTranscript
#guard sepNode.toBytes != sepTranscript
#guard sepLeaf != plainDigest
#guard sepNode != plainDigest
#guard sepTranscript != plainDigest.toBytes

-- Extension hasher matches base hasher on flattened coordinates under domain separation.
def extMatchingRow : Array GoldilocksExt :=
  #[⟨Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0⟩,
    ⟨Goldilocks.ofUInt64 0, Goldilocks.ofUInt64 0⟩,
    ⟨Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2⟩,
    ⟨Goldilocks.ofUInt64 3, Goldilocks.ofUInt64 4⟩]

#guard (extHasherSep).hashRows extMatchingRow == (baseHasherSep).hashRows matchingRow
#guard (extHasherSep).compress d0 d1 == (baseHasherSep).compress d0 d1

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

-- Domain-separated challenger produces distinct challenges from stock challenger.
#guard
  let init := ChallengerState.new ByteArray.empty
  let sPlain := challenger.observe init (.digest d1)
  let sSep := (challengerSep).observe init (.digest d1)
  (challenger.sampleExt sPlain).1 != ((challengerSep).sampleExt sSep).1

-- Custom tags separate from standard tags.
def customSep : DomainSep where
  leafTag := 0x10
  nodeTag := 0x20
  transcriptTag := 0x30
  leaf_ne_node := by decide
  leaf_ne_transcript := by decide
  node_ne_transcript := by decide

#guard (baseHasherSep customSep).hashRows matchingRow != (baseHasherSep).hashRows matchingRow
#guard (baseHasherSep customSep).compress d0 d1 != (baseHasherSep).compress d0 d1

end CertiFriTest.P3.DomainSep
