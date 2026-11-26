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

/-! ## Multi-level `derive_key` parity across all 10 `v6` and `v6-zk` contexts

Each context is tested on the canonical `i % 251` input at lengths spanning
empty (`0`), single-block (`64`), 1-chunk (`1024`), 2-chunk (`1025`),
3-chunk unbalanced (`2049`), 5-chunk 3-level (`4097`), and 9-chunk 4-level
(`8193`) BLAKE3 Merkle trees against `blake3::derive_key`. -/

private def input251 (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := n) fun i => (i.val % 251).toUInt8)

private def multiLevelDomainVectors : Array (Blake3Domain × Nat × String) := #[
  (.merkleLeaf, 0, "a6205af23604bdace5d8217b52809fab1922c6f1033c72ce8d5b80055a0cdf6a"),
  (.merkleLeaf, 64, "84fb68595017ce36f8115560264ca543da724257398e7b5980432f26ac8b1dd4"),
  (.merkleLeaf, 1024, "54d3cf7f1ab87ae044c967bd6be149eaa7095a38694b2645cb92f0ff392cca3e"),
  (.merkleLeaf, 1025, "e4ae7be6e15c5cf2bc97126c1b0440ac584c77981528337a8064365ae915e419"),
  (.merkleLeaf, 2049, "1d9888bc844f399130325de4a2c30142d5ee86596fb5718e5ea8bc2c3e00933d"),
  (.merkleLeaf, 4097, "ffd20dd7c4a23bb980a2d9c3f5698ed17820bbc634c4335b6e7cc9f568dc3e7d"),
  (.merkleLeaf, 8193, "6be8ca1b9ad822f514fa35748fb8dcc19e6f468ec85271c5b3823389c0e67a46"),
  (.merkleCompress, 0, "f3dbd1c88fcc4e67e3aa4f5b8dbdf0febc7b06be403748689d4aaa64310133db"),
  (.merkleCompress, 64, "8b14c7db6f612da11fa63c6fbec9783e35f74ab3dedf6f382fff8ace42e1b379"),
  (.merkleCompress, 1024, "85340510c80725b2cf4db65cf57dd4641453e207c43c91d83fadb5e89b3e5a6f"),
  (.merkleCompress, 1025, "110aa265d508a4ac2458e18d524e7ebc906a145fcc6de568d3d4c206c2d159fe"),
  (.merkleCompress, 2049, "b6cca4de20a8b516994feea65a2efc85aabe499ec95cb2edd4f4fa2686c0f026"),
  (.merkleCompress, 4097, "d5f1d8cf1ef4a9f5e1a6620cc928918d9600510a614b237874900376d082e9f0"),
  (.merkleCompress, 8193, "2ec9735242a25e07a2107cb3bd00bd9ecbe753a403e42153e704977b6dad3901"),
  (.transcriptSingle, 0, "7cc59d6ab80ef3056cb1cc7da8dbcdf8a4026e0b3531aee245341d6d3a72d9fc"),
  (.transcriptSingle, 64, "564bfbbd3a13dffeae73bb990fc9be38f41bcde9c9ee34610f80a0eb0275b74f"),
  (.transcriptSingle, 1024, "3a7b3864ac80349422b57fda6fd93b2efd8cffc0cd1038075fea30f6032bb8c7"),
  (.transcriptSingle, 1025, "fefa64fee1d7c8547c1dcdf198f31327d2821eaf59b97d005572c875a413d5dc"),
  (.transcriptSingle, 2049, "229fac00b21e9a8c9cd53028cde501c3998ccaa72526b9aa339083fb04cbdbd6"),
  (.transcriptSingle, 4097, "87058e365cc75eaca53fb0ff4fb4c25d48f65049257cae5d807b22decb17ffa6"),
  (.transcriptSingle, 8193, "71f8b57065a7eb3506926ceda42542116cda7acd9bdaf5976be021848756b1e6"),
  (.transcriptBatch, 0, "2ead4673a0bf6d0aeb83c5f96456bf706afca9c64f3753c2ea42c32f1eb2a437"),
  (.transcriptBatch, 64, "9ab321067511d9761b1c1728a7c0a7e65711ad39a8d8944fd940ad10af69a068"),
  (.transcriptBatch, 1024, "354b9eaf62dee90d996b674a794bd176d184a6c9f3b1ff6dbee05571207b7920"),
  (.transcriptBatch, 1025, "c4d296b7c62f540291093be21d238a19fc94205f4573ee1d97644237f28758c4"),
  (.transcriptBatch, 2049, "70a661402c14063ade49916ad2eb6c5b59f44ad461ece07935d57c81d4759916"),
  (.transcriptBatch, 4097, "783dd4f2b8561085c114d353191e2abe8749989a916524b7a7ebd80a334cead6"),
  (.transcriptBatch, 8193, "f2a343d4b6b553cb33d3f9f74ab1e647fd7691401be910680a553f1bdb10b165"),
  (.verifyingKey, 0, "1ab08f8c7b0bd06336afe5c9300f5812fce9c0e8ea6fe7f8d04ebf37f5110f96"),
  (.verifyingKey, 64, "05607faedc09fcf4457ebd86c28fc7c2da344c6a6c73327a264192f9ed121b97"),
  (.verifyingKey, 1024, "336695dde1cf70cb2b370cb05830560b5bdeb5269ea17a4f130cfed55390298d"),
  (.verifyingKey, 1025, "8bedc19f8a7772e52f2ce3becac656e352d8a32e265ea643fdb2bb56ae957e51"),
  (.verifyingKey, 2049, "5711f20789ca11e0a9bd01bd10da9b8e76a28b4a3356eca2fc3e9fe03f88b1bc"),
  (.verifyingKey, 4097, "b55ace42e477ee08f2a82dbe9f41440a924eb71a03816fa54c2ef69524569f16"),
  (.verifyingKey, 8193, "fc5fb0c4adba81037775f5ec8d1a892c7c3c0a6b28089860bd61c7718468acb0"),
  (.zkMerkleLeaf, 0, "022645c31d68cf5cc5d49dfa8bf46060cfaff4d620bf40c2d3d8dce69b651421"),
  (.zkMerkleLeaf, 64, "4c94869d991764f736f9a071e2f28294ea3302fbea22626c9eedd35b54b2152a"),
  (.zkMerkleLeaf, 1024, "992112216bc63fc5e8001b9629956de88b86559edc63718de1356a1b1b3b0d74"),
  (.zkMerkleLeaf, 1025, "d79d112ff18c035c1a7634b691fa67f16a8b15b1249fac0ced58936f799cf77c"),
  (.zkMerkleLeaf, 2049, "aac0a41c15f64b7ebb707ff5f3040ac98cbe93ca200368db551e4e9c00545a35"),
  (.zkMerkleLeaf, 4097, "f07beba94fac50b1786047286e314f9004144ac689d559cbff8ba063f70b4da0"),
  (.zkMerkleLeaf, 8193, "e93507eb46a3448aba804ce5f1d2fecf7ed6cc1880f420e20bdb6bcf5b1cf256"),
  (.zkMerkleCompress, 0, "533170b759042b54aae33bedeb89b37ae5f09e65af502269fd8c7636d1d5197a"),
  (.zkMerkleCompress, 64, "a96715eb2d8a0e5c7291bb6b1ab0732f57e960ec084fa706f0a8bc7a89f30786"),
  (.zkMerkleCompress, 1024, "f4d637709e85b394e0859ee75975a610b50a0f6088e06f8c09abc962fb8af240"),
  (.zkMerkleCompress, 1025, "63799057ea9b315f407b86a06762c47b061437bd8aa6a198e75f1c87ba6a7284"),
  (.zkMerkleCompress, 2049, "6d2d110b9b998925f1627896b9a372b5f785d009c50574d5ff754e87331eb21f"),
  (.zkMerkleCompress, 4097, "1c64104f3f0be649e58120bb5a39e06358e145444a16104fb7807a655fda83e7"),
  (.zkMerkleCompress, 8193, "40b00f2cf7449e52e9ceacc09e39868951e9c89b36948fd1e86082babb522cc8"),
  (.zkTranscriptSingle, 0, "869c780196c455c210fb8ec562d26ef029f1c8f6c8559002918e4648bb2833d5"),
  (.zkTranscriptSingle, 64, "0e24845fd2d4adcb66968668818e8a2f7334bcf4742027dda64edbc5320ed4b2"),
  (.zkTranscriptSingle, 1024, "47ef043dcba00b79e8edb4202d51ff8778ff2fbc88a095f62fcda54c7b6d8ea7"),
  (.zkTranscriptSingle, 1025, "baec3db3647179628e87a768ee09dd4eda2737350e47083f502b4e9eee770c0b"),
  (.zkTranscriptSingle, 2049, "96839147592baffa1c2d07a9f6ae10435c9934aa1ac664b5c82cccb16beb7418"),
  (.zkTranscriptSingle, 4097, "6217bb97ea04dff48d437371a173c23e655d7b05e604c0103a528178dee60d28"),
  (.zkTranscriptSingle, 8193, "cb2c27afd865a526bede516cdc968c09ff318697a25cc8e5a6537707663bfce2"),
  (.zkTranscriptBatch, 0, "a07b3253afe23c893d8f23265a51bc626b2d32cebb646aa7e70aa0fb0b19ce97"),
  (.zkTranscriptBatch, 64, "df56dca8b83164b920f28f4032a167fe6264e1f8afb9ce40b571a2f5dc7ef775"),
  (.zkTranscriptBatch, 1024, "0444d6799db425248970e412094ff9c93ef9fe9ba37d47f0830ecc53af0f8fc9"),
  (.zkTranscriptBatch, 1025, "00c5c9436ff350f6c6c7f990380b260e027a2d8ecbffd79c772d3669cf4bb478"),
  (.zkTranscriptBatch, 2049, "2e5ad9205a05799c1be87d25bb6f54bf2402ea8a558546aac003f9f60da3920c"),
  (.zkTranscriptBatch, 4097, "0428a55a420d4fbf74de53bb08c44972cecee40a0e3bd00e185d46b4bc3c3d33"),
  (.zkTranscriptBatch, 8193, "a790becd177a9e7814bca8307898922dd97f19e4b6823c841104767b5480ae1b"),
  (.zkVerifyingKey, 0, "6f1402c2a53077ff44d7c4cc8926a7f7b0974b75170d2e2f8b0a7d1158211095"),
  (.zkVerifyingKey, 64, "edd83a2877624a855e203886b9c8fdc8a217fc12d1e7912bf33a8e2317cc3944"),
  (.zkVerifyingKey, 1024, "02f4c01bea021aaf8fda9ee9eea91d3592b8910ab6f723dcdc29f93624236e10"),
  (.zkVerifyingKey, 1025, "e1903e07aa79331ef3018a5e9584c8a810c12c3934b60cd13d93940581e7ecea"),
  (.zkVerifyingKey, 2049, "4fc672a56434a2ccbc0a00f1fdb7909690fa0c0c2e4b7e56f796c0b25067197b"),
  (.zkVerifyingKey, 4097, "0e8be6694b3c5e8c7de82de4ada8fb04e7cf76f531218d5f64eaa02dba52b13f"),
  (.zkVerifyingKey, 8193, "bb6fd10eee6bdadcdef65935a993dc3de0451b2485f31691e1cda5340faef171")]

#guard multiLevelDomainVectors.size = 70
#guard multiLevelDomainVectors.all fun (dom, n, expected) =>
  (dom.hash (input251 n)).toHex == expected

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
