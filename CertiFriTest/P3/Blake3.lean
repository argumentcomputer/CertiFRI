import CertiFriP3.Blake3

/-!
# Tests of BLAKE3

Checks of `CertiFriP3/Blake3.lean` and `CertiFriP3/Digest.lean` against the
test vectors of the BLAKE3 reference: the input of length `n` is the bytes
`i % 251` for `i < n`, and the digest is the first 32 bytes of the `hash`
entry of the reference's `test_vectors.json`. The digests below were computed
with the `blake3` crate and with Plonky3's `Blake3` hasher at revision
`3152b14a`, which agree.

The lengths cover the empty input, the boundaries of a block (64 bytes) and of
a chunk (1024 bytes), and trees of one to a hundred chunks, complete and not.
One more vector folds the digests of the inputs of every length up to 300.
-/

namespace CertiFriTest.P3.Blake3

open CertiFri CertiFri.P3

/-- The test input of length `n`: the bytes `i % 251`. -/
def input (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := n) fun i => (i.val % 251).toUInt8)

/-- `(n, digest)`: the digest of the `n` bytes `i % 251` for `i < n`. -/
def vectors : Array (Nat × String) := #[
  (0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
  (1, "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"),
  (2, "7b7015bb92cf0b318037702a6cdd81dee41224f734684c2c122cd6359cb1ee63"),
  (3, "e1be4d7a8ab5560aa4199eea339849ba8e293d55ca0a81006726d184519e647f"),
  (4, "f30f5ab28fe047904037f77b6da4fea1e27241c5d132638d8bedce9d40494f32"),
  (5, "b40b44dfd97e7a84a996a91af8b85188c66c126940ba7aad2e7ae6b385402aa2"),
  (6, "06c4e8ffb6872fad96f9aaca5eee1553eb62aed0ad7198cef42e87f6a616c844"),
  (7, "3f8770f387faad08faa9d8414e9f449ac68e6ff0417f673f602a646a891419fe"),
  (8, "2351207d04fc16ade43ccab08600939c7c1fa70a5c0aaca76063d04c3228eaeb"),
  (63, "e9bc37a594daad83be9470df7f7b3798297c3d834ce80ba85d6e207627b7db7b"),
  (64, "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"),
  (65, "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee"),
  (127, "d81293fda863f008c09e92fc382a81f5a0b4a1251cba1634016a0f86a6bd640d"),
  (128, "f17e570564b26578c33bb7f44643f539624b05df1a76c81f30acd548c44b45ef"),
  (129, "683aaae9f3c5ba37eaaf072aed0f9e30bac0865137bae68b1fde4ca2aebdcb12"),
  (1023, "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"),
  (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
  (1025, "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
  (2048, "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"),
  (2049, "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"),
  (3072, "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"),
  (3073, "7124b49501012f81cc7f11ca069ec9226cecb8a2c850cfe644e327d22d3e1cd3"),
  (4096, "015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969"),
  (4097, "9b4052b38f1c5fc8b1f9ff7ac7b27cd242487b3d890d15c96a1c25b8aa0fb995"),
  (5120, "9cadc15fed8b5d854562b26a9536d9707cadeda9b143978f319ab34230535833"),
  (5121, "628bd2cb2004694adaab7bbd778a25df25c47b9d4155a55f8fbd79f2fe154cff"),
  (6144, "3e2e5b74e048f3add6d21faab3f83aa44d3b2278afb83b80b3c35164ebeca205"),
  (6145, "f1323a8631446cc50536a9f705ee5cb619424d46887f3c376c695b70e0f0507f"),
  (7168, "61da957ec2499a95d6b8023e2b0e604ec7f6b50e80a9678b89d2628e99ada77a"),
  (7169, "a003fc7a51754a9b3c7fae0367ab3d782dccf28855a03d435f8cfe74605e7817"),
  (8192, "aae792484c8efe4f19e2ca7d371d8c467ffb10748d8a5a1ae579948f718a2a63"),
  (8193, "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b"),
  (16384, "f875d6646de28985646f34ee13be9a576fd515f76b5b0a26bb324735041ddde4"),
  (31744, "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47"),
  (102400, "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085")]

/-- `(m, digest)`: the digests of the inputs of every length `n ≤ m`, folded from 32
zero bytes by `acc ↦ blake3 (acc ++ blake3 (input n))`. -/
def sweepVector : Nat × String :=
  (300, "78f9898fc41b2dd7787f3e50ce64037f4aea8f679cc4f2b45844f53c685bc028")

#guard vectors.size = 35
#guard vectors.all fun (n, digest) => (Blake3.hash (input n)).toHex == digest

/-- The digests of the inputs of every length up to `m`, folded into one. -/
def sweep (m : Nat) : ByteArray :=
  (List.range (m + 1)).foldl (fun acc n => blake3 (acc ++ blake3 (input n)))
    (ByteArray.mk (Array.replicate 32 0))

#guard (Digest.ofBytes? (sweep sweepVector.1)).map (·.toHex) == some sweepVector.2

/-! ## Bytes and digests -/

-- `blake3` gives the bytes of the digest.
#guard (blake3 (input 0)).size = 32
#guard (blake3 (input 0)).data.toList.take 4 = [0xaf, 0x13, 0x49, 0xb9]
#guard [0, 1, 64, 1025].all fun n =>
  blake3 (input n) == (Blake3.hash (input n)).toBytes
    && Digest.ofBytes? (blake3 (input n)) == some (Blake3.hash (input n))

-- A digest has exactly 32 bytes.
#guard (Digest.ofBytes? (input 31)).isNone ∧ (Digest.ofBytes? (input 33)).isNone
#guard (Digest.ofBytes? (input 32)).map (·.toBytes) == some (input 32)
#guard (Digest.ofBytes? (input 32)).map (·.w0) == some 0x03020100
#guard (Digest.ofBytes? (input 32)).map (·.w7) == some 0x1f1e1d1c

-- Hexadecimal text, first byte first, in either case.
#guard (Digest.ofBytes? (input 32)).map (·.toHex)
  == some "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
#guard Digest.ofHex? "000102030405060708090A0B0C0D0E0F101112131415161718191a1b1c1d1e1f"
  == Digest.ofBytes? (input 32)
#guard vectors.all fun (_, digest) => (Digest.ofHex? digest).map (·.toHex) == some digest
#guard (Digest.ofHex? "0001").isNone ∧ (Digest.ofHex? "").isNone
#guard (Digest.ofHex? "g00102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f").isNone
#guard (Digest.ofHex? "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1").isNone

-- Two digests are compressed as their 64 bytes are hashed.
#guard [(0, 1), (64, 65), (1024, 3)].all fun (m, n) =>
  let left := Blake3.hash (input m)
  let right := Blake3.hash (input n)
  Blake3.hashPair left right == Blake3.hash (left.toBytes ++ right.toBytes)

end CertiFriTest.P3.Blake3
