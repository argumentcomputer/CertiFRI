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

/-! ## Official keyed-hash and `derive_key` test vectors

Reference inputs are the bytes `i % 251` for `i < n`, using the official BLAKE3
test key `"whats the Elvish word for friend"` and official `derive_key` context
`"BLAKE3 2019-12-27 16:13:59 test vectors context"`, verified against the Rust
`blake3` crate across single-block, single-chunk, and multi-level trees up to
100 chunks (`102,400` bytes). -/

/-- Official BLAKE3 test key (`"whats the Elvish word for friend"`). -/
def officialKey : Digest :=
  (Digest.ofBytes? "whats the Elvish word for friend".toUTF8).getD default

/-- Official BLAKE3 `derive_key` test context string. -/
def officialDeriveKeyContext : String :=
  "BLAKE3 2019-12-27 16:13:59 test vectors context"

/-- Official `blake3::keyed_hash` test vectors (`(n, hexDigest)`). -/
def keyedVectors : Array (Nat × String) := #[
  (0, "92b2b75604ed3c761f9d6f62392c8a9227ad0ea3f09573e783f1498a4ed60d26"),
  (1, "6d7878dfff2f485635d39013278ae14f1454b8c0a3a2d34bc1ab38228a80c95b"),
  (2, "5392ddae0e0a69d5f40160462cbd9bd889375082ff224ac9c758802b7a6fd20a"),
  (3, "39e67b76b5a007d4921969779fe666da67b5213b096084ab674742f0d5ec62b9"),
  (63, "bb1eb5d4afa793c1ebdd9fb08def6c36d10096986ae0cfe148cd101170ce37ae"),
  (64, "ba8ced36f327700d213f120b1a207a3b8c04330528586f414d09f2f7d9ccb7e6"),
  (65, "c0a4edefa2d2accb9277c371ac12fcdbb52988a86edc54f0716e1591b4326e72"),
  (127, "c64200ae7dfaf35577ac5a9521c47863fb71514a3bcad18819218b818de85818"),
  (128, "b04fe15577457267ff3b6f3c947d93be581e7e3a4b018679125eaf86f6a628ec"),
  (129, "d4a64dae6cdccbac1e5287f54f17c5f985105457c1a2ec1878ebd4b57e20d38f"),
  (1023, "c951ecdf03288d0fcc96ee3413563d8a6d3589547f2c2fb36d9786470f1b9d6e"),
  (1024, "75c46f6f3d9eb4f55ecaaee480db732e6c2105546f1e675003687c31719c7ba4"),
  (1025, "357dc55de0c7e382c900fd6e320acc04146be01db6a8ce7210b7189bd664ea69"),
  (2048, "879cf1fa2ea0e79126cb1063617a05b6ad9d0b696d0d757cf053439f60a99dd1"),
  (2049, "9f29700902f7c86e514ddc4df1e3049f258b2472b6dd5267f61bf13983b78dd5"),
  (3072, "044a0e7b172a312dc02a4c9a818c036ffa2776368d7f528268d2e6b5df191770"),
  (3073, "68dede9bef00ba89e43f31a6825f4cf433389fedae75c04ee9f0cf16a427c95a"),
  (4096, "befc660aea2f1718884cd8deb9902811d332f4fc4a38cf7c7300d597a081bfc0"),
  (4097, "00df940cd36bb9fa7cbbc3556744e0dbc8191401afe70520ba292ee3ca80abbc"),
  (7168, "b42835e40e9d4a7f42ad8cc04f85a963a76e18198377ed84adddeaecacc6f3fc"),
  (7169, "ed9b1a922c046fdb3d423ae34e143b05ca1bf28b710432857bf738bcedbfa511"),
  (8192, "dc9637c8845a770b4cbf76b8daec0eebf7dc2eac11498517f08d44c8fc00d58a"),
  (8193, "954a2a75420c8d6547e3ba5b98d963e6fa6491addc8c023189cc519821b4a1f5"),
  (16384, "9e9fc4eb7cf081ea7c47d1807790ed211bfec56aa25bb7037784c13c4b707b0d"),
  (31744, "efa53b389ab67c593dba624d898d0f7353ab99e4ac9d42302ee64cbf9939a419"),
  (102400, "1c35d1a5811083fd7119f5d5d1ba027b4d01c0c6c49fb6ff2cf75393ea5db4a7")]

/-- Official `blake3::derive_key` test vectors (`(n, hexDigest)`). -/
def deriveKeyVectors : Array (Nat × String) := #[
  (0, "98fae6da3c112c3727c06ac7b0e27536718cccd43eedd2c2333463f0c6dae2c6"),
  (1, "e5e0049fea7713a073bf060745f6ee83f1951c447a450d9418e716254b975457"),
  (2, "3dd3dbc276690a36a13c5343f7c811e667f70800f9ac1064cf41e929f7a40e2b"),
  (3, "d4c8020c7512d59585d0f2f3e631ad5118e33b4e8d9efe102688605e943e8898"),
  (63, "0467d8bbfd691d5d0903480b80821249f3e651ca9e07271b7d64176ca3e59570"),
  (64, "d0e05f223dc1ad757d64a9268e0b35a1a619e9415216ffb18cf6404801c52d99"),
  (65, "5ef48660f62efe2bb3ded071c6f35700b0371b843fd52335ec186e21ecc21af7"),
  (127, "5aef747946c72f9196c1efb1843ead302bb945a7123cb86b72987e0b4d57d46f"),
  (128, "9a8dfffc79e07a1a7038cdc537218bf9828920b1437911cef02952e2c580c485"),
  (129, "4fbad266b2616e67d9a0b8b6f53529175260c36ad6d3e096a345afa4cb5205c2"),
  (1023, "b05f08a60c5a38a6f942ceedf9945afe93324aa1f57377580617f42c906da8f5"),
  (1024, "284d70facfb1eda96080cffe91a9143dc36ca5812604ac1c87a02c58f06a598a"),
  (1025, "799fe85dc79b41b3e56bc31dc454e1942a7a425deb2d6ea10c68b1bc8a8dd06b"),
  (2048, "3e77872aeccc948729251279665ff9e78e3c2647507972160c3685ff4de9be25"),
  (2049, "548a4fc1805e7fd72cfa9d78f8eb83135e6a65ac447ee7dd003b0ebed841e69d"),
  (3072, "83c7a53925f9c380e7b1bbc948a9618a8bfe586613fd49408399f2cdaad70306"),
  (3073, "f2f6935dc3f0a8f761ed9598b217ba7350fe57abf68ea18bb020402e5e66e7e3"),
  (4096, "6317dbd0b03b0e0d886050efc9142678f7cb903fd4cf71371bf15a091dce8a21"),
  (4097, "4169134d3efcd89b97e56db1d7206fe4fcd5aa77fe34bfda579c6172b3980160"),
  (7168, "ec39bef31b7c6ed2d0f6ebb87251fcddb82357fc1c1fc0000696735a93a9dbe5"),
  (7169, "b66408ea135a1630affe94bfe54cb1278e92230a2b9f04af8568772c346f15f5"),
  (8192, "a47d8ab169c83a47eb4de03995a0aaf66fb15235caf76b822f274fde7968fc8e"),
  (8193, "974a7eb4f4fbdcded432d16f7d489801a8a127eef43c7570c7b8ba9948ddcd9a"),
  (16384, "0e7e1686b0524f90b7d28df8efc6777caec092247d647c1f2f154bb3e2e2a4e4"),
  (31744, "0e6cde4d03a9cc8550a06b9b3fc4dc730feebc58d77b200dc751f66fdfe293fd"),
  (102400, "c334f916c9f57c71ef5570c3d41700af9a3a4fd59c9e1b32cff72bfd21c5e314")]

#guard keyedVectors.size = 26
#guard keyedVectors.all fun (n, digest) => (Blake3.keyedHash officialKey (input n)).toHex == digest
#guard blake3KeyedHash officialKey (input 64) == (Blake3.keyedHash officialKey (input 64)).toBytes

#guard deriveKeyVectors.size = 26
#guard deriveKeyVectors.all fun (n, digest) =>
  (Blake3.deriveKey officialDeriveKeyContext (input n)).toHex == digest
#guard blake3DeriveKey officialDeriveKeyContext (input 1025)
  == (Blake3.deriveKey officialDeriveKeyContext (input 1025)).toBytes

end CertiFriTest.P3.Blake3
