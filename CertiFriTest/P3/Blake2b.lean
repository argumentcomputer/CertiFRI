import CertiFriP3.Blake2b

/-!
# RFC 7693 `BLAKE2b-512` executable tests

Executable `#guard` checks of `Digest64` round-trips, RFC 7693 KAT vectors
(empty, `"abc"`, exact 128-byte block, 129-byte and 256-byte multi-block inputs,
personalization, keyed hashing), and 1-block `hashPair64` parity with
streaming `hash (a.toBytes ++ b.toBytes)`.
-/

namespace CertiFriTest.P3.Blake2b

open CertiFri.P3

private def patternBytes (n : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := n) (fun i => (i.val % 256).toUInt8))

-- RFC 7693 KATs (matching Python `hashlib.blake2b(..., digest_size=64)` bit-for-bit)
#guard (Blake2b.hash ByteArray.empty).toHex
  == "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"

#guard (Blake2b.hash "abc".toUTF8).toHex
  == "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"

#guard (Blake2b.hash (patternBytes 128)).toHex
  == "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115"

#guard (Blake2b.hash (patternBytes 129)).toHex
  == "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f"

#guard (Blake2b.hash (patternBytes 256)).toHex
  == "1ecc896f34d3f9cac484c73f75f6a5fb58ee6784be41b35f46067b9c65c63a6794d3d744112c653f73dd7deb6666204c5a9bfa5b46081fc10fdbe7884fa5cbf8"

-- RFC 7693 §2.5 personalization KAT (`person = "CertiFRI:v6:leaf"`)
#guard (Blake2b.hashWithPersonal "CertiFRI:v6:leaf".toUTF8 "abc".toUTF8).toHex
  == "3e4a33fd0d3805521940e601c499e14d40587e60b66bd910fd8a65e5c458341a714cd538d676865f62fc45f31a71d4e95e7e8ebc2cc99ead15655ce251f58b3a"

-- RFC 7693 keyed hashing KATs (key = 32 × 'k')
private def testKey32 : ByteArray :=
  ByteArray.mk (Array.replicate 32 0x6b)

#guard (Blake2b.hashKeyed testKey32 ByteArray.empty ByteArray.empty).toHex
  == "c4bdf2f7b446de109ebab2e1fd4ff2a52a03c1ecd7cc139083dddb757f9b5745e5600c0cce096588ffd3cfede30d89bef150f8ea497617cada8a719d6a44315f"

#guard (Blake2b.hashKeyed testKey32 ByteArray.empty "abc".toUTF8).toHex
  == "2ca403f5c2ab8f47e1168b8432648cd87dfb5fb846204c7ff0ee4783926e74bffa97610aa84b22b0ca0d6a76171702b863c8c6cd97f3accd06d92b2d9ad571f8"

-- `Digest64` byte and hex round-trips + 1-block `hashPair64` parity
#guard
  let a := Blake2b.hash "left".toUTF8
  let b := Blake2b.hash "right".toUTF8
  a.toBytes.size == 64 && b.toBytes.size == 64
    && Digest64.ofBytes? a.toBytes == some a
    && Digest64.ofHex? a.toHex == some a
    && Digest64.ofBytes? ByteArray.empty == none
    && Blake2b.hashPair64 a b == Blake2b.hash (a.toBytes ++ b.toBytes)
    && Blake2b.hashPair64WithPersonal "ix/v6/b2b/node".toUTF8 a b
        == Blake2b.hashWithPersonal "ix/v6/b2b/node".toUTF8 (a.toBytes ++ b.toBytes)

end CertiFriTest.P3.Blake2b
