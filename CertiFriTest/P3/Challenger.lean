import CertiFriP3.Challenger

/-!
# Tests of the BLAKE3 challenger

Checks of `CertiFriP3/Challenger.lean` against transcripts of Plonky3's
`SerializingChallenger64<Goldilocks, HashChallenger<u8, H, 32>>` at revision
`3152b14a`. A transcript is a list of steps: each observation is replayed, and
each sampled value is compared with the one Plonky3 sampled at that point.

* Two transcripts use BLAKE3, from an empty and from a nonempty initial state.
  They mix observations of base elements, extension elements and digests with
  samples of extension elements and of bits: a sample from the empty
  transcript, samples in a row across one and several refills of the output
  buffer, observations after a sample that left output unread, and checks of
  proof-of-work witnesses, valid and not.
* A word sampled from BLAKE3 is rejected with probability `2^-32`, so those
  transcripts never reject. A third transcript replaces BLAKE3 with a toy hash,
  on both sides, whose digests hold words that must be rejected: all ones, and
  the order `p` itself; and the largest word that must be accepted, `p - 1`.

In the transcripts a digest is observed by Plonky3 as a `MerkleCap` with one
root or as a `Hash`, which are the same 32 bytes; a base element may be given
by a word that is not canonical.
-/

namespace CertiFriTest.P3.Challenger

open CertiFri CertiFri.P3

/-- One step of a transcript, with the value Plonky3 produced if it samples. -/
inductive Step where
  /-- `observe(a)` for the base element of word `a`. -/
  | observeBase (a : UInt64)
  /-- `observe_algebra_element` of the extension element `c0 + c1 X`. -/
  | observeExt (c0 c1 : UInt64)
  /-- `observe` of the digest written in hexadecimal. -/
  | observeDigest (hex : String)
  /-- `sample_algebra_element`, which gave `c0 + c1 X`. -/
  | sampleExt (c0 c1 : UInt64)
  /-- `sample_bits(bits)`, which gave `value`. -/
  | sampleBits (bits value : Nat)
  /-- `check_witness(bits, witness)`, which gave `ok`. -/
  | checkWitness (bits : Nat) (witness : UInt64) (ok : Bool)

/-- Replay a transcript from step number `index` on. The result is the number
of the first step at which the challenger differs from Plonky3, if any. -/
def firstMismatch (chal : Challenger ChallengerState Goldilocks GoldilocksExt Digest) :
    (index : Nat) → ChallengerState → List Step → Option Nat
  | _, _, [] => none
  | index, s, step :: steps =>
    match step with
    | .observeBase a =>
      firstMismatch chal (index + 1) (chal.observe s (.base (Goldilocks.ofUInt64 a))) steps
    | .observeExt c0 c1 =>
      firstMismatch chal (index + 1)
        (chal.observe s (.ext ⟨Goldilocks.ofUInt64 c0, Goldilocks.ofUInt64 c1⟩)) steps
    | .observeDigest hex =>
      match Digest.ofHex? hex with
      | some d => firstMismatch chal (index + 1) (chal.observe s (.digest d)) steps
      | none => some index
    | .sampleExt c0 c1 =>
      let sampled := chal.sampleExt s
      if sampled.1.c0.val == c0 && sampled.1.c1.val == c1 then
        firstMismatch chal (index + 1) sampled.2 steps
      else some index
    | .sampleBits bits value =>
      let sampled := chal.sampleBits s bits
      if sampled.1 == value then firstMismatch chal (index + 1) sampled.2 steps else some index
    | .checkWitness bits witness ok =>
      let checked := chal.checkWitness s bits (Goldilocks.ofUInt64 witness)
      if checked.1 == ok then firstMismatch chal (index + 1) checked.2 steps else some index

/-- The order of Goldilocks, as a word. -/
def order : UInt64 := 0xFFFFFFFF00000001

/-- Word `k` of the digest of the toy hash, for the fingerprint `s` of the
input: all ones or the order (both rejected), the order minus one (accepted),
or a mixed word. -/
def toyWord (s k : UInt64) : UInt64 :=
  let kind := (s + k) % 4
  if kind == 0 then 0xFFFFFFFFFFFFFFFF
  else if kind == 2 then (if ((s >>> 2) &&& 1) == 0 then order else order - 1)
  else ((s + k) * (0x9E3779B97F4A7C15 : UInt64)) ^^^ (s >>> 7)

/-- A byte hash whose digests hold words that sampling must reject. The
fingerprint of the input is its bytes folded by `s ↦ 31 * s + byte`, plus its
length; the digest is four words, most significant byte first. -/
def toyHash (input : ByteArray) : ByteArray :=
  let s : UInt64 := input.foldl (fun s byte => s * 31 + byte.toUInt64) 0 + input.size.toUInt64
  ([0, 1, 2, 3] : List UInt64).foldl (fun digest k =>
    ([56, 48, 40, 32, 24, 16, 8, 0] : List UInt64).foldl
      (fun digest shift => digest.push (toyWord s k >>> shift).toUInt8) digest) ByteArray.empty

/-- The digest written in hexadecimal, as bytes. -/
def hexBytes (text : String) : ByteArray :=
  ((Digest.ofHex? text).map (·.toBytes)).getD ByteArray.empty

/-! ## Transcripts of Plonky3 -/

/-- A transcript of the BLAKE3 challenger from the empty initial state. -/
def blake3Script : List Step := [
  .sampleExt 0xcc9a93cae41f3262 0x9bcb25c9adc112b7,
  .observeBase 0x8b109bc99cad92bc,
  .observeBase 0xffffffff00000000,
  .observeBase 0x0000000000000000,
  .sampleExt 0x31ef92bd9dc8933f 0xb2dfb383946d25db,
  .sampleExt 0xcd152300b5cae567 0x6cc2ab069ee99360,
  .sampleExt 0x1382f9cac8a20866 0x5cdde6f1607c0e57,
  .observeDigest "ca8a33e272e3736e30b0984b6ac674e45f847b8efc19efdb9ef8f3260cebe47d",
  .sampleBits 10 52,
  .sampleBits 1 1,
  .sampleBits 63 4267412668040119304,
  .sampleBits 20 103626,
  .sampleBits 5 27,
  .observeExt 0xae22dcc7a59eab38 0xd9e9dafd7585b629,
  .sampleExt 0x44f72f40e6d0f4a1 0xd66a3024aad236cf,
  .observeBase 0xcb632a5f35cd9351,
  .sampleBits 16 26780,
  .sampleExt 0x1c55239b5cf21978 0x6dbc626bc2a5fa1d,
  .observeDigest "b9ca78a3183a0365e1e57477602c33965e1f5ef725aeb1eb527f0358d893e072",
  .observeExt 0xffffffff00000000 0x0000000000000001,
  .observeBase 0x0000000100000000,
  .sampleBits 0 0,
  .sampleBits 32 1124696483,
  .sampleExt 0xaaaf6c35b4ceaafd 0x72cbb8f5a9df2b58,
  .sampleExt 0xaafde0efde7cb73d 0xb0ba73f7f7f6c3c3,
  .sampleExt 0xa29470b4731c6768 0xa5a17cd3f2622af5,
  .observeDigest "c9ba0ebd0a83892e05cca1be93d3a489226c96e7aeb846cbf9877b2f92ff61b2",
  .sampleExt 0xcb35c0785487b6fc 0xfc94161f4978df5f,
  .sampleExt 0x1b601a37bd9b9207 0x5becd82608d512cc,
  .sampleExt 0xa0efae4ddd101b2e 0xc74be2d02aa68340,
  .sampleExt 0x7926d0abdd15c9dc 0x3fcd03cfa65bb3f9,
  .sampleExt 0xe553d8b992d62967 0xcd74e18b45a01502,
  .sampleExt 0x09c3cf1359efde06 0x969a467824525599,
  .sampleExt 0xa27834ffb4850708 0xd8edfe0e89dc0899,
  .sampleExt 0x198de35e0c9595b9 0x584cb6c4262d8f50,
  .sampleExt 0xd5364611ddb069f3 0x0ea4c0c878644749,
  .sampleExt 0x116818ecefd60c08 0x7cb1fafb4b92498a,
  .sampleExt 0x7f11a6a6a6bca811 0xa7b1dd6256568122,
  .sampleBits 7 17,
  .sampleBits 7 36,
  .sampleBits 7 79,
  .checkWitness 12 0x000000000000083b true,
  .sampleExt 0x744f8226a173dc80 0x0e6902cc3fc519ac,
  .checkWitness 0 0x0000000000003039 true,
  .sampleBits 8 103,
  .checkWitness 3 0x0000000000000005 false,
  .checkWitness 3 0x0000000000000006 false,
  .checkWitness 1 0x0000000000000007 true,
  .sampleExt 0x3565f46c6637303b 0x9800cfbe2d557549,
  .checkWitness 5 0x000000000000000f true,
  .sampleBits 30 761967677]

/-- A transcript of the BLAKE3 challenger whose initial state is the 41 bytes
`0, 1, …, 40`. -/
def blake3InitialScript : List Step := [
  .observeDigest "3b99c3a1264f9c9be490b59cebf8422b86055aee7f40f1c27a2155acf94e6822",
  .observeBase 0x5db4f164d76aed54,
  .sampleExt 0xed99e202bf122b3c 0xe365c54468cbac55,
  .sampleBits 13 1049,
  .observeExt 0x02cad037dd5f4791 0x9d1c14de185aa272,
  .sampleBits 13 3071,
  .sampleBits 13 7154,
  .sampleBits 13 1098,
  .sampleBits 13 1480,
  .sampleBits 13 4307,
  .sampleExt 0x57b93ca982432dad 0xadb6b9e4b7c4e21b,
  .checkWitness 8 0x000000000000002b true,
  .sampleExt 0x513a8fa45ddafde7 0xc36dbb3e5f995bbc]

/-- A transcript of the challenger over the toy hash, which makes sampling reject words. -/
def toyScript : List Step := [
  .sampleExt 0x316b3a0fa4f9b89b 0xffffffff00000000,
  .sampleExt 0xf4fc469ca664c061 0x48ce139f090693ae,
  .sampleBits 63 9223372032559808512,
  .sampleBits 9 84,
  .sampleExt 0x5f54023291eb4fc4 0x23cb17bd929c57fe,
  .observeBase 0x0000000000000003,
  .sampleExt 0x66532d67ef726a9e 0x29c23192e9df62e4,
  .sampleBits 11 2047,
  .sampleExt 0x82e2c3c6f966ba2e 0x4671ce53fff3bdc4,
  .sampleExt 0xde4c44f95fa2d1f8 0xa3dd30765c39a992,
  .observeExt 0x0000000000000000 0x0000000000000001,
  .sampleBits 40 1095216660481,
  .observeBase 0x0000000001010104,
  .sampleExt 0x449f1c8b908ad8db 0x070800156ffdd0a1,
  .sampleBits 11 2047,
  .sampleExt 0x272787bf33149347 0xffffffff00000000,
  .sampleExt 0xebd8932230fb8b2d 0x588d342c2783602d,
  .observeBase 0x0000000002020205,
  .sampleExt 0x354ce5f89cf0c518 0xf9ddea6d9d67dd22,
  .sampleBits 11 1510,
  .sampleExt 0x5d1128f2417cedbc 0x9569e27ecc33493a,
  .sampleExt 0x5916eef3cd465114 0xffffffff00000000,
  .observeBase 0x0000000003030306,
  .sampleExt 0x3fa63bfb48f600ff 0x00174f48499d08c9,
  .sampleBits 11 1411,
  .sampleExt 0xc5ba31758d1565d5 0x28e669c1cbd14464,
  .sampleExt 0xec577c32c83c4cb2 0x93156042d7757244,
  .observeExt 0x0000000000000003 0x0000000000000004,
  .sampleBits 40 1099511627775,
  .observeBase 0x0000000004040407,
  .sampleExt 0x2ef3c1e1543cdb5a 0xffffffff00000000,
  .sampleBits 11 816,
  .sampleExt 0x3c787b27d4211634 0xffffffff00000000,
  .sampleExt 0x00d776bad6bc0e1e 0xe83ff28841016e77,
  .observeBase 0x0000000005050508,
  .sampleExt 0xffffffff00000000 0x13af5c4c0c565b70,
  .sampleBits 11 2047,
  .sampleExt 0xd63c21df0efb632e 0xffffffff00000000,
  .sampleExt 0x67bac90b6cffa532 0x2bcbdafc6e64bd5c,
  .observeBase 0x0000000006060609,
  .sampleExt 0x1af251fced261585 0xdf01450feccb1daf,
  .sampleBits 11 1637,
  .sampleExt 0xf7ab678ccf403e53 0xb8e7231b64e52cb5,
  .sampleExt 0xffffffff00000000 0x7b7430ae659e245f,
  .observeExt 0x0000000000000006 0x0000000000000007,
  .sampleBits 40 1095216660480,
  .observeBase 0x000000000707070a,
  .sampleExt 0xb8b71b9794e67407 0x7c26140092516fdd,
  .sampleBits 11 1973,
  .sampleExt 0xffffffff00000000 0x28a2d09c4a154f4f,
  .sampleExt 0xffffffff00000000 0xf35343ccfe727305,
  .observeBase 0x000000000808080b,
  .sampleExt 0xffffffff00000000 0x84f6661605f330be,
  .sampleBits 11 2047,
  .sampleExt 0x49016aa33b6808d0 0x6faabc7a12823038,
  .sampleExt 0xffffffff00000000 0x33d94be913172842,
  .observeBase 0x000000000909090c,
  .sampleExt 0xdbaa6323594dda67 0x9f3910b458f6e25d,
  .sampleBits 11 2047,
  .sampleExt 0x3734c6e4e413cfd4 0xfb85f277e5e8c70e,
  .sampleExt 0x4d070c68d3c0dca0 0x10f630fa2d37d4fa,
  .observeExt 0x0000000000000009 0x000000000000000a,
  .sampleBits 40 1099511627775,
  .observeBase 0x000000000a0a0a0d,
  .sampleExt 0x7e28443d8fcfae88 0xffffffff00000000,
  .sampleBits 11 1698,
  .sampleExt 0x92be892cdcba13fd 0x562f9ca1ddcf1bc3,
  .sampleExt 0xffffffff00000000 0xffffffff00000000,
  .observeBase 0x000000000b0b0b0e,
  .sampleExt 0x57a5c1fd416a7244 0x1a0ad27243f14a6e,
  .sampleBits 11 508,
  .sampleExt 0x6424266d8c5c71a6 0xffffffff00000000,
  .sampleExt 0xafdafcad6cdd23e2 0x73abe0386a282bcc]

/-- `(n, digest)`: the toy hash of the `n` bytes `7 * i + 1` for `i < n`. -/
def toyHashVectors : Array (Nat × String) := #[
  (0, "ffffffffffffffff9e3779b97f4a7c15ffffffff00000001daa66d2c7ddf743f"),
  (1, "ffffffff00000001daa66d2c7ddf743fffffffffffffffff1715609f7c746c69"),
  (2, "56e27eb562eddf5dffffffff00000001935172286182d787ffffffffffffffff"),
  (3, "53e46c151a00b8aeffffffffffffffff90535f881895b0d8ffffffff00000001"),
  (4, "ffffffff000000015e5bb4bb54e25fe7ffffffffffffffff9acaa82e537757d1"),
  (5, "ffffffffffffffff4319d3bb9c7f72d2ffffffff000000007f88c72e9b146a88"),
  (6, "20ec2b605981536fffffffffffffffff5d5b1ed3581e5b39ffffffff00000001"),
  (7, "ef20961f370c9805ffffffff000000002b8f89923699906fffffffffffffffff"),
  (8, "ffffffffffffffff4eb50d4b39950f78ffffffff000000008b2400be38081742"),
  (9, "ffffffff0000000081fbce7d5f436105ffffffffffffffffbe6ac1ee59de696b"),
  (10, "e259ca2be4532340ffffffff000000001ec8bdb4e7ce5b6affffffffffffffff"),
  (11, "7f7708e5d3985804ffffffffffffffffbbe60590d277405affffffff00000000")]

-- The toy hash is the one Plonky3 ran with.
#guard toyHashVectors.size = 12
#guard toyHashVectors.all fun (n, expected) =>
  toyHash (ByteArray.mk (Array.ofFn (n := n) fun i => (7 * i.val + 1).toUInt8)) == hexBytes expected

#guard blake3Script.length = 51
#guard firstMismatch challenger 0 (ChallengerState.new ByteArray.empty) blake3Script == none

#guard blake3InitialScript.length = 13
#guard firstMismatch challenger 0
  (ChallengerState.new (ByteArray.mk (Array.ofFn (n := 41) fun i => i.val.toUInt8)))
  blake3InitialScript == none

#guard toyScript.length = 73
#guard firstMismatch (challengerWith toyHash) 0 (ChallengerState.new (ByteArray.mk #[1, 2, 3]))
  toyScript == none

/-! ## The byte challenger -/

/-- The state after observing the base elements of the given words. -/
def observed (words : List UInt64) : ChallengerState :=
  challenger.observeAll (ChallengerState.new ByteArray.empty)
    (words.map fun w => .base (Goldilocks.ofUInt64 w))

/-- The words sampled by `count` calls of `sampleBits 64` in a row. -/
def sampledWords (s : ChallengerState) (count : Nat) : List Nat :=
  challenger.sampleIndices 64 count s

/-- The big-endian number written by `count` bytes of `bytes` from `start` on. -/
def bigEndian (bytes : ByteArray) (start count : Nat) : Nat :=
  (List.range count).foldl (fun acc i => 256 * acc + (bytes.get! (start + i)).toNat) 0

-- Nothing is hashed before the first sample: the initial state and the bytes
-- observed are the input of the first hash.
#guard (observed [1, 2]).input = ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0]
#guard (observed [1, 2]).output = []

-- The first word sampled is the last eight bytes of the digest as a big-endian
-- number, the second the eight bytes before, and so on. The fifth word comes
-- from the digest of the first digest.
#guard
  let first := blake3 (observed [1, 2]).input
  let second := blake3 first
  sampledWords (observed [1, 2]) 6
    = [bigEndian first 24 8, bigEndian first 16 8, bigEndian first 8 8, bigEndian first 0 8,
       bigEndian second 24 8, bigEndian second 16 8]

-- After a sample the input buffer is the digest, and an observation appends
-- to it and discards what is left of the output.
#guard
  let first := blake3 (observed [1, 2]).input
  let sampled := challenger.sampleBits (observed [1, 2]) 64
  let after := challenger.observe sampled.2 (.base (Goldilocks.ofUInt64 3))
  sampled.2.input = first ∧ sampled.2.output.length = 24
    ∧ after.input = first ++ ByteArray.mk #[3, 0, 0, 0, 0, 0, 0, 0] ∧ after.output = []
    ∧ sampledWords after 1 = [bigEndian (blake3 after.input) 24 8]

-- An extension element is observed as its two coordinates, and a digest as
-- its 32 bytes.
#guard (challenger.observe (ChallengerState.new ByteArray.empty)
    (.ext ⟨Goldilocks.ofUInt64 1, Goldilocks.ofUInt64 2⟩)).input = (observed [1, 2]).input
#guard (challenger.observe (ChallengerState.new (ByteArray.mk #[9]))
    (.digest (Blake3.hash ByteArray.empty))).input = ByteArray.mk #[9] ++ blake3 ByteArray.empty

-- Sampling bits keeps the low bits of a word and consumes the whole word.
#guard
  let word := (sampledWords (observed [7]) 1).headD 0
  (List.range 70).all fun bits =>
    let sampled := challenger.sampleBits (observed [7]) bits
    sampled.1 == word % 2 ^ bits && sampled.2.output.length == 24

/-! ## The bound on rejections -/

/-- A hash whose digest is 32 bytes `0xFF`: every word is rejected. -/
def rejecting (_ : ByteArray) : ByteArray :=
  ByteArray.mk (Array.replicate 32 0xFF)

-- After `rejectionFuel` rejected words sampling fails closed (`none`) and the
-- `Challenger` interface marks the state exhausted so witness checks reject
-- even at zero proof-of-work difficulty.
#guard ChallengerState.rejectionFuel = 256
#guard (ChallengerState.sampleBase rejecting (ChallengerState.new ByteArray.empty)).isNone
#guard (ChallengerState.sampleExt? rejecting (ChallengerState.new ByteArray.empty)).isNone
#guard (ChallengerState.sampleExt3? rejecting (ChallengerState.new ByteArray.empty)).isNone
#guard (ChallengerState.sampleBaseWith blake3 0 (ChallengerState.new ByteArray.empty)).isNone
#guard (ChallengerState.sampleBaseWith blake3 1 (ChallengerState.new ByteArray.empty)).isSome
#guard
  let chal := challengerWith rejecting
  let sampled := chal.sampleExt (ChallengerState.new ByteArray.empty)
  let afterObs := chal.observe sampled.2 (.base Goldilocks.one)
  let checked := chal.checkWitness afterObs 0 Goldilocks.zero
  sampled.2.exhausted && !chal.ok sampled.2 && afterObs.exhausted && !chal.ok afterObs
    && !checked.1
#guard
  let chal := challenger3With rejecting
  let sampled := chal.sampleExt (ChallengerState.new ByteArray.empty)
  let checked := chal.checkWitness sampled.2 0 Goldilocks.zero
  sampled.2.exhausted && !chal.ok sampled.2 && !checked.1

end CertiFriTest.P3.Challenger
