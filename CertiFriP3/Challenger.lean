import CertiFri.Challenger
import CertiFriP3.GoldilocksExt
import CertiFriP3.GoldilocksExt3
import CertiFriP3.Blake3

/-!
# The BLAKE3 challenger

Plonky3's `SerializingChallenger64<Goldilocks, HashChallenger<u8, Blake3, 32>>`
(`challenger/src/serializing_challenger.rs`, `challenger/src/hash_challenger.rs`),
as an instance of the `Challenger` interface: `challenger`.

## The byte challenger

`HashChallenger` works on bytes and holds two buffers.

* Observing a byte appends it to the input buffer and discards the output
  buffer: bytes of an earlier output that were not sampled are lost.
* Sampling a byte takes the *last* byte of the output buffer. When the output
  buffer is empty, the input buffer is hashed first; the 32 bytes of the digest
  become both the output buffer and the new content of the input buffer. So the
  input of a hash is the previous digest followed by what was observed since,
  and sampling more than 32 bytes without observing hashes the previous digest
  alone.
* The initial state is an input buffer; it is not hashed until the first
  sample.

## Field elements

* A base element is observed as its eight bytes: the canonical word, least
  significant byte first. An extension element is observed as its two
  coordinates, `c0` then `c1`. A digest is observed as its 32 bytes, in order.
  Nothing is added to delimit the values.
* A machine word is sampled as eight bytes, the first sampled byte being the
  least significant. As bytes leave the output buffer from its end, the first
  word sampled after a hash is bytes 24 to 31 of the digest read as a
  big-endian number.
* A base element is sampled by rejection: words are sampled until one is below
  the order `p`, and that word is the element. Nothing is masked, because `p`
  has 64 bits. A word is rejected with probability below `2^-32`.
* An extension element is sampled as two base elements, `c0` then `c1`.
* `sampleBits` samples one word and keeps its low `bits` bits. It always
  consumes eight bytes and never rejects.

## Totality

Rejection sampling has no bound in Plonky3. Here `sampleBaseWith` / `sampleBase`
stop after `rejectionFuel` rejected words in a row and fail closed by returning
`none`. For the total `Challenger` interface, `sampleExt` / `sampleExt3` record
exhaustion in `ChallengerState.exhausted` (sticky across further observations
and samples), causing `Challenger.ok` and `Challenger.checkWitness` — and
therefore verification — to reject. For a hash that behaves like a random
function this event has probability below `2^-8192` per sample and is not
reachable in practice.

Plonky3's `sample_bits` panics unless `bits < 64` and `2^bits < p`. Here it is
total: from 64 bits on the whole word is returned.

The challenger is defined over any byte hash (`challengerWith`), so that the
rejection can be tested with a hash that provokes it. Nothing is proved here.
The challenger is tested against transcripts produced by Plonky3
(`CertiFriTest/P3/Challenger.lean`).

Not covered: the search for a proof-of-work witness (`grind`). Checking a
witness is `Challenger.checkWitness`, which is written against the interface
and is tested with this challenger.
-/

namespace CertiFri.P3

/-- The state of the byte challenger: the two buffers of Plonky3's
`HashChallenger`. -/
structure ChallengerState where
  /-- The bytes the next hash takes: the previous digest, if any hash was
  taken, followed by the bytes observed since. Plonky3's `input_buffer`. -/
  input : ByteArray
  /-- The bytes of the last digest that can still be sampled, the next one to
  be sampled first. Plonky3's `output_buffer`, last byte first. -/
  output : List UInt8
  /-- Sticky failure bit set when bounded rejection sampling exhausts
  `rejectionFuel` consecutive rejected words. -/
  exhausted : Bool := false
  deriving DecidableEq, Inhabited

namespace ChallengerState

/-- The state of `HashChallenger::new(initial, hasher)`: `initial` is the
input buffer and no output is available. -/
def new (initial : ByteArray) : ChallengerState :=
  { input := initial, output := [], exhausted := false }

/-- Observe bytes, first to last: they are appended to the input buffer and
the output buffer is discarded. Preserves `exhausted`. -/
def observeBytes (s : ChallengerState) (bytes : ByteArray) : ChallengerState :=
  { s with input := s.input ++ bytes, output := [] }

/-- Sample one byte: the last byte of the output buffer, after hashing the
input buffer if the output buffer is empty. A hash with an empty output, for
which Plonky3 panics, gives the byte zero. -/
def sampleByte (hash : ByteArray → ByteArray) (s : ChallengerState) : UInt8 × ChallengerState :=
  match s.output with
  | byte :: output => (byte, { s with output := output })
  | [] =>
    let digest := hash s.input
    match digest.toList.reverse with
    | byte :: output => (byte, { input := digest, output := output })
    | [] => (0, { input := digest, output := [] })

/-- Sample `count` bytes into a word, the first at bit `shift`, each next one
eight bits higher, on top of `acc`. -/
def sampleBytes (hash : ByteArray → ByteArray) :
    (count : Nat) → (shift acc : UInt64) → ChallengerState → UInt64 × ChallengerState
  | 0, _, acc, s => (acc, s)
  | count + 1, shift, acc, s =>
    let sampled := sampleByte hash s
    sampleBytes hash count (shift + 8) (acc ||| (sampled.1.toUInt64 <<< shift)) sampled.2

/-- Sample a machine word: eight bytes, the first sampled being the least
significant (`u64::from_le_bytes(inner.sample_array())`). -/
def sampleWord (hash : ByteArray → ByteArray) (s : ChallengerState) : UInt64 × ChallengerState :=
  sampleBytes hash 8 0 0 s

/-- The number of words in a row that sampling a base element may reject
before it gives up. -/
def rejectionFuel : Nat := 256

/-- Sample a base element by rejection, with at most `fuel` words: the first
sampled word below the order is the element. Fails closed (`none`) if `s` is
already exhausted or all `fuel` words are rejected. -/
def sampleBaseWith (hash : ByteArray → ByteArray) :
    (fuel : Nat) → ChallengerState → Option (Goldilocks × ChallengerState)
  | 0, _ => none
  | fuel + 1, s =>
    if s.exhausted then none
    else
      let sampled := sampleWord hash s
      match Goldilocks.ofCanonical? sampled.1 with
      | some a => some (a, sampled.2)
      | none => sampleBaseWith hash fuel sampled.2

/-- Sample a base element: Plonky3's `sample` at the base field, failing closed
(`none`) after `rejectionFuel` consecutive rejected words. -/
def sampleBase (hash : ByteArray → ByteArray) (s : ChallengerState) :
    Option (Goldilocks × ChallengerState) :=
  sampleBaseWith hash rejectionFuel s

/-- Sample a quadratic-extension element (`c0`, then `c1`), failing closed
(`none`) if either base coordinate exhausts `rejectionFuel`. -/
def sampleExt? (hash : ByteArray → ByteArray) (s : ChallengerState) :
    Option (GoldilocksExt × ChallengerState) :=
  match sampleBase hash s with
  | none => none
  | some (c0, s1) =>
    match sampleBase hash s1 with
    | none => none
    | some (c1, s2) => some (⟨c0, c1⟩, s2)

/-- Sample a cubic-extension element (`c0`, `c1`, `c2`), failing closed (`none`)
if any base coordinate exhausts `rejectionFuel`. -/
def sampleExt3? (hash : ByteArray → ByteArray) (s : ChallengerState) :
    Option (GoldilocksExt3 × ChallengerState) :=
  match sampleBase hash s with
  | none => none
  | some (c0, s1) =>
    match sampleBase hash s1 with
    | none => none
    | some (c1, s2) =>
      match sampleBase hash s2 with
      | none => none
      | some (c2, s3) => some (⟨c0, c1, c2⟩, s3)

/-- Sample an extension element: Plonky3's `sample_algebra_element`, two base
elements, `c0` then `c1`. Marks `exhausted := true` on rejection exhaustion so
the verifier fails closed. -/
def sampleExt (hash : ByteArray → ByteArray) (s : ChallengerState) :
    GoldilocksExt × ChallengerState :=
  match sampleExt? hash s with
  | some res => res
  | none => (0, { s with output := [], exhausted := true })

/-- Sample a cubic-extension element: three base elements, `c0`, `c1`, `c2`.
Marks `exhausted := true` on rejection exhaustion so the verifier fails closed. -/
def sampleExt3 (hash : ByteArray → ByteArray) (s : ChallengerState) :
    GoldilocksExt3 × ChallengerState :=
  match sampleExt3? hash s with
  | some res => res
  | none => (0, { s with output := [], exhausted := true })

/-- Sample an integer below `2 ^ bits`: Plonky3's `sample_bits`, the low bits
of one sampled word. From 64 bits on, the whole word. -/
def sampleBits (hash : ByteArray → ByteArray) (s : ChallengerState) (bits : Nat) :
    Nat × ChallengerState :=
  let sampled := sampleWord hash s
  (sampled.1.toNat % 2 ^ bits, sampled.2)

/-- Observe one value: a base element as its eight bytes (Plonky3's
`observe`), an extension element as its coordinates `c0`, `c1`
(`observe_algebra_element`), a digest as its 32 bytes. -/
def observe (s : ChallengerState) : Observation Goldilocks GoldilocksExt Digest → ChallengerState
  | .base a => s.observeBytes (a.pushBytes ByteArray.empty)
  | .ext e => s.observeBytes (e.c1.pushBytes (e.c0.pushBytes ByteArray.empty))
  | .digest d => s.observeBytes d.toBytes

/-- Observe one value for the cubic extension: a base element as 8 bytes, a
cubic-extension element as 24 bytes (`c0`, `c1`, `c2`), a digest as 32 bytes. -/
def observe3 (s : ChallengerState) : Observation Goldilocks GoldilocksExt3 Digest → ChallengerState
  | .base a => s.observeBytes (a.pushBytes ByteArray.empty)
  | .ext e => s.observeBytes (e.pushBytes ByteArray.empty)
  | .digest d => s.observeBytes d.toBytes

end ChallengerState

/-- Plonky3's `SerializingChallenger64<Goldilocks, HashChallenger<u8, H, 32>>`
over the byte hash `hash`. -/
def challengerWith (hash : ByteArray → ByteArray) :
    Challenger ChallengerState Goldilocks GoldilocksExt Digest where
  observe := ChallengerState.observe
  sampleExt := ChallengerState.sampleExt hash
  sampleBits := ChallengerState.sampleBits hash
  ok s := !s.exhausted

/-- The challenger of the BLAKE3 configuration:
`SerializingChallenger64<Goldilocks, HashChallenger<u8, Blake3, 32>>`. -/
def challenger : Challenger ChallengerState Goldilocks GoldilocksExt Digest :=
  challengerWith blake3

/-- Plonky3's `SerializingChallenger64<Goldilocks, HashChallenger<u8, H, 32>>`
instantiated for the cubic trinomial extension `GoldilocksExt3`. -/
def challenger3With (hash : ByteArray → ByteArray) :
    Challenger ChallengerState Goldilocks GoldilocksExt3 Digest where
  observe := ChallengerState.observe3
  sampleExt := ChallengerState.sampleExt3 hash
  sampleBits := ChallengerState.sampleBits hash
  ok s := !s.exhausted

/-- The BLAKE3 challenger for `Goldilocks` / `GoldilocksExt3`. -/
def challenger3 : Challenger ChallengerState Goldilocks GoldilocksExt3 Digest :=
  challenger3With blake3

end CertiFri.P3
