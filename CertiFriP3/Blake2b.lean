import CertiFriP3.Digest

/-!
# RFC 7693 `BLAKE2b-512`

Pure-Lean specification of RFC 7693 `BLAKE2b-512` (unkeyed, keyed, and natively
personalized via the 16-byte parameter-block `personal` field):

* **State width:** 512 bits (`8 × UInt64`, `Digest64`).
* **Block size:** 128 bytes (`16 × UInt64`, `Block`).
* **Rounds:** 12 rounds (`96` 64-bit `G` quarter-rounds, rotations `32, 24, 16, 63`).
* **1-block 2-to-1 Merkle compression:** two 64-byte digests (`left || right`)
  are exactly 128 bytes, so `hashPair64` / `hashPair64WithPersonal` executes a
  **single** `BLAKE2b` compression call (`tLo = 128, tHi = 0, isLast = true`).
* **Concrete post-quantum security:** unlike `BLAKE3-XOF48`/`BLAKE3-XOF64` (which
  retain a 256-bit internal chaining value capping concrete BHT collision
  resistance at `85.3` bits on every `> 64`-byte input), `BLAKE2b-512` has a
  full 512-bit internal state (`255.71` bits classical BCS `c = 3/2`, `170.7`
  bits BHT quantum collision, `204.8` bits CNS quantum collision, and `256`
  bits Grover preimage).

## Kernel-checked RFC 7693 KAT theorems (zero `sorry`, zero `native_decide`)

All known-answer tests in this module are proved in the Lean kernel using pure
`decide` over verified half-round execution traces (`compress_of_trace`):
* `kat_empty` / `kat_empty_hex`: empty message `""`
* `kat_abc` / `kat_abc_hex`: RFC 7693 Appendix A vector `"abc"`
* `kat_exact128` / `kat_exact128_hex`: exact 128-byte single-block input `0..127`
* `kat_hashPair64_exact128`: 1-block `hashPair64` matches `hash` on `left || right`
* `kat_multi129` / `kat_multi129_hex`: 129-byte multi-block input `0..128`
  (exercises non-final + final compression and byte counter `tLo = 128 → 129`)
* `kat_personal_abc` / `kat_personal_abc_hex`: RFC 7693 §2.5 16-byte
  personalization (`"ix/v6/b2b/leaf"`) on `"abc"`
-/

namespace CertiFri.P3.Blake2b

open LittleEndian

/-- RFC 7693 §2.6 initialization vector `IV[0..7]` (fractional parts of the
square roots of the first eight primes). -/
def iv : Digest64 :=
  ⟨0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
   0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179⟩

/-- A 128-byte message block as sixteen little-endian 64-bit words. -/
structure Block where
  m0 : UInt64
  m1 : UInt64
  m2 : UInt64
  m3 : UInt64
  m4 : UInt64
  m5 : UInt64
  m6 : UInt64
  m7 : UInt64
  m8 : UInt64
  m9 : UInt64
  m10 : UInt64
  m11 : UInt64
  m12 : UInt64
  m13 : UInt64
  m14 : UInt64
  m15 : UInt64
  deriving DecidableEq, Inhabited

/-- The all-zero 128-byte block. -/
def Block.zero : Block :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The sixteen 64-bit words of the BLAKE2b compression working vector `v[0..15]`. -/
structure State where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64
  deriving DecidableEq, Inhabited

/-- Rotate a 64-bit word right by `n` bits (`0 < n < 64`). -/
@[inline] def rotR64 (x n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- RFC 7693 §3.1 mixing function `G(v, a, b, c, d, x, y)` with rotations
`(R1, R2, R3, R4) = (32, 24, 16, 63)`. -/
@[inline] def mix (a b c d x y : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let a := a + b + x
  let d := rotR64 (d ^^^ a) 32
  let c := c + d
  let b := rotR64 (b ^^^ c) 24
  let a := a + b + y
  let d := rotR64 (d ^^^ a) 16
  let c := c + d
  let b := rotR64 (b ^^^ c) 63
  (a, b, c, d)

/-- RFC 7693 §2.7 message word permutation `SIGMA[r mod 10]` applied to `m`. -/
def sigmaBlock (r : Nat) (m : Block) : Block :=
  match r % 10 with
  | 0 => m
  | 1 => ⟨m.m14, m.m10, m.m4, m.m8, m.m9, m.m15, m.m13, m.m6,
          m.m1, m.m12, m.m0, m.m2, m.m11, m.m7, m.m5, m.m3⟩
  | 2 => ⟨m.m11, m.m8, m.m12, m.m0, m.m5, m.m2, m.m15, m.m13,
          m.m10, m.m14, m.m3, m.m6, m.m7, m.m1, m.m9, m.m4⟩
  | 3 => ⟨m.m7, m.m9, m.m3, m.m1, m.m13, m.m12, m.m11, m.m14,
          m.m2, m.m6, m.m5, m.m10, m.m4, m.m0, m.m15, m.m8⟩
  | 4 => ⟨m.m9, m.m0, m.m5, m.m7, m.m2, m.m4, m.m10, m.m15,
          m.m14, m.m1, m.m11, m.m12, m.m6, m.m8, m.m3, m.m13⟩
  | 5 => ⟨m.m2, m.m12, m.m6, m.m10, m.m0, m.m11, m.m8, m.m3,
          m.m4, m.m13, m.m7, m.m5, m.m15, m.m14, m.m1, m.m9⟩
  | 6 => ⟨m.m12, m.m5, m.m1, m.m15, m.m14, m.m13, m.m4, m.m10,
          m.m0, m.m7, m.m6, m.m3, m.m9, m.m2, m.m8, m.m11⟩
  | 7 => ⟨m.m13, m.m11, m.m7, m.m14, m.m12, m.m1, m.m3, m.m9,
          m.m5, m.m0, m.m15, m.m4, m.m8, m.m6, m.m2, m.m10⟩
  | 8 => ⟨m.m6, m.m15, m.m14, m.m9, m.m11, m.m3, m.m0, m.m8,
          m.m12, m.m2, m.m13, m.m7, m.m1, m.m4, m.m10, m.m5⟩
  | _ => ⟨m.m10, m.m2, m.m8, m.m4, m.m7, m.m6, m.m1, m.m5,
          m.m15, m.m11, m.m9, m.m14, m.m3, m.m12, m.m13, m.m0⟩

/-- Column step (first half-round) with pre-permuted block `pm = sigmaBlock r m`. -/
def roundCol (s : State) (pm : Block) : State :=
  let (v0, v4, v8, v12) := mix s.v0 s.v4 s.v8 s.v12 pm.m0 pm.m1
  let (v1, v5, v9, v13) := mix s.v1 s.v5 s.v9 s.v13 pm.m2 pm.m3
  let (v2, v6, v10, v14) := mix s.v2 s.v6 s.v10 s.v14 pm.m4 pm.m5
  let (v3, v7, v11, v15) := mix s.v3 s.v7 s.v11 s.v15 pm.m6 pm.m7
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- Diagonal step (second half-round) with pre-permuted block `pm = sigmaBlock r m`. -/
def roundDiag (s : State) (pm : Block) : State :=
  let (v0, v5, v10, v15) := mix s.v0 s.v5 s.v10 s.v15 pm.m8 pm.m9
  let (v1, v6, v11, v12) := mix s.v1 s.v6 s.v11 s.v12 pm.m10 pm.m11
  let (v2, v7, v8, v13) := mix s.v2 s.v7 s.v8 s.v13 pm.m12 pm.m13
  let (v3, v4, v9, v14) := mix s.v3 s.v4 s.v9 s.v14 pm.m14 pm.m15
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- One full BLAKE2b round at round index `r` (`0 ≤ r < 12`). -/
def round (r : Nat) (s : State) (m : Block) : State :=
  let pm := sigmaBlock r m
  roundDiag (roundCol s pm) pm

/-- Run `k` BLAKE2b rounds starting at round index `r`. -/
def roundsFrom (r : Nat) : Nat → State → Block → State
  | 0, s, _ => s
  | k + 1, s, m => roundsFrom (r + 1) k (round r s m) m

/-- Run all 12 RFC 7693 BLAKE2b rounds (`r = 0..11`). -/
def rounds12 (s : State) (m : Block) : State :=
  roundsFrom 0 12 s m

/-- Initialize the 16-word compression working vector from chaining state `h`,
128-bit byte counter `(tLo, tHi)`, and final-block indicator `isLast`. -/
def initCompressState (h : Digest64) (tLo tHi : UInt64) (isLast : Bool) : State :=
  let f0 : UInt64 := if isLast then 0xffffffffffffffff else 0
  ⟨h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7,
   iv.w0, iv.w1, iv.w2, iv.w3, iv.w4 ^^^ tLo, iv.w5 ^^^ tHi, iv.w6 ^^^ f0, iv.w7⟩

/-- Feed-forward finalization `h'[i] = h[i] ^^^ v[i] ^^^ v[i + 8]`. -/
def finalizeCompress (h : Digest64) (v : State) : Digest64 :=
  ⟨h.w0 ^^^ v.v0 ^^^ v.v8, h.w1 ^^^ v.v1 ^^^ v.v9,
   h.w2 ^^^ v.v2 ^^^ v.v10, h.w3 ^^^ v.v3 ^^^ v.v11,
   h.w4 ^^^ v.v4 ^^^ v.v12, h.w5 ^^^ v.v5 ^^^ v.v13,
   h.w6 ^^^ v.v6 ^^^ v.v14, h.w7 ^^^ v.v7 ^^^ v.v15⟩

/-- RFC 7693 §3.2 BLAKE2b compression function `F(h, m, t, f)`. -/
def compress (h : Digest64) (m : Block) (tLo tHi : UInt64) (isLast : Bool) : Digest64 :=
  finalizeCompress h (rounds12 (initCompressState h tLo tHi isLast) m)

/-- Read a 128-byte little-endian block from `bytes` starting at byte `offset`,
zero-padded past the end. -/
def bytesBlock (bytes : ByteArray) (offset : Nat) : Block :=
  ⟨word64 bytes offset, word64 bytes (offset + 8),
   word64 bytes (offset + 16), word64 bytes (offset + 24),
   word64 bytes (offset + 32), word64 bytes (offset + 40),
   word64 bytes (offset + 48), word64 bytes (offset + 56),
   word64 bytes (offset + 64), word64 bytes (offset + 72),
   word64 bytes (offset + 80), word64 bytes (offset + 88),
   word64 bytes (offset + 96), word64 bytes (offset + 104),
   word64 bytes (offset + 112), word64 bytes (offset + 120)⟩

/-- Assemble two 64-byte digests directly into a single 128-byte block
(`left || right`), with zero byte serialization roundtrip. -/
def pair64Block (left right : Digest64) : Block :=
  ⟨left.w0, left.w1, left.w2, left.w3, left.w4, left.w5, left.w6, left.w7,
   right.w0, right.w1, right.w2, right.w3, right.w4, right.w5, right.w6, right.w7⟩

/-- RFC 7693 §2.5 parameter-block initialization for sequential mode (`fanout = 1`,
`depth = 1`), output length `outLen` (`64` for BLAKE2b-512), key length `keyLen`
(`0..64`), and optional up-to-16-byte `personal` domain-separation tag (zero-padded
into bytes `48..63` = `w6, w7`). -/
def initState (outLen : UInt8 := 64) (keyLen : UInt8 := 0)
    (personal : ByteArray := ByteArray.empty) : Digest64 :=
  let p0 : UInt64 := (0x01010000 : UInt64) ||| (keyLen.toUInt64 <<< 8) ||| outLen.toUInt64
  let p6 : UInt64 := word64 personal 0
  let p7 : UInt64 := word64 personal 8
  ⟨iv.w0 ^^^ p0, iv.w1, iv.w2, iv.w3, iv.w4, iv.w5, iv.w6 ^^^ p6, iv.w7 ^^^ p7⟩

/-- Initial chaining state for unkeyed `BLAKE2b-512` with optional 16-byte `personal`. -/
def initState512 (personal : ByteArray := ByteArray.empty) : Digest64 :=
  initState 64 0 personal

/-- Standard unkeyed, unpersonalized RFC 7693 `BLAKE2b-512` initial state
(`IV[0] ^^^ 0x01010040`, `IV[1..7]`). -/
def initState512Plain : Digest64 :=
  initState 64 0 ByteArray.empty

/-- Initial chaining state for unkeyed `BLAKE2b-512` with UTF-8 personalization string
(must be `≤ 16` bytes for injective domain separation). -/
def initState512OfString (personal : String) : Digest64 :=
  initState512 personal.toUTF8

/-- Add `delta` bytes to the 128-bit little-endian byte counter `(tLo, tHi)`. -/
@[inline] def addCounter (tLo tHi delta : UInt64) : UInt64 × UInt64 :=
  let nextLo := tLo + delta
  let nextHi := if nextLo < tLo then tHi + 1 else tHi
  (nextLo, nextHi)

/-- Compress `n` non-final 128-byte blocks starting at block index `startIdx`. -/
def chainBlocks (h : Digest64) (blockAt : Nat → Block) (tLo tHi : UInt64) (startIdx : Nat) :
    Nat → Digest64 × UInt64 × UInt64
  | 0 => (h, tLo, tHi)
  | n + 1 =>
    let (tLo', tHi') := addCounter tLo tHi 128
    let h' := compress h (blockAt startIdx) tLo' tHi' false
    chainBlocks h' blockAt tLo' tHi' (startIdx + 1) n

/-- Hash `totalLen` bytes supplied as 128-byte blocks `blockAt 0, blockAt 1, ...`,
starting from chaining state `h` and byte counter `(tLo, tHi)`.

Matches RFC 7693 §3.3 exactly:
* `totalLen = 0`: one compression of `Block.zero` with `isLast = true`.
* `1 ≤ totalLen ≤ 128`: zero non-final blocks and one final compression with
  `t += totalLen` and `isLast = true` (so 128-byte inputs execute 1 block!).
* `totalLen > 128`: `(totalLen - 1) / 128` non-final 128-byte blocks followed by
  one final block of `totalLen - 128 * numFull` bytes (`1..128`) with `isLast = true`. -/
def hashBlocksFrom (h : Digest64) (tLo tHi : UInt64) (totalLen : Nat)
    (blockAt : Nat → Block) : Digest64 :=
  if totalLen = 0 then
    compress h Block.zero tLo tHi true
  else
    let numFull := (totalLen - 1) / 128
    let finalLen := totalLen - 128 * numFull
    let (hPre, tLoPre, tHiPre) := chainBlocks h blockAt tLo tHi 0 numFull
    let (tLoF, tHiF) := addCounter tLoPre tHiPre finalLen.toUInt64
    compress hPre (blockAt numFull) tLoF tHiF true

/-- Hash a `ByteArray` using a precomputed initial chaining state `h`. -/
def hashWithInit (h : Digest64) (bytes : ByteArray) : Digest64 :=
  hashBlocksFrom h 0 0 bytes.size (fun i => bytesBlock bytes (128 * i))

/-- Unkeyed RFC 7693 `BLAKE2b-512` with optional 16-byte `personal` domain tag. -/
def hashWithPersonal (personal : ByteArray) (bytes : ByteArray) : Digest64 :=
  hashWithInit (initState512 personal) bytes

/-- Keyed RFC 7693 `BLAKE2b-512` (`key.size ≤ 64`) with optional 16-byte `personal`. -/
def hashKeyed (key : ByteArray) (personal : ByteArray := ByteArray.empty)
    (bytes : ByteArray) : Digest64 :=
  if key.size = 0 then
    hashWithPersonal personal bytes
  else
    let h0 := initState 64 key.size.toUInt8 personal
    let keyBlock := bytesBlock key 0
    if bytes.size = 0 then
      compress h0 keyBlock 128 0 true
    else
      let h1 := compress h0 keyBlock 128 0 false
      hashBlocksFrom h1 128 0 bytes.size (fun i => bytesBlock bytes (128 * i))

/-- Standard unkeyed, unpersonalized RFC 7693 `BLAKE2b-512`. -/
def hash (bytes : ByteArray) : Digest64 :=
  hashWithInit initState512Plain bytes

/-- Standard RFC 7693 `BLAKE2b-512` returning a 64-byte `ByteArray`. -/
def blake2b512 (bytes : ByteArray) : ByteArray :=
  (hash bytes).toBytes

/-- Single-block 2-to-1 Merkle compression of `left || right` (exact 128-byte
single block: `tLo = 128, tHi = 0, isLast = true`) under initial state `h`. -/
def hashPair64WithInit (h left right : Digest64) : Digest64 :=
  compress h (pair64Block left right) 128 0 true

/-- Single-block 2-to-1 Merkle compression with 16-byte `personal` domain tag. -/
def hashPair64WithPersonal (personal : ByteArray) (left right : Digest64) : Digest64 :=
  hashPair64WithInit (initState512 personal) left right

/-- Single-block 2-to-1 Merkle compression under plain `BLAKE2b-512`. -/
def hashPair64 (left right : Digest64) : Digest64 :=
  hashPair64WithInit initState512Plain left right

/-! ## Kernel-checked RFC 7693 KAT verification machinery (zero `native_decide`) -/

private def checkHalfRounds (r : Nat) :
    Nat → State → Block → List (State × State) → Option State
  | 0, s, _, [] => some s
  | k + 1, s, m, (sc, sd) :: rest =>
    let pm := sigmaBlock r m
    if roundCol s pm == sc && roundDiag sc pm == sd then
      checkHalfRounds (r + 1) k sd m rest
    else none
  | _, _, _, _ => none

private theorem roundsFrom_of_checkHalfRounds :
    ∀ r k s m trace res,
      checkHalfRounds r k s m trace = some res → roundsFrom r k s m = res
  | _, 0, s, _, [], res, h => by
    simp only [checkHalfRounds, Option.some.injEq] at h
    exact h
  | r, k + 1, s, m, (sc, sd) :: rest, res, h => by
    simp only [checkHalfRounds] at h
    split at h
    · next hcd =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hcd
      have hround : round r s m = sd := by
        unfold round
        dsimp only
        rw [hcd.1, hcd.2]
      rw [roundsFrom, hround]
      exact roundsFrom_of_checkHalfRounds (r + 1) k sd m rest res h
    · cases h
  | _, 0, _, _, _ :: _, _, h => by simp [checkHalfRounds] at h
  | _, _ + 1, _, _, [], _, h => by simp [checkHalfRounds] at h

private theorem compress_of_trace (h : Digest64) (m : Block) (tLo tHi : UInt64) (isLast : Bool)
    (trace : List (State × State)) (final : State) (out : Digest64)
    (htr : checkHalfRounds 0 12 (initCompressState h tLo tHi isLast) m trace = some final)
    (hout : finalizeCompress h final = out) :
    compress h m tLo tHi isLast = out := by
  unfold compress rounds12
  rw [roundsFrom_of_checkHalfRounds 0 12 _ m trace final htr, hout]

private theorem hashWithInit_singleBlock_of_trace (h : Digest64) (bytes : ByteArray)
    (m : Block) (trace : List (State × State)) (final : State) (out : Digest64)
    (hpos : 0 < bytes.size) (hle : bytes.size ≤ 128)
    (hm : bytesBlock bytes 0 = m)
    (htr : checkHalfRounds 0 12 (initCompressState h bytes.size.toUInt64 0 true) m trace = some final)
    (hout : finalizeCompress h final = out) :
    hashWithInit h bytes = out := by
  have hne : bytes.size ≠ 0 := by omega
  have hfull : (bytes.size - 1) / 128 = 0 := by omega
  unfold hashWithInit hashBlocksFrom
  simp only [hne, ↓reduceIte, hfull, Nat.mul_zero, Nat.sub_zero, chainBlocks, addCounter]
  have h0 : (0 : UInt64) + bytes.size.toUInt64 = bytes.size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp
  have hlt : ¬ (bytes.size.toUInt64 < 0) := by
    intro hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    simp at this
  rw [h0, ite_eq_right hlt, hm]
  exact compress_of_trace h m bytes.size.toUInt64 0 true trace final out htr hout

private theorem hashWithInit_twoBlock_of_trace (h mid out : Digest64) (bytes : ByteArray)
    (m0 m1 : Block) (tr0 tr1 : List (State × State)) (fin0 fin1 : State)
    (hlo : 128 < bytes.size) (hhi : bytes.size ≤ 256)
    (hm0 : bytesBlock bytes 0 = m0)
    (hm1 : bytesBlock bytes 128 = m1)
    (htr0 : checkHalfRounds 0 12 (initCompressState h 128 0 false) m0 tr0 = some fin0)
    (hmid : finalizeCompress h fin0 = mid)
    (htr1 : checkHalfRounds 0 12 (initCompressState mid bytes.size.toUInt64 0 true) m1 tr1 = some fin1)
    (hout : finalizeCompress mid fin1 = out) :
    hashWithInit h bytes = out := by
  have hne : bytes.size ≠ 0 := by omega
  have hfull : (bytes.size - 1) / 128 = 1 := by omega
  unfold hashWithInit hashBlocksFrom
  simp only [hne, ↓reduceIte, hfull, Nat.mul_one, chainBlocks, addCounter, Nat.mul_zero]
  have h128 : (0 : UInt64) + 128 = 128 := by decide
  have h128lt : ¬ ((128 : UInt64) < 0) := by decide
  rw [h128, ite_eq_right h128lt, hm0]
  have hc0 : compress h m0 128 0 false = mid :=
    compress_of_trace h m0 128 0 false tr0 fin0 mid htr0 hmid
  rw [hc0, hm1]
  have hsum : (128 : UInt64) + (bytes.size - 128).toUInt64 = bytes.size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    have hlt256 : bytes.size < UInt64.size := by
      have : UInt64.size = 2 ^ 64 := rfl
      omega
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.toUInt64,
      UInt64.toNat_ofNat]
    have h1 : 128 % UInt64.size = 128 := by decide
    have h2 : (bytes.size - 128) % UInt64.size = bytes.size - 128 := Nat.mod_eq_of_lt (by omega)
    have h3 : bytes.size % UInt64.size = bytes.size := Nat.mod_eq_of_lt hlt256
    rw [h1, h2, h3]
    have h4 : 128 + (bytes.size - 128) = bytes.size := by omega
    rw [h4, h3]
  have hnotlt : ¬ (bytes.size.toUInt64 < 128) := by
    intro hlt
    have h' := UInt64.lt_iff_toNat_lt.mp hlt
    have hlt256 : bytes.size < UInt64.size := by
      have : UInt64.size = 2 ^ 64 := rfl
      omega
    have h3 : bytes.size.toUInt64.toNat = bytes.size := by
      simp [Nat.toUInt64, Nat.mod_eq_of_lt hlt256]
    have h128' : (128 : UInt64).toNat = 128 := by decide
    omega
  rw [hsum, ite_eq_right hnotlt]
  exact compress_of_trace mid m1 bytes.size.toUInt64 0 true tr1 fin1 out htr1 hout

/-! ## RFC 7693 KAT data and kernel-checked proofs -/

/-- Exact 128-byte input `[0x00, 0x01, ..., 0x7f]` for single-block KAT testing. -/
def kat128Input : ByteArray :=
  ByteArray.mk #[
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
    0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f]

/-- Exact 129-byte input `[0x00, 0x01, ..., 0x80]` for multi-block KAT testing. -/
def kat129Input : ByteArray :=
  ByteArray.mk #[
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x3a, 0x3b, 0x3c, 0x3d, 0x3e, 0x3f,
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
    0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59, 0x5a, 0x5b, 0x5c, 0x5d, 0x5e, 0x5f,
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7b, 0x7c, 0x7d, 0x7e, 0x7f,
    0x80]

/-- Left 64-byte digest corresponding to bytes `0..63` of `kat128Input`. -/
def katPairLeft : Digest64 :=
  ⟨0x0706050403020100, 0x0f0e0d0c0b0a0908, 0x1716151413121110, 0x1f1e1d1c1b1a1918,
   0x2726252423222120, 0x2f2e2d2c2b2a2928, 0x3736353433323130, 0x3f3e3d3c3b3a3938⟩

/-- Right 64-byte digest corresponding to bytes `64..127` of `kat128Input`. -/
def katPairRight : Digest64 :=
  ⟨0x4746454443424140, 0x4f4e4d4c4b4a4948, 0x5756555453525150, 0x5f5e5d5c5b5a5958,
   0x6766656463626160, 0x6f6e6d6c6b6a6968, 0x7776757473727170, 0x7f7e7d7c7b7a7978⟩

private def katTraceEmpty : List (State × State) := [
  (⟨0xf0c9aa0de38b9b89, 0x63b7dedf4a4e5ad3, 0xbe50eb454e0a93d7, 0x949804b0483ead14, 0xbbdf873400fee49a, 0xed49c30cd311d50e, 0xa056671704b00d71, 0x75e6432fc4661b06, 0x685eb2bc42983d3d, 0x7bee264bf3cdadfe, 0xb2752dadd66bd8f9, 0xa99463cb37905929, 0xf111fd8b64c5099d, 0x254ef880a19a8726, 0x789d43381c47f584, 0xa25ef57d7da312ee⟩, ⟨0x86b7dbabb0f09c18, 0x042b1d69e8a11a6c, 0xa84662dec110476d, 0x9709cc4f004ad3ca, 0x55da1906e421bacd, 0x552d6643edbe2b38, 0xebf8498c61853a98, 0xb3df98146350f817, 0xade0f8639f37e49b, 0xec7f4ce9c51d9f7a, 0x8232ddb10c8c3e1d, 0x75e0f3b5a9602f64, 0xa2112e107cb01dbe, 0x91981bac4b25d069, 0x1b16c273a86528a0, 0x047f4d89b9d2ccbd⟩),
  (⟨0x7597e574ee6d10de, 0xb974c78aaae43a04, 0xc5d55a51fe575cff, 0xf18abe4759fed175, 0xf1f45e6d2565d3a7, 0x97c68a326942dbfe, 0xe338f534aed18e9c, 0xdcd0fe6c8ee4ea45, 0x61ffdff4cbe8502a, 0x2bff06c5e025999f, 0x400ad77c8ca91db4, 0x48c926d5b11170b6, 0xca7c9c35ae2f90ed, 0xa205240e52476224, 0x32e74f25f0f4717f, 0xf89f2bc3b91b1768⟩, ⟨0x36185660d108f0c7, 0xcfcd9962b53fe049, 0x11ccf85c39377f86, 0xbbbdb3fefae9e9b0, 0x5b1f303ac5bcb86b, 0x97b49ace92cf0a15, 0x6472d7b32530c50e, 0x572e972204667c58, 0x44b1d40ca9c8066e, 0x75b10f57195b18a1, 0xe363abde303e86e1, 0x0126b77ac912752e, 0xc0c33857c12fe3ee, 0x0336ceb7dd3c3994, 0xba21342d679d2b71, 0xb4a3d8acadd424c9⟩),
  (⟨0x91b4d86319f47b70, 0x469b66ce9f88da4a, 0xe3eddd888a34b56d, 0x17612d2583bd8473, 0xc44b69001aa5be08, 0xe95308acc8d9c31f, 0x060df14b0a0d83e8, 0xdfbd444ab656618e, 0x6258e5478e7c0d3a, 0x2bb0b6cb33150e63, 0x6ea8f5dcaecab12d, 0x6baa4021df462eac, 0xc5bcc65e92bf4800, 0x20ccd3a9b504fb3c, 0x514fda18b26d462a, 0x17ff45e56fe425f2⟩, ⟨0x959ce92262e83562, 0xa2f873ba883d7d94, 0x79495c5b96225cc2, 0x39913eb994355f22, 0x6e72f0501a64cba2, 0x2f9c44071c7725e9, 0xb9d3d70a2689a2f3, 0x667ecabcec2e627d, 0x06a15fd6238074f9, 0x6addd0bbf8e07976, 0x8d5b2a110e226427, 0x8aa6f025cde3ce1b, 0xe3d399d165880128, 0xaeb88cc6b19c7545, 0x131f159f3ae81ed6, 0x918818b6f25f0e10⟩),
  (⟨0x3c8e17e391dd5415, 0x4e264c713f9796e6, 0xe047061009887dbd, 0xf5cdb0111dd8c9b2, 0x18c5747e6f78f118, 0xacf32d592b6e16a2, 0x879f47a6b2979547, 0x01d7c279c4de0811, 0x341c844e232c2b9d, 0x2de802030f55f838, 0x6ee671791597b4ab, 0xd55647a67f1a0c1b, 0x14b6244b17cf7601, 0xade15b0e9a4943bb, 0x5b476604e773298a, 0xd87287f17f9e2c40⟩, ⟨0xcee31fda05e09423, 0xefeec4549c15a21f, 0xd7d5fe1369ef4085, 0x615f00105d32f7d4, 0x3f44f6806f36fd46, 0xdb903c77d05b05ce, 0xaea137baedc0d85f, 0x5df3f6686032bf07, 0x5b4ecebdab91e534, 0x4d69a0c0f87a43a9, 0x88a9c4a6a0b8ab8b, 0xcd79abe1df0619dd, 0x12430a0e9e785d66, 0xd30283fa38662610, 0xb55f0b7d935008e6, 0x56ee0c36592d3413⟩),
  (⟨0xda24e4d46f83de11, 0x784212467c8f71ad, 0xa6a997b180932b22, 0xb0fe2364ef3e7983, 0x85fe04dc156873b1, 0x71b0bcd1695bc422, 0x8652ae22e6ef1f8e, 0x88495f1ab76fb00b, 0x0903cc17f0d87570, 0x941b4f12a4b32bd1, 0x631b36f25b949df9, 0x358f83616a6f1aad, 0xc245314b28db73e8, 0xf29b2c5493bb64f2, 0x1591624987b3b3bb, 0x83cd54b6a1ac0682⟩, ⟨0x422cd0531747177d, 0xaca90170cb46a77c, 0x5cd2fa092cd7c8a7, 0x7f0290d3d3506b11, 0xe0998256b1a83796, 0x9154735d4dee0e42, 0xf300188dda5a2a4e, 0xd63b00bfcf9b5b79, 0xc6fd8363131940c6, 0x384aa9b9967d6616, 0xbefd17039890726b, 0xd7944d418ae50366, 0x565ee70ce3a3f797, 0x123ff76b45d6f0be, 0x2119fc17ce5cf03d, 0xe26e3b5f74e2df5f⟩),
  (⟨0x3c884fbc9ca90049, 0x0fe56dd291d29a49, 0x511db812713334d2, 0xf932dd0f49536f17, 0x63ef5d7d5aa6df55, 0xfdfd71892f1e8680, 0xc7ec2e8f50698272, 0xa11bba5142e8097f, 0xa83653ac7eeade9c, 0xaf1941c0ef12a7cb, 0x62bcb23cc23580e4, 0x737896530713ac32, 0xb5ec17c4f738e831, 0x19ec530728d2be10, 0xda529870bada1ff9, 0xc5db2f3bc4dafe00⟩, ⟨0xc56fa3d1f32216b7, 0x108741b173e06ef4, 0x1a42f2499884fd79, 0x82b7cd387ac87998, 0x0c17788b8bfec6a7, 0xc0942feb77ede861, 0xaaf66a5d1e50371a, 0x12284b38714398f2, 0x211d5a79dcc87351, 0xa39e2eee1331487f, 0x6aa3f5799cac7bde, 0x6dce90611e8c49b4, 0xe5510583b53b11dd, 0xdc1d868b72087351, 0xdb649b979cadfdb8, 0xf8c9ca72db180c7c⟩),
  (⟨0x31d2a544ad7f53f8, 0xa6f3699adc4b70ac, 0x1fad71e6a1aa2e38, 0x8a635d27b6f08285, 0xaa575442aa70a084, 0x2190cbb53b541368, 0x48a3c28b3219f546, 0x01d250f008c732e8, 0x356022c67b6626d8, 0xc51f92276dd710e3, 0x7e25f47a73d80306, 0xf56a6ccece87f68f, 0x4a26fbc969c799a9, 0x87bb3f354d9ed14d, 0xe90935d5b8cdbff7, 0x5087bd7743d1dad9⟩, ⟨0x3c276d02a14cedac, 0x0fd2643bbd110738, 0x0d9615f347f5254a, 0x2eefd79efcdc87ea, 0xb02e00ba1b23a7e0, 0x43116aa3e003eae1, 0x1bbfd31d44648cb0, 0x33dfdd62b493838c, 0xf5f9bdadc7ca05ec, 0xa222266996eab711, 0x494b49594878733c, 0x2de4d19b0c99e71e, 0xd0d76870986018a0, 0xd8a9ea79a59ee131, 0x0355f7434b60216f, 0x20229725d0bba2a8⟩),
  (⟨0x5c01c666e0baf5ab, 0x8a1525795a6823da, 0x4573281bc764a530, 0x775a83be21162771, 0xcbbb3482d7b90fde, 0xaa337551d5ab3431, 0xafeac664201b1b8b, 0x031eb96c2c82ed8d, 0x0a71c2eb4f96e7f0, 0xe228ec315786abd9, 0xcbe85c392b077ef3, 0x9505920a79e76d3d, 0xf06778114b4adc38, 0x077cb29f3651d022, 0xbb63824ab88eed64, 0x055516912a6063fb⟩, ⟨0xd2cd698694395bd7, 0xd51a6e46a0364bc8, 0x4f68675b2aa47970, 0x88fff62acac216e7, 0x156565e554198e1e, 0x24e9b1cd1fb4e51c, 0x0b9db0a5ea50cda8, 0xf88c2b77e7e88dc5, 0xfa909068c548a051, 0x4f588f1b7bfe1897, 0xdeecf52b52094375, 0x9ed45a3bd09b6ab7, 0xd804e4d38d1b69ae, 0x2a688ade25c46549, 0x2cedc8be2c0132b4, 0x76fe4ecb23a19759⟩),
  (⟨0x4f74e6b6a7c81096, 0xd82a98e12e403537, 0x00dfb41d91cfb93b, 0x66e4077a064feadb, 0xf8945897c632854d, 0xaf48bc04efc58b86, 0x49787e3feef910f6, 0xa18ac7ef5e711ae4, 0x9b083b015c6c6407, 0x898226cf19b7c190, 0x8165a3038ba6fa58, 0xb5928620fc9dcb5d, 0x3b2e2a3d66ed97fe, 0x9ffa4205cd4cfe2c, 0x6984382bc1b1e624, 0x85b2f7ef348ff13d⟩, ⟨0x7281cd46b839be05, 0xf3bba6993c631226, 0x302370868ee3afe6, 0xe614e77fee66bcbe, 0xfb4c5ed9c7877de5, 0xf8fb96470f646616, 0x6572de3722b9c93d, 0xcf770c34d4211c89, 0x6a037263f4b25583, 0x7b3aa802c227f264, 0x0fb9e1a8a71e12e2, 0x60a1e0638e752f67, 0x2f3a886f774a26ee, 0x91ef0d2f5ab5b373, 0xe484eb277173d89a, 0xeb51d183a067c336⟩),
  (⟨0x8f5263aa4292edda, 0xd0f96254a2ac8d6c, 0x1f0790738bface5d, 0x23d90ac1b97eb980, 0x3b404190e90a9791, 0x5a2623537cf2222f, 0x6a0245fd274dccbd, 0x62e8560211edb2f6, 0xbc241741b654fa38, 0x495134dde89c0427, 0x3c70634b49fbb364, 0x5f393c0dfe003942, 0x499587d97eae0066, 0xbca3c18ba91bdff4, 0x6bc7dfe931cafae8, 0x9bb7413910b0e7a4⟩, ⟨0x22d18eaf3ffebbc9, 0x5ea01fce59cdfa7f, 0xce80a7099d0c6c35, 0xcf19c03a772a9905, 0x2ea69dacbb393845, 0xbdd5ded96b68c732, 0x9e43ee5a72786677, 0xe0e7619e24d85128, 0x3ce3705ced4fc276, 0xe7533d31893ddbd6, 0x67b3e8dd35cdc859, 0xec858051b6ef936d, 0xd5f7e9f445812aa3, 0x4bcbfa73f9aea040, 0x0abe5c5a6bc343f4, 0x7c0d8de479024d31⟩),
  (⟨0x38288d31380a9ad8, 0xaf9d97460378bd3c, 0x9dbc75b9c819429a, 0xd46fa309fd49dad3, 0x7b436afbf35dc4c1, 0x9de7556dd3e59df6, 0xceaf28c8737ca028, 0xd837b3d9ccaf0090, 0x5b11d5a8c57c44aa, 0xddd43228d7b33570, 0x57a07431812a3ffa, 0x487558dd871170ee, 0x5f77869e539cbc85, 0xb9e89305f6b754c6, 0x8ba4f9fbe4e1ae63, 0x76ef316f04153145⟩, ⟨0xc49dff996e1909bf, 0xae6416b1e707d43f, 0xadf3f9f93c268f87, 0xe69cbd8f49b67afc, 0xd3e9f2e4e29ac0cf, 0x5eb6ab98f46a6425, 0x613326dfdf1e16c2, 0x8abada8fb1e1464f, 0xf2a2bd227faeef7a, 0x7f1d56fb2843bb0f, 0x41d54936181de2e3, 0x008ec5cc9f9d7dba, 0x92af8b0df750c63c, 0x3511cf8cee15f03a, 0x8d02f2da8c788da1, 0xda4fcb78f612cef9⟩),
  (⟨0xe63014c7bceefaf9, 0x31c7b3350f26f9f8, 0x6cc945913d98678e, 0xc5ef07a3a4a7b246, 0xa77053dd9cec5fb0, 0x18dfa627d01d832d, 0xa67aab5855dd6bcd, 0x7747e4dbf7922049, 0x1e100ba7a24d1fb3, 0xa8c323f9dbba0002, 0x8e9f711408bd74a3, 0xef349de952c6e0df, 0x838a41d31875b6c6, 0xf43e04a07b6b372d, 0xb58dfbf56e79bfbd, 0xe120c86a08110fbf⟩, ⟨0xf073bffaf051091c, 0x2aae4f5841e01ac0, 0xd27ff3884b83021c, 0xce5f22010215aa1e, 0x07c8eb0f00adc62b, 0xfc64ba212c28bea0, 0x405e700d2c635d3c, 0xee9b2389c76da0d2, 0x992358dff5eeaa2c, 0xe31bb3f840d77b3d, 0x8f56581bf550d5a6, 0x7244c8cc4aea1a65, 0x059e57df9c5b1a28, 0x2cd19c3e43725bac, 0x0a6ae1b28c4adac7, 0x7b99756ece63ee7e⟩)
]

private def katFinalEmpty : State :=
  ⟨0xf073bffaf051091c, 0x2aae4f5841e01ac0, 0xd27ff3884b83021c, 0xce5f22010215aa1e,
   0x07c8eb0f00adc62b, 0xfc64ba212c28bea0, 0x405e700d2c635d3c, 0xee9b2389c76da0d2,
   0x992358dff5eeaa2c, 0xe31bb3f840d77b3d, 0x8f56581bf550d5a6, 0x7244c8cc4aea1a65,
   0x059e57df9c5b1a28, 0x2cd19c3e43725bac, 0x0a6ae1b28c4adac7, 0x7b99756ece63ee7e⟩

/-- RFC 7693 `BLAKE2b-512("")` digest. -/
def katDigestEmpty : Digest64 :=
  ⟨0x03590142f7026a78, 0x72d2522585fdc6c6, 0x614758e140472f91, 0x19541ff717e2868a,
   0x5358eeaf31105ed2, 0x4bb04e9344648913, 0x55b748145b683a90, 0xcee29bfe1a706fd5⟩

private def katBlockAbc : Block :=
  ⟨0x0000000000636261, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def katTraceAbc : List (State × State) := [
  (⟨0xf0c9aa0f86491dea, 0x63b7dedf4a4e5ad3, 0xbe50eb454e0a93d7, 0x949804b0483ead14, 0xb7defc3d0277e11f, 0xed49c30cd311d50e, 0xa056671704b00d71, 0x75e6432fc4661b06, 0xee5e0f39647a9fff, 0x7bee264bf3cdadfe, 0xb2752dadd66bd8f9, 0xa99463cb37905929, 0x7772fc2886a76c5f, 0x254ef880a19a8726, 0x789d43381c47f584, 0xa25ef57d7da312ee⟩, ⟨0x86b7c1568029bb79, 0xc12cbcc809ff59f3, 0xc6a5214cc0eaca8e, 0x0c87cd524c14cc5d, 0x44ee6039bd86a9f7, 0xa447c850aa694a7e, 0xde080f1bb1c0f84b, 0x595cb8a9a1aca66c, 0xbec3ae837eac4887, 0x6267fc79df9d6ad1, 0xfa87b01273fa6dbe, 0x521a715c63e08d8a, 0xe02d0975b8d37a83, 0x1c7b754f08b7d193, 0x8f885a76b6e578fe, 0x2318a24e2140fc64⟩),
  (⟨0x7d7ebc91065eb487, 0x2985dbd3b522b163, 0x83dcc7c95110e507, 0xd5f7d943ae7a12d4, 0xa2a2bb290a6fa0ac, 0x48daa2180cca574f, 0x25804d5986d6e07f, 0x47dc958f84e67b9c, 0xe089c6944d999f41, 0x607c07b706df2755, 0x4defb1cc1d0e5211, 0x53fd198002cb9dc5, 0x9c62f81da3622dd5, 0x4134955aae31cc2d, 0x8f1947927dee7a35, 0x3561197657eee886⟩, ⟨0x53281e83806010f2, 0x3594b403f81b4393, 0x8cd63c7462de0dff, 0x85f693f3da53f974, 0xbaabdbb2f386d9ae, 0xca5425aec65a10a8, 0xc6a22e2ff0f7aa48, 0xc6a56a51cb89c595, 0x224e6a3369224f96, 0x500e125e58a92923, 0xe9e4ad0d0e1a0d48, 0x85df9dc143c59a74, 0x92a3aaaa6d952b7f, 0xc5fdf71090fae853, 0x2a8a40f15a462dd0, 0x572d17effdd37358⟩),
  (⟨0x224d9730ddde8c9b, 0xe430476788c41ef0, 0x4f163fda2e4243bf, 0x41dd8960f0de029d, 0x1161e9566cec8636, 0x956fe864884ac584, 0x4dfeb83fd06a086b, 0x78c811fddf5c5824, 0x1cc968515f81e2e0, 0xaef099868dce0a96, 0x5d62892a32598f4d, 0xc92583e5a4ae6f86, 0xdc073c3e56ef42ae, 0x3052cabffb0fb2d1, 0x69ea4685aa4d57b0, 0xeb3719d34531eb68⟩, ⟨0x60ed96aa7ad41725, 0xe46a743c71800b9d, 0x1a04b543a01f156b, 0xa2f8716e775c4877, 0xda0a61bcde4267ea, 0xb1dd230754d7bdee, 0x25a1422779e06d14, 0xe6823ae4c3ff58a5, 0xa1677e19f37fd5da, 0x22bdce6976b08c51, 0xf1de8696bec11bf1, 0xa0ebd586a4a1d2c8, 0xc804ebab11c99fa9, 0x8e0cec959c715793, 0x7c45557fae0d4d89, 0x716343f52fdd265e⟩),
  (⟨0x6b864497a655fb47, 0xc1fd6110ffa75065, 0x817908f78a142cfa, 0xce1577a72bc1ce7b, 0xc4b99c558f3684e9, 0x065b83216e96ed93, 0xf2d93929736e5b04, 0x2795f81cfb8f7633, 0xd2d2821a8aa43e4c, 0xa898085d8e04f013, 0x38bf8d18c9a387f9, 0xd750375d8da19646, 0xe88b2359a43154a6, 0x2bb39bdbff08e7ec, 0x8eee368bc701c9f4, 0x21ddda93f0e5d3d8⟩, ⟨0xbb2a77d3a8382351, 0x45eb47971f23b103, 0x98be297f6e45c684, 0xa36077dee3370b89, 0x8a03c4cb7e97590a, 0x24192e49ebf54ea0, 0x4f82c9401cb32d7a, 0x8ccd013726420dc4, 0xa9c9a8f17b1fc614, 0x55908187977514a0, 0x5b44273e66b19d27, 0xb6d5c9fca2579327, 0x086092cfb858437e, 0x5c4be2156dbeecf9, 0x2efede99ed4eff16, 0x3e7b5f234cd1f804⟩),
  (⟨0x3e5bab618a5fbc72, 0x9be6aa793ad3a7c9, 0xc5252a4d03f65b2f, 0x1fe21186bd238be3, 0x475dcc427f3fcd87, 0xbb2d4d7552ba222d, 0xcdcfc26e59d1d349, 0x8bc33bc025ae3c8e, 0x5a8388e35cb33b75, 0xec74922286e7b930, 0x3a03d6ba54158e95, 0xaa550590a17d6cd1, 0x1222a0cc9444c711, 0x303dfd40b9230c9c, 0x7709a29326a5c548, 0xadd65a4af0cfb375⟩, ⟨0xc79c15b3d423b099, 0x2da2224e8da97556, 0x77d2b26df1c45c55, 0x8934eb09a3456052, 0x0f6d9eeed157da2a, 0x6fe66467af88c0a9, 0x4eb0b76284c7aafb, 0x299c8e725d954697, 0xb2240b59e6d567d3, 0x2643c2370e49ebfd, 0x79e02eef20cdb1ae, 0x64b3eed7bb602f39, 0xb97d2d439e4df63d, 0xc718e755294c9111, 0x1f0893f2772bb373, 0x1205ea4a7859807d⟩),
  (⟨0xf4e55384dc924147, 0xf015d00b613578c6, 0x648495058cae3d2f, 0x54567270ac75c4ea, 0xb7b58d9367a4043d, 0x02ca058bf3799684, 0xb9668b8ebf3fa717, 0x292f756a3507a223, 0xc601582b84c4b49a, 0x53e84b90ddbf8985, 0x42b26ef24a2100f5, 0x35134241b118cf10, 0xd8a6cfd32f7ab2e6, 0x1925e46b74e53ba5, 0xc70d65404fc75525, 0x57dc2cd554e40ca1⟩, ⟨0xe58f97d6385baee4, 0x7640aa9764da137a, 0xdeb4c7c23efe287e, 0x70f6f41c8783c9f6, 0x7127cd48c76a7708, 0x9e472af0be3db3f6, 0x0f244c62ddf71788, 0x219828aa83880842, 0x41cca9073c8c4d0d, 0x5c7912bc10df3b4b, 0xa2c3abbd37510ee2, 0xcb5668cc2a9f7859, 0x8733794f07ac1500, 0xc67a6be42335aa6f, 0xacb22b28681e4c82, 0xdb2161604cbc9828⟩),
  (⟨0xd0d5bb6a10dae2b5, 0xf5d2174aff6cf2cd, 0x39337b3da7e963ab, 0x588d5ef9a0a6492f, 0x860aa9f111072cea, 0x90ee681d04ce182a, 0x7e1ec202f5042fa8, 0x04d72048395b53ff, 0x391b02b399972abc, 0xa93d75cc5e322748, 0x74550619f0763471, 0x4795d2168937df08, 0xfee428bf8b86c15e, 0x4ca1f5f07a552d91, 0x5ca64dd877b9e682, 0x34881f3a14e9e908⟩, ⟨0x6e2d286eeadedc81, 0xbcf02c0787e86358, 0x57d56a56dd015edf, 0x55d899d40a5d0d0a, 0x819415b56220c459, 0xb63c479a6a769f02, 0x258e55e0ec1f362a, 0x3a3b4ec60e19dfdc, 0x04d769b3fcb048db, 0xb78a9a33e9bff4dd, 0x5777272ae1e930c0, 0x5a387849e578dbf6, 0x92aac307cf2c0afc, 0x30aaccc4f06dafaa, 0x483893cc094f8863, 0xe03c6cc89c26bf92⟩),
  (⟨0x2c42e52d8c060ff2, 0xa357b3b1736ec0a1, 0xd916516a31320b04, 0x41d37d7ecbfc6541, 0x8ffac8c5ec5cb0e6, 0x1355530d9510b6da, 0x56af9e7816abf9be, 0x1c460b4a606cc880, 0x7b7cc36bc928376b, 0x3981e9894b87e52a, 0x70e55e0e63448924, 0xbf9c914183b31c1b, 0xf2d1af914f0bf16d, 0x7fc4a1651e4130e8, 0x58ff19794c000469, 0xe113c5832e0abbd3⟩, ⟨0xffc83ece76024d01, 0x1be7bffb8c5cc5f9, 0xa35a18cbac4c65b7, 0xb7c2c7e6d88c285f, 0x81937da314a50838, 0xe1179523a2541963, 0x3a1fad7106232b8f, 0x1c7ede92ab8b9c46, 0xa3c2d35e4f685c10, 0xa53d3f73aa619624, 0x30bbcc0285a22f65, 0xbcefbb6a81539e5d, 0x3841def6f4c9848a, 0x98662c85fba726d4, 0x7762439bd5a851bd, 0xb0b9f0d443d1a889⟩),
  (⟨0xa9126c152d800655, 0xac1632ba715ebf08, 0x7c1849df4e91206f, 0x94aaf312690f9253, 0x4165a65ac9e3c45b, 0xdfe2d8cd3101f453, 0x41aa56fe49862d7f, 0x13e3a2c50cfad099, 0x87047c8ec6295331, 0x40e7b1fdda2d2585, 0x3e4ba8ddb8e29996, 0x49989dfa62e90301, 0x64d2d77cbda6949a, 0xc6927901cb3215c7, 0xa5c81bdf8924e48a, 0xc4fe53007c9d0df7⟩, ⟨0x753a70a1e8faeadd, 0x6b0d43ca2c25d629, 0xf8343ba8b94f8c0b, 0xbc7d062b0db5cf35, 0x58540ee1b1aebc47, 0x63c5b9b80d294cb9, 0x490870ecad27debd, 0xb2a90ddf667287fe, 0x316cc9ebeefad8fc, 0x4a466bcd021526a4, 0x5da7f7638cec5669, 0xd9c8826727d306fc, 0x88ed6c4f3bd7a537, 0x19ae688ddf67f026, 0x4d8707aab40f7e6d, 0xfd3f572687fea4f1⟩),
  (⟨0xc0df0f0e596ec5a9, 0x87ca07d5e3d64cb6, 0xd11bc20e8ef44efc, 0x0df3ea89aaa44e12, 0xb4014455ff7c2ca0, 0x65bf544e084bb313, 0x3478342ab05ecf87, 0x88274463ca98e874, 0xa9502da0417b08d5, 0x0a28a074aea2f05d, 0x15e30f6c705383f7, 0xdade744ed33782e5, 0xd66561a10d1d1c0d, 0xd9b961e2d51134aa, 0xe5c30363d6ab824f, 0x0d3efe25194b38bd⟩, ⟨0xe630c747ccd59c4f, 0xbc713d41127571ca, 0x46db183025025078, 0x6727e81260610140, 0x2d04185eac2a8cba, 0x5f311b88904056ec, 0x40bd313009201aab, 0x0099d4f82a2a1eab, 0x6dd4fbc1de60165d, 0xb3b0b51de3c86270, 0x900aee2f233b08e5, 0xa07199d87ad058d8, 0x2c6b25593d717852, 0x37e8ca471beaa5f8, 0x2cfc1bac10ef4457, 0x01369ec18746e775⟩),
  (⟨0xfdd2c6435d5a301b, 0x6e446afbc3efad36, 0x46d963ee934efeea, 0x5523c5b930d1aeb6, 0x2ca29c4d619bafa1, 0xfcd5d76a6de20047, 0x8b7f1e6cfc2a0039, 0xadbdc7977150b805, 0x7ccca8ba533b7361, 0xacc8f98717c8e4a3, 0x7afe95b81b3993db, 0x3bbceb651eeed2c9, 0xcae4b9c0357b6205, 0x3fb8d71b07b5efa5, 0xac2678144c9a382a, 0x8d7d58ee3d275626⟩, ⟨0xe801f73b9768c760, 0x35c6d22320be511d, 0x306f27584f65495e, 0xb51776adf569a77b, 0xf4f1be86690b3c34, 0x3cc88735d1475e4b, 0x5dac67921ff76949, 0x1cdb9d31ad70cc4e, 0x35ba354a9c7df448, 0x4929cbe45679d73e, 0x733d1a17248f39db, 0x92d57b736f5f170a, 0x61b5c0a41d491399, 0xb5c333457e12844a, 0xbd696be010d0d889, 0x02231e1a917fe0bd⟩),
  (⟨0xac495068076fe1c4, 0xf3ae6a427a75e234, 0x83933b99d54089ee, 0x31db95ba436e4db7, 0x5198d8d539a3fbce, 0xb8eacc53aead98b1, 0x55b2599798b3a4a1, 0xb20b2179d2dcd8c6, 0xe799f6cc9a2a23d7, 0x5d6a76c05f26fe94, 0x5fae8064a9ba0517, 0x06ed116649fdb58d, 0x94a2b1744065ba29, 0x88297fb94160bd39, 0x6ce4fc1f51b7e632, 0x4072027e06ce90be⟩, ⟨0x12ef8a641ec4f6d6, 0xbced5de977c9faf5, 0x733ca476c5148639, 0x97df596b0610f6fc, 0xf42c16519ad5afa7, 0xaa5ac1888e10467e, 0x217d930aa51787f3, 0x906a6ff19e573942, 0x75ab709bd3dcbf24, 0xee7ce1f345947aa4, 0xf8960d6c2faf5f5e, 0xe332538a36b6d246, 0x885bef040ef6aa0b, 0xa4939a417bfb78a3, 0x646cbb7af6dce980, 0xe813a23c60af3b82⟩)
]

private def katFinalAbc : State :=
  ⟨0x12ef8a641ec4f6d6, 0xbced5de977c9faf5, 0x733ca476c5148639, 0x97df596b0610f6fc,
   0xf42c16519ad5afa7, 0xaa5ac1888e10467e, 0x217d930aa51787f3, 0x906a6ff19e573942,
   0x75ab709bd3dcbf24, 0xee7ce1f345947aa4, 0xf8960d6c2faf5f5e, 0xe332538a36b6d246,
   0x885bef040ef6aa0b, 0xa4939a417bfb78a3, 0x646cbb7af6dce980, 0xe813a23c60af3b82⟩

/-- RFC 7693 Appendix A `BLAKE2b-512("abc")` digest. -/
def katDigestAbc : Digest64 :=
  ⟨0x0d4d1c983fa580ba, 0xe9f6129fb697276a, 0xb7c45a68142f214c, 0xd1a2ffdb6fbb124b,
   0x2d79ab2a39c5877d, 0x95cc3345ded552c2, 0x5a92f1dba88ad318, 0x239900d4ed8623b9⟩

private def katBlockExact128 : Block :=
  pair64Block katPairLeft katPairRight

private def katTraceExact128 : List (State × State) := [
  (⟨0xfce69820f398254c, 0xfb29447a67d3b4d2, 0x6ab848ba7e813e78, 0x54f62acbc45ac7a3, 0xd133caff35a4ac1f, 0xf51fe27e1dfc14d3, 0x0eaba7be119fa97b, 0x0822ecc94f3e3b75, 0xc323a856de359924, 0x94080a0787607d39, 0x3f24fa943e91ea27, 0x5941806344cc196b, 0x4ad8f2a657686088, 0xf07b130c0c0f9155, 0xea6f72fedc981de5, 0xfd3de2458228a7dc⟩, ⟨0x87ee2c12dc562ac5, 0xe0ef8de36d08cf56, 0x97c8855d0faaeafc, 0xa859ce50aab48074, 0xa93bf237e8feab7e, 0xe5a86d979f4273d4, 0xa21c4881eebdabe2, 0x5ae5c0bb4957ddbe, 0x636a9d55d7b54898, 0xdfa71c8f35b77475, 0x8d872828f3945ff4, 0x716bcabab3b61390, 0x7c7c7b4242f646fb, 0x6318aae6cf452590, 0x99b519b03687dd7b, 0x77635110f0911827⟩),
  (⟨0x6c91d4882c864247, 0x5491a03dd9e3a3e5, 0xb07b0656655a6188, 0x7d0178284913c5ba, 0xc99ebc96447f0157, 0xedc252f382ed50d1, 0x9032b2f53e11bf03, 0xb276764baee1824a, 0x8855b53f825329ef, 0xe96c1323a6455633, 0x6fd034d43f25d86b, 0x8a267d5e611a0dd5, 0xaaba16a0d5c0f85a, 0x299cb4b9e1e75745, 0x6313cf4e3b0b75dc, 0x68d2d2e6a7954cdd⟩, ⟨0x0cb6b74c99372042, 0x9ec3dd149ab55a94, 0xc8a393df5c3a5b22, 0xf0f1ffab90fca84a, 0x502f19d714a82802, 0xd064149fa7beeb22, 0xed04099b0b35bb5b, 0x1472344dad7d57bf, 0x4d2c668267d74f1f, 0x74120c4f37718af8, 0x53dc172fa8885753, 0x6d616b04e9313831, 0x140351f446a6dbc5, 0x366546d2f9b0b7e9, 0x06ee73467a4e8621, 0xc623115e67b19887⟩),
  (⟨0xba7105913174ede0, 0xc00c3c1cc4e278d5, 0xed96488c5a858036, 0x83e10241fad7296f, 0x330c8e0cd63cd985, 0xb7c0b372b26c20e9, 0x0e597a4d9e2bcce1, 0xb6c895dfb485ade8, 0x2f60d6ca8fe767c6, 0x3997b9b9453fc0cb, 0x7686d5f77bccc9f1, 0xd4eba9b00f3a9072, 0x9294f5ee7fc89933, 0x691f9c6a2ce32409, 0x39d60542f108b8be, 0x89445da4e347b816⟩, ⟨0x363b88c9e5c34597, 0x9f3444934666700e, 0xdeed88d524df660c, 0x3ea223d521a0a4af, 0x644b464b7d490145, 0x28b529566c856de5, 0xae9256b5096820b6, 0x372f64aa54f6d097, 0x77d5d275e5f49de5, 0xa36582305c84b7f1, 0x616790560d5fc2fc, 0x2d33108211bff04b, 0x56669ed4836e3971, 0xe1ceb84bcb8aae5d, 0x7c76d3f4d7571e4d, 0x166be24f50c6a50f⟩),
  (⟨0xfa44898e9f5e5964, 0xbe9c72921b02d022, 0xf495fa79d93c5a0e, 0x41cda3e98a7cf98f, 0x63a2b96e269da2df, 0x89ce98339dc1b20a, 0xca34e25cfc7d664d, 0xb342eb2fb0c9f12c, 0x60e07347a6834167, 0x8c6196998f12090a, 0x755b3930a216bba2, 0xac863d0e9d7c4117, 0xcbe1e76c30eb10fd, 0xe36cbb132bc41dcb, 0xc50cba73141e59a4, 0xfe1bc0fac8784938⟩, ⟨0x5a63308eee7a9248, 0xf7169b44896ad6cc, 0xb50779263e3a64be, 0xd6008ebfbe33097c, 0x8e077f9efb54f7a8, 0xf41328480c08f319, 0x6a87a4083d4f73ce, 0xc45ee32ea583e314, 0xbd2d18c3dcce06ee, 0x2ec8d16833f1c982, 0x720a50a06d123d16, 0xd28311d0edc99c02, 0xb3bb8557d42ef574, 0xd56033eb08b713a9, 0x69dbee8bc2fd5fd1, 0x6464c22965c88b48⟩),
  (⟨0xc447b58e9b5c62d3, 0x7b15f9f7dc727154, 0x3c35693ba860f0ad, 0x8a76be204caf0e7e, 0x79d5af212fa621c2, 0x1309529df9cdca2b, 0x697ecd2ab555ea18, 0x5230b0a32c105b9b, 0xb9626480f4939e7a, 0xa8fb654c1c7ca01a, 0xead57741ac0810fd, 0xb05a21308c237aeb, 0x1afe257093c21f5f, 0xb207b33f19531345, 0x2c647053df76f71e, 0x0b1558b70888d97e⟩, ⟨0x75d1c3a6f493737e, 0x10eb6b299486f774, 0x4ca3d1e1ad47dbf8, 0xc094e252c36665c4, 0x7ac88d2e8e59ab29, 0xad5c19dd2cf856b8, 0x8049b723c3c551a8, 0x7fcc31309cdcd184, 0x002725122c0c7582, 0x90dfac1f87a06690, 0x415234177690e754, 0x25b53ad7a5e34984, 0xf67a6e0bc0b2cd8b, 0x27d45253bfdcdadc, 0x9fca888d5c14cc68, 0x566875c584b6b141⟩),
  (⟨0xfe41187db6ebf2aa, 0xfeec5100594c4e22, 0x400e5c4ef70b83f9, 0x156c7816e3d5238b, 0x832ffee74b3b522d, 0x61028ca6bf054f50, 0xc4ae1c394de2aa17, 0x6baa6a6419487296, 0x4ebdb25c1817c885, 0x829907224ecadade, 0xeeeb7ef58150a90a, 0x5b7237012991a8a0, 0xf948ab0cfa414721, 0xa64bb581f4808be5, 0x857d6815be86bb32, 0x0e89325fb1df321a⟩, ⟨0x2ac6a92bb9c11d37, 0xf506e6594244c601, 0x7f765f49a6053c33, 0x908da1da9f98bb42, 0x8e0c63439ff0eeed, 0x907346ef6e3f05ef, 0xf027286f0334110b, 0x8ec217a5d9f77e20, 0x9ba9ae774a3fe5ac, 0x5e92e125d5cb844c, 0xfcd7d201025cd242, 0x3b139a80b52b63ed, 0xc778ed2e9009b9d4, 0xcd9d0038a4ab2b79, 0x575d14116428bd4f, 0xe520020af82b3121⟩),
  (⟨0xc0d3e346b420225a, 0xf3c20fbf01ae96b0, 0xf62ce01f0613b5c7, 0x140aef0a5f162d53, 0xec0669a146ecbb49, 0xea5b34c3ab72be67, 0x9bf8222fd6aff8d4, 0xcf299b4d64757abf, 0x876f70966897d60a, 0x2a96cd8c1f1f1773, 0xd256649296aa71db, 0x91aa76b7dd2b3cde, 0xbea7edce37165361, 0xacdcece4f03e58bb, 0x5cfb8eafe3feb65d, 0xf1fd709384a9fc43⟩, ⟨0xf1d4799d6685f26a, 0x134da394efd37c4f, 0xa63bb6cf3deecc23, 0xce47f62598a42fb0, 0xaba591a1e0d6038e, 0xb1d70d59ec49a768, 0xd3d84a1a99d9fb99, 0x9eb959c19b867d73, 0xb5dc75e2b8ca7ffc, 0x72433209a46fadbb, 0x588a99fe3e9204c5, 0xc4d33a5885c45f4f, 0xf6a22fcb30419784, 0xe87fe3d697ba8596, 0x3cf0c4fc69a48308, 0x9ff717e9641f254d⟩),
  (⟨0x2f1ba89bcfd01f0b, 0x40f633e270d0a8db, 0xb5e561d308433ba9, 0x061504be30d31e85, 0x84367defa476d54a, 0xba9637bb3a5d05f2, 0x02d58a0a4bd4e98b, 0xfc7202e62e61e4ec, 0x80cfec6413940cf6, 0x9857cb9f7b285885, 0x44362b7de7e47d40, 0x549e4b1d8174fd74, 0x486bad9c607f359a, 0xa526c01bea9b9ccd, 0x991be76acbc7d5c9, 0x646f2d4ee7c8233b⟩, ⟨0x4e8212337c087683, 0x2cee433b83459545, 0x5f661019ec052d63, 0xccd46756018fb046, 0x51fbec755804b265, 0x877f962b401f7394, 0xe5a0397b442de915, 0xec810afec7757b88, 0x58d2b5975d51279a, 0x7ce18c0569e30325, 0x6d2434b9e3a09e94, 0xb0adfe138a159ccd, 0x03b074b17d7f0864, 0x4485cc1aed01b0be, 0xc0edef4fb64039f5, 0x564e9c1d7f2d0087⟩),
  (⟨0xa91014dc6b9e34f9, 0xd7290f0749e29b2a, 0xc7840b5cf85b2cf4, 0x6695572c686a11f5, 0x2eeb71cd3e249f92, 0x52aa2246b1e8f7e0, 0x287b84cfe8204250, 0x00f5352785624aec, 0x46a8db6477f62ea0, 0x72a363fc9f34ac69, 0x103c8528a5a38524, 0x5e89001c9b918691, 0x7395d35046a0bf9a, 0x19eb0cffc5f02683, 0x654afa495d799cd2, 0xfab0d5bf7b65fe7f⟩, ⟨0x55706df4f6d2c8d7, 0xe66c32920624db6a, 0xfee85647c19e99cb, 0x12154ab3fc7efb15, 0x80848f6c55f5928d, 0xad0230647c622820, 0xf795864952fe502c, 0xd97fac464674ef84, 0x6c8535b0368e8001, 0x364db88ffd890650, 0x8db8a46b5ce63d9e, 0x43d0373684027346, 0x09793da1cbea1aa2, 0xd8a4b3dff02c0ff2, 0x1f11b68dd4b675e3, 0x81efaefc1db26f42⟩),
  (⟨0x79df0022a49167d3, 0xfce4e3201a1f096d, 0xdaaf41e00f86d334, 0x65c2f57fd9a07c82, 0xa882cb5dc3238b6f, 0x0b63b2112d05338f, 0x90659fb6257ad9b9, 0xa2d39bd411273d2a, 0xe13cfdf610f56fb8, 0x7ebbccc9a7b13a44, 0xa58e3d059ec01209, 0x6a9809a768ebc12c, 0x08c7122fb63480a3, 0x1288c901a818180f, 0x7c7441ce172c252b, 0xd678358d699ca2ec⟩, ⟨0xe03f56ce20ac9b8e, 0x8569c5ce0b8060f6, 0x3ea6040c7ddf4664, 0xd6dcda83481ad8c3, 0x0e4e985e09112b90, 0x6fa0fc5c5466660e, 0xf67de03356cd4000, 0xa0b8fe64144e581d, 0xeac2dce5d4939780, 0x5505eb1a3862f3a2, 0x4bcfb7ef52721e5b, 0x4a64702ea64f6318, 0xa2fbb9b96903dfdf, 0x75b5ad763575f3f7, 0xb747c9de8ef149da, 0x81b3c4b2e0f8f215⟩),
  (⟨0xef709a7a6836ca48, 0xc94ad94dc1fd9311, 0x3e174ec3953f4e17, 0x6f8027713bd3f309, 0xa51c0c9b13b7ba8a, 0x37ce826d2e9b0f6e, 0xc24dea8b58b64043, 0xe43bba1dfb7a2b58, 0xb8409f73b9b72467, 0x85eca5c5a4a72652, 0x53b9ed76de1d5d4a, 0xf36801178d43426d, 0x87c1aacc8dbb3f5e, 0xe9598ec7f2aeb868, 0x8eaa4728a09d7e32, 0x39a000e3b77414ac⟩, ⟨0x97a32c6efcd82059, 0x0a03839f325818a6, 0xdb578d0d2d3e4b18, 0xe33f974a8a83062f, 0x0ef3f03da3a3e102, 0xb4c914c5001da029, 0x8bb6178bc441aedc, 0x117edd498ff4a84d, 0x6a90dffe0a4252c7, 0xd0d788539ddb9d35, 0x03abf69457776c0f, 0x826d06d08ad74dc4, 0xab47e9be98655776, 0xab9adde2efaa4dde, 0xe887815cf67b883b, 0x4291fac32234abfd⟩),
  (⟨0xa4934c6e57364a37, 0x8b96b90c74e25d1b, 0x484c83a7a41acd26, 0xfc31e16ff633e952, 0x11d6a0598d2a6dfc, 0x2db7f01f8b12f38b, 0x331ea1ba2a458ff9, 0xf637a9d464292e56, 0x27c434d42960b0e2, 0xc8864e3019813829, 0x8bfd4498fef4d78e, 0x1bd51ed10f0b3715, 0x31a82f1869d3e27c, 0x3d7131ab2d3d3a8a, 0xbd9f82fd48a0fac6, 0xf1915be75d76d08e⟩, ⟨0xf6d9360fe5e06aae, 0x37f993b386c67f4d, 0xba62cb94eee374b9, 0x5c5e99d1420b52a5, 0x5aaa9dd00bc93f88, 0x35d54d904a443b60, 0x588e73d2e6e1352b, 0x36e128e87f68b8d1, 0x463297f46fbebac5, 0x2d5c83577d8c26d3, 0xb4f321d9b008df34, 0xf76f273da2fa1abc, 0x0f9ffc039fdb72d5, 0xcfcaf4c1a5ca4e70, 0x7eadba76e361c2a2, 0x78d046fca04bf528⟩)
]

private def katFinalExact128 : State :=
  ⟨0xf6d9360fe5e06aae, 0x37f993b386c67f4d, 0xba62cb94eee374b9, 0x5c5e99d1420b52a5,
   0x5aaa9dd00bc93f88, 0x35d54d904a443b60, 0x588e73d2e6e1352b, 0x36e128e87f68b8d1,
   0x463297f46fbebac5, 0x2d5c83577d8c26d3, 0xb4f321d9b008df34, 0xf76f273da2fa1abc,
   0x0f9ffc039fdb72d5, 0xcfcaf4c1a5ca4e70, 0x7eadba76e361c2a2, 0x78d046fca04bf528⟩

/-- RFC 7693 `BLAKE2b-512` digest of exact 128-byte input `0..127` (`kat128Input`). -/
def katDigestExact128 : Digest64 :=
  ⟨0xdae2479c78e31923, 0xa1c2be617f80fea5, 0x32ff193fa07f53a6, 0x0e7e4bd6bfec7ee8,
   0x043b33ac39f4cf8c, 0x611ad1ddc4b0190f, 0x39a0100ffec14ae2, 0x15d1a30dcc5d6c80⟩

private def katTraceMulti1290 : List (State × State) := [
  (⟨0xfce69820f398254c, 0xfb29447a67d3b4d2, 0x23e097aaf3a9fb3e, 0x54f62acbc45ac7a3, 0xd133caff35a4ac1f, 0xf51fe27e1dfc14d3, 0x0accb7227842d04b, 0x0822ecc94f3e3b75, 0xc323a856de359924, 0x94080a0787607d39, 0xf4ff23aa97a79345, 0x5941806344cc196b, 0x4ad8f2a657686088, 0xf07b130c0c0f9155, 0xd0d6c459fc776f32, 0xfd3de2458228a7dc⟩, ⟨0x6d7f456e820314e8, 0xdf1638051d4399e9, 0x7980e4aa5c125589, 0x909f69b0264b578b, 0xdcf62aab0bb2de7a, 0xe35107222fc8ce39, 0xb6d6f7d2cb81597b, 0xd4dc100ccad30dec, 0x1cc685632f34d2f8, 0x1dfb95a1b88797dc, 0x154cbbaff606375d, 0xf900f25eeb40c699, 0x3bbebb168ee00ad7, 0xaf5dd3c5edec3f00, 0xf8ed0199e3b06b3d, 0x494ebb8199ed4672⟩),
  (⟨0x52322552cd547844, 0xc154fce8a2bd8c52, 0xcf2b7d565b11657a, 0x474ec9c84a260051, 0xd708762618715567, 0xce37f6454a9fe40e, 0x47c4f6f00f839f62, 0x40e2a0bae04df500, 0xd36bd16374e16891, 0xf79aa87a4a0333d7, 0xf3e4ad686b793c07, 0x1b5ffd37ca4dfac2, 0x26dcddfa4b573701, 0x3bdc5c964aaae46d, 0x4d2a5e46ee27dc5a, 0x5cf9822b4165d781⟩, ⟨0xfbe126a23df6cd4e, 0xb9b6984f79435ad2, 0x8b1045996f7d8533, 0x2fd5dec33218aa4a, 0x6f4b87d69c2d1770, 0xb486c04f89c46733, 0x17d1d5a26bcae4cc, 0x1c4419948c7ca8e1, 0x52478025dbb7cc59, 0xf4979767c72b99ea, 0xbf41f8be7374350d, 0x9968608f850b6f68, 0x7ff447a283fa4f80, 0xa2c8570312263bcd, 0x99164c337c7932b7, 0x67c1987a94794e77⟩),
  (⟨0x2be0f180f936e963, 0x308f9ce3cedc841c, 0x9a0401aab5d4910c, 0x54fcda9c407526c8, 0x6fde5e8d22761e29, 0x0c345a1f4f26c62d, 0xfcf1bce185f5a9de, 0x1560556a26a973fe, 0xade08f21114d6519, 0xd5fff4d3c2e33ca1, 0xcea57a5e5eb5383a, 0x1345ddee89ae4942, 0xa5149d6480164c49, 0x6d1c44c3844bb9b7, 0x9557e00fa03afed2, 0xcb66fa8a5848ec2c⟩, ⟨0xeb36ac07b95fa83d, 0x5372c61571742438, 0xa2f6f6b1d704c3fd, 0x530cde25a292e1bf, 0xf8d3e0924429eac2, 0xc16a34cc93674bce, 0x3ac178591dbacc60, 0xe00a3a916425edad, 0x5543481c06508a65, 0x6bd4c2c2f32fc707, 0x84e18ff8e38e900a, 0xd2fda5d34088cdc6, 0xcfbdbc88cd4e98ff, 0x136f3105714454ba, 0x87c55d03aece23ec, 0xf24328ce40cbfd52⟩),
  (⟨0xdeac18d4878a8c36, 0xe7aef12617943da6, 0x7d6a6044cb9ed6d8, 0xa4acf99db1c792f8, 0x505b9368783c3bea, 0xa283cb3b59a51d04, 0xc75607b2c19ad290, 0xb67a1f9021160ca0, 0x4438c8063f626b42, 0xf5e4298640462502, 0xab761db068df12fb, 0xc1fc01ddcccafe94, 0xf9682b214c1c6b7f, 0x1b5d891f2c823700, 0x57acb38dba6d017d, 0xcc2586742c0bd1f1⟩, ⟨0x6a0b84796ab63c5e, 0xf262a4266effd6e3, 0x11a632cf0abd13f6, 0x09b34b0b95a24eb5, 0x82a8e41392fea302, 0xb88adb19dc870398, 0xb5a04dd7faf232d2, 0x14174c80ede9d498, 0xa59e2e918110e412, 0x0cb1894d659e949a, 0xc6ca3badad01d128, 0xe6090e26ea2d555c, 0xdbc7ba27f60749a4, 0x3e1032f301574aea, 0xf7ba16a0022cb689, 0x4309b241efc23ed6⟩),
  (⟨0x6e5fcdc38a6cb7a2, 0x468a8ae4cef4cb70, 0x1fe94c335434a224, 0xb406cf68846de0e2, 0x6f48e540579dd886, 0xef6f4a7020bda15b, 0x312366af3837f672, 0xc41f010f2edd2918, 0x1cf3604615a561b9, 0xda8704040d575e38, 0x02f72203844ad215, 0xdd68e58ca57a6641, 0xb85cd0a7accf6da9, 0x55ef316cc3ad2aff, 0x213f0504ad627dd2, 0xbe438d1a8523b244⟩, ⟨0xd1c7372603773044, 0x3b659eef58240bc6, 0x0cc29311f6be13f6, 0xe9c6bd8ce8e6520f, 0x18e831180bbd5117, 0x45bef1a9cf60cfee, 0x7b6377aedefb6641, 0x33e6f6a6a99c3611, 0x33ceb005a9f9cd42, 0xbb9e66d78388beac, 0xcface4a53e603b38, 0x4143514dfd473c0c, 0x9591f52de87c3774, 0xa0ec792c4582b86f, 0x86cfb38112de8bb4, 0x30f64a784f0f6871⟩),
  (⟨0x5c30b99d670d3100, 0x6f657ec118f42987, 0xa71baa02a5b85b25, 0x54eb2183d8e3dc70, 0x89187b93776ae85e, 0x5f1dd05818c76138, 0x73c4fc8fa6ce4a9c, 0x36af952073b70bf3, 0xb788eb2f5ad1491a, 0x703a8bb366897bcf, 0x817342a6a2c5a3d8, 0x4b8ec07fd1df7c01, 0xb97f960a1c82f359, 0x95667050ca4a0042, 0xe7606d7e5a81ac5b, 0x6f7fce2080928ce6⟩, ⟨0x68474682d8b359f7, 0x8a7700faf008e44d, 0x8ade4c348bb57450, 0xce0b6a6ab239ea25, 0x1c4f9fd2eee850e6, 0x9583cae8c6becffd, 0x88712394041a30d9, 0xf1a574be997cf7a6, 0xcecca07fcfe75983, 0x9f8cbd127ce2fb74, 0xdca5cc88a90d5ac9, 0xfcd88a8bcbef15a6, 0xcacb6c095ef86b1f, 0xb89fd47dace6439a, 0x2d78cfd20be7b848, 0x38ce4a23793c55b8⟩),
  (⟨0x10fd4944f2c0a884, 0x734f520584bd6a9c, 0xcae9b416a9054e55, 0xb2c10c86dac0b56e, 0x4fb7798706384c66, 0x6c2a43950c6c51c5, 0x3566b996a392b449, 0xf65a6bc23a9013bc, 0xd20a6c9d1f84552c, 0x72d2da53c1471b30, 0x4a063da66b919470, 0x0fbe870405dd68ed, 0x8f3764fb2e66d3f6, 0x660e1e78accd132a, 0x64bac24c1ac70eb8, 0xfb00a5245bd504d9⟩, ⟨0x96047ee265e7d867, 0x2943af9d3c4fdb22, 0xd883b7db89408f15, 0x1c8551acf7f41554, 0x7ae2c50ee42b0fad, 0x847145fc889c8fa4, 0x5d2a6c7c8d0b10b3, 0xc17c9407c50e3593, 0x50657fa1a5c9c865, 0xce194a790a4bff3e, 0x90a00d366c30e434, 0x84ac678e8336f9ac, 0xff095ca72c7e6c94, 0xfc485a910fa8ffdc, 0x1c4a22791c00daf0, 0xec9dcfff81721aca⟩),
  (⟨0xed6e014d9b502f95, 0x0051c9a44a7c7d01, 0x30c1e173e93d7c90, 0x4761983c89db7198, 0x4cc386c9d7683d55, 0xd20b2e46ccdd4bbe, 0x9276e9aa997f1478, 0xc0456d9827153620, 0xabd831f761cc9a6b, 0xf2edb67ab08dc24c, 0xcda43e7e283af85c, 0x9ad1fed375fe5f41, 0xc26f746d3ca5e40c, 0x15460fdf95865ac7, 0xd755556f3aab6863, 0xbcb71e0fe1099866⟩, ⟨0x8c1df7569fae8331, 0x9324f55c559ca7f0, 0x3c87a436367ddbc9, 0x96b01d7bf6b0e248, 0xa269e4d5b1d2fcc8, 0x28e3da9a9987aabf, 0x709683496598a489, 0xfe641ee468dfcfb2, 0xb231d5c39bd95170, 0xc52a6667f7e1ae9f, 0x020178df459708e9, 0xe1fcdec861c8299b, 0xe356f0f71ba185b4, 0x4046fa950d011b76, 0x833dd84ecae58ade, 0xc1fefe43cb4bcdbe⟩),
  (⟨0xf60c5ed02e1cdf34, 0x1f91b4d3cf805959, 0x6c5c994712da0d73, 0x5687f71e5815dd11, 0x3e51791941c2ded1, 0x0f5b2f97ee92c149, 0xa379d2a53e863351, 0x3a545a3df48c0cc9, 0x8fe7737f8d0fdbfb, 0x1b69b5d7d6d62b56, 0x917d1e1d9f0c0319, 0xee0d5d6b4806eeb3, 0x3ea3691e6a4da8f4, 0xe6a770066bbabcb9, 0x51e651c9ca339d9b, 0x6236ff5e885a05f1⟩, ⟨0x19b2eb773131f12d, 0xd97831c3e81a23b4, 0x812580e91bdb8578, 0x78bf3c34eb94cf2f, 0x811ddeab24051a41, 0x0495ada406df226a, 0xb04af269eed30a09, 0xb7c4aeb032eba882, 0xffa20c6bff3c9555, 0x9defa629413d15f5, 0x978434449d624f75, 0xbf9a8696c407716e, 0xbe4fca456f25e4c0, 0xf5eff8ef1f1448c3, 0x5b6d5fa7ac9d565d, 0xfdbf11faef5b3fca⟩),
  (⟨0xa9adfdd10eb5af3d, 0x744a9c9fe0360b95, 0x9d1979f42c3c3b10, 0x4cc0204efd9d6495, 0xc25bf75b849dd815, 0x0a4b3bc7dc4683a5, 0x400da74a062e0f77, 0xa9ea565b1b365b31, 0x415d32eb9154ad65, 0xa2f5cf2c64fb22c5, 0x55324795b036469c, 0x090ad01c2573972c, 0x7a0e6e0145af42dd, 0xd7d659655302308d, 0xd438746ce71007ff, 0x829e8a119f3d3fb3⟩, ⟨0xebd619b5f8b1be70, 0xadb61ae7ab72c55d, 0x47c295aac773ac11, 0xb95cb48ae12de89d, 0xe8be1ed9ab263cab, 0x11e3d6b1b536e88d, 0x0bdf88c3bbb50d49, 0xe26217ae989c995f, 0x8b0b490c4dcad7f7, 0xc793250325155fde, 0xd1f1ee1cec7bccf8, 0xb776d05cdb8b693d, 0x3a6ad9b73c6ed2da, 0x181f764c0a7e7684, 0x19e7b3e915674b9f, 0x8374129d8a5c4958⟩),
  (⟨0x8828fb6d2e4d1ca7, 0xe806561a4a110858, 0xc8a6ab4d917dc596, 0xa317b0e65e146c19, 0x078a7546f20338b9, 0x90549a2a5224ca76, 0x4b79820694b8dc63, 0x9dca45680487e6ef, 0x1e458a6e05688bd8, 0xba127f459229557d, 0xbb0cfb8d8a54afc5, 0x5e015088779e8cc2, 0xf883129fd5accfbd, 0x78b991c39e6484be, 0x35ed7b8b3aa8f252, 0x7fe985b74a920f95⟩, ⟨0x0ad76ffc76b7f19d, 0x354559e0593ec7e0, 0x8dfb209efd29190b, 0xbda437d2fe1aa312, 0xd4c172d185e8199d, 0x51c3c1252a14346d, 0xed5ba474830380d4, 0x692d47b3f994748e, 0x6423fec1649c9bf9, 0xf66da7dc7de21f96, 0xf324a746f2b365ce, 0x3dbd1d348a49f817, 0xf80ad2f5a0562b6b, 0xded1eaf7a9c54847, 0x43384486d3c2e9ef, 0xaef183f14834569d⟩),
  (⟨0xf8a4db776c892090, 0xea739ec5c7f38271, 0x9d6003c2ca07d89e, 0x5989b9295dff2c72, 0x2960a50612f97155, 0xb467f73ac9d9448b, 0x9238880a0c9af77d, 0x4091e0dfeccf6ce0, 0xde8f7f63a058ea3c, 0x2ecde2cabad08181, 0x9a2037e3855b0041, 0xac5b676e31d4cc4a, 0xaa2728e08cb6c38c, 0x28afe5c3cbefb70d, 0x8e4785d4090a439a, 0x437072a46ebc6531⟩, ⟨0x406b15a03c849bd0, 0x8e00417da54b6655, 0x1471183449b5b968, 0xa817ee624e0a19ec, 0x1b71c12be9147700, 0x38a6c598699b7a08, 0x3fa1eac5d2430c19, 0x8441dc2a281c1730, 0xd5c276ede847eac2, 0xdb59a57f62470265, 0x00bab2b1a3787149, 0x6ce8f5f753895c5b, 0x6566d526f81f8cde, 0x1d54cdaf31ef5c4a, 0x17633d3f6b177255, 0x36ca6fbb1eb2c3ee⟩)
]

private def katFinalMulti1290 : State :=
  ⟨0x406b15a03c849bd0, 0x8e00417da54b6655, 0x1471183449b5b968, 0xa817ee624e0a19ec,
   0x1b71c12be9147700, 0x38a6c598699b7a08, 0x3fa1eac5d2430c19, 0x8441dc2a281c1730,
   0xd5c276ede847eac2, 0xdb59a57f62470265, 0x00bab2b1a3787149, 0x6ce8f5f753895c5b,
   0x6566d526f81f8cde, 0x1d54cdaf31ef5c4a, 0x17633d3f6b177255, 0x36ca6fbb1eb2c3ee⟩

private def katMidMulti129 : Digest64 :=
  ⟨0xffa0852a267eb85a, 0xee3e4a8743c6c30b, 0x28a559f71459300a, 0x61b0eeaf429e7346,
   0x2f194672bced790f, 0xbef760bb734a4a5d, 0x37410e514215c327, 0xe96b7e8825d0f5a7⟩

private def katBlockMulti1291 : Block :=
  ⟨0x0000000000000080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def katTraceMulti1291 : List (State × State) := [
  (⟨0xc7d5b034714885b8, 0x5e57002c17805531, 0x9a6bc900d51a3d2d, 0x143f260072afaf42, 0x9bd78e2ff5ba444a, 0xbf6f0d38f87396e0, 0x71e81ad890fff276, 0xcdde2a6babdcfe4f, 0xd4f02380770171ea, 0xee96d2751c568cb9, 0x02716dd436d4b0c7, 0x2fcdadfcdfae3972, 0x1c5b895f038d0eff, 0x96ffc278615b21b0, 0x7331c8bb78a56a80, 0x0f6c6f2e6f946253⟩, ⟨0x155aa825609dc3de, 0xbd78d6afdb6dd4e3, 0xd3a6a4e7c30b625a, 0x7463c2951d4fa1b6, 0x31dbbcab1fe4930c, 0x2845d54ac61b99f3, 0x99556cc0fdc8dfd5, 0xc56d8246e3ed8cca, 0x09ea705833e2e0bb, 0xdca0d0313b17e7ac, 0x1a37001295ec6bbf, 0x21930dcb4c09e2d6, 0x46b816759ff71709, 0x534e320abe2b3dbd, 0xdd3d64af5b99de68, 0x119d1372d6eee8b5⟩),
  (⟨0xdcf6d0e90490e714, 0xf8d71bcea880450a, 0xd23b24d592c4dce9, 0xf58793180c937517, 0x55a2334c84eb90a8, 0x944cc98c78b6ec71, 0x749bedfba36132e2, 0x4f5370d185aa33e9, 0xbf1175bec67b587e, 0xd93e0b123aada00c, 0x5f72e5d1004003cb, 0x1c1ff654c9835f63, 0x95b1c383910a051e, 0xdcfae77548a51e70, 0xa9ee4976b8922305, 0x22b92254552d24df⟩, ⟨0xfd9b37890e5c7ab1, 0x948e584ddc7fb4cd, 0x67874ee7a163c118, 0xe9e97cbb1a818758, 0x2b948f0ffceb4dfb, 0x8c725c1d08357d7d, 0xa529195eee36e410, 0x0cba05df19832e43, 0xc3a5bbaf04352767, 0x0b75f1d177772764, 0x4a6eb31d150e1992, 0x758fc22ce7854e69, 0x7e844e65253f24bd, 0xb3ca374d40455c17, 0x084ac0045a01f846, 0xc290d5f1c0d35da6⟩),
  (⟨0x352d5f7295709853, 0x95d8aaa6f8f164cc, 0x4ad62ccbb2a47b1c, 0x322f1a0111b46a9d, 0x1260b79f0ad97932, 0xd90cced7b6024d89, 0x9a9ad6bb514f5b8d, 0x27abcc0ba0b6fcb3, 0x02cdc3160f44733e, 0x98519157cf3d14c6, 0xf368afd88bae7832, 0xa85e71630df4cb5b, 0x10af1b55b363c2db, 0xe7eb3128c4fb6a3b, 0xd35e9f4d71a5b65e, 0x3df6c6f8f23c2587⟩, ⟨0x87679bc00731c9e5, 0xceb1a09d65e61ed8, 0x8c438795198878d3, 0x1baa52b735df5a3c, 0x9aa3b8f8eec8e759, 0x6e4786514150e3d1, 0x709d689996abe967, 0xa4b0e4a7f27b9636, 0x4b99fcee3f10ca1f, 0x1a4b5d6b6e3505c1, 0xce0eae5d1b1695e1, 0x2670ab77d0f0aacc, 0x84ef3792a21f453a, 0xb12c1be39a618ce2, 0x14d176820726a20e, 0x21573e295b9b34fd⟩),
  (⟨0x5fd564f2d242bb49, 0x979a46288da4ea66, 0xe0d6db246c3a6dcf, 0x477dab9daaef90b5, 0x8c51d235554757c8, 0xeb59137444014904, 0x26e2594744bd561b, 0x69afa1f5473740cd, 0x7be2f92376eba1ef, 0x2f0d9683c46d433f, 0x7084c6561e58a098, 0x33f5a4c4210f0025, 0xd863083090f674a6, 0xd76baaccc8630071, 0xeb6357c41b10840b, 0x99c334bc6f124be3⟩, ⟨0x8fd2ef6998497502, 0x523e3ec03de3ed44, 0x38bf86b90d7b936f, 0x320a1c996607b525, 0x6eb965c017b00153, 0xce22f71620109144, 0xc6caed8bf328be86, 0xab2dc442ce4fdc13, 0x3bafebbe3d2e0a5a, 0xe9662c266e08cc01, 0x23b50c89920d3817, 0xf0a4e9959215f380, 0x7a1b10aa0ae75bfc, 0x44ba43ad28549096, 0x9f32292c70ef5eab, 0x39d9f684a0c74aa4⟩),
  (⟨0x73dae3b827761eab, 0x15346e6783e1d17a, 0xecb57a97cb9abdf6, 0x290dac0a4c5901f1, 0x9d70fd45f154a8d0, 0xe5b68490ed66f689, 0x33697d6944f25947, 0xae1493c3ed37846d, 0x3bf6f02c8fd6f3be, 0x06087ad9535e29b6, 0x749fb8e6688f40a2, 0x9cdf82cfee9ab28f, 0x5b28d6c4ce11a3e1, 0xa70160948079e73a, 0xe09f9cfe75c9ab22, 0x17a9bd9d7796a8b7⟩, ⟨0x0872677b72d00e8f, 0x0654d061954ac407, 0x30b0ef366ed88883, 0x32765e235a2fa44c, 0x1772843b8afc4b73, 0x3b4c3d239865540a, 0x421dd0232fcfdfc8, 0x9e10faf75c2fe701, 0x5aee9da11811b5a0, 0xe04ef6ced9ffdc32, 0xb346e1a391c0535e, 0x9cb80c815b9176a2, 0xf9130091594186ff, 0xe64c081b4a6f5313, 0x91e27a125fc07cce, 0xdb5b6b39daf83ce8⟩),
  (⟨0x15d0a09f0ccaff77, 0xcb56e7f8902d0a2a, 0x9596209051cdf326, 0x12d71db2059e5c88, 0xcc4d3e28eb245ce3, 0xbcae68509937d713, 0x13b65722354e83a3, 0x74890c00bd74cc78, 0x13cd2bfc7b6c8b04, 0x57e2ee5b2ee71990, 0xab1c4aa7a982cb8a, 0x780b42971184b707, 0x1450b15d7c62ea3d, 0x0fb4ac89acfa37c0, 0x366d54fe3495b2e1, 0x6eab7e70aa170e42⟩, ⟨0x331442fb424df789, 0x8bd42c3d587933b6, 0x76e691541bfb19da, 0xf398b3ab658a885e, 0x6f80cccb492cf709, 0xb1bab0f33980c07a, 0x87a660ef74a4fb36, 0x7b1fdaf72d34e6a0, 0x514889b89a22296c, 0xa3b431b5d051b577, 0x38486272008b40c2, 0xef15dd5528afd872, 0xbdf132cd4bcd9324, 0x99c2d55e190a1e50, 0x877a37cfb8218cc3, 0x81163f019a33fe99⟩),
  (⟨0x4d268e440c469482, 0x5b0c7ccda4a6d97d, 0x258a6b2b003cbf1e, 0xd925442f5076b933, 0x2231d6fa5b67b8d2, 0xc18cdf1633ccb705, 0xfb42e36c05cc542d, 0xd4bf15d4a22007b0, 0xbb899500ad787999, 0xfdbbf0160b4abecf, 0xdb5c09516d7a8018, 0x00333f66eca749ed, 0xa9898d91f3f21322, 0xd113d3ff96ad00ea, 0x7a920d0bf2f879ca, 0x0890d1a9d448bfd8⟩, ⟨0x613d7c087b357247, 0xf8b318dca111b193, 0xed14aa2466abb748, 0x63c33e9e7c0b91db, 0x6d6e2b7c24999ad3, 0xd9cdf87270af38c2, 0x2f274f01c8b82b0a, 0x4c1e385d013bd5e0, 0xd4c4350a44d31a8a, 0xdedb36cac261d2bf, 0x3e6cf2970375ba21, 0xb5f01f2212c2966c, 0x5c3ba13226545ed7, 0xe448d9e56c004df1, 0x87f93ae53551fdce, 0xceb4f5668fd77d16⟩),
  (⟨0xc9673b67d172b90d, 0x5724bcd467e706de, 0x9c92e79de7c114a9, 0xd3b160e01b48fa30, 0x6942d46ee35d9da3, 0x5f6745ac857be03d, 0x60beed465ec99761, 0x03c56628e0c80ca6, 0x4e1af9d4400d6522, 0x2b100953149bec97, 0x300998d49739f9e7, 0x222d5af0ee659426, 0xbfbb70fc68aa43e2, 0xce742ae41b70512e, 0xd76a86a0f8017c03, 0x79ad21217a4d7a1d⟩, ⟨0x0f48a21821282137, 0x2fdc17cbbd8629e7, 0x92192fe899953e9d, 0xa4315ba7f3c7e2b6, 0xc85b63c48b21e47b, 0x77ab0229c7a91a14, 0x6963ae486c015e85, 0x14269c6fb99fbd67, 0x7bd3ac160dc3c3fd, 0x831097bab0b1b8de, 0xddafa01729ed0a67, 0xc349ba94c0d524ea, 0xf30181c6ca16b5de, 0x59bf41e05f89f7b9, 0x5158a296b0771859, 0x810223eb414f704b⟩),
  (⟨0x2050720717894c6b, 0xea92011fa1791864, 0x0c566a2bf82277da, 0x6d1579d3017ea5e0, 0xc41b9d493fd67bf5, 0xba453630f01d48bb, 0x1faea96063d40759, 0x32651a27ee4e78a5, 0xaaa1a28ef4d47b43, 0x9e287c3264477034, 0x9f0edf4ac361d914, 0x2d8f0ca8a3303911, 0xc871460cc26b332c, 0x40713034b55d5f41, 0x0b7db9b7ef505206, 0x7e1c813da905382b⟩, ⟨0xd0e04b2fff60fdbd, 0xc0636f6b20dd79c3, 0x1012942390bcdb1c, 0x739641a477c26e76, 0x9eddce21cecc4198, 0xa84350d7736e6d2b, 0x784d0929659aa51e, 0x783b358609ede97b, 0x6d4a950caebd1e20, 0x0d0bcd98d10b6c6d, 0x226b0a9c4e0d5e02, 0x8a04407fa95d0889, 0x954f074543fae2ec, 0x6f7b433f3b1dee76, 0xc0dddd9332774d8e, 0xd4b87e43e6225be9⟩),
  (⟨0xd23bc5b7cdea26bc, 0xef298156b6d2ce99, 0x9d9b9cebbd28fa2d, 0x17ca00b42f2969d2, 0xa36efdae7c012850, 0x1989af4880628ea5, 0x688b9b2a427ddaf1, 0xf3526accb01667a6, 0x33cad2b2c1bc734f, 0x0a4616b062b7a0f9, 0xa17e320be7ef948b, 0x5251bceff5722232, 0x38a85fec180e371b, 0x4de4407f89ceb10f, 0xbaf259bb515ff5aa, 0x60bb70580cac1040⟩, ⟨0xfadcbbfe25c51b54, 0x4a748bdc351154b0, 0x61cab8a45c08a501, 0x3e99810a80ae28ba, 0x2eff83053d0eb85c, 0x1af993288a6a5ada, 0x7264d3e084382919, 0x56bf3041d3ecfe6c, 0xfb8328cb073f3c18, 0x941f43254b04ca36, 0x026b8f69924d489e, 0x4b8d06ab79dcbfaa, 0x17dcab2a154d5a0c, 0xe2c6853b68788102, 0x8f63c4ece6828164, 0x1e0cb83c1edfaebb⟩),
  (⟨0x5b445c614107d6a8, 0x2cacce769b5e34e2, 0x75e7ac00294dd583, 0x7190280fc33b2ffc, 0x0995fd7f93529a61, 0xba7d8458d0920867, 0x0d429aed302a08dc, 0xc0d575bd90c632be, 0xb5a2e3e2179d4f48, 0x1a006d5db3ab816b, 0xa719520dd1180307, 0xbc5dcc1da6c31189, 0x42812cdad25d7f07, 0xaeddfbafe0fe1cf6, 0x9deb7325e37e7201, 0x268c3bd4a192486f⟩, ⟨0x0d97f3a76b0715e3, 0x554f083f3d1c77d0, 0x6ed9068e13a12c80, 0xa5689a55b8668f66, 0x07048527bab5e793, 0xa4c96bce608000d7, 0x27878b543a474f4c, 0x7e09903937752248, 0x071f2cccc237b51b, 0xa9c03655bc8236c0, 0x25b2a70a692d36bf, 0x089c5b716cb79db4, 0x32694c9a4a864672, 0xf692343312398bc1, 0xd9cc109b22095eab, 0xce8dbd9c64c7584a⟩),
  (⟨0xadab5c40831ff4c9, 0x868e9dab4cdeee50, 0x35580694622fa14e, 0xe588b97ca0b1211b, 0x5ff092271a26f013, 0xd74436f5313785f6, 0x5678a73191178072, 0x17a87a0e3735daf3, 0x36f6aa62d0718f5a, 0xe7d432e737d9b752, 0xb5cb272adccce5bb, 0x49c2b3eaab4f8214, 0xc09cc291e744a5ea, 0xae6e092b6ecd4054, 0x20375ab923f32d83, 0xb6096e9450984d4e⟩, ⟨0x09563d8392c163fd, 0xd98f58aeebd0129b, 0x22c290dbd001f2c5, 0x46b1cb82cad5c4b5, 0xaf2e61e137559700, 0x7923cdf1889ed57b, 0xcb88e404ae50bbeb, 0xf85357b4ac6475ac, 0xa9ebbbe360ae4c52, 0x56af4f2f94577807, 0x38f74cb51a268383, 0x194c61d05af1feac, 0x94d6e33d9206f64b, 0x7b4cd56aacce336f, 0xd5afdf9af72faf9b, 0x9e5ced990a72a027⟩)
]

private def katFinalMulti1291 : State :=
  ⟨0x09563d8392c163fd, 0xd98f58aeebd0129b, 0x22c290dbd001f2c5, 0x46b1cb82cad5c4b5,
   0xaf2e61e137559700, 0x7923cdf1889ed57b, 0xcb88e404ae50bbeb, 0xf85357b4ac6475ac,
   0xa9ebbbe360ae4c52, 0x56af4f2f94577807, 0x38f74cb51a268383, 0x194c61d05af1feac,
   0x94d6e33d9206f64b, 0x7b4cd56aacce336f, 0xd5afdf9af72faf9b, 0x9e5ced990a72a027⟩

/-- RFC 7693 `BLAKE2b-512` digest of 129-byte multi-block input `0..128` (`kat129Input`). -/
def katDigestMulti129 : Digest64 :=
  ⟨0x5f1d034ad41197f5, 0x611e5d063c41a997, 0x32908599de7e414c, 0x3e4d44fdd2ba495f,
   0x14e1c4ae19be1844, 0xbc987820571aac49, 0x296635cf1b6ad757, 0x8f64c4a583c6202c⟩

private def katTracePersonalAbc : List (State × State) := [
  (⟨0xf0c9aa0f86491dea, 0x63b7dedf4a4e5ad3, 0x195257f959096e32, 0x00db27e317221cdb, 0xb7defc3d0277e11f, 0xed49c30cd311d50e, 0x9145d1e9f80e4d23, 0x45714e1378e24a82, 0xee5e0f39647a9fff, 0x7bee264bf3cdadfe, 0x67a3851c31029794, 0xdd122039fd83f28e, 0x7772fc2886a76c5f, 0x254ef880a19a8726, 0xa27691efa840d325, 0x7170c68a43964df2⟩, ⟨0x55a9918b92e21d2b, 0x126ffcfc8a96b26f, 0x4477af288fec914c, 0xa63cf6ba33431406, 0x44257f15fead36a0, 0x9d776fc66ec15530, 0x7bdd1c89e0a485e3, 0x967717939d8454e9, 0x2e8f82d270c2f2ec, 0xcf906d10e6ff8d5c, 0x392d938c0ee780ab, 0xa09cc277b8684888, 0xfe8ed69437550919, 0xcfc0340690baf461, 0xa1c917e5d865298f, 0xb6bd4f652e813d81⟩),
  (⟨0x435e9232de3204f1, 0x979a7d66fd66d0c8, 0xe22dad4c6d5fbcbf, 0x3291675664c7dece, 0x63428571d88f8764, 0x4c669e47a3629490, 0xc5a5f93ff17f98a8, 0x96297b6bc1541b43, 0x982ec329a0e57294, 0xc1805f87d5bf8361, 0x430a1d06047169c4, 0x3ec9e4bd74aa787e, 0xc2c4e584c8e0b973, 0x880cfe788e989d41, 0x60e84ad993ec0cc2, 0x9fe6ccd73238eece⟩, ⟨0x87b81235519eac38, 0xadd37f4ac5f82bb6, 0x8da94066a226de52, 0x0a8202dbb6a66f44, 0x9a7ef14294d2c83a, 0x617253a7540b7533, 0x9f29d2f3e97273f2, 0xab7c4483ca2b3b02, 0x40ec35ef96669bd1, 0x39916eb233266d0f, 0x474bc8697a0fa82e, 0x1f07e1da2217661c, 0xb8948a7a0de85a7c, 0x08922d820525527d, 0xc955a439682b439d, 0x50953414657a41bd⟩),
  (⟨0xfb23e82ee2043117, 0x045f1f2be499e4b8, 0x10ff77105fa202fa, 0x5fe0ad0f505b0013, 0x78e7201c19704240, 0x033261f3c5195d47, 0x09775c4a24d15206, 0xa3dddb1d03fdb6b5, 0xe49f74b8f72a9d85, 0x74807cc028be4fcd, 0xe097cd90c66019b5, 0x780c88214e778e97, 0xb81a10bac62078a7, 0x1bc81b79edbfe34e, 0xb599f34d66c9ba24, 0x7358ba4b46f4b530⟩, ⟨0x74ada3e45a869af4, 0xa07ee0c429f5a7de, 0x772dbefec5b44154, 0x45944126ce206de2, 0x7797986a5676347d, 0xb6938f04b121da60, 0x0384407d2757cf79, 0x712148f3d097adbf, 0x7ac0c8a88a5f517a, 0xd707bfce4f6e31b1, 0x2d1e9e43ebf9e1a6, 0x136a4570b321969c, 0xcc126f35aedd9c39, 0x0800f90de41f6aa1, 0x53844a96b951a37e, 0x6a9d9544988ad788⟩),
  (⟨0xacd5c53e26806a6d, 0xf82486695e3eeb5d, 0xf30ae9fee51d9aff, 0x94cdcf835b118500, 0x22d08c14695e6260, 0x6576f2753ca3417a, 0x91ac27992ed9d313, 0xdbc7c3e25d5aa8d8, 0xd1f8cee5412cabcc, 0x93a96f9a1d76c9a2, 0xb08ef94e6f7d63bb, 0xb3fba49992f43d33, 0x3916b2f4967606d7, 0x7d98c72c6ef6012c, 0x2f12a7575a4dcc28, 0x9a5e92ff03aa8739⟩, ⟨0x3f153527d1f805b2, 0xed59e861539396dd, 0xfc90ef0683ada8e1, 0x15425daadf86de3f, 0x12de48a06fe1f766, 0x3dbdf17afeb97674, 0x743ed24ca5f7ca26, 0xda1b41b5c54c8a53, 0xc0b3e1ffa2744780, 0x54cb26432ce60d6c, 0x321685c91188e2f1, 0x5996537894813d7e, 0x8a2bf63750c6e355, 0xc22cd01eadfd30e7, 0x22ff8b6076e2470a, 0x20fe5f9c19f959ea⟩),
  (⟨0xff17978b4f864c8a, 0xc379344618df8e39, 0xbfb6c4388d110dcd, 0x57d1c92d8098ad33, 0x68d9ef2a0ab71598, 0x882ff555cd0113f4, 0x2f77305a61092d07, 0xd9c88c430f7e1229, 0x9948ee56081367dd, 0xdc76a0c320120912, 0xd95c9ac853ef0c45, 0x84906fed5c7a4db5, 0xc775ee0889c6945e, 0x87fb3cc909f0f1e4, 0x47fee0f1f035df21, 0x6dcfeafbf8554f3b⟩, ⟨0xfda938171dc6bc71, 0xe9e5befc43980d30, 0x8345f7729cdf4b1f, 0x911fd896b4a14a78, 0x757712588b642403, 0xddf0917ea9ea64bd, 0x1547c519d49a3f14, 0x7f66a8aa7f50fb87, 0x5675f2a23ff856ea, 0x6acfa9136ce395ac, 0x9899e38955ca69ad, 0xfc56b8d723e24e7a, 0x879819cb91e2761d, 0x27ad163a1960825b, 0x12deea65c57c33f4, 0xda6b197b1752f74e⟩),
  (⟨0x47aed869f2c63533, 0x7c95a1fd2f9026d1, 0x208d3ee4eee4dcc8, 0xafa3b4a0c5b56890, 0x42b10b119657cb66, 0xe9f6e987bb4e3e66, 0xa147aa9f794baaf2, 0x1d798ba8ca47a93b, 0xf5d6087282b0b10c, 0xc04425419faaabd7, 0xd75c5717c1a2254d, 0x11a1f68bf4e0f60c, 0x66977f664e00067e, 0x60918877524bcfeb, 0x8a21942de18464b7, 0xf0aa8b0306110f58⟩, ⟨0x30f41b88454ed1d2, 0x7e5e40f5e340a7cc, 0x3e640889fe06782e, 0x3a70cff1d884c684, 0x45ea2887994fd5d2, 0xcb986ab8fd815573, 0xd869252c7a2e2833, 0x389e3544cce0cd78, 0x1c12275e22a99497, 0x6ae9047cb0d07867, 0x1a826ccae9faf480, 0x8cb466cf0773c210, 0x943698859748980a, 0x3ad4d5034161a091, 0xed1b87f998b0a0f1, 0x9b2098f167498441⟩),
  (⟨0x5483372fe0ee3240, 0xbd991375f1ca911d, 0x168429d9e77d1800, 0xb6a1b4ad23b15c1f, 0x122cee8418b9f377, 0x1f363346c78dd445, 0xa5c13efec0a599ca, 0xa654b8d9d9ffc6ac, 0x54b284620e137327, 0xfc397e6472ce79fc, 0xad56635c0f1abb7a, 0x10b8f31a92b42b75, 0xeeca1d5508810206, 0xefb01c394edb82e8, 0xb24ff60029491cab, 0xc1d8748da310cb9e⟩, ⟨0x69c79b1cb914faec, 0x453daee31d952dc7, 0x408ffff5ced55e64, 0xbf0afd34b3aa758b, 0x88544393d8cd7b5b, 0xd666b0f5d3d4efd8, 0x9ee48f4d9ac410f7, 0x0dff651a10ece1ac, 0x8548afcf052e0f6e, 0x32167bca9b599858, 0x9d3d68dcf9dfe5ea, 0x2e911bc8a6470a9b, 0x62e6ffcc86029005, 0xa0eecf28a3b19dbd, 0x20baaa28ae09c92b, 0xe417620838640b75⟩),
  (⟨0xd8678fc60fb7f895, 0x8c6af02b88b53624, 0x4990323d94196fbe, 0x55f5af753fb46816, 0x22b1a91b04f4a4f5, 0xb6009598a3cc8b84, 0x8b707f694ef6ee9f, 0x367cd86f730c62aa, 0x77136598ffafd034, 0x2bc6da9ec6ad5d47, 0xafa39d4e8dfb772c, 0x93d52111c29b218a, 0xd9e9cf8769849f4a, 0xa6d4deb1700933ff, 0x4ad58e00944d6bd7, 0x6850a906f33716a9⟩, ⟨0x86f025a50ba24e51, 0x530a726f655017a1, 0x05d4058543c531bd, 0x4d3e7b6e5f916f08, 0xc5a9fb161875808e, 0x95d1ec0af9e72d92, 0x653f96c9ae2f3c42, 0xac4e81e26c06ac72, 0xd3e1ba290a9c096c, 0xb643df5516d2a1ba, 0xb260f6432b49f11e, 0x09b0c9be5ab46cff, 0xb7b2ed22c9e6ab62, 0xe5a172f8e412651c, 0xb9989dda1db26de3, 0xc209c643b715ed9a⟩),
  (⟨0xfdf1abbf9efcbffc, 0x91c00d5f184ad410, 0x66e28d4a8b550452, 0x38915d7b9dd39bd5, 0x0adf49c752479b89, 0x8231091bd158db5d, 0xbf46e3fe2497b586, 0x30c3fcab6558a724, 0x34382fe7d3c73cd9, 0x69fb2a6951bfe373, 0xa46d81048b2b4c90, 0x27659e7f63744e68, 0x72651000ce0265d4, 0xf8922ae52d701537, 0x05c68aa48d5659de, 0xa0c6447fcd3aa656⟩, ⟨0xc9091ebf5e0ca3d6, 0xa0a135023d4bc938, 0x3b1f5718c6c02d9d, 0x74fb783087ec6628, 0x0538e4e471eff8f2, 0xfb52b73444ef68c3, 0x1a633d4cc0e2e49e, 0x07b6339df48e17f4, 0xa0a3d4ec2c5589dd, 0x3316a29faf26d2b3, 0xb54f3279cfc0bc1c, 0x42abdd0360184ded, 0x28655241d9401e28, 0x8e8de6c2e959a9f4, 0x4bce09b616b0c15a, 0x5372746623b07ee8⟩),
  (⟨0x6165515628afc62b, 0xe7a9509badc8cc7b, 0x454005c187dba869, 0xceec0d744068e897, 0xb81504297d010649, 0x5d7b463f4d6819ba, 0x274156e5892acb51, 0x171e1d70bd65ee77, 0x4f29cfa6e633aa47, 0x6508c77a8d39965d, 0x7c1dda2ec4adf386, 0xd9b56f1d9d5c9d40, 0x97c977d9d3b6ce88, 0xc68f8ccbc894b8b6, 0x35bad453d6a09997, 0x373f91260d806fab⟩, ⟨0xa3c41b4044e421e8, 0xb991711af2921f8b, 0xbd125afe2622241c, 0x7b5b740685082c83, 0x9c8a5bd908b89138, 0xf7e5c2f46eaf0aef, 0x48d1d95fca80bdec, 0x10a0321e2a9d341e, 0x68e42ec4f5ae1733, 0xba1f4f84436693de, 0x1f1162d0f99bc774, 0x8ece25365eded949, 0xcfd35cd4285e6bb1, 0x8be530c774a8bcf3, 0xe94d1092037137b3, 0x275bd853ab0ecd3b⟩),
  (⟨0x3420af6d16f7420e, 0x09097d374e66238d, 0xca35e3b82584b534, 0x6e5f84a889862fc2, 0x95af8e4f3cbfe1cf, 0x41b897930927e913, 0xc163ba525152ccb8, 0x0e99c68ddaa3678e, 0x3905ff7456a8dc6a, 0xf74e02ee69b70d9a, 0xa4e072731c48b570, 0xe52f3dc534b17ce6, 0x69c3527ed15d996a, 0x27451ce0ebbe74f4, 0x91fb39e63603c92d, 0x51b56af429322526⟩, ⟨0x08e3beefd537146a, 0xd79b9d7f16d596ce, 0x69c4487005c9434e, 0x18e8776a029bf754, 0xae01405527a86bb3, 0xe943eb4e89147bec, 0x54c04b0d77587da2, 0x14e0efaee7b757bf, 0x1a84e9fd767a8d53, 0xc3d9c458af81d01a, 0xe7ab8248f19dd4bf, 0x274e4073ccb09858, 0xf339997ef450b57b, 0xf5e882522046fa43, 0xdc45e8adafd6976f, 0x399e01ceb0e8f15b⟩),
  (⟨0xb67d3dd2123eb6b8, 0x6d80de3865303227, 0xc5b1c16bdfb4a613, 0xde71f8afd3646419, 0x181dc1b1a0a6fbd6, 0x213c5429bc786b5a, 0x3e91b981138dd64f, 0x68e224219dfda6ce, 0xf396de55c50c4b70, 0xbc3f7f7e1b7a2ac0, 0x9865f12eeb540e04, 0x84d9838627efc661, 0xd082bef208b457e3, 0x38b8d22c36c15007, 0xddc3174696f4bd75, 0x02cf84ca46e7c733⟩, ⟨0x8a0200fd59399b8e, 0x9e4c7b82789aa68e, 0xf8b9c4e569916727, 0x56bbebe896af09d5, 0x483c4fb6e5347858, 0x3a7b6f445849adf0, 0xe81aa6b628999002, 0x8b6ae0a2b1c8311a, 0x8f90af06b33b02cb, 0x4432165c503995ca, 0xaf75d8a3a6a6af84, 0x8634b093eb35f3b6, 0x8fc5efd946b6040a, 0x5086b3cad8037fba, 0xa4f2b4440972bde3, 0x8ebf0252e5dc8c4f⟩)
]

private def katFinalPersonalAbc : State :=
  ⟨0x8a0200fd59399b8e, 0x9e4c7b82789aa68e, 0xf8b9c4e569916727, 0x56bbebe896af09d5,
   0x483c4fb6e5347858, 0x3a7b6f445849adf0, 0xe81aa6b628999002, 0x8b6ae0a2b1c8311a,
   0x8f90af06b33b02cb, 0x4432165c503995ca, 0xaf75d8a3a6a6af84, 0x8634b093eb35f3b6,
   0x8fc5efd946b6040a, 0x5086b3cad8037fba, 0xa4f2b4440972bde3, 0x8ebf0252e5dc8c4f⟩

/-- RFC 7693 `BLAKE2b-512` digest of `"abc"` with personalization `"ix/v6/b2b/leaf"`. -/
def katDigestPersonalAbc : Digest64 :=
  ⟨0x6f9b499c18bf500d, 0x6119c35bac69947f, 0x6ba2ef3431a33088, 0x75c0ae412287cc92,
   0x96f7f2100e64fe83, 0xf1f8b402ab74be55, 0x6109e46fac85e8e3, 0x5e3549882206b34e⟩

section KatProofs
set_option maxRecDepth 8192

/-- Kernel-checked RFC 7693 KAT: `BLAKE2b-512("") = katDigestEmpty`. -/
theorem kat_empty : hash ByteArray.empty = katDigestEmpty := by
  unfold hash hashWithInit hashBlocksFrom
  have h0 : ByteArray.empty.size = 0 := rfl
  simp only [h0, ↓reduceIte]
  exact compress_of_trace initState512Plain Block.zero 0 0 true
    katTraceEmpty katFinalEmpty katDigestEmpty (by decide) (by decide)

/-- Kernel-checked RFC 7693 KAT hex string for `""`. -/
theorem kat_empty_hex :
    (hash ByteArray.empty).toHex =
      "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce" := by
  rw [kat_empty]
  decide

/-- Kernel-checked RFC 7693 Appendix A KAT: `BLAKE2b-512("abc") = katDigestAbc`. -/
theorem kat_abc : hash "abc".toUTF8 = katDigestAbc :=
  hashWithInit_singleBlock_of_trace initState512Plain "abc".toUTF8 katBlockAbc
    katTraceAbc katFinalAbc katDigestAbc (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Kernel-checked RFC 7693 Appendix A KAT hex string for `"abc"`. -/
theorem kat_abc_hex :
    (hash "abc".toUTF8).toHex =
      "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923" := by
  rw [kat_abc]
  decide

/-- Kernel-checked RFC 7693 KAT for an exact 128-byte single-block input (`0..127`). -/
theorem kat_exact128 : hash kat128Input = katDigestExact128 :=
  hashWithInit_singleBlock_of_trace initState512Plain kat128Input katBlockExact128
    katTraceExact128 katFinalExact128 katDigestExact128
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Kernel-checked RFC 7693 KAT hex string for exact 128-byte input `0..127`. -/
theorem kat_exact128_hex :
    (hash kat128Input).toHex =
      "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115" := by
  rw [kat_exact128]
  decide

/-- Kernel-checked 1-block 2-to-1 compression KAT: `hashPair64` agrees with
`hash (left.toBytes ++ right.toBytes)` on the exact 128-byte vector `0..127`. -/
theorem kat_hashPair64_exact128 :
    hashPair64 katPairLeft katPairRight = hash kat128Input := by
  rw [kat_exact128]
  unfold hashPair64 hashPair64WithInit
  exact compress_of_trace initState512Plain katBlockExact128 128 0 true
    katTraceExact128 katFinalExact128 katDigestExact128 (by decide) (by decide)

/-- Kernel-checked RFC 7693 multi-block KAT for 129-byte input `0..128`
(exercises non-final block 0 at `tLo = 128` and final block 1 at `tLo = 129`). -/
theorem kat_multi129 : hash kat129Input = katDigestMulti129 :=
  hashWithInit_twoBlock_of_trace initState512Plain katMidMulti129 katDigestMulti129 kat129Input
    katBlockExact128 katBlockMulti1291 katTraceMulti1290 katTraceMulti1291
    katFinalMulti1290 katFinalMulti1291
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Kernel-checked RFC 7693 multi-block KAT hex string for 129-byte input `0..128`. -/
theorem kat_multi129_hex :
    (hash kat129Input).toHex =
      "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f" := by
  rw [kat_multi129]
  decide

/-- Kernel-checked RFC 7693 §2.5 personalization KAT: `BLAKE2b-512("abc")` under
16-byte personalization `"ix/v6/b2b/leaf"` differs from unpersonalized `"abc"`
and matches the exact RFC 7693 reference vector. -/
theorem kat_personal_abc :
    hashWithPersonal "ix/v6/b2b/leaf".toUTF8 "abc".toUTF8 = katDigestPersonalAbc :=
  hashWithInit_singleBlock_of_trace (initState512 "ix/v6/b2b/leaf".toUTF8) "abc".toUTF8 katBlockAbc
    katTracePersonalAbc katFinalPersonalAbc katDigestPersonalAbc
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Kernel-checked RFC 7693 §2.5 personalization KAT hex string. -/
theorem kat_personal_abc_hex :
    (hashWithPersonal "ix/v6/b2b/leaf".toUTF8 "abc".toUTF8).toHex =
      "0d50bf189c499b6f7f9469ac5bc319618830a33134efa26b92cc872241aec07583fe640e10f2f79655be74ab02b4f8f1e3e885ac6fe409614eb306228849355e" := by
  rw [kat_personal_abc]
  decide

end KatProofs

end CertiFri.P3.Blake2b
