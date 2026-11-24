/-!
# Digests of 32 bytes

The output of BLAKE3, and the node of a Merkle tree built from it. A digest is
kept as eight 32-bit words, the form in which BLAKE3 produces and consumes it:
byte `i` of the digest is byte `i % 4` of word `i / 4`, least significant byte
first. Keeping words makes a digest exactly 32 bytes by construction and lets
two digests be compressed without passing through bytes.

This file has the type and its conversions to and from bytes and hexadecimal
text. Nothing is proved about the conversions; they are tested in
`CertiFriTest/P3/Blake3.lean`.
-/

namespace CertiFri.P3

/-- A digest of 32 bytes, as eight little-endian 32-bit words. -/
structure Digest where
  /-- Bytes 0 to 3. -/
  w0 : UInt32
  /-- Bytes 4 to 7. -/
  w1 : UInt32
  /-- Bytes 8 to 11. -/
  w2 : UInt32
  /-- Bytes 12 to 15. -/
  w3 : UInt32
  /-- Bytes 16 to 19. -/
  w4 : UInt32
  /-- Bytes 20 to 23. -/
  w5 : UInt32
  /-- Bytes 24 to 27. -/
  w6 : UInt32
  /-- Bytes 28 to 31. -/
  w7 : UInt32
  deriving DecidableEq, Inhabited

namespace LittleEndian

/-- Byte `i` of `bytes`, or zero past the end. -/
@[inline] def byteOrZero (bytes : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bytes.size then bytes[i] else 0

/-- The 32-bit word at bytes `i` to `i + 3` of `bytes`, least significant byte
first, with zeros past the end. -/
@[inline] def word32 (bytes : ByteArray) (i : Nat) : UInt32 :=
  (byteOrZero bytes i).toUInt32 ||| ((byteOrZero bytes (i + 1)).toUInt32 <<< 8)
    ||| ((byteOrZero bytes (i + 2)).toUInt32 <<< 16)
    ||| ((byteOrZero bytes (i + 3)).toUInt32 <<< 24)

/-- Append the four bytes of a 32-bit word, least significant first. -/
@[inline] def pushWord32 (bytes : ByteArray) (w : UInt32) : ByteArray :=
  (((bytes.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push (w >>> 24).toUInt8

/-- The 64-bit word at bytes `i` to `i + 7` of `bytes`, least significant byte
first, with zeros past the end. -/
@[inline] def word64 (bytes : ByteArray) (i : Nat) : UInt64 :=
  (byteOrZero bytes i).toUInt64
    ||| ((byteOrZero bytes (i + 1)).toUInt64 <<< 8)
    ||| ((byteOrZero bytes (i + 2)).toUInt64 <<< 16)
    ||| ((byteOrZero bytes (i + 3)).toUInt64 <<< 24)
    ||| ((byteOrZero bytes (i + 4)).toUInt64 <<< 32)
    ||| ((byteOrZero bytes (i + 5)).toUInt64 <<< 40)
    ||| ((byteOrZero bytes (i + 6)).toUInt64 <<< 48)
    ||| ((byteOrZero bytes (i + 7)).toUInt64 <<< 56)

/-- Append the eight bytes of a 64-bit word, least significant first. -/
@[inline] def pushWord64 (bytes : ByteArray) (w : UInt64) : ByteArray :=
  (((((((bytes.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8).push
    (w >>> 24).toUInt8).push (w >>> 32).toUInt8).push (w >>> 40).toUInt8).push
    (w >>> 48).toUInt8).push (w >>> 56).toUInt8

end LittleEndian

namespace Digest

open LittleEndian

/-- The 32 bytes of the digest. -/
def toBytes (d : Digest) : ByteArray :=
  [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7].foldl pushWord32 (ByteArray.emptyWithCapacity 32)

/-- The digest with the given bytes, if there are exactly 32 of them. -/
def ofBytes? (bytes : ByteArray) : Option Digest :=
  if bytes.size = 32 then
    some ⟨word32 bytes 0, word32 bytes 4, word32 bytes 8, word32 bytes 12,
      word32 bytes 16, word32 bytes 20, word32 bytes 24, word32 bytes 28⟩
  else none

/-- The hexadecimal digit of a value below 16, in lower case. -/
private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- The value of a hexadecimal digit, in either case. -/
private def hexValue? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48).toUInt8
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87).toUInt8
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55).toUInt8
  else none

/-- The bytes written by pairs of hexadecimal digits, first byte first. -/
private def hexBytes? : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | hi :: lo :: rest, acc =>
    match hexValue? hi, hexValue? lo with
    | some h, some l => hexBytes? rest (acc.push (h <<< 4 ||| l))
    | _, _ => none

/-- The digest as 64 hexadecimal digits in lower case, first byte first. -/
def toHex (d : Digest) : String :=
  String.ofList <| d.toBytes.toList.flatMap fun (byte : UInt8) =>
    [hexDigit (byte >>> 4), hexDigit (byte &&& 15)]

/-- The digest written as 64 hexadecimal digits, first byte first. -/
def ofHex? (text : String) : Option Digest :=
  (hexBytes? text.toList ByteArray.empty).bind ofBytes?

instance : Repr Digest := ⟨fun d _ => Std.Format.text d.toHex⟩

end Digest

/-- Legacy 48-byte (384-bit) BLAKE3 XOF digest, as twelve little-endian 32-bit words.

**Retired for concrete 128-bit post-quantum security:** although black-box ROM
cardinality is `2^384`, `BLAKE3-XOF48` (and `BLAKE3-XOF64`) widen only the root
output block while retaining a 256-bit internal chaining value (`cv`), capping
concrete collision resistance on every `> 64`-byte input (all internal 2-to-1
Merkle nodes and wide leaves) at `128` bits classical / `85.3` bits BHT quantum.
Retained solely for historical comparison; use `Digest64` (RFC 7693 `BLAKE2b-512`,
true 512-bit internal state) for certified 128-bit post-quantum proofs, and
32-byte `Digest` (`BLAKE3-256`) for 128-bit classical proofs. -/
structure Digest48 where
  /-- Bytes 0 to 3. -/
  w0 : UInt32
  /-- Bytes 4 to 7. -/
  w1 : UInt32
  /-- Bytes 8 to 11. -/
  w2 : UInt32
  /-- Bytes 12 to 15. -/
  w3 : UInt32
  /-- Bytes 16 to 19. -/
  w4 : UInt32
  /-- Bytes 20 to 23. -/
  w5 : UInt32
  /-- Bytes 24 to 27. -/
  w6 : UInt32
  /-- Bytes 28 to 31. -/
  w7 : UInt32
  /-- Bytes 32 to 35. -/
  w8 : UInt32
  /-- Bytes 36 to 39. -/
  w9 : UInt32
  /-- Bytes 40 to 43. -/
  w10 : UInt32
  /-- Bytes 44 to 47. -/
  w11 : UInt32
  deriving DecidableEq, Inhabited

namespace Digest48

open LittleEndian

/-- The first 32 bytes of a 48-byte XOF digest (matching the 32-byte digest). -/
def prefix32 (d : Digest48) : Digest :=
  ⟨d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7⟩

/-- The 48 bytes of the digest. -/
def toBytes (d : Digest48) : ByteArray :=
  [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7, d.w8, d.w9, d.w10, d.w11].foldl
    pushWord32 (ByteArray.emptyWithCapacity 48)

/-- The 48-byte digest with the given bytes, if there are exactly 48 of them. -/
def ofBytes? (bytes : ByteArray) : Option Digest48 :=
  if bytes.size = 48 then
    some ⟨word32 bytes 0, word32 bytes 4, word32 bytes 8, word32 bytes 12,
      word32 bytes 16, word32 bytes 20, word32 bytes 24, word32 bytes 28,
      word32 bytes 32, word32 bytes 36, word32 bytes 40, word32 bytes 44⟩
  else none

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

def hexValue? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48).toUInt8
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87).toUInt8
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55).toUInt8
  else none

def hexBytes? : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | hi :: lo :: rest, acc =>
    match hexValue? hi, hexValue? lo with
    | some h, some l => hexBytes? rest (acc.push (h <<< 4 ||| l))
    | _, _ => none

/-- The 48-byte digest as 96 hexadecimal digits in lower case, first byte first. -/
def toHex (d : Digest48) : String :=
  String.ofList <| d.toBytes.toList.flatMap fun (byte : UInt8) =>
    [hexDigit (byte >>> 4), hexDigit (byte &&& 15)]

/-- The 48-byte digest written as 96 hexadecimal digits, first byte first. -/
def ofHex? (text : String) : Option Digest48 :=
  (hexBytes? text.toList ByteArray.empty).bind ofBytes?

instance : Repr Digest48 := ⟨fun d _ => Std.Format.text d.toHex⟩

end Digest48

/-- A 64-byte (512-bit) digest, as eight little-endian 64-bit words: the native
output and internal chaining state of RFC 7693 `BLAKE2b-512`.

With a true 512-bit internal state and 128-byte block (`left64 || right64` =
one single compression call), `BLAKE2b-512` achieves `255.71` bits of classical
incremental-sponge collision resistance (`c = 3/2`), `170.7` bits BHT quantum
collision resistance (`+42.7` bits headroom above 128-bit PQ), `204.8` bits CNS
quantum collision resistance, and `256` bits Grover preimage security. -/
structure Digest64 where
  /-- Bytes 0 to 7. -/
  w0 : UInt64
  /-- Bytes 8 to 15. -/
  w1 : UInt64
  /-- Bytes 16 to 23. -/
  w2 : UInt64
  /-- Bytes 24 to 31. -/
  w3 : UInt64
  /-- Bytes 32 to 39. -/
  w4 : UInt64
  /-- Bytes 40 to 47. -/
  w5 : UInt64
  /-- Bytes 48 to 55. -/
  w6 : UInt64
  /-- Bytes 56 to 63. -/
  w7 : UInt64
  deriving DecidableEq, Inhabited

namespace Digest64

open LittleEndian

/-- The 64 bytes of the digest, little-endian word by word. -/
def toBytes (d : Digest64) : ByteArray :=
  [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7].foldl
    pushWord64 (ByteArray.emptyWithCapacity 64)

/-- The 64-byte digest with the given bytes, if there are exactly 64 of them. -/
def ofBytes? (bytes : ByteArray) : Option Digest64 :=
  if bytes.size = 64 then
    some ⟨word64 bytes 0, word64 bytes 8, word64 bytes 16, word64 bytes 24,
      word64 bytes 32, word64 bytes 40, word64 bytes 48, word64 bytes 56⟩
  else none

def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

def hexValue? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48).toUInt8
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87).toUInt8
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55).toUInt8
  else none

def hexBytes? : List Char → ByteArray → Option ByteArray
  | [], acc => some acc
  | [_], _ => none
  | hi :: lo :: rest, acc =>
    match hexValue? hi, hexValue? lo with
    | some h, some l => hexBytes? rest (acc.push (h <<< 4 ||| l))
    | _, _ => none

/-- The 64-byte digest as 128 hexadecimal digits in lower case, first byte first. -/
def toHex (d : Digest64) : String :=
  String.ofList <| d.toBytes.data.toList.flatMap fun (byte : UInt8) =>
    [hexDigit (byte >>> 4), hexDigit (byte &&& 15)]

/-- The 64-byte digest written as 128 hexadecimal digits, first byte first. -/
def ofHex? (text : String) : Option Digest64 :=
  (hexBytes? text.toList ByteArray.empty).bind ofBytes?

instance : Repr Digest64 := ⟨fun d _ => Std.Format.text d.toHex⟩

private theorem uint64_toNat_shift_byte (w k : UInt64) (hk : k.toNat < 64) :
    ((w >>> k).toUInt8).toNat = (w.toNat / 2 ^ k.toNat) % 256 := by
  have hmod : k.toNat % 64 = k.toNat := Nat.mod_eq_of_lt hk
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hmod, Nat.shiftRight_eq_div_pow]

private theorem uint64_eq_of_bytes {a b : UInt64}
    (h0 : a.toUInt8 = b.toUInt8)
    (h1 : (a >>> 8).toUInt8 = (b >>> 8).toUInt8)
    (h2 : (a >>> 16).toUInt8 = (b >>> 16).toUInt8)
    (h3 : (a >>> 24).toUInt8 = (b >>> 24).toUInt8)
    (h4 : (a >>> 32).toUInt8 = (b >>> 32).toUInt8)
    (h5 : (a >>> 40).toUInt8 = (b >>> 40).toUInt8)
    (h6 : (a >>> 48).toUInt8 = (b >>> 48).toUInt8)
    (h7 : (a >>> 56).toUInt8 = (b >>> 56).toUInt8) : a = b := by
  have e0 : a.toNat % 256 = b.toNat % 256 := by
    have := congrArg UInt8.toNat h0
    simpa [UInt64.toNat_toUInt8] using this
  have e1 : (a.toNat / 2 ^ 8) % 256 = (b.toNat / 2 ^ 8) % 256 := by
    have := congrArg UInt8.toNat h1
    rw [uint64_toNat_shift_byte a 8 (by decide), uint64_toNat_shift_byte b 8 (by decide)] at this
    exact this
  have e2 : (a.toNat / 2 ^ 16) % 256 = (b.toNat / 2 ^ 16) % 256 := by
    have := congrArg UInt8.toNat h2
    rw [uint64_toNat_shift_byte a 16 (by decide), uint64_toNat_shift_byte b 16 (by decide)] at this
    exact this
  have e3 : (a.toNat / 2 ^ 24) % 256 = (b.toNat / 2 ^ 24) % 256 := by
    have := congrArg UInt8.toNat h3
    rw [uint64_toNat_shift_byte a 24 (by decide), uint64_toNat_shift_byte b 24 (by decide)] at this
    exact this
  have e4 : (a.toNat / 2 ^ 32) % 256 = (b.toNat / 2 ^ 32) % 256 := by
    have := congrArg UInt8.toNat h4
    rw [uint64_toNat_shift_byte a 32 (by decide), uint64_toNat_shift_byte b 32 (by decide)] at this
    exact this
  have e5 : (a.toNat / 2 ^ 40) % 256 = (b.toNat / 2 ^ 40) % 256 := by
    have := congrArg UInt8.toNat h5
    rw [uint64_toNat_shift_byte a 40 (by decide), uint64_toNat_shift_byte b 40 (by decide)] at this
    exact this
  have e6 : (a.toNat / 2 ^ 48) % 256 = (b.toNat / 2 ^ 48) % 256 := by
    have := congrArg UInt8.toNat h6
    rw [uint64_toNat_shift_byte a 48 (by decide), uint64_toNat_shift_byte b 48 (by decide)] at this
    exact this
  have e7 : (a.toNat / 2 ^ 56) % 256 = (b.toNat / 2 ^ 56) % 256 := by
    have := congrArg UInt8.toNat h7
    rw [uint64_toNat_shift_byte a 56 (by decide), uint64_toNat_shift_byte b 56 (by decide)] at this
    exact this
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  exact UInt64.toNat_inj.mp (by omega)

private def word64Bytes (w : UInt64) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8,
    (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8]

private theorem pushWord64_toList (bytes : ByteArray) (w : UInt64) :
    (LittleEndian.pushWord64 bytes w).data.toList = bytes.data.toList ++ word64Bytes w := by
  simp [LittleEndian.pushWord64, word64Bytes, ByteArray.push, List.append_assoc]

private theorem word64Bytes_injective {a b : UInt64} (h : word64Bytes a = word64Bytes b) :
    a = b := by
  simp only [word64Bytes, List.cons.injEq, and_true] at h
  exact uint64_eq_of_bytes h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

private theorem flatMap_fixed_pos_injective {α β : Type} {f : α → List β} {k : Nat} (hk : 0 < k)
    (hlen : ∀ x, (f x).length = k) (hinj : ∀ x y, f x = f y → x = y) :
    ∀ {l₁ l₂ : List α}, l₁.flatMap f = l₂.flatMap f → l₁ = l₂
  | [], [], _ => rfl
  | [], b :: l₂, h => by
    have := congrArg List.length h
    simp [hlen] at this
    omega
  | a :: l₁, [], h => by
    have := congrArg List.length h
    simp [hlen] at this
    omega
  | a :: l₁, b :: l₂, h => by
    simp only [List.flatMap_cons] at h
    have hab : f a = f b ∧ l₁.flatMap f = l₂.flatMap f :=
      List.append_inj h (by rw [hlen, hlen])
    rw [hinj a b hab.1, flatMap_fixed_pos_injective hk hlen hinj hab.2]

private theorem foldl_pushWord64_toList (acc : ByteArray) (ws : List UInt64) :
    (ws.foldl LittleEndian.pushWord64 acc).data.toList =
      acc.data.toList ++ ws.flatMap word64Bytes := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, pushWord64_toList, List.append_assoc]

private theorem toBytes_toList (d : Digest64) :
    d.toBytes.data.toList =
      [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7].flatMap word64Bytes := by
  unfold Digest64.toBytes
  rw [foldl_pushWord64_toList]
  rfl

/-- Every `Digest64` encodes to exactly 64 bytes. -/
theorem toBytes_length (d : Digest64) : d.toBytes.data.toList.length = 64 := by
  rw [toBytes_toList]
  simp [word64Bytes]

/-- Every `Digest64.toBytes` has `ByteArray.size = 64`. -/
theorem toBytes_size (d : Digest64) : d.toBytes.size = 64 := by
  rw [ByteArray.size, ← Array.length_toList]
  exact toBytes_length d

end Digest64

/-- `Digest64.toBytes` is injective. -/
theorem digest64_toBytes_injective {d₁ d₂ : Digest64} (h : d₁.toBytes = d₂.toBytes) : d₁ = d₂ := by
  have hlist : d₁.toBytes.data.toList = d₂.toBytes.data.toList :=
    congrArg (fun b => b.data.toList) h
  rw [Digest64.toBytes_toList, Digest64.toBytes_toList] at hlist
  have hws := Digest64.flatMap_fixed_pos_injective (k := 8) (by decide)
    (fun _ => rfl) (fun _ _ => Digest64.word64Bytes_injective) hlist
  cases d₁; cases d₂
  simp only [List.cons.injEq, and_true] at hws
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hws
  rfl

end CertiFri.P3
