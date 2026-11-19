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

end CertiFri.P3
