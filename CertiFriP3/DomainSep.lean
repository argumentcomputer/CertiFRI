import CertiFriP3.Hashers
import CertiFriP3.Challenger

/-!
# Domain-separated BLAKE3 Merkle hashers and Fiat–Shamir challenger

Plonky3's stock BLAKE3 configuration (`CertiFriP3/Hashers.lean`,
`CertiFriP3/Challenger.lean`) invokes the same plain BLAKE3 byte hash for
Merkle leaf hashing, Merkle 2-to-1 node compression, and Fiat–Shamir
transcript hashing. The random-oracle security model (`Proofs/`) models these
three operations as three independent query types (`HashQuery.rows`,
`HashQuery.node`, `FSQuery.chal`).

This module provides an opt-in domain-separated BLAKE3 parameterization that
discharges that domain-separation gap while leaving stock Plonky3 `baseHasher`,
`extHasher`, and `challenger` untouched for backwards compatibility with
existing Plonky3 vectors.

## Encoding

Each of the three roles prefixes its BLAKE3 input with a distinct tag byte from
`DomainSep`:

* `sep.leafTag` (default `0x00`): Merkle leaf / row hashing.
* `sep.nodeTag` (default `0x01`): Merkle internal 2-to-1 compression of two
  32-byte digests.
* `sep.transcriptTag` (default `0x02`): Fiat–Shamir challenger transcript
  hashing.

## Theorems proved

All proofs stay in core Lean (no Mathlib, no `sorry`, no `native_decide`):

* `DomainSep.leafBytes_ne_nodeBytes`, `DomainSep.leafBytes_ne_transcriptBytes`,
  `DomainSep.nodeBytes_ne_transcriptBytes`: the three BLAKE3 input domains are
  pairwise disjoint.
* `DomainSep.tagBytes_injective`, `DomainSep.nodeBytes_injective`: fixed-tag
  and internal-node encodings are injective.
* `DomainSep.rowBytes_injective`, `DomainSep.extRowBytes_injective`: canonical
  row serializations are injective, so distinct rows hash to distinct BLAKE3
  inputs.
-/

namespace CertiFri.P3

/-- Explicit domain-separation tags for the three oracle roles of a BLAKE3-based
FRI verifier: Merkle leaf hashing, Merkle internal 2-to-1 compression, and
Fiat–Shamir transcript hashing. -/
structure DomainSep where
  /-- Single-byte tag prefixed to Merkle leaf (row) hash inputs. -/
  leafTag : UInt8
  /-- Single-byte tag prefixed to Merkle internal 2-to-1 node hash inputs. -/
  nodeTag : UInt8
  /-- Single-byte tag prefixed to Fiat–Shamir transcript hash inputs. -/
  transcriptTag : UInt8
  /-- Leaf and node tags are distinct. -/
  leaf_ne_node : leafTag ≠ nodeTag
  /-- Leaf and transcript tags are distinct. -/
  leaf_ne_transcript : leafTag ≠ transcriptTag
  /-- Node and transcript tags are distinct. -/
  node_ne_transcript : nodeTag ≠ transcriptTag

namespace DomainSep

/-- The standard domain-separation tags: `0x00` for Merkle leaves, `0x01` for
Merkle internal nodes, and `0x02` for Fiat–Shamir transcript hashing. -/
def standard : DomainSep where
  leafTag := 0x00
  nodeTag := 0x01
  transcriptTag := 0x02
  leaf_ne_node := by decide
  leaf_ne_transcript := by decide
  node_ne_transcript := by decide

/-- Prefix a payload with a single domain-separation tag byte. -/
def tagBytes (tag : UInt8) (payload : ByteArray) : ByteArray :=
  ByteArray.mk (#[tag] ++ payload.data)

/-- Domain-separated BLAKE3 input for a Merkle leaf payload. -/
def leafBytes (sep : DomainSep) (payload : ByteArray) : ByteArray :=
  tagBytes sep.leafTag payload

/-- Domain-separated BLAKE3 input for compressing two 32-byte Merkle digests. -/
def nodeBytes (sep : DomainSep) (left right : Digest) : ByteArray :=
  tagBytes sep.nodeTag (left.toBytes ++ right.toBytes)

/-- Domain-separated BLAKE3 input for hashing a Fiat–Shamir challenger buffer. -/
def transcriptBytes (sep : DomainSep) (input : ByteArray) : ByteArray :=
  tagBytes sep.transcriptTag input

/-! ## Disjointness of the three BLAKE3 input domains -/

theorem tagBytes_toList (tag : UInt8) (payload : ByteArray) :
    (tagBytes tag payload).data.toList = tag :: payload.data.toList := by
  simp [tagBytes]

theorem tagBytes_ne_of_ne_tag {t₁ t₂ : UInt8} (h : t₁ ≠ t₂) (p₁ p₂ : ByteArray) :
    tagBytes t₁ p₁ ≠ tagBytes t₂ p₂ := by
  intro heq
  have hlist : (tagBytes t₁ p₁).data.toList = (tagBytes t₂ p₂).data.toList :=
    congrArg (fun b => b.data.toList) heq
  rw [tagBytes_toList, tagBytes_toList] at hlist
  exact h (List.cons.inj hlist).1

theorem tagBytes_injective {tag : UInt8} {p₁ p₂ : ByteArray}
    (h : tagBytes tag p₁ = tagBytes tag p₂) : p₁ = p₂ := by
  have hlist : (tagBytes tag p₁).data.toList = (tagBytes tag p₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  rw [tagBytes_toList, tagBytes_toList] at hlist
  cases p₁ with | mk d₁ =>
  cases p₂ with | mk d₂ =>
  exact congrArg ByteArray.mk (Array.toList_inj.mp (List.cons.inj hlist).2)

/-- A Merkle leaf input never collides with a Merkle internal-node input. -/
theorem leafBytes_ne_nodeBytes (sep : DomainSep) (payload : ByteArray) (left right : Digest) :
    sep.leafBytes payload ≠ sep.nodeBytes left right :=
  tagBytes_ne_of_ne_tag sep.leaf_ne_node _ _

/-- A Merkle leaf input never collides with a Fiat–Shamir transcript input. -/
theorem leafBytes_ne_transcriptBytes (sep : DomainSep) (payload input : ByteArray) :
    sep.leafBytes payload ≠ sep.transcriptBytes input :=
  tagBytes_ne_of_ne_tag sep.leaf_ne_transcript _ _

/-- A Merkle internal-node input never collides with a Fiat–Shamir transcript input. -/
theorem nodeBytes_ne_transcriptBytes (sep : DomainSep) (left right : Digest) (input : ByteArray) :
    sep.nodeBytes left right ≠ sep.transcriptBytes input :=
  tagBytes_ne_of_ne_tag sep.node_ne_transcript _ _

/-! ## Injectivity of canonical encodings -/

private theorem uint32_toNat_shift_byte (w k : UInt32) (hk : k.toNat < 32) :
    ((w >>> k).toUInt8).toNat = (w.toNat / 2 ^ k.toNat) % 256 := by
  have hmod : k.toNat % 32 = k.toNat := Nat.mod_eq_of_lt hk
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, hmod, Nat.shiftRight_eq_div_pow]

private theorem uint32_eq_of_bytes {a b : UInt32}
    (h0 : a.toUInt8 = b.toUInt8)
    (h1 : (a >>> 8).toUInt8 = (b >>> 8).toUInt8)
    (h2 : (a >>> 16).toUInt8 = (b >>> 16).toUInt8)
    (h3 : (a >>> 24).toUInt8 = (b >>> 24).toUInt8) : a = b := by
  have e0 : a.toNat % 256 = b.toNat % 256 := by
    have := congrArg UInt8.toNat h0
    simpa [UInt32.toNat_toUInt8] using this
  have e1 : (a.toNat / 256) % 256 = (b.toNat / 256) % 256 := by
    have := congrArg UInt8.toNat h1
    rw [uint32_toNat_shift_byte a 8 (by decide), uint32_toNat_shift_byte b 8 (by decide)] at this
    exact this
  have e2 : (a.toNat / 65536) % 256 = (b.toNat / 65536) % 256 := by
    have := congrArg UInt8.toNat h2
    rw [uint32_toNat_shift_byte a 16 (by decide), uint32_toNat_shift_byte b 16 (by decide)] at this
    exact this
  have e3 : (a.toNat / 16777216) % 256 = (b.toNat / 16777216) % 256 := by
    have := congrArg UInt8.toNat h3
    rw [uint32_toNat_shift_byte a 24 (by decide), uint32_toNat_shift_byte b 24 (by decide)] at this
    exact this
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  exact UInt32.toNat_inj.mp (by omega)

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

private def word32Bytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

private def goldilocksBytes (a : Goldilocks) : List UInt8 :=
  let w := a.val
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8,
    (w >>> 32).toUInt8, (w >>> 40).toUInt8, (w >>> 48).toUInt8, (w >>> 56).toUInt8]

private theorem pushWord32_toList (bytes : ByteArray) (w : UInt32) :
    (LittleEndian.pushWord32 bytes w).data.toList = bytes.data.toList ++ word32Bytes w := by
  simp [LittleEndian.pushWord32, word32Bytes, ByteArray.push, List.append_assoc]

private theorem pushBytes_toList (bytes : ByteArray) (a : Goldilocks) :
    (a.pushBytes bytes).data.toList = bytes.data.toList ++ goldilocksBytes a := by
  simp [Goldilocks.pushBytes, goldilocksBytes, ByteArray.push, List.append_assoc]

private theorem word32Bytes_injective {a b : UInt32} (h : word32Bytes a = word32Bytes b) :
    a = b := by
  simp only [word32Bytes, List.cons.injEq, and_true] at h
  exact uint32_eq_of_bytes h.1 h.2.1 h.2.2.1 h.2.2.2

private theorem goldilocksBytes_injective {a b : Goldilocks}
    (h : goldilocksBytes a = goldilocksBytes b) : a = b := by
  simp only [goldilocksBytes, List.cons.injEq, and_true] at h
  exact Goldilocks.ext (uint64_eq_of_bytes h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2)

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

private theorem foldl_pushWord32_toList (acc : ByteArray) (ws : List UInt32) :
    (ws.foldl LittleEndian.pushWord32 acc).data.toList =
      acc.data.toList ++ ws.flatMap word32Bytes := by
  induction ws generalizing acc with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, pushWord32_toList, List.append_assoc]

private theorem digest_toBytes_toList (d : Digest) :
    d.toBytes.data.toList = [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7].flatMap word32Bytes := by
  unfold Digest.toBytes
  rw [foldl_pushWord32_toList]
  rfl

theorem digest_toBytes_length (d : Digest) : d.toBytes.data.toList.length = 32 := by
  rw [digest_toBytes_toList]
  simp [word32Bytes]

/-- `Digest.toBytes` is injective. -/
theorem digest_toBytes_injective {d₁ d₂ : Digest} (h : d₁.toBytes = d₂.toBytes) : d₁ = d₂ := by
  have hlist : d₁.toBytes.data.toList = d₂.toBytes.data.toList :=
    congrArg (fun b => b.data.toList) h
  rw [digest_toBytes_toList, digest_toBytes_toList] at hlist
  have hws := flatMap_fixed_pos_injective (k := 4) (by decide)
    (fun _ => rfl) (fun _ _ => word32Bytes_injective) hlist
  cases d₁; cases d₂
  simp only [List.cons.injEq, and_true] at hws
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hws
  rfl

/-- `nodeBytes` is injective in both child digests. -/
theorem nodeBytes_injective (sep : DomainSep) {l₁ r₁ l₂ r₂ : Digest}
    (h : sep.nodeBytes l₁ r₁ = sep.nodeBytes l₂ r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hpay := tagBytes_injective h
  have hlist : (l₁.toBytes ++ r₁.toBytes).data.toList = (l₂.toBytes ++ r₂.toBytes).data.toList :=
    congrArg (fun b => b.data.toList) hpay
  rw [ByteArray.data_append, ByteArray.data_append, Array.toList_append, Array.toList_append] at hlist
  have hlr := List.append_inj hlist (by rw [digest_toBytes_length, digest_toBytes_length])
  refine ⟨digest_toBytes_injective ?_, digest_toBytes_injective ?_⟩
  · cases h1 : l₁.toBytes; cases h2 : l₂.toBytes
    rw [h1, h2] at hlr
    exact congrArg ByteArray.mk (Array.toList_inj.mp hlr.1)
  · cases h1 : r₁.toBytes; cases h2 : r₂.toBytes
    rw [h1, h2] at hlr
    exact congrArg ByteArray.mk (Array.toList_inj.mp hlr.2)

private theorem foldl_pushBytes_toList (acc : ByteArray) (xs : List Goldilocks) :
    (xs.foldl Goldilocks.pushBytes acc).data.toList =
      acc.data.toList ++ xs.flatMap goldilocksBytes := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, pushBytes_toList, List.append_assoc]

/-- `Hashers.rowBytes` is injective on canonical Goldilocks rows. -/
theorem rowBytes_injective {r₁ r₂ : Array Goldilocks}
    (h : Hashers.rowBytes r₁ = Hashers.rowBytes r₂) : r₁ = r₂ := by
  have hlist : (Hashers.rowBytes r₁).data.toList = (Hashers.rowBytes r₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [Hashers.rowBytes, ← Array.foldl_toList, foldl_pushBytes_toList] at hlist
  have hnil : ∀ n, (ByteArray.emptyWithCapacity n).data.toList = [] := fun _ => rfl
  rw [hnil, hnil, List.nil_append, List.nil_append] at hlist
  exact Array.toList_inj.mp
    (flatMap_fixed_pos_injective (k := 8) (by decide) (fun _ => rfl)
      (fun _ _ => goldilocksBytes_injective) hlist)

private def extBytes (e : GoldilocksExt) : List UInt8 :=
  goldilocksBytes e.c0 ++ goldilocksBytes e.c1

private theorem foldl_extPushBytes_toList (acc : ByteArray) (xs : List GoldilocksExt) :
    (xs.foldl (fun bytes e => Goldilocks.pushBytes (Goldilocks.pushBytes bytes e.c0) e.c1)
        acc).data.toList =
      acc.data.toList ++ xs.flatMap extBytes := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, pushBytes_toList, extBytes, List.append_assoc]

/-- `Hashers.extRowBytes` is injective on quadratic-extension rows. -/
theorem extRowBytes_injective {r₁ r₂ : Array GoldilocksExt}
    (h : Hashers.extRowBytes r₁ = Hashers.extRowBytes r₂) : r₁ = r₂ := by
  have hlist : (Hashers.extRowBytes r₁).data.toList = (Hashers.extRowBytes r₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [Hashers.extRowBytes, ← Array.foldl_toList, foldl_extPushBytes_toList] at hlist
  have hnil : ∀ n, (ByteArray.emptyWithCapacity n).data.toList = [] := fun _ => rfl
  rw [hnil, hnil, List.nil_append, List.nil_append] at hlist
  refine Array.toList_inj.mp
    (flatMap_fixed_pos_injective (k := 16) (by decide) (fun e => by simp [extBytes, goldilocksBytes])
      (fun e₁ e₂ he => ?_) hlist)
  have hpair := List.append_inj he (by simp [goldilocksBytes])
  cases e₁; cases e₂
  dsimp only at hpair
  rw [goldilocksBytes_injective hpair.1, goldilocksBytes_injective hpair.2]

private def ext3Bytes (e : GoldilocksExt3) : List UInt8 :=
  goldilocksBytes e.c0 ++ goldilocksBytes e.c1 ++ goldilocksBytes e.c2

private theorem foldl_ext3PushBytes_toList (acc : ByteArray) (xs : List GoldilocksExt3) :
    (xs.foldl GoldilocksExt3.pushBytes acc).data.toList =
      acc.data.toList ++ xs.flatMap ext3Bytes := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    simp only [List.foldl_cons, List.flatMap_cons, ih, GoldilocksExt3.pushBytes, pushBytes_toList,
      ext3Bytes, List.append_assoc]

/-- `Hashers.ext3RowBytes` is injective on cubic-extension rows. -/
theorem ext3RowBytes_injective {r₁ r₂ : Array GoldilocksExt3}
    (h : Hashers.ext3RowBytes r₁ = Hashers.ext3RowBytes r₂) : r₁ = r₂ := by
  have hlist : (Hashers.ext3RowBytes r₁).data.toList = (Hashers.ext3RowBytes r₂).data.toList :=
    congrArg (fun b => b.data.toList) h
  simp only [Hashers.ext3RowBytes, ← Array.foldl_toList, foldl_ext3PushBytes_toList] at hlist
  have hnil : ∀ n, (ByteArray.emptyWithCapacity n).data.toList = [] := fun _ => rfl
  rw [hnil, hnil, List.nil_append, List.nil_append] at hlist
  refine Array.toList_inj.mp
    (flatMap_fixed_pos_injective (k := 24) (by decide)
      (fun e => by simp [ext3Bytes, goldilocksBytes])
      (fun e₁ e₂ he => ?_) hlist)
  have h12 := List.append_inj he (by simp [goldilocksBytes])
  have h01 := List.append_inj h12.1 (by simp [goldilocksBytes])
  cases e₁; cases e₂
  dsimp only at h12 h01
  rw [goldilocksBytes_injective h01.1, goldilocksBytes_injective h01.2,
    goldilocksBytes_injective h12.2]

end DomainSep

/-! ## Opt-in domain-separated hashers and challenger -/

/-- Opt-in domain-separated Merkle hasher over `Goldilocks` using BLAKE3 with
explicit distinct leaf and internal-node tags. -/
def baseHasherSep (sep : DomainSep := .standard) : MerkleHasher Goldilocks Digest where
  hashRows row := Blake3.hash (sep.leafBytes (Hashers.rowBytes row))
  compress left right := Blake3.hash (sep.nodeBytes left right)

/-- Opt-in domain-separated Merkle hasher over `GoldilocksExt` using BLAKE3 with
explicit distinct leaf and internal-node tags. -/
def extHasherSep (sep : DomainSep := .standard) : MerkleHasher GoldilocksExt Digest where
  hashRows row := Blake3.hash (sep.leafBytes (Hashers.extRowBytes row))
  compress left right := Blake3.hash (sep.nodeBytes left right)

/-- Opt-in domain-separated Merkle hasher over `GoldilocksExt3` using BLAKE3 with
explicit distinct leaf and internal-node tags. -/
def ext3HasherSep (sep : DomainSep := .standard) : MerkleHasher GoldilocksExt3 Digest where
  hashRows row := Blake3.hash (sep.leafBytes (Hashers.ext3RowBytes row))
  compress left right := Blake3.hash (sep.nodeBytes left right)

/-- Opt-in domain-separated BLAKE3 byte hash for the Fiat–Shamir challenger. -/
def blake3Transcript (sep : DomainSep := .standard) (input : ByteArray) : ByteArray :=
  blake3 (sep.transcriptBytes input)

/-- Opt-in domain-separated BLAKE3 challenger over `Goldilocks` / `GoldilocksExt`,
prefixing every transcript hash with `sep.transcriptTag`. -/
def challengerSep (sep : DomainSep := .standard) :
    Challenger ChallengerState Goldilocks GoldilocksExt Digest :=
  challengerWith (blake3Transcript sep)

/-- Opt-in domain-separated BLAKE3 challenger over `Goldilocks` / `GoldilocksExt3`,
prefixing every transcript hash with `sep.transcriptTag`. -/
def challenger3Sep (sep : DomainSep := .standard) :
    Challenger ChallengerState Goldilocks GoldilocksExt3 Digest :=
  challenger3With (blake3Transcript sep)

end CertiFri.P3
