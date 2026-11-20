import CertiFriProofs.Exec.Stark.Preamble

/-!
# The first message determines what it encodes

The verifier absorbs its inputs as a flat list of field elements and digests.
The security proof reads the structure back from that list: the activation
bitmaps, the trace heights, the public claims, and for a batch the headers of
all shards and the messages. This file shows that the encodings of the two
entry points are injective on inputs within the size bounds, and packages the
decoders.

## Contents

* `decodeBy enc valid`: the decoder of an encoding, by choice: a valid input
  with the given encoding, if there is one. `decodeBy_eq_some`, `decodeBy_enc`.
* `singleHeaderMessage`: the first message of `Stark.verify`, as a function of
  a header. `firstMessage_eq`.
* `singleHeaderMessage_injective`, `batchFirstMessage_injective`: the first
  messages of `Stark.verify` and of `Stark.verifyBatch` determine the header
  and the preamble, within the size bounds.
* `natOf`: the natural number below a bound that a field element encodes.
* `singleVariant`, `batchVariant`: the layouts of the two entry points
  (`Variant`), with `singleVariant_dec0`, `batchVariant_dec0` and
  `batchVariant_shard`.

## Proof

An encoding is prefix-decodable when the encoding of an input, followed by
anything, determines the input and what follows it. One observation is
prefix-decodable; so are two prefix-decodable encodings one after the other, a
list of known length of prefix-decodable entries, and such a list of any length
up to the bound with its length in front. Each first message is a prefix fixed
by the system followed by such pieces.

## Assumptions

Sizes are absorbed as field elements. Two sizes up to the bound `N` are
distinguished only if they are different field elements: this is the
hypothesis `hcast`, which holds when `N` is below the characteristic. An input
with a size above the bound is not covered.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri

/-! ## Decoding by choice -/

open Classical in
/-- The decoder of the encoding `enc` on the inputs that satisfy `valid`: an
input with the encoding `b`, if there is one. -/
noncomputable def decodeBy {α β : Type} (enc : α → β) (valid : α → Prop) (b : β) : Option α :=
  if h : ∃ a, valid a ∧ enc a = b then some (Classical.choose h) else none

/-- A decoded input is valid and has the given encoding. -/
theorem decodeBy_eq_some {α β : Type} {enc : α → β} {valid : α → Prop} {b : β} {a : α}
    (h : decodeBy enc valid b = some a) : valid a ∧ enc a = b := by
  unfold decodeBy at h
  split at h
  · next hex =>
    cases h
    exact Classical.choose_spec hex
  · cases h

/-- An injective encoding is decoded. -/
theorem decodeBy_enc {α β : Type} {enc : α → β} {valid : α → Prop}
    (hinj : ∀ a a', valid a → valid a' → enc a = enc a' → a = a') {a : α} (ha : valid a) :
    decodeBy enc valid (enc a) = some a := by
  have hex : ∃ a', valid a' ∧ enc a' = enc a := ⟨a, ha, rfl⟩
  rw [decodeBy, dite_eq_left hex]
  exact congrArg some (hinj _ _ (Classical.choose_spec hex).1 ha (Classical.choose_spec hex).2)

/-! ## Prefix-decodable encodings -/

/-- An encoding into lists is *prefix-decodable* on the inputs that satisfy
`valid`: an encoding followed by anything determines the input and what follows
it. -/
private def PrefixDec {α β : Type} (valid : α → Prop) (enc : α → List β) : Prop :=
  ∀ a a', valid a → valid a' → ∀ rest rest', enc a ++ rest = enc a' ++ rest' →
    a = a' ∧ rest = rest'

/-- A prefix-decodable encoding is injective on the valid inputs. -/
private theorem PrefixDec.inj {α β : Type} {valid : α → Prop} {enc : α → List β}
    (h : PrefixDec valid enc) {a a' : α} (ha : valid a) (ha' : valid a') (e : enc a = enc a') :
    a = a' :=
  (h a a' ha ha' [] [] (by rw [e])).1

/-- One entry, given by a function that is injective on the valid inputs, is
prefix-decodable. -/
private theorem prefixDec_singleton {α β : Type} {valid : α → Prop} {f : α → β}
    (hf : ∀ a a', valid a → valid a' → f a = f a' → a = a') :
    PrefixDec valid fun a => [f a] := by
  intro a a' ha ha' rest rest' e
  obtain ⟨e₁, e₂⟩ := List.cons.inj e
  exact ⟨hf a a' ha ha' e₁, e₂⟩

/-- Lists of the same length of valid inputs, each input encoded by a
prefix-decodable encoding, are determined by the concatenation of the
encodings, followed by anything. -/
private theorem PrefixDec.flatMap {α β : Type} {valid : α → Prop} {enc : α → List β}
    (h : PrefixDec valid enc) :
    ∀ l l' : List α, l.length = l'.length → (∀ a ∈ l, valid a) → (∀ a ∈ l', valid a) →
      ∀ rest rest', l.flatMap enc ++ rest = l'.flatMap enc ++ rest' → l = l' ∧ rest = rest' := by
  intro l
  induction l with
  | nil =>
    intro l' hlen _ _ rest rest' e
    obtain rfl : l' = [] := List.length_eq_zero_iff.mp hlen.symm
    exact ⟨rfl, e⟩
  | cons a l ih =>
    intro l' hlen hl hl' rest rest' e
    cases l' with
    | nil => cases hlen
    | cons a' l' =>
      rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at e
      obtain ⟨ha, e₁⟩ := h a a' (hl a List.mem_cons_self) (hl' a' List.mem_cons_self) _ _ e
      obtain ⟨ht, e₂⟩ := ih l' (Nat.succ.inj hlen) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
        (fun x hx => hl' x (List.mem_cons_of_mem _ hx)) rest rest' e₁
      exact ⟨by rw [ha, ht], e₂⟩

/-- Lists of the same length of valid inputs, mapped entry by entry by a
function that is injective on the valid inputs, are determined by the mapped
list, followed by anything. -/
private theorem map_append_inj {α β : Type} {valid : α → Prop} {f : α → β}
    (hf : ∀ a a', valid a → valid a' → f a = f a' → a = a') {l l' : List α}
    (hlen : l.length = l'.length) (hl : ∀ a ∈ l, valid a) (hl' : ∀ a ∈ l', valid a)
    {rest rest' : List β} (e : l.map f ++ rest = l'.map f ++ rest') : l = l' ∧ rest = rest' :=
  (prefixDec_singleton hf).flatMap l l' hlen hl hl' rest rest'
    (by rw [← List.map_eq_flatMap, ← List.map_eq_flatMap]; exact e)

variable {F EF D K : Type} [FieldOps F] [Field K]

/-! ## The two first messages -/

/-- The first message of `Stark.verify`, as a function of the header of the
proof: the activation bitmap, the commitment to the main traces, the trace
heights and the public claims. -/
def singleHeaderMessage (sys : System F D) (h : ShardHeader F D) : RawMsg F EF D :=
  shapeMessage sys ++ activeMessage h.active ++ fixedMessage sys
    ++ [.digest h.stage1Commit] ++ h.logDegrees.toList.map observeNat ++ claimsMessage h.claims

/-- The first message of `Stark.verify` is that of the header of the proof. -/
theorem firstMessage_eq {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (claims : Array (Array F)) :
    firstMessage sys proof claims =
      singleHeaderMessage sys ⟨proof.active, proof.stage1Commit, proof.logDegrees, claims⟩ :=
  rfl

/-- The numbers the bounds allow are at most `N`. -/
structure BoundsLE (sys : System F D) (B : Bounds) (N : ℕ) : Prop where
  /-- The number of circuits. -/
  circuits : sys.circuits.size ≤ N
  /-- The trace heights. -/
  logDegree : sys.maxLogDegree ≤ N
  /-- The number of shards. -/
  shards : B.shards ≤ N
  /-- The number of claims. -/
  claims : B.claims ≤ N
  /-- The number of messages. -/
  messages : B.messages ≤ N
  /-- The length of a claim or a message. -/
  len : B.len ≤ N

/-! ## The pieces of a first message -/

/-- Among the executable values, one is not zero. -/
private theorem one_ne_zero_exec (r : Refines F K) : (1 : F) ≠ 0 := by
  intro h
  have e := congrArg r.toModel h
  rw [r.map_one, r.map_zero] at e
  exact one_ne_zero e

/-- Numbers up to the bound are distinguished by their field elements. -/
private theorem fieldOfNat_inj (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {a b : ℕ} (ha : a ≤ N)
    (hb : b ≤ N) (h : (fieldOfNat a : F) = fieldOfNat b) : a = b :=
  hcast a b ha hb (by rw [← toModel_fieldOfNat r a, ← toModel_fieldOfNat r b, h])

/-- Sizes up to the bound are distinguished by their observations. -/
private theorem observeNat_inj (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {a b : ℕ} (ha : a ≤ N)
    (hb : b ≤ N) (h : (observeNat a : Observation F EF D) = observeNat b) : a = b :=
  fieldOfNat_inj r hcast ha hb (Observation.base.inj h)

/-- An activation bit is determined by its observation. -/
private theorem bit_inj (r : Refines F K) {a a' : Bool}
    (h : (.base (if a then 1 else 0) : Observation F EF D) = .base (if a' then 1 else 0)) :
    a = a' := by
  have e := Observation.base.inj h
  cases a <;> cases a'
  · rfl
  · exact absurd e.symm (one_ne_zero_exec r)
  · exact absurd e (one_ne_zero_exec r)
  · rfl

/-- Activation bitmaps of the same size are determined by their observations,
followed by anything. -/
private theorem activeMessage_append_inj (r : Refines F K) {a a' : Array Bool}
    (hsize : a.size = a'.size) {rest rest' : List (Observation F EF D)}
    (e : activeMessage a ++ rest = activeMessage a' ++ rest') : a = a' ∧ rest = rest' := by
  obtain ⟨hl, e⟩ := map_append_inj (valid := fun _ => True)
    (f := fun b : Bool => (.base (if b then 1 else 0) : Observation F EF D))
    (fun _ _ _ _ => bit_inj r) (l := a.toList) (l' := a'.toList) hsize (fun _ _ => trivial)
    (fun _ _ => trivial) e
  exact ⟨Array.toList_inj.mp hl, e⟩

/-- Lists of the same length of sizes up to the bound are determined by their
observations, followed by anything. -/
private theorem observeNats_append_inj (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {l l' : List ℕ}
    (hlen : l.length = l'.length) (hl : ∀ x ∈ l, x ≤ N) (hl' : ∀ x ∈ l', x ≤ N)
    {rest rest' : List (Observation F EF D)}
    (e : l.map observeNat ++ rest = l'.map observeNat ++ rest') : l = l' ∧ rest = rest' :=
  map_append_inj (fun _ _ ha hb => observeNat_inj r hcast ha hb) hlen hl hl' e

/-- A list of at most `N` valid inputs, encoded as its length followed by the
encodings of its entries, is prefix-decodable. -/
private theorem PrefixDec.lengthPrefixed (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {α : Type}
    {valid : α → Prop} {enc : α → List (Observation F EF D)} (h : PrefixDec valid enc) :
    PrefixDec (fun l : List α => l.length ≤ N ∧ ∀ a ∈ l, valid a)
      fun l => observeNat l.length :: l.flatMap enc := by
  intro l l' hl hl' rest rest' e
  obtain ⟨e₁, e₂⟩ := List.cons.inj e
  exact h.flatMap l l' (observeNat_inj r hcast hl.1 hl'.1 e₁) hl.2 hl'.2 rest rest' e₂

/-- An array of at most `N` field elements, encoded as its size followed by its
entries, is prefix-decodable. -/
private theorem prefixDec_claim (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) :
    PrefixDec (fun c : Array F => c.size ≤ N) fun c =>
      (observeNat c.size :: c.toList.map .base : List (Observation F EF D)) := by
  intro c c' hc hc' rest rest' e
  obtain ⟨e₁, e₂⟩ := List.cons.inj e
  obtain ⟨hl, e₃⟩ := map_append_inj (valid := fun _ => True)
    (fun _ _ _ _ => Observation.base.inj) (observeNat_inj r hcast hc hc' e₁) (fun _ _ => trivial)
    (fun _ _ => trivial) e₂
  exact ⟨Array.toList_inj.mp hl, e₃⟩

/-- At most `N` public claims of length at most `N` are prefix-decodable. -/
private theorem prefixDec_claims (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) :
    PrefixDec (fun cs : Array (Array F) => cs.size ≤ N ∧ ∀ c ∈ cs, c.size ≤ N)
      (claimsMessage : Array (Array F) → List (Observation F EF D)) := by
  intro cs cs' hcs hcs' rest rest' e
  obtain ⟨hl, e⟩ := (prefixDec_claim r hcast).lengthPrefixed r hcast cs.toList cs'.toList
    ⟨hcs.1, fun c hc => hcs.2 c (Array.mem_toList_iff.mp hc)⟩
    ⟨hcs'.1, fun c hc => hcs'.2 c (Array.mem_toList_iff.mp hc)⟩ rest rest' e
  exact ⟨Array.toList_inj.mp hl, e⟩

omit [FieldOps F] in
/-- The trace heights of a header within the bounds are at most `N`. -/
private theorem logDegree_le_of_headerOk {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) {h : ShardHeader F D} (hh : HeaderOk sys B h) :
    ∀ x ∈ h.logDegrees.toList, x ≤ N := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hle := hh.logDegree_le i
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi),
    Option.getD_some] at hle
  rw [Array.getElem_toList]
  exact hle.trans hN.logDegree

omit [FieldOps F] in
/-- A header within the bounds has at most `N` trace heights. -/
private theorem size_logDegrees_le_of_headerOk {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) {h : ShardHeader F D} (hh : HeaderOk sys B h) :
    h.logDegrees.size ≤ N := by
  rw [hh.logDegrees]
  calc (activeIndices h.active).length
      ≤ (List.range h.active.size).length := List.length_filter_le _ _
    _ = sys.circuits.size := by rw [List.length_range, hh.active]
    _ ≤ N := hN.circuits

omit [FieldOps F] in
/-- A header within the bounds has at most `N` public claims, of length at most
`N`. -/
private theorem claims_le_of_headerOk {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) {h : ShardHeader F D} (hh : HeaderOk sys B h) :
    h.claims.size ≤ N ∧ ∀ c ∈ h.claims, c.size ≤ N :=
  ⟨hh.claims.trans hN.claims, fun c hc => (hh.claim_len c hc).trans hN.len⟩

/-- The header of a shard, as the first message of a batch holds it, is
prefix-decodable. -/
private theorem prefixDec_header (r : Refines F K) {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) :
    PrefixDec (HeaderOk sys B) fun h : ShardHeader F D =>
      (activeMessage h.active ++ [.digest h.stage1Commit]
        ++ observeNat h.logDegrees.size :: h.logDegrees.toList.map observeNat
        ++ claimsMessage h.claims : List (Observation F EF D)) := by
  intro h h' hh hh' rest rest' e
  simp only [List.append_assoc, List.cons_append, List.nil_append] at e
  obtain ⟨ha, e⟩ := activeMessage_append_inj r (hh.active.trans hh'.active.symm) e
  obtain ⟨hd, e⟩ := List.cons.inj e
  obtain ⟨hn, e⟩ := List.cons.inj e
  have hlen : h.logDegrees.toList.length = h'.logDegrees.toList.length :=
    observeNat_inj r hcast (size_logDegrees_le_of_headerOk hN hh)
      (size_logDegrees_le_of_headerOk hN hh') hn
  obtain ⟨hl, e⟩ := observeNats_append_inj r hcast hlen (logDegree_le_of_headerOk hN hh)
    (logDegree_le_of_headerOk hN hh') e
  obtain ⟨hc, e⟩ := prefixDec_claims r hcast h.claims h'.claims (claims_le_of_headerOk hN hh)
    (claims_le_of_headerOk hN hh') rest rest' e
  refine ⟨?_, e⟩
  cases h
  cases h'
  simp only [ShardHeader.mk.injEq]
  exact ⟨ha, Observation.digest.inj hd, Array.toList_inj.mp hl, hc⟩

/-- A message of a batch with at most `N` arguments, encoded as the number of
its arguments, the arguments and its multiplicity, is prefix-decodable. -/
private theorem prefixDec_message (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) :
    PrefixDec (fun m : BatchMessage F => m.args.size ≤ N) fun m =>
      (observeNat m.args.size :: m.args.toList.map .base ++ [.base m.multiplicity] :
        List (Observation F EF D)) := by
  intro m m' hm hm' rest rest' e
  simp only [List.append_assoc] at e
  obtain ⟨hargs, e⟩ := prefixDec_claim r hcast m.args m'.args hm hm' _ _ e
  obtain ⟨hmul, e⟩ := List.cons.inj e
  refine ⟨?_, e⟩
  cases m
  cases m'
  simp only [BatchMessage.mk.injEq]
  exact ⟨hargs, Observation.base.inj hmul⟩

/-! ## The first message determines its input -/

/-- **The first message of `Stark.verify` determines the header.** -/
theorem singleHeaderMessage_injective (r : Refines F K) {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {h h' : ShardHeader F D} (hh : HeaderOk sys B h) (hh' : HeaderOk sys B h')
    (heq : (singleHeaderMessage sys h : RawMsg F EF D) = singleHeaderMessage sys h') : h = h' := by
  simp only [singleHeaderMessage, List.append_assoc, List.cons_append, List.nil_append] at heq
  obtain ⟨ha, e⟩ := activeMessage_append_inj r (hh.active.trans hh'.active.symm)
    (List.append_cancel_left heq)
  obtain ⟨hd, e⟩ := List.cons.inj (List.append_cancel_left e)
  have hlen : h.logDegrees.toList.length = h'.logDegrees.toList.length := by
    rw [Array.length_toList, Array.length_toList, hh.logDegrees, hh'.logDegrees, ha]
  obtain ⟨hl, e⟩ := observeNats_append_inj r hcast hlen (logDegree_le_of_headerOk hN hh)
    (logDegree_le_of_headerOk hN hh') e
  have hc := (prefixDec_claims r hcast).inj (claims_le_of_headerOk hN hh)
    (claims_le_of_headerOk hN hh') e
  cases h
  cases h'
  simp only [ShardHeader.mk.injEq]
  exact ⟨ha, Observation.digest.inj hd, Array.toList_inj.mp hl, hc⟩

/-- **The first message of `Stark.verifyBatch` determines the preamble.** -/
theorem batchFirstMessage_injective (r : Refines F K) {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {p p' : BatchPreamble F D} (hp : PreOk sys B p) (hp' : PreOk sys B p')
    (heq : (batchFirstMessage sys p : RawMsg F EF D) = batchFirstMessage sys p') : p = p' := by
  rw [batchFirstMessage, batchFirstMessage,
    List.append_assoc (shapeMessage sys ++ fixedMessage sys),
    List.append_assoc (shapeMessage sys ++ fixedMessage sys)] at heq
  obtain ⟨hhs, e⟩ := (prefixDec_header r hN hcast).lengthPrefixed r hcast p.headers.toList
    p'.headers.toList
    ⟨hp.shards.trans hN.shards, fun h hh => hp.header h (Array.mem_toList_iff.mp hh)⟩
    ⟨hp'.shards.trans hN.shards, fun h hh => hp'.header h (Array.mem_toList_iff.mp hh)⟩ _ _
    (List.append_cancel_left heq)
  have hms := ((prefixDec_message r hcast).lengthPrefixed r hcast).inj
    (a := p.messages.toList) (a' := p'.messages.toList)
    ⟨hp.messages.trans hN.messages,
      fun m hm => (hp.message_len m (Array.mem_toList_iff.mp hm)).trans hN.len⟩
    ⟨hp'.messages.trans hN.messages,
      fun m hm => (hp'.message_len m (Array.mem_toList_iff.mp hm)).trans hN.len⟩ e
  cases p
  cases p'
  simp only [BatchPreamble.mk.injEq]
  exact ⟨Array.toList_inj.mp hhs, Array.toList_inj.mp hms⟩

/-! ## The layouts of the two entry points -/

open Classical in
/-- The natural number up to `N` that the field element `b` encodes; zero if
there is none. -/
noncomputable def natOf (N : ℕ) (b : F) : ℕ :=
  if h : ∃ n, n ≤ N ∧ fieldOfNat n = b then Nat.find h else 0

/-- A number up to the bound is decoded from its field element. -/
theorem natOf_fieldOfNat (r : Refines F K) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) {n : ℕ} (hn : n ≤ N) :
    natOf N (fieldOfNat n : F) = n := by
  have hex : ∃ m, m ≤ N ∧ (fieldOfNat m : F) = fieldOfNat n := ⟨n, hn, rfl⟩
  rw [natOf, dite_eq_left hex]
  classical exact fieldOfNat_inj r hcast (Nat.find_spec hex).1 hn (Nat.find_spec hex).2

/-- The layout of `Stark.verify`: the first message encodes a header, read as
the preamble of a batch of one shard with no message; the chain is about
shard `0`. -/
noncomputable def singleVariant (sys : System F D) (B : Bounds) : Variant F EF D where
  dec0 m := (decodeBy (singleHeaderMessage sys) (HeaderOk sys B) m).map fun h => ⟨#[h], #[]⟩
  shard _ := 0

/-- The layout of `Stark.verifyBatch`: the first message encodes the preamble,
and the message of round `2` holds the position of the shard after the
absorbed challenge. -/
noncomputable def batchVariant (sys : System F D) (B : Bounds) (N : ℕ) : Variant F EF D where
  dec0 := decodeBy (batchFirstMessage sys) (PreOk sys B)
  shard m :=
    match m with
    | _ :: .base b :: _ => natOf N b
    | _ => 0

/-- The first message of `Stark.verify` is decoded. -/
theorem singleVariant_dec0 (r : Refines F K) {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {h : ShardHeader F D} (hh : HeaderOk sys B h) :
    (singleVariant (EF := EF) sys B).dec0 (singleHeaderMessage sys h) = some ⟨#[h], #[]⟩ := by
  have hdec := decodeBy_enc (enc := singleHeaderMessage (EF := EF) sys)
    (fun _ _ ha ha' e => singleHeaderMessage_injective r hN hcast ha ha' e) hh
  simp only [singleVariant, hdec, Option.map_some]

/-- The first message of `Stark.verifyBatch` is decoded. -/
theorem batchVariant_dec0 (r : Refines F K) {sys : System F D} {B : Bounds} {N : ℕ}
    (hN : BoundsLE sys B N) (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b)
    {p : BatchPreamble F D} (hp : PreOk sys B p) :
    (batchVariant (EF := EF) sys B N).dec0 (batchFirstMessage sys p) = some p :=
  decodeBy_enc (fun _ _ ha ha' e => batchFirstMessage_injective r hN hcast ha ha' e) hp

/-- The position of a shard is decoded from the message of round `2`. -/
theorem batchVariant_shard (r : Refines F K) (sys : System F D) (B : Bounds) {N : ℕ}
    (hcast : ∀ a b : ℕ, a ≤ N → b ≤ N → (a : K) = (b : K) → a = b) (γ : EF) {i : ℕ} (hi : i ≤ N)
    (rest : RawMsg F EF D) :
    (batchVariant (EF := EF) sys B N).shard (.ext γ :: observeNat i :: rest) = i :=
  natOf_fieldOfNat r hcast hi

end CertiFri.Exec.Stark
