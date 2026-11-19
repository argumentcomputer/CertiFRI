import CertiFriProofs.Theory.Oracle.MerkleVerify
import CertiFriProofs.Theory.Oracle.Collision

/-!
# Openings present in a log

When the hash functions of a Merkle tree are a random oracle, what a root can be
opened to is read off the log of the queries made so far. This file defines that
reading and proves its first properties.

* `hashLookup l q` is the answer the log `l` holds for the hash query `q`.
* `MerkleRO.logHasher l` is the hasher of the log `l`. Its digests are terms
  (`MerkleRO.Dig`): a digest in `D`, or an unevaluated hash. It answers with the
  digest the log holds when its inputs are digests and the query is in the log,
  and with the unevaluated term otherwise. An unevaluated term is never a
  digest, and never hashes to one.
* `Opens l root dims index rows` says the log holds an opening of `rows` at
  `index` under `root`: the executable check `Merkle.verifyOpening` accepts for
  some path under the hasher of the log. So every hash evaluation the check
  needs is an entry of `l`.

## Results

* `Opens.mono`: an opening in `l` is in `l'` when `l'` holds every hash answer
  `l` holds. This is the case when `l` is a prefix of `l'` (`Opens.of_prefix`),
  and when `l ⊆ l'` and `l'` has no repeated query (`Opens.of_subset`).
* `Opens.transfer`: the general form, also used for the frozen trees of
  `MerkleFrozen.lean`. An opening in `l'` is in `l` when the hash entries of
  `l'` whose answers lie in a set `P` of digests are in `l`, the inputs of such
  a `node` entry are in `P`, and the root is in `P`.
* `opens_congr`: `Opens` only depends on the hash answers of the log, so a new
  challenge entry changes nothing (`opens_append_chal`).
* `MerkleRO.logCollision_of_collides`: a collision of the hasher of a log is a
  collision of the log.

That an accepting run of the oracle check leaves the opening in the log is in
`MerkleAccept.lean`; binding is in `MerkleBinding.lean`.

There are no assumptions: the statements hold for every log, also one with a
repeated query, where `hashLookup` reads the first entry of a query.

Not covered: openings that share siblings between paths. An opening here is one
path per index, as in `Merkle.verifyOpening`.
-/

namespace CertiFri.Oracle

universe u

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle MerkleRO

/-- The observation that reads the digest of every hash entry. A challenge is
not a digest. With this observation, a collision of a log (`LogCollision`) is
two hash entries with different queries and the same answer. -/
def hashObs : (x : FSQuery Msg Chal (HashQuery T D)) → MerkleAnswer Msg Chal T D x → Option D :=
  FSQuery.liftObs fun _ d => some d

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))]

/-- The answer the log holds for the hash query `q`, if any. -/
def hashLookup (l : Log (MerkleAnswer Msg Chal T D)) (q : HashQuery T D) : Option D :=
  List.dlookup (FSQuery.other q) l

/-- A hash answer in the log stays the answer when the log grows. -/
theorem hashLookup_of_prefix {l l' : Log (MerkleAnswer Msg Chal T D)} (hl : l <+: l')
    {q : HashQuery T D} {y : D} (h : hashLookup l q = some y) : hashLookup l' q = some y :=
  dlookup_of_prefix h hl

/-- A hash answer the log holds is an entry of the log. -/
theorem mem_of_hashLookup {l : Log (MerkleAnswer Msg Chal T D)} {q : HashQuery T D} {y : D}
    (h : hashLookup l q = some y) : (⟨.other q, y⟩ : Sigma (MerkleAnswer Msg Chal T D)) ∈ l :=
  List.of_mem_dlookup h

/-- In a log without a repeated query, a hash entry is the answer the log holds. -/
theorem hashLookup_of_mem {l : Log (MerkleAnswer Msg Chal T D)} (hl : l.NodupKeys)
    {q : HashQuery T D} {y : D} (h : (⟨.other q, y⟩ : Sigma (MerkleAnswer Msg Chal T D)) ∈ l) :
    hashLookup l q = some y :=
  List.mem_dlookup hl h

/-- A new challenge entry changes no hash answer. -/
theorem hashLookup_append_chal (l : Log (MerkleAnswer Msg Chal T D)) {i : ℕ}
    (t : Transcript Msg Chal i) (m : Msg) (c : Chal i) (q : HashQuery T D) :
    hashLookup (l ++ [⟨.chal t m, c⟩]) q = hashLookup l q := by
  unfold hashLookup
  rw [List.dlookup_append, List.dlookup_cons_ne _ _ (by simp), List.dlookup_nil, Option.or_none]

/-- Two hash queries with the same answer in the log are a collision of the log. -/
theorem logCollision_of_hashLookup {l : Log (MerkleAnswer Msg Chal T D)} {q q' : HashQuery T D}
    {y : D} (hq : hashLookup l q = some y) (hq' : hashLookup l q' = some y) (hne : q ≠ q') :
    LogCollision hashObs l :=
  ⟨⟨.other q, y⟩, mem_of_hashLookup hq, ⟨.other q', y⟩, mem_of_hashLookup hq',
    fun h => hne (FSQuery.other.inj h), y, rfl, rfl⟩

/-! ## The hasher of a log -/

namespace MerkleRO

/-- A digest computed against a log: a digest in `D`, or a hash that the log
does not evaluate, kept as a term. -/
inductive Dig (T D : Type) : Type
  /-- A digest. -/
  | known (d : D) : Dig T D
  /-- The hash of entries that is not in the log. -/
  | leaf (xs : Array T) : Dig T D
  /-- A compression that is not in the log, or one of whose inputs is not a digest. -/
  | pair (a b : Dig T D) : Dig T D

/-- The hasher of the log `l`. The hash of entries is the answer the log holds,
or the term `leaf`. The compression of two digests is the answer the log holds,
or the term `pair`; a compression with an input that is not a digest is the
term `pair`. -/
def logHasher (l : Log (MerkleAnswer Msg Chal T D)) : MerkleHasher T (Dig T D) where
  hashRows xs := (hashLookup l (.rows xs)).elim (.leaf xs) .known
  compress a b :=
    match a, b with
    | .known a', .known b' => (hashLookup l (.node a' b')).elim (.pair a b) .known
    | _, _ => .pair a b

variable {l l' : Log (MerkleAnswer Msg Chal T D)}

/-- The hash of entries under the hasher of a log, unfolded. -/
theorem logHasher_hashRows (l : Log (MerkleAnswer Msg Chal T D)) (xs : Array T) :
    (logHasher l).hashRows xs = (hashLookup l (.rows xs)).elim (.leaf xs) .known := rfl

/-- The hash of entries is a digest exactly when the log holds it. -/
theorem logHasher_hashRows_eq_known {xs : Array T} {y : D} :
    (logHasher l).hashRows xs = .known y ↔ hashLookup l (.rows xs) = some y := by
  rw [logHasher_hashRows]
  cases hashLookup l (.rows xs) <;> simp

/-- A compression is a digest exactly when its inputs are digests and the log
holds it. -/
theorem logHasher_compress_eq_known {a b : Dig T D} {y : D} :
    (logHasher l).compress a b = .known y ↔
      ∃ a' b', a = .known a' ∧ b = .known b' ∧ hashLookup l (.node a' b') = some y := by
  cases a <;> cases b <;> try simp [logHasher]
  next a' b' => cases hashLookup l (.node a' b') <;> simp

/-- The hash of entries is a digest or the unevaluated term. -/
theorem logHasher_hashRows_cases (l : Log (MerkleAnswer Msg Chal T D)) (xs : Array T) :
    (logHasher l).hashRows xs = .leaf xs ∨ ∃ y, (logHasher l).hashRows xs = .known y := by
  rw [logHasher_hashRows]
  cases hashLookup l (.rows xs) <;> simp

/-- A compression is a digest or the unevaluated term. -/
theorem logHasher_compress_cases (l : Log (MerkleAnswer Msg Chal T D)) (a b : Dig T D) :
    (logHasher l).compress a b = .pair a b ∨ ∃ y, (logHasher l).compress a b = .known y := by
  cases a <;> cases b <;> try simp [logHasher]
  next a' b' => cases hashLookup l (.node a' b') <;> simp

/-- The hasher of a log only collides on two logged queries with the same
answer: a collision of the hasher is a collision of the log. -/
theorem logCollision_of_collides (h : (logHasher l).Collides) : LogCollision hashObs l := by
  rcases h with ⟨xs, ys, hne, heq⟩ | ⟨⟨a, b⟩, ⟨a', b'⟩, hne, heq⟩
  · rcases logHasher_hashRows_cases l xs with hx | ⟨y, hx⟩
    · rcases logHasher_hashRows_cases l ys with hy | ⟨y, hy⟩
      · rw [hx, hy] at heq
        exact absurd (Dig.leaf.inj heq) hne
      · rw [hx, hy] at heq
        cases heq
    · exact logCollision_of_hashLookup (logHasher_hashRows_eq_known.mp hx)
        (logHasher_hashRows_eq_known.mp (heq ▸ hx)) fun h => hne (HashQuery.rows.inj h)
  · simp only at heq
    rcases logHasher_compress_cases l a b with hx | ⟨y, hx⟩
    · rcases logHasher_compress_cases l a' b' with hy | ⟨y, hy⟩
      · rw [hx, hy] at heq
        obtain ⟨rfl, rfl⟩ := Dig.pair.inj heq
        exact absurd rfl hne
      · rw [hx, hy] at heq
        cases heq
    · obtain ⟨a₀, b₀, rfl, rfl, hq⟩ := logHasher_compress_eq_known.mp hx
      obtain ⟨a₁, b₁, rfl, rfl, hq'⟩ := logHasher_compress_eq_known.mp (heq ▸ hx)
      refine logCollision_of_hashLookup hq hq' fun h => hne ?_
      obtain ⟨rfl, rfl⟩ := HashQuery.node.inj h
      rfl

end MerkleRO

/-! ## Openings -/

open Classical in
/-- The log `l` holds an opening of `rows` at `index` under `root`, for matrices
of dimensions `dims`: for some path, the executable check accepts when every
hash evaluation is looked up in `l`. A hash that `l` does not hold is not a
digest, so the check then fails. -/
def Opens (l : Log (MerkleAnswer Msg Chal T D)) (root : D) (dims : Array Dimensions)
    (index : ℕ) (rows : Array (Array T)) : Prop :=
  ∃ path : List D,
    Merkle.verifyOpening (logHasher l) (.known root) dims index rows (path.map .known) = true

section Opens

variable {l l' : Log (MerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions}
  {index : ℕ} {rows : Array (Array T)}

/-- `Opens` unfolded: the shape of the opening is right, and the climb from the
leaf under the hasher of the log reaches the root. -/
theorem opens_iff :
    Opens l root dims index rows ↔ ∃ path : List D,
      dims.size ≠ 0 ∧ widthsMatch dims.toList rows.toList = true
        ∧ path.length = maxLogHeight dims.toList ∧ index < 2 ^ maxLogHeight dims.toList
        ∧ climb (logHasher l) dims.toList rows.toList (maxLogHeight dims.toList) index
            (groupDigest (logHasher l) dims.toList rows.toList (maxLogHeight dims.toList))
            (path.map .known) = .known root := by
  unfold Opens Merkle.verifyOpening
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq, List.length_map,
    and_assoc, ne_eq, Array.size_eq_zero_iff]

/-- An opening has one row per matrix. -/
theorem Opens.size_rows (h : Opens l root dims index rows) : rows.size = dims.size := by
  obtain ⟨path, _, hw, _⟩ := opens_iff.mp h
  simpa only [Array.length_toList] using widthsMatch_length hw

/-- An opening is at an index of the tallest matrix. -/
theorem Opens.index_lt (h : Opens l root dims index rows) :
    index < 2 ^ maxLogHeight dims.toList := by
  obtain ⟨path, _, _, _, hindex, _⟩ := opens_iff.mp h
  exact hindex

end Opens

/-! ## Moving an opening between logs -/

namespace MerkleRO

section Transfer

variable {l l' : Log (MerkleAnswer Msg Chal T D)} {P : D → Prop}

/-- A hash of entries that is a digest in `P` under `l'` is the same digest
under `l`. -/
theorem hashRows_transfer
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    {xs : Array T} {y : D} (hy : P y) (h : (logHasher l').hashRows xs = .known y) :
    (logHasher l).hashRows xs = .known y :=
  logHasher_hashRows_eq_known.mpr (hA _ y hy (logHasher_hashRows_eq_known.mp h))

/-- A compression that is a digest in `P` under `l'` has inputs in `P` and is
the same digest under `l`. -/
theorem compress_transfer
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    (hB : ∀ a b y, P y → hashLookup l' (.node a b) = some y → P a ∧ P b)
    {a b : Dig T D} {y : D} (hy : P y) (h : (logHasher l').compress a b = .known y) :
    ∃ a' b', a = .known a' ∧ b = .known b' ∧ P a' ∧ P b'
      ∧ (logHasher l).compress (.known a') (.known b') = .known y := by
  obtain ⟨a', b', rfl, rfl, hq⟩ := logHasher_compress_eq_known.mp h
  obtain ⟨ha, hb⟩ := hB a' b' y hy hq
  exact ⟨a', b', rfl, rfl, ha, hb,
    logHasher_compress_eq_known.mpr ⟨a', b', rfl, rfl, hA _ y hy hq⟩⟩

/-- A parent that is a digest in `P` under `l'` is the parent of a digest in
`P`, and is the same digest under `l`. -/
theorem parent_transfer
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    (hB : ∀ a b y, P y → hashLookup l' (.node a b) = some y → P a ∧ P b)
    {index : ℕ} {digest sibling : Dig T D} {y : D} (hy : P y)
    (h : parent (logHasher l') index digest sibling = .known y) :
    ∃ d, P d ∧ digest = .known d ∧ parent (logHasher l) index (.known d) sibling = .known y := by
  by_cases hpar : index % 2 = 0
  · simp only [parent, hpar, ↓reduceIte] at h ⊢
    obtain ⟨a', b', rfl, rfl, ha, _, hc⟩ := compress_transfer hA hB hy h
    exact ⟨a', ha, rfl, hc⟩
  · simp only [parent, hpar, ↓reduceIte] at h ⊢
    obtain ⟨a', b', rfl, rfl, _, hb, hc⟩ := compress_transfer hA hB hy h
    exact ⟨b', hb, rfl, hc⟩

/-- An injection that gives a digest in `P` under `l'` is applied to a digest
in `P`, and gives the same digest under `l`. -/
theorem inject_transfer
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    (hB : ∀ a b y, P y → hashLookup l' (.node a b) = some y → P a ∧ P b)
    {dims : List Dimensions} {rows : List (Array T)} {g : ℕ} {digest : Dig T D} {y : D}
    (hy : P y) (h : inject (logHasher l') dims rows g digest = .known y) :
    ∃ d, P d ∧ digest = .known d ∧ inject (logHasher l) dims rows g (.known d) = .known y := by
  by_cases hg : hasHeight dims g = true
  · simp only [inject, hg, ↓reduceIte] at h ⊢
    obtain ⟨a', b', rfl, hgroup, ha, hb, hc⟩ := compress_transfer hA hB hy h
    refine ⟨a', ha, rfl, ?_⟩
    rw [show groupDigest (logHasher l) dims rows g = .known b' from
      hashRows_transfer hA hb hgroup]
    exact hc
  · simp only [inject, hg, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact ⟨y, hy, h, rfl⟩

/-- A climb that reaches a digest in `P` under `l'` starts from a digest in
`P`, and reaches the same digest under `l`. -/
theorem climb_transfer
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    (hB : ∀ a b y, P y → hashLookup l' (.node a b) = some y → P a ∧ P b)
    (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List (Dig T D)) (h index : ℕ) (digest : Dig T D) (y : D), P y →
      climb (logHasher l') dims rows h index digest path = .known y →
      ∃ d, P d ∧ digest = .known d
        ∧ climb (logHasher l) dims rows h index (.known d) path = .known y
  | [], _, _, _, y, hy, hc => ⟨y, hy, hc, rfl⟩
  | sibling :: path, h, index, digest, y, hy, hc => by
    rw [climb] at hc
    obtain ⟨d₁, hd₁, hinject, hclimb⟩ :=
      climb_transfer hA hB dims rows path (h - 1) (index / 2) _ y hy hc
    obtain ⟨d₂, hd₂, hparent, hinject'⟩ := inject_transfer hA hB hd₁ hinject
    obtain ⟨d, hd, rfl, hparent'⟩ := parent_transfer hA hB hd₂ hparent
    exact ⟨d, hd, rfl, by rw [climb, hparent', hinject', hclimb]⟩

end Transfer

end MerkleRO

section Mono

variable {l l' : Log (MerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions}
  {index : ℕ} {rows : Array (Array T)}

/-- **Moving an opening to another log.** Let `P` be a set of digests such that
every hash entry of `l'` with an answer in `P` is in `l`, and the two inputs of
a `node` entry of `l'` with an answer in `P` are in `P`. Then an opening in `l'`
under a root in `P` is in `l`. -/
theorem Opens.transfer {P : D → Prop}
    (hA : ∀ q y, P y → hashLookup l' q = some y → hashLookup l q = some y)
    (hB : ∀ a b y, P y → hashLookup l' (.node a b) = some y → P a ∧ P b)
    (hroot : P root) (h : Opens l' root dims index rows) : Opens l root dims index rows := by
  obtain ⟨path, hsize, hw, hlen, hindex, hclimb⟩ := opens_iff.mp h
  obtain ⟨d, hd, hleaf, hclimb'⟩ := climb_transfer hA hB _ _ _ _ _ _ root hroot hclimb
  refine opens_iff.mpr ⟨path, hsize, hw, hlen, hindex, ?_⟩
  rw [show groupDigest (logHasher l) dims.toList rows.toList (maxLogHeight dims.toList)
    = .known d from hashRows_transfer hA hd hleaf]
  exact hclimb'

/-- **Monotonicity.** An opening in `l` is in every log that holds the hash
answers `l` holds. -/
theorem Opens.mono (hl : ∀ q y, hashLookup l q = some y → hashLookup l' q = some y)
    (h : Opens l root dims index rows) : Opens l' root dims index rows :=
  h.transfer (P := fun _ => True) (fun q y _ => hl q y) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
    trivial

/-- An opening in a log is in every extension of the log. -/
theorem Opens.of_prefix (hl : l <+: l') (h : Opens l root dims index rows) :
    Opens l' root dims index rows :=
  h.mono fun _ _ hq => hashLookup_of_prefix hl hq

/-- An opening in a log is in every log without a repeated query that contains
its entries. -/
theorem Opens.of_subset (hl : l ⊆ l') (hl' : l'.NodupKeys) (h : Opens l root dims index rows) :
    Opens l' root dims index rows :=
  h.mono fun _ _ hq => hashLookup_of_mem hl' (hl (mem_of_hashLookup hq))

/-- `Opens` only depends on the hash answers the log holds. -/
theorem opens_congr (hl : ∀ q, hashLookup l q = hashLookup l' q) :
    Opens l root dims index rows ↔ Opens l' root dims index rows :=
  ⟨Opens.mono fun q _ hq => hl q ▸ hq, Opens.mono fun q _ hq => hl q ▸ hq⟩

/-- A new challenge entry changes no opening. -/
theorem opens_append_chal {i : ℕ} (t : Transcript Msg Chal i) (m : Msg) (c : Chal i) :
    Opens (l ++ [⟨.chal t m, c⟩]) root dims index rows ↔ Opens l root dims index rows :=
  opens_congr (hashLookup_append_chal l t m c)

end Mono

end CertiFri.Oracle
