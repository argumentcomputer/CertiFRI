import CertiFriProofs.Theory.Oracle.MerkleOpens

/-!
# Accepted openings are in the log

The link between the oracle check of an opening (`verifyOpeningM`) and the
openings a log holds (`Opens`).

## Results

* `opens_of_outcome_verifyOpeningM`: if the oracle check of an opening, run from
  any log, returns `true`, then the final log holds the opening.
* `opens_of_outcome_verifyOpeningsM`: the same for each query of an accepted
  check at several indices.
* `opens_iff_outcome`: a log holds an opening exactly when the oracle check, run
  from that log, accepts for some path without adding an entry.

There are no assumptions on the log the run starts from.

Not covered: probabilities. These are statements about every outcome of a run.
-/

namespace CertiFri.Oracle

universe u

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle MerkleRO

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))]

/-! ## An accepting run leaves the opening in the log -/

namespace MerkleRO

section Outcome

variable {l₀ l₁ l : Log (MerkleAnswer Msg Chal T D)}

/-- After the query for a hash of entries, the hasher of the log gives the answer. -/
theorem hashRows_of_outcome {xs : Array T} {y : D} (h : Outcome (hashRowsM xs) l₀ y l₁)
    (hl : l₁ <+: l) : (logHasher l).hashRows xs = .known y :=
  logHasher_hashRows_eq_known.mpr (hashLookup_of_prefix hl (Outcome.dlookup_query h))

/-- After the query for a compression, the hasher of the log gives the answer. -/
theorem compress_of_outcome {a b y : D} (h : Outcome (compressM a b) l₀ y l₁) (hl : l₁ <+: l) :
    (logHasher l).compress (.known a) (.known b) = .known y :=
  logHasher_compress_eq_known.mpr
    ⟨a, b, rfl, rfl, hashLookup_of_prefix hl (Outcome.dlookup_query h)⟩

/-- After `parentM`, the hasher of the log gives its result. -/
theorem parent_of_outcome {index : ℕ} {digest sibling y : D}
    (h : Outcome (parentM index digest sibling) l₀ y l₁) (hl : l₁ <+: l) :
    parent (logHasher l) index (.known digest) (.known sibling) = .known y := by
  unfold parentM at h
  unfold parent
  split at h
  · next hpar => rw [ite_eq_left hpar]; exact compress_of_outcome h hl
  · next hpar => rw [ite_eq_right hpar]; exact compress_of_outcome h hl

/-- After `injectM`, the hasher of the log gives its result. -/
theorem inject_of_outcome {dims : List Dimensions} {rows : List (Array T)} {g : ℕ}
    {digest y : D} (h : Outcome (injectM dims rows g digest) l₀ y l₁) (hl : l₁ <+: l) :
    inject (logHasher l) dims rows g (.known digest) = .known y := by
  unfold injectM at h
  unfold inject
  split at h
  · next hg =>
    obtain ⟨group, l', hgroup, hc⟩ := outcome_bind.mp h
    rw [ite_eq_left hg, show groupDigest (logHasher l) dims rows g = .known group from
      hashRows_of_outcome hgroup (hc.prefix.trans hl)]
    exact compress_of_outcome hc hl
  · next hg =>
    obtain ⟨rfl, _⟩ := h
    rw [ite_eq_right hg]

/-- After `climbM`, the hasher of the log climbs to its result. -/
theorem climb_of_outcome (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List D) (h index : ℕ) (digest y : D) (l₀ l₁ : Log (MerkleAnswer Msg Chal T D)),
      Outcome (climbM dims rows h index digest path) l₀ y l₁ → l₁ <+: l →
      climb (logHasher l) dims rows h index (.known digest) (path.map .known) = .known y
  | [], _, _, _, _, _, _, hc, _ => by
    obtain ⟨rfl, _⟩ := hc
    rfl
  | sibling :: path, h, index, digest, y, l₀, l₁, hc, hl => by
    rw [climbM] at hc
    obtain ⟨node, la, hnode, hc⟩ := outcome_bind.mp hc
    obtain ⟨digest', lb, hinject, hc⟩ := outcome_bind.mp hc
    have hlb : lb <+: l := hc.prefix.trans hl
    rw [List.map_cons, climb, parent_of_outcome hnode (hinject.prefix.trans hlb),
      inject_of_outcome hinject hlb]
    exact climb_of_outcome dims rows path _ _ digest' y lb l₁ hc hl

end Outcome

/-- If `allM` returns `true`, each computation of the list returned `true` in
its turn, and left a prefix of the final log. -/
theorem outcome_allM {X : Type*} {Y : X → Type*} [DecidableEq X] :
    ∀ {cs : List (OracleComp Y Bool)} {l₀ l : Log Y}, Outcome (allM cs) l₀ true l →
      ∀ c ∈ cs, ∃ l₁ l₂, Outcome c l₁ true l₂ ∧ l₂ <+: l
  | [], _, _, _, _, hc => nomatch hc
  | c :: cs, l₀, l, h, c', hc' => by
    rw [allM] at h
    obtain ⟨b, l₁, hb, hrest⟩ := outcome_bind.mp h
    cases b with
    | false => exact absurd hrest.1 (by simp)
    | true =>
      rw [ite_eq_left rfl] at hrest
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨l₀, l₁, hb, hrest.prefix⟩
      · exact outcome_allM hrest c' hc'

end MerkleRO

section Accept

variable [DecidableEq D] {l₀ l : Log (MerkleAnswer Msg Chal T D)} {root : D}
  {dims : Array Dimensions}

/-- **An accepted opening is in the log.** If the oracle check of an opening,
run from any log, returns `true`, then the final log holds the opening. -/
theorem opens_of_outcome_verifyOpeningM {index : ℕ} {rows : Array (Array T)} {path : List D}
    (h : Outcome (verifyOpeningM root dims index rows path) l₀ true l) :
    Opens l root dims index rows := by
  unfold verifyOpeningM at h
  split at h
  · next hshape =>
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hshape
    obtain ⟨leaf, l₁, hleaf, h⟩ := outcome_bind.mp h
    obtain ⟨digest, l₂, hclimb, hroot, rfl⟩ := outcome_bind.mp h
    obtain rfl : digest = root := by simpa using hroot.symm
    refine opens_iff.mpr ⟨path, by simpa using hshape.1.1.1, hshape.1.1.2, hshape.1.2,
      hshape.2, ?_⟩
    rw [show groupDigest (logHasher l) dims.toList rows.toList (maxLogHeight dims.toList)
      = .known leaf from hashRows_of_outcome hleaf hclimb.prefix]
    exact climb_of_outcome _ _ path _ _ leaf digest l₁ l hclimb (List.prefix_refl l)
  · exact absurd h.1 (by simp)

/-- **Each opening of an accepted check at several indices is in the log.** If
the oracle check of an opening at several indices, run from any log, returns
`true`, then the final log holds the opening of each query. -/
theorem opens_of_outcome_verifyOpeningsM {indices : Array ℕ}
    {openedRows : Array (Array (Array T))} {paths : Array (List D)}
    (h : Outcome (verifyOpeningsM root dims indices openedRows paths) l₀ true l)
    {query index : ℕ} {rows : Array (Array T)} (hindex : indices[query]? = some index)
    (hrows : openedRows[query]? = some rows) : Opens l root dims index rows := by
  unfold verifyOpeningsM at h
  split at h
  · have hquery : query < indices.size := (Array.getElem?_eq_some_iff.mp hindex).1
    obtain ⟨l₁, l₂, hrun, hl⟩ := outcome_allM h
      (verifyQueryM root dims indices openedRows paths query)
      (List.mem_map.mpr ⟨query, List.mem_range.mpr hquery, rfl⟩)
    unfold verifyQueryM at hrun
    rw [hindex, hrows] at hrun
    cases hpath : paths[query]? with
    | none =>
      rw [hpath] at hrun
      exact absurd hrun.1 (by simp)
    | some path =>
      rw [hpath] at hrun
      exact (opens_of_outcome_verifyOpeningM hrun).of_prefix hl
  · exact absurd h.1 (by simp)

end Accept

/-! ## `Opens` by the oracle check -/

namespace MerkleRO

section Replay

variable {l : Log (MerkleAnswer Msg Chal T D)}

/-- A climb under the hasher of a log that reaches a digest starts from one. -/
theorem climb_eq_known {dims : List Dimensions} {rows : List (Array T)}
    {path : List (Dig T D)} {h index : ℕ} {digest : Dig T D} {y : D}
    (hc : climb (logHasher l) dims rows h index digest path = .known y) :
    ∃ d, digest = .known d ∧ climb (logHasher l) dims rows h index (.known d) path = .known y := by
  obtain ⟨d, -, hd, hc'⟩ := climb_transfer (P := fun _ => True) (l := l) (l' := l)
    (fun _ _ _ hq => hq) (fun _ _ _ _ _ => ⟨trivial, trivial⟩) dims rows path h index digest y
    trivial hc
  exact ⟨d, hd, hc'⟩

/-- An injection under the hasher of a log that gives a digest is applied to one. -/
theorem inject_eq_known {dims : List Dimensions} {rows : List (Array T)} {g : ℕ}
    {digest : Dig T D} {y : D} (h : inject (logHasher l) dims rows g digest = .known y) :
    ∃ d, digest = .known d ∧ inject (logHasher l) dims rows g (.known d) = .known y := by
  obtain ⟨d, -, hd, h'⟩ := inject_transfer (P := fun _ => True) (l := l) (l' := l)
    (fun _ _ _ hq => hq) (fun _ _ _ _ _ => ⟨trivial, trivial⟩) trivial h
  exact ⟨d, hd, h'⟩

/-- A hash of entries the log holds is the result of its query, with no new entry. -/
theorem outcome_hashRowsM {xs : Array T} {y : D} (h : (logHasher l).hashRows xs = .known y) :
    Outcome (hashRowsM xs) l y l :=
  outcome_query.mpr (.inl ⟨logHasher_hashRows_eq_known.mp h, rfl⟩)

/-- A compression the log holds is the result of its query, with no new entry. -/
theorem outcome_compressM {a b y : D}
    (h : (logHasher l).compress (.known a) (.known b) = .known y) :
    Outcome (compressM a b) l y l := by
  obtain ⟨a', b', ha, hb, hq⟩ := logHasher_compress_eq_known.mp h
  cases ha
  cases hb
  exact outcome_query.mpr (.inl ⟨hq, rfl⟩)

/-- A parent the log holds is the result of `parentM`, with no new entry. -/
theorem outcome_parentM {index : ℕ} {digest sibling y : D}
    (h : parent (logHasher l) index (.known digest) (.known sibling) = .known y) :
    Outcome (parentM index digest sibling) l y l := by
  unfold parent at h
  unfold parentM
  split at h
  · next hpar => rw [ite_eq_left hpar]; exact outcome_compressM h
  · next hpar => rw [ite_eq_right hpar]; exact outcome_compressM h

/-- An injection the log holds is the result of `injectM`, with no new entry. -/
theorem outcome_injectM {dims : List Dimensions} {rows : List (Array T)} {g : ℕ}
    {digest y : D} (h : inject (logHasher l) dims rows g (.known digest) = .known y) :
    Outcome (injectM dims rows g digest) l y l := by
  unfold inject at h
  unfold injectM
  split at h
  · next hg =>
    obtain ⟨_, group, _, hgroup, _⟩ := logHasher_compress_eq_known.mp h
    rw [hgroup] at h
    rw [ite_eq_left hg]
    exact outcome_bind.mpr ⟨group, l, outcome_hashRowsM hgroup, outcome_compressM h⟩
  · next hg =>
    cases h
    rw [ite_eq_right hg]
    exact ⟨rfl, rfl⟩

/-- A climb the log holds is the result of `climbM`, with no new entry. -/
theorem outcome_climbM (dims : List Dimensions) (rows : List (Array T)) :
    ∀ (path : List D) (h index : ℕ) (digest y : D),
      climb (logHasher l) dims rows h index (.known digest) (path.map .known) = .known y →
      Outcome (climbM dims rows h index digest path) l y l
  | [], _, _, _, _, hc => by
    cases hc
    exact ⟨rfl, rfl⟩
  | sibling :: path, h, index, digest, y, hc => by
    rw [List.map_cons, climb] at hc
    obtain ⟨d₁, hinject, hclimb⟩ := climb_eq_known hc
    obtain ⟨d₂, hparent, hinject'⟩ := inject_eq_known hinject
    rw [climbM]
    exact outcome_bind.mpr ⟨d₂, l, outcome_parentM hparent, outcome_bind.mpr
      ⟨d₁, l, outcome_injectM hinject', outcome_climbM dims rows path _ _ d₁ y hclimb⟩⟩

end Replay

end MerkleRO

/-- **`Opens` by the oracle check.** The log `l` holds an opening exactly when,
for some path, the oracle check run from `l` accepts and adds no entry: every
query it makes is answered by `l`. -/
theorem opens_iff_outcome [DecidableEq D] {l : Log (MerkleAnswer Msg Chal T D)} {root : D}
    {dims : Array Dimensions} {index : ℕ} {rows : Array (Array T)} :
    Opens l root dims index rows ↔
      ∃ path, Outcome (verifyOpeningM root dims index rows path) l true l := by
  refine ⟨fun h => ?_, fun ⟨path, h⟩ => opens_of_outcome_verifyOpeningM h⟩
  obtain ⟨path, hsize, hw, hlen, hindex, hclimb⟩ := opens_iff.mp h
  obtain ⟨leaf, hleaf, hclimb'⟩ := climb_eq_known hclimb
  refine ⟨path, ?_⟩
  unfold verifyOpeningM
  rw [ite_eq_left (by simp [hsize, hw, hlen, hindex])]
  exact outcome_bind.mpr ⟨leaf, l, outcome_hashRowsM hleaf, outcome_bind.mpr
    ⟨root, l, outcome_climbM _ _ path _ _ leaf root hclimb', by simp, rfl⟩⟩

end CertiFri.Oracle
