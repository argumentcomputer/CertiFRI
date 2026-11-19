import CertiFriProofs.Theory.Oracle.MerkleBinding
import CertiFriProofs.Theory.Oracle.FiatShamirInterp

/-!
# Frozen trees

Once a Merkle root is in play, the openings a log holds under it cannot grow,
unless a later hash answer equals a digest that is already in play. This file
defines "in play" and that bad event, bounds its probability, and proves the
stability of `Opens`.

* `Present digestsOf r l d`: the digest `d` is present in the log `l`. It is the
  answer of a hash entry, one of the two inputs of a logged `node` query, or one
  of the digests `digestsOf m` of a message `m` among the first `r` messages of
  a logged challenge query. (`digestsOf` says which digests a prover message
  contains; `r` is the number of rounds.)
* `Hit digestsOf r l x y`: the bad event. `x` is a hash query and its answer `y`
  is present in `l`.

## Results

* `exists_finset_present`: at most `(K * r + 3) * l.length` digests are present
  in `l`, when a message contains at most `K` digests.
* `fractionLE_hit`, `prob_hasBad_hit_le`: so at most a fraction
  `(K * r + 3) * l.length / card D` of the answers to a query is a hit, and a
  computation with at most `Q` queries from the empty log leaves a log with a
  hit with probability at most `(K * r + 3) * Q * (Q - 1) / (2 * card D)`.
* `hasBad_hit_of_logCollision`: a collision is a hit, so a log without a hit
  has no collision.
* `Opens.of_append_of_not_hit` (**stability**): if `root` is present in `l` and
  no entry of `l ++ t` after `l` is a hit, an opening under `root` in `l ++ t`
  is in `l`. `opens_append_iff_of_not_hit` and `opens_concat_iff_of_not_hit`
  state it as an equivalence, for several new entries and for one.

Only the first `r` messages of a challenge query count as present. A challenge
query may hold a transcript of any length, so without this cut the number of
present digests is not bounded by the length of the log, and the bad-event
theorem, which needs a bound for every log, does not apply. The messages a
verifier of `r` rounds reads are among the first `r` (`present_of_mentions`).

Not covered: digests that enter play in another way than through the log (for
example digests fixed in the statement).
-/

namespace CertiFri.Oracle

universe u w

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle MerkleRO

/-! ## Digests present in a log -/

/-- The digests a hash entry brings into play: its answer, and the two inputs
of a `node` query. A challenge entry brings none. -/
def hashDigests : (x : FSQuery Msg Chal (HashQuery T D)) → MerkleAnswer Msg Chal T D x → List D
  | .chal _ _, _ => []
  | .other (.rows _), y => [y]
  | .other (.node a b), y => [a, b, y]

/-- The digests an entry of the log brings into play: those of the first `r`
messages of a challenge query, and those of a hash entry. -/
def entryDigests (digestsOf : Msg → List D) (r : ℕ) (e : Sigma (MerkleAnswer Msg Chal T D)) :
    List D :=
  (e.1.msgs.take r).flatMap digestsOf ++ hashDigests e.1 e.2

/-- The digest `d` is present in the log `l`: it is the answer of a hash entry,
one of the two inputs of a logged `node` query, or one of the digests of a
message among the first `r` messages of a logged challenge query. -/
def Present (digestsOf : Msg → List D) (r : ℕ) (l : Log (MerkleAnswer Msg Chal T D)) (d : D) :
    Prop :=
  ∃ e ∈ l, d ∈ entryDigests digestsOf r e

/-- The bad event of a frozen tree: the answer `y` to the hash query `x` is a
digest present in the log `l`. A challenge is never a hit. -/
def Hit (digestsOf : Msg → List D) (r : ℕ) (l : Log (MerkleAnswer Msg Chal T D)) :
    (x : FSQuery Msg Chal (HashQuery T D)) → MerkleAnswer Msg Chal T D x → Prop
  | .chal _ _, _ => False
  | .other _, y => Present digestsOf r l y

section Present

variable {digestsOf : Msg → List D} {r : ℕ} {l l' : Log (MerkleAnswer Msg Chal T D)}

/-- A digest present in a log is present in every log that contains its entries. -/
theorem Present.mono {d : D} (h : Present digestsOf r l d) (hl : l ⊆ l') :
    Present digestsOf r l' d := by
  obtain ⟨e, he, hd⟩ := h
  exact ⟨e, hl he, hd⟩

/-- The answer of a hash entry is present. -/
theorem present_of_mem {q : HashQuery T D} {y : D}
    (h : (⟨.other q, y⟩ : Sigma (MerkleAnswer Msg Chal T D)) ∈ l) : Present digestsOf r l y :=
  ⟨_, h, List.mem_append_right _ (by cases q <;> simp [hashDigests])⟩

/-- The two inputs of a logged `node` query are present. -/
theorem present_of_mem_node {a b y : D}
    (h : (⟨.other (.node a b), y⟩ : Sigma (MerkleAnswer Msg Chal T D)) ∈ l) :
    Present digestsOf r l a ∧ Present digestsOf r l b :=
  ⟨⟨_, h, List.mem_append_right _ (by simp [hashDigests])⟩,
    ⟨_, h, List.mem_append_right _ (by simp [hashDigests])⟩⟩

/-- The digests of a message that a challenge query of the log holds as its
message of a round below `r` are present. -/
theorem present_of_mentions {j : ℕ} {m : Msg} {d : D} (h : Mentions l j m) (hj : j < r)
    (hd : d ∈ digestsOf m) : Present digestsOf r l d := by
  obtain ⟨e, he, hm⟩ := h
  refine ⟨e, he, List.mem_append_left _ (List.mem_flatMap.mpr ⟨m, ?_, hd⟩)⟩
  exact List.mem_of_getElem? ((List.getElem?_take_of_lt hj).trans hm)

/-- `Hit` on a hash query, unfolded. -/
theorem hit_other {q : HashQuery T D} {y : D} :
    Hit digestsOf r l (.other q) y ↔ Present digestsOf r l y :=
  Iff.rfl

/-- An answer with the digest of an earlier hash entry is a hit. -/
theorem hit_of_hitsDigest {x : FSQuery Msg Chal (HashQuery T D)}
    {y : MerkleAnswer Msg Chal T D x} (h : HitsDigest hashObs l x y) : Hit digestsOf r l x y := by
  obtain ⟨⟨x', y'⟩, he, _, z, hz, hy⟩ := h
  cases x with
  | chal t m => cases hy
  | other q =>
    cases x' with
    | chal t m => cases hz
    | other q' =>
      obtain rfl : y' = z := Option.some.inj hz
      obtain rfl : y = y' := Option.some.inj hy
      exact present_of_mem he

/-- **A collision is a hit.** A log with two hash entries with different queries
and the same answer has an entry that is a hit with respect to the entries
before it. -/
theorem hasBad_hit_of_logCollision (h : LogCollision hashObs l) :
    HasBad (Hit digestsOf r) l :=
  (logCollision_iff_hasBad.mp h).imp fun _ _ _ => hit_of_hitsDigest

/-- A log without a hit has no collision. -/
theorem not_logCollision_of_not_hasBad_hit (h : ¬ HasBad (Hit digestsOf r) l) :
    ¬ LogCollision hashObs l :=
  fun hcol => h (hasBad_hit_of_logCollision hcol)

end Present

/-! ## Counting the present digests -/

namespace MerkleRO

/-- A list of lists of length at most `K` flattens to at most `K` elements per
member. -/
theorem length_flatMap_le {α β : Type*} (f : α → List β) {K : ℕ} (hK : ∀ a, (f a).length ≤ K) :
    ∀ l : List α, (l.flatMap f).length ≤ K * l.length
  | [] => by simp
  | a :: l => by
    have h₁ := length_flatMap_le f hK l
    have h₂ := hK a
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    omega

/-- The sum of the first `Q` natural numbers, as a real number. -/
theorem sum_range_cast (Q : ℕ) : ∑ i ∈ Finset.range Q, (i : ℝ) = Q * (Q - 1) / 2 := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

end MerkleRO

section Count

variable {digestsOf : Msg → List D} {r K : ℕ}

/-- An entry brings at most `K * r + 3` digests into play, when a message
contains at most `K` digests. -/
theorem length_entryDigests_le (hK : ∀ m, (digestsOf m).length ≤ K)
    (e : Sigma (MerkleAnswer Msg Chal T D)) : (entryDigests digestsOf r e).length ≤ K * r + 3 := by
  have h₁ : ((e.1.msgs.take r).flatMap digestsOf).length ≤ K * r :=
    (length_flatMap_le digestsOf hK _).trans (Nat.mul_le_mul_left K (List.length_take_le r _))
  have h₂ : (hashDigests e.1 e.2).length ≤ 3 := by
    obtain ⟨x, y⟩ := e
    cases x with
    | chal t m => exact Nat.zero_le 3
    | other q => cases q <;> exact Nat.le_of_ble_eq_true rfl
  rw [entryDigests, List.length_append]
  omega

/-- **The number of present digests.** When a message contains at most `K`
digests, the digests present in a log `l` lie in a set of at most
`(K * r + 3) * l.length` elements. -/
theorem exists_finset_present (hK : ∀ m, (digestsOf m).length ≤ K)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    ∃ S : Finset D, S.card ≤ (K * r + 3) * l.length ∧ ∀ d, Present digestsOf r l d → d ∈ S := by
  classical
  refine ⟨(l.flatMap (entryDigests digestsOf r)).toFinset, ?_, fun d hd => ?_⟩
  · exact (List.toFinset_card_le _).trans (length_flatMap_le _ (length_entryDigests_le hK) l)
  · rw [List.mem_toFinset, List.mem_flatMap]
    exact hd

variable [Fintype D] [Nonempty D]

/-- At most a fraction `(K * r + 3) * l.length / card D` of the digests is
present in a log `l`. -/
theorem fractionLE_present (hK : ∀ m, (digestsOf m).length ≤ K)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    FractionLE (fun y : D => Present digestsOf r l y)
      ((K * r + 3) * l.length / Fintype.card D) := by
  obtain ⟨S, hS, hmem⟩ := exists_finset_present (r := r) hK l
  refine ⟨S, ?_, hmem⟩
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact_mod_cast hS

variable [∀ i, Fintype (Chal i)]

/-- **The fraction of hits.** For every log `l` and every query, at most a
fraction `(K * r + 3) * l.length / card D` of the answers is a hit. -/
theorem fractionLE_hit (hK : ∀ m, (digestsOf m).length ≤ K)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    ∀ x : FSQuery Msg Chal (HashQuery T D),
      FractionLE (Hit digestsOf r l x) ((K * r + 3) * l.length / Fintype.card D)
  | .chal _ _ => (FractionLE.false.mono_right (by positivity)).mono_left fun _ h => h
  | .other _ => fractionLE_present hK l

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))] [∀ i, Nonempty (Chal i)] {α : Type w}

/-- **The probability of a hit.** When a message contains at most `K` digests,
a computation that makes at most `Q` queries from the empty log leaves a log
with an entry that is a hit with respect to the entries before it with
probability at most `(K * r + 3) * Q * (Q - 1) / (2 * card D)`. -/
theorem prob_hasBad_hit_le (hK : ∀ m, (digestsOf m).length ≤ K)
    {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (Hit digestsOf r) l) c []
      ≤ (K * r + 3) * Q * (Q - 1) / (2 * Fintype.card D) := by
  have h := prob_hasBad_le (bad := Hit digestsOf r)
    (ε := fun n => (K * r + 3) * n / Fintype.card D) (fun n => by positivity)
    (fun l x _ => fractionLE_hit hK l x) hc
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_range_cast]
  ring

end Count

/-! ## Stability -/

section Stable

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))] {digestsOf : Msg → List D} {r : ℕ}
  {l t : Log (MerkleAnswer Msg Chal T D)} {root : D} {dims : Array Dimensions} {index : ℕ}
  {rows : Array (Array T)}

/-- The answer of a hash query the log holds is present. -/
theorem present_of_hashLookup {q : HashQuery T D} {y : D} (h : hashLookup l q = some y) :
    Present digestsOf r l y :=
  present_of_mem (mem_of_hashLookup h)

/-- The two inputs of a `node` query the log answers are present. -/
theorem present_of_hashLookup_node {a b y : D} (h : hashLookup l (.node a b) = some y) :
    Present digestsOf r l a ∧ Present digestsOf r l b :=
  present_of_mem_node (mem_of_hashLookup h)

/-- If no entry after `l` is a hit, a hash entry of `l ++ t` whose answer is
present in `l` is an entry of `l`. -/
theorem hashLookup_of_append_of_not_hit
    (hno : ¬ HasBadFrom (Hit digestsOf r) l.length (l ++ t)) {q : HashQuery T D} {y : D}
    (hy : Present digestsOf r l y) (h : hashLookup (l ++ t) q = some y) :
    hashLookup l q = some y := by
  unfold hashLookup at h ⊢
  rw [List.dlookup_append] at h
  cases hl : List.dlookup (FSQuery.other q) l with
  | some y' => rwa [hl, Option.some_or] at h
  | none =>
    rw [hl, Option.none_or] at h
    obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem (List.of_mem_dlookup h)
    exact absurd ⟨l ++ t₁, ⟨.other q, y⟩, t₂, by rw [List.append_assoc], by simp,
      hy.mono (List.subset_append_left l t₁)⟩ hno

/-- **Stability.** If `root` is present in the log `l`, and no entry of `l ++ t`
after `l` is a hit with respect to the entries before it, then an opening under
`root` that `l ++ t` holds is already in `l`. -/
theorem Opens.of_append_of_not_hit (hroot : Present digestsOf r l root)
    (hno : ¬ HasBadFrom (Hit digestsOf r) l.length (l ++ t))
    (h : Opens (l ++ t) root dims index rows) : Opens l root dims index rows :=
  h.transfer (P := Present digestsOf r l)
    (fun _ _ hy hq => hashLookup_of_append_of_not_hit hno hy hq)
    (fun _ _ _ hy hq => present_of_hashLookup_node (hashLookup_of_append_of_not_hit hno hy hq))
    hroot

/-- If `root` is present in `l` and no entry after `l` is a hit, `l ++ t` holds
the same openings under `root` as `l`. -/
theorem opens_append_iff_of_not_hit (hroot : Present digestsOf r l root)
    (hno : ¬ HasBadFrom (Hit digestsOf r) l.length (l ++ t)) :
    Opens (l ++ t) root dims index rows ↔ Opens l root dims index rows :=
  ⟨Opens.of_append_of_not_hit hroot hno, Opens.of_prefix (List.prefix_append l t)⟩

/-- If `root` is present in `l` and the new entry `e` is not a hit, `l ++ [e]`
holds the same openings under `root` as `l`. -/
theorem opens_concat_iff_of_not_hit {e : Sigma (MerkleAnswer Msg Chal T D)}
    (hroot : Present digestsOf r l root) (he : ¬ Hit digestsOf r l e.1 e.2) :
    Opens (l ++ [e]) root dims index rows ↔ Opens l root dims index rows :=
  opens_append_iff_of_not_hit hroot fun h =>
    (hasBadFrom_concat.mp h).elim (not_hasBadFrom_of_length_le le_rfl) fun h' => he h'.2

end Stable

end CertiFri.Oracle
