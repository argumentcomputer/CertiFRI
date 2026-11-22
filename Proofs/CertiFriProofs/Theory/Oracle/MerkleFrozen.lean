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
  of the digests `digestsOf j m` of the `j`-th message `m` (`j < r`) of a logged
  challenge query. (`digestsOf` is round-indexed so rounds with different numbers
  of roots are counted tightly.)
* `Hit digestsOf r l x y`: the bad event. `x` is a hash query and its answer `y`
  is present in `l`. Challenge queries are never hits.

## Results

* `exists_finset_present`: at most `presentCap M l` digests are present in `l`,
  where each challenge entry contributes at most `M` digests (the total across
  rounds `< r`) and each hash entry contributes at most `3`.
* `prob_hasBad_hit_le_potential`: a computation with at most `Q` queries from
  the empty log leaves a log with a hit with probability at most
  `hitPotential M 0 Q / card D`, accounting for the fact that challenge queries
  have zero hit probability while hash queries add at most `3` digests.
* `prob_hasBad_hit_le`: closed-form corollary
  `(max M 3 + 3) * Q ^ 2 / (4 * card D)`.
* `hasBad_hit_of_logCollision`: a collision is a hit, so a log without a hit
  has no collision.
* `Opens.of_append_of_not_hit` (**stability**): if `root` is present in `l` and
  no entry of `l ++ t` after `l` is a hit, an opening under `root` in `l ++ t`
  is in `l`. `opens_append_iff_of_not_hit` and `opens_concat_iff_of_not_hit`
  state it as an equivalence, for several new entries and for one.
-/

namespace CertiFri.Oracle

universe u w

variable {Msg : Type u} {Chal : ℕ → Type} {T D : Type}

open OracleComp Merkle MerkleRO

/-! ## Digests present in a log -/

/-- The digests a hash entry brings into play: its answer, and the two inputs
of a `node` query. A challenge entry brings none here. -/
def hashDigests : (x : FSQuery Msg Chal (HashQuery T D)) → MerkleAnswer Msg Chal T D x → List D
  | .chal _ _, _ => []
  | .other (.rows _), y => [y]
  | .other (.node a b), y => [a, b, y]

/-- The digests of the first `r` messages of a query, using round-indexed `digestsOf`. -/
def chalDigests (digestsOf : ℕ → Msg → List D) (r : ℕ) (x : FSQuery Msg Chal (HashQuery T D)) :
    List D :=
  ((x.msgs.take r).zipIdx).flatMap fun p => digestsOf p.2 p.1

/-- The digests an entry of the log brings into play: those of the first `r`
messages of a challenge query, and those of a hash entry. -/
def entryDigests (digestsOf : ℕ → Msg → List D) (r : ℕ) (e : Sigma (MerkleAnswer Msg Chal T D)) :
    List D :=
  chalDigests digestsOf r e.1 ++ hashDigests e.1 e.2

/-- The digest `d` is present in the log `l`: it is the answer of a hash entry,
one of the two inputs of a logged `node` query, or one of the digests of a
message among the first `r` messages of a logged challenge query. -/
def Present (digestsOf : ℕ → Msg → List D) (r : ℕ) (l : Log (MerkleAnswer Msg Chal T D)) (d : D) :
    Prop :=
  ∃ e ∈ l, d ∈ entryDigests digestsOf r e

/-- The bad event of a frozen tree: the answer `y` to the hash query `x` is a
digest present in the log `l`. A challenge is never a hit. -/
def Hit (digestsOf : ℕ → Msg → List D) (r : ℕ) (l : Log (MerkleAnswer Msg Chal T D)) :
    (x : FSQuery Msg Chal (HashQuery T D)) → MerkleAnswer Msg Chal T D x → Prop
  | .chal _ _, _ => False
  | .other _, y => Present digestsOf r l y

section Present

variable {digestsOf : ℕ → Msg → List D} {r : ℕ} {l l' : Log (MerkleAnswer Msg Chal T D)}

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
    (hd : d ∈ digestsOf j m) : Present digestsOf r l d := by
  obtain ⟨e, he, hm⟩ := h
  refine ⟨e, he, List.mem_append_left _ (List.mem_flatMap.mpr ⟨(m, j), ?_, hd⟩)⟩
  rw [List.mem_zipIdx_iff_getElem?]
  exact (List.getElem?_take_of_lt hj).trans hm

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

/-! ## Counting the present digests with separate challenge and hash weights -/

namespace MerkleRO

/-- The weight an entry adds to the upper bound on present digests: `M` for a
challenge entry and `3` for a hash entry. -/
def entryCap (M : ℕ) (x : FSQuery Msg Chal (HashQuery T D)) : ℕ :=
  match x with
  | .chal _ _ => M
  | .other _ => 3

/-- Upper bound on the number of digests present in a log `l`: `M` per challenge
entry and `3` per hash entry. -/
def presentCap (M : ℕ) (l : Log (MerkleAnswer Msg Chal T D)) : ℕ :=
  (l.map fun e => entryCap M e.1).sum

@[simp] theorem presentCap_nil (M : ℕ) :
    presentCap (Msg := Msg) (Chal := Chal) (T := T) (D := D) M [] = 0 := rfl

theorem presentCap_append_singleton (M : ℕ) (l : Log (MerkleAnswer Msg Chal T D))
    (e : Sigma (MerkleAnswer Msg Chal T D)) :
    presentCap M (l ++ [e]) = presentCap M l + entryCap M e.1 := by
  simp [presentCap]

/-- The Bellman potential for the hit probability (multiplied by `|D|`):
starting with at most `p` present digests and at most `q` queries remaining,
where each challenge query adds `M` digests with hit probability `0` and each
hash query adds `3` digests with hit probability `p / |D|`. -/
noncomputable def hitPotential (M p q : ℕ) : ℝ :=
  (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one fun h =>
    (h : ℝ) * ((p : ℝ) + M * (q - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2

theorem hitPotential_nonneg (M p q : ℕ) : 0 ≤ hitPotential M p q := by
  unfold hitPotential
  have h0 : (0 : ℕ) ∈ Finset.range (q + 1) := Finset.mem_range.mpr (Nat.succ_pos q)
  have hle := Finset.le_sup' (f := fun h : ℕ =>
    (h : ℝ) * ((p : ℝ) + M * (q - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2) h0
  have hval : ((0 : ℕ) : ℝ) * ((p : ℝ) + M * (q - 0 : ℕ)) + (3 : ℝ) * (0 : ℕ) * (0 - 1 : ℕ) / 2 = 0 := by
    simp
  exact hval ▸ hle

theorem hitPotential_mono_q (M p q : ℕ) : hitPotential M p q ≤ hitPotential M p (q + 1) := by
  unfold hitPotential
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h : ℕ =>
    (h : ℝ) * ((p : ℝ) + M * (q + 1 - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2) hmem)
  have hsub : ((q - h : ℕ) : ℝ) ≤ ((q + 1 - h : ℕ) : ℝ) := by exact_mod_cast (by omega : q - h ≤ q + 1 - h)
  gcongr

theorem hitPotential_chal_step (M p q : ℕ) :
    hitPotential M (p + M) q ≤ hitPotential M p (q + 1) := by
  unfold hitPotential
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h : ℕ =>
    (h : ℝ) * ((p : ℝ) + M * (q + 1 - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2) hmem)
  have hsub : ((q + 1 - h : ℕ) : ℝ) = ((q - h : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : q + 1 - h = q - h + 1)
  rw [hsub]
  push_cast
  linarith

theorem hitPotential_hash_step (M p q : ℕ) :
    (p : ℝ) + hitPotential M (p + 3) q ≤ hitPotential M p (q + 1) := by
  unfold hitPotential
  rw [add_comm, Finset.sup'_add]
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h + 1 ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h' : ℕ =>
    (h' : ℝ) * ((p : ℝ) + M * (q + 1 - h' : ℕ)) + (3 : ℝ) * h' * (h' - 1 : ℕ) / 2) hmem)
  have hsub1 : q + 1 - (h + 1) = q - h := by omega
  have hsub2 : h + 1 - 1 = h := by omega
  rw [hsub1, hsub2]
  have h3 : (3 : ℝ) * (h : ℝ) + 3 * (h : ℝ) * ((h - 1 : ℕ) : ℝ) / 2 =
      3 * ((h + 1 : ℕ) : ℝ) * (h : ℝ) / 2 := by
    cases h with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hM : (0 : ℝ) ≤ (M : ℝ) * ((q - h : ℕ) : ℝ) := by positivity
  push_cast at h3 ⊢
  nlinarith

/-- Closed-form upper bound on `hitPotential M 0 Q`:
`hitPotential M 0 Q ≤ (max M 3 + 3) * Q ^ 2 / 4`. -/
theorem hitPotential_zero_le (M Q : ℕ) :
    hitPotential M 0 Q ≤ ((max M 3 + 3 : ℕ) : ℝ) * (Q : ℝ) ^ 2 / 4 := by
  unfold hitPotential
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hle : h ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  set M' : ℕ := max M 3
  have hMM' : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast le_max_left M 3
  have h3M' : (3 : ℝ) ≤ (M' : ℝ) := by exact_mod_cast le_max_right M 3
  have hsub : ((Q - h : ℕ) : ℝ) = (Q : ℝ) - (h : ℝ) := Nat.cast_sub hle
  have hh1 : ((h - 1 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.sub_le h 1
  have hstep1 : (h : ℝ) * ((0 : ℕ) + (M : ℝ) * ((Q - h : ℕ) : ℝ)) +
      3 * (h : ℝ) * ((h - 1 : ℕ) : ℝ) / 2 ≤
      (h : ℝ) * ((M' : ℝ) * ((Q : ℝ) - (h : ℝ))) + 3 * (h : ℝ) * (h : ℝ) / 2 := by
    rw [Nat.cast_zero, zero_add, hsub]
    have hnn1 : 0 ≤ (Q : ℝ) - (h : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hle)
    have h1 : (h : ℝ) * ((M : ℝ) * ((Q : ℝ) - (h : ℝ))) ≤
        (h : ℝ) * ((M' : ℝ) * ((Q : ℝ) - (h : ℝ))) := by gcongr
    have h2 : 3 * (h : ℝ) * ((h - 1 : ℕ) : ℝ) / 2 ≤ 3 * (h : ℝ) * (h : ℝ) / 2 := by gcongr
    linarith
  refine hstep1.trans ?_
  have hpos : (0 : ℝ) < 4 * (M' : ℝ) - 6 := by linarith
  have hkey : 0 ≤ ((4 * (M' : ℝ) - 6) * (h : ℝ) - 2 * (M' : ℝ) * (Q : ℝ)) ^ 2 +
      6 * ((M' : ℝ) - 3) * (Q : ℝ) ^ 2 := by
    have hsq1 : 0 ≤ ((4 * (M' : ℝ) - 6) * (h : ℝ) - 2 * (M' : ℝ) * (Q : ℝ)) ^ 2 := sq_nonneg _
    have hsq2 : 0 ≤ (Q : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hmul : (4 * (M' : ℝ) - 6) *
      (((M' : ℝ) + 3) * (Q : ℝ) ^ 2 - 4 * ((h : ℝ) * ((M' : ℝ) * ((Q : ℝ) - (h : ℝ))) +
        3 * (h : ℝ) * (h : ℝ) / 2)) =
      ((4 * (M' : ℝ) - 6) * (h : ℝ) - 2 * (M' : ℝ) * (Q : ℝ)) ^ 2 +
        6 * ((M' : ℝ) - 3) * (Q : ℝ) ^ 2 := by ring
  have hdiff : 0 ≤ ((M' : ℝ) + 3) * (Q : ℝ) ^ 2 -
      4 * ((h : ℝ) * ((M' : ℝ) * ((Q : ℝ) - (h : ℝ))) + 3 * (h : ℝ) * (h : ℝ) / 2) := by
    nlinarith
  push_cast
  linarith

/-- Length of `flatMap` over a `zipIdx` list bounded by a sum of per-index bounds. -/
theorem length_flatMap_zipIdx_le {α β : Type*} (f : ℕ → α → List β) (bound : ℕ → ℕ)
    (hbound : ∀ j a, (f j a).length ≤ bound j) :
    ∀ (l : List α) (k : ℕ),
      ((l.zipIdx k).flatMap fun p => f p.2 p.1).length ≤
        ∑ j ∈ Finset.range l.length, bound (k + j)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.length_cons,
      Finset.sum_range_succ', Nat.add_zero]
    have ih := length_flatMap_zipIdx_le f bound hbound l (k + 1)
    have hsum : ∑ j ∈ Finset.range l.length, bound (k + 1 + j) =
        ∑ j ∈ Finset.range l.length, bound (k + (j + 1)) :=
      Finset.sum_congr rfl fun j _ => by rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [hsum] at ih
    have ha := hbound k a
    simp only [Nat.add_zero]
    omega

end MerkleRO

section Count

variable {digestsOf : ℕ → Msg → List D} {r M : ℕ}

/-- An entry brings at most `entryCap M e.1` digests into play when every
challenge query brings at most `M` digests across rounds `< r`. -/
theorem length_entryDigests_le
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    (e : Sigma (MerkleAnswer Msg Chal T D)) :
    (entryDigests digestsOf r e).length ≤ entryCap M e.1 := by
  obtain ⟨x, y⟩ := e
  cases x with
  | chal t m =>
    simp only [entryDigests, hashDigests, List.append_nil, entryCap]
    exact hM (.chal t m)
  | other q =>
    simp only [entryDigests, chalDigests, FSQuery.msgs, List.take_nil, List.zipIdx_nil,
      List.flatMap_nil, List.nil_append, entryCap]
    cases q with
    | rows _ => exact show 1 ≤ 3 by decide
    | node _ _ => exact le_refl 3

/-- **The number of present digests.** The digests present in a log `l` lie in a
set of at most `presentCap M l` elements. -/
theorem exists_finset_present
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    ∃ S : Finset D, S.card ≤ presentCap M l ∧ ∀ d, Present digestsOf r l d → d ∈ S := by
  classical
  refine ⟨(l.flatMap (entryDigests digestsOf r)).toFinset, ?_, fun d hd => ?_⟩
  · refine (List.toFinset_card_le _).trans ?_
    induction l with
    | nil => simp [presentCap]
    | cons e l ih =>
      rw [List.flatMap_cons, List.length_append, presentCap, List.map_cons, List.sum_cons]
      have he := length_entryDigests_le hM e
      change (entryDigests digestsOf r e).length + (l.flatMap (entryDigests digestsOf r)).length ≤
        entryCap M e.1 + presentCap M l
      omega
  · rw [List.mem_toFinset, List.mem_flatMap]
    exact hd

variable [Fintype D] [Nonempty D]

/-- At most a fraction `presentCap M l / card D` of the digests is present in a log `l`. -/
theorem fractionLE_present
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    FractionLE (fun y : D => Present digestsOf r l y)
      ((presentCap M l : ℝ) / Fintype.card D) := by
  obtain ⟨S, hS, hmem⟩ := exists_finset_present (r := r) hM l
  refine ⟨S, ?_, hmem⟩
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact_mod_cast hS

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))] [∀ i, Fintype (Chal i)]
  [∀ i, Nonempty (Chal i)] {α : Type w}

/-- **The probability of a hit, from any log, via the Bellman potential.** -/
theorem prob_hasBadFrom_hit_le
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q)
    (l : Log (MerkleAnswer Msg Chal T D)) :
    prob (fun _ l' => HasBadFrom (Hit digestsOf r) l.length l') c l
      ≤ hitPotential M (presentCap M l) Q / Fintype.card D := by
  classical
  have hDpos : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  induction c generalizing l Q with
  | pure a =>
    rw [prob_pure, ite_eq_right (not_hasBadFrom_of_length_le le_rfl)]
    exact div_nonneg (hitPotential_nonneg M _ Q) hDpos.le
  | queryBind x k ih =>
    cases Q with
    | zero => exact absurd hc (queryBound_queryBind_zero x k)
    | succ Q =>
      cases hx : l.dlookup x with
      | some y =>
        rw [prob_queryBind_of_lookup hx]
        exact (ih y (hc y) l).trans
          (div_le_div_of_nonneg_right (hitPotential_mono_q M _ Q) hDpos.le)
      | none =>
        have hYpos : (0 : ℝ) < Fintype.card (MerkleAnswer Msg Chal T D x) :=
          Nat.cast_pos.mpr Fintype.card_pos
        set B := hitPotential M (presentCap M l + entryCap M x) Q / Fintype.card D with hBdef
        have hB0 : 0 ≤ B := div_nonneg (hitPotential_nonneg M _ Q) hDpos.le
        have hstep : ∀ y : MerkleAnswer Msg Chal T D x,
            prob (fun _ l' => HasBadFrom (Hit digestsOf r) l.length l') (k y) (l ++ [⟨x, y⟩])
              ≤ (if Hit digestsOf r l x y then 1 else 0) + B := by
          intro y
          by_cases hb : Hit digestsOf r l x y
          · rw [ite_eq_left hb]
            exact (prob_le_one _ _ _).trans (le_add_of_nonneg_right hB0)
          · rw [ite_eq_right hb, zero_add]
            refine le_trans (prob_mono_of_outcome fun a l' ha h => ?_)
              ((ih y (hc y) (l ++ [⟨x, y⟩])).trans (le_of_eq ?_))
            · obtain ⟨t, rfl⟩ := ha.prefix
              rw [List.append_assoc, List.singleton_append] at h ⊢
              rw [List.length_append, List.length_singleton]
              exact (hasBadFrom_length_cons h).resolve_left hb
            · rw [presentCap_append_singleton]
        rw [prob_queryBind_of_fresh hx, div_le_iff₀ hYpos]
        cases x with
        | chal t m =>
          have hzero : ∀ y, Hit digestsOf r l (.chal t m) y = False := fun _ => rfl
          have hsum : ∑ y : MerkleAnswer Msg Chal T D (.chal t m),
              prob (fun _ l' => HasBadFrom (Hit digestsOf r) l.length l') (k y)
                (l ++ [⟨.chal t m, y⟩]) ≤
              Fintype.card (MerkleAnswer Msg Chal T D (.chal t m)) * B := by
            calc ∑ y, prob (fun _ l' => HasBadFrom (Hit digestsOf r) l.length l') (k y)
                    (l ++ [⟨.chal t m, y⟩])
                ≤ ∑ _y : MerkleAnswer Msg Chal T D (.chal t m), B :=
                  Finset.sum_le_sum fun y _ => by simpa [hzero y] using hstep y
              _ = Fintype.card (MerkleAnswer Msg Chal T D (.chal t m)) * B := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          refine hsum.trans ?_
          rw [mul_comm]
          refine mul_le_mul_of_nonneg_right ?_ hYpos.le
          exact div_le_div_of_nonneg_right (hitPotential_chal_step M (presentCap M l) Q) hDpos.le
        | other q =>
          have hfrac : FractionLE (Hit digestsOf r l (.other q))
              ((presentCap M l : ℝ) / Fintype.card D) :=
            fractionLE_present hM l
          calc ∑ y : D, prob (fun _ l' => HasBadFrom (Hit digestsOf r) l.length l') (k y)
                  (l ++ [⟨.other q, y⟩])
              ≤ ∑ y : D, ((if Hit digestsOf r l (.other q) y then (1 : ℝ) else 0) + B) :=
                Finset.sum_le_sum fun y _ => hstep y
            _ = (∑ y : D, if Hit digestsOf r l (.other q) y then (1 : ℝ) else 0) +
                  Fintype.card D * B := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ ≤ ((presentCap M l : ℝ) / Fintype.card D) * Fintype.card D + Fintype.card D * B :=
                add_le_add_left hfrac.sum_ite_le _
            _ = ((presentCap M l : ℝ) + hitPotential M (presentCap M l + 3) Q) /
                  Fintype.card D * Fintype.card D := by
                rw [hBdef, entryCap]
                field_simp
            _ ≤ (hitPotential M (presentCap M l) (Q + 1) / Fintype.card D) * Fintype.card D :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right (hitPotential_hash_step M (presentCap M l) Q) hDpos.le)
                  hDpos.le

/-- **The probability of a hit, via the Bellman potential.** -/
theorem prob_hasBad_hit_le_potential
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (Hit digestsOf r) l) c []
      ≤ hitPotential M 0 Q / Fintype.card D := by
  simpa only [HasBad, List.length_nil, presentCap_nil] using prob_hasBadFrom_hit_le hM hc []

/-- **The probability of a hit (tight closed form).** When every challenge query
contains at most `M` digests across the first `r` rounds, a computation that makes
at most `Q` queries from the empty log leaves a log with a hit with probability at
most `(max M 3 + 3) * Q ^ 2 / (4 * card D)`. -/
theorem prob_hasBad_hit_le
    (hM : ∀ (x : FSQuery Msg Chal (HashQuery T D)), (chalDigests digestsOf r x).length ≤ M)
    {c : OracleComp (MerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (Hit digestsOf r) l) c []
      ≤ ((max M 3 + 3 : ℕ) : ℝ) * (Q : ℝ) ^ 2 / (4 * Fintype.card D) := by
  refine (prob_hasBad_hit_le_potential hM hc).trans ?_
  have hle := hitPotential_zero_le M Q
  have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  calc hitPotential M 0 Q / Fintype.card D
      ≤ (((max M 3 + 3 : ℕ) : ℝ) * (Q : ℝ) ^ 2 / 4) / Fintype.card D :=
        div_le_div_of_nonneg_right hle hD
    _ = ((max M 3 + 3 : ℕ) : ℝ) * (Q : ℝ) ^ 2 / (4 * Fintype.card D) := by ring

end Count

/-! ## Stability -/

section Stable

variable [DecidableEq (FSQuery Msg Chal (HashQuery T D))] {digestsOf : ℕ → Msg → List D} {r : ℕ}
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

/-! ## Incremental sponge chaining (`entryCap = 1`, collision prefactor `c = 3 / 2`)

In full-transcript Fiat–Shamir (`FSQuery`), each challenge query repeats every
prior round's Merkle roots, giving `entryCap = M ≈ batches + rounds` and a
collision prefactor `c = (max M 3 + 3) / 4` (e.g., `7.75` for `M = 28`, limiting
32-byte digests to `126.52` bits).

In an incremental sponge (`SpongeQuery`), each challenge step `i` takes only
the previous chaining digest `prev : D` and step `i`'s message `m` (bringing at
most `M ≤ 3` digests into play — specifically **`M = 1`** when each Merkle root
is absorbed individually), and outputs `(nextState, chal_i) : D × Chal i`.

We track two disjoint bad events simultaneously:
* `SpongeHit` (on `.chal` queries only): `nextState` collides with the initial
  state `s₀` or any previously seen sponge state (`prev` or `nextState`),
  increasing the sponge-state count by `2` per challenge query (`0` per hash).
* `SpongeMerkleHit` (on `.other` hash queries only): the hash output hits any
  Merkle digest already in play (`M ≤ 3` per challenge query, `3` per hash).

A joint Bellman potential `jointHitPotential M pM pS q` proves that for ANY
`M ≤ 3` (including `M = 1`, `entryCap = 1`) and any `Q`-query computation from
the empty log,
  `prob (HasBad (JointHit s₀ stepDigestsOf r)) c [] ≤ 3 * Q ^ 2 / (2 * |D|)`.
This shrinks the BCS collision prefactor from `7.75` to the optimal `3 / 2`
(`126.52b → 127.71b` on 32-byte BLAKE3 with zero prover cost, and `191.71b`
classical / `128.0b` BHT quantum on 48-byte BLAKE3 XOF). -/

/-- Queries to an incremental sponge + auxiliary random oracle:
`.chal i prev m` absorbs step `i`'s message `m` into sponge chaining state `prev`
and returns `(nextState, chal_i)`; `.other q` queries the auxiliary oracle. -/
inductive SpongeQuery (Msg : Type u) (D : Type) (X' : Type w) : Type max u w
  | chal (i : ℕ) (prev : D) (m : Msg)
  | other (q : X')
  deriving DecidableEq

/-- Answer type of an incremental sponge + auxiliary random oracle. -/
def SpongeAnswer (Chal : ℕ → Type) (D : Type) {X' : Type w} (Y' : X' → Type) :
    SpongeQuery Msg D X' → Type
  | .chal i _ _ => D × Chal i
  | .other q => Y' q

instance {X' : Type w} {Y' : X' → Type} [Fintype D] [∀ i, Fintype (Chal i)] [∀ q, Fintype (Y' q)] :
    ∀ x : SpongeQuery Msg D X', Fintype (SpongeAnswer Chal D Y' x)
  | .chal _ _ _ => inferInstanceAs (Fintype (D × Chal _))
  | .other q => inferInstanceAs (Fintype (Y' q))

instance {X' : Type w} {Y' : X' → Type} [Nonempty D] [∀ i, Nonempty (Chal i)]
    [∀ q, Nonempty (Y' q)] :
    ∀ x : SpongeQuery Msg D X', Nonempty (SpongeAnswer Chal D Y' x)
  | .chal _ _ _ => inferInstanceAs (Nonempty (D × Chal _))
  | .other q => inferInstanceAs (Nonempty (Y' q))

/-- Incremental sponge + Merkle hash random oracle answers. -/
abbrev SpongeMerkleAnswer (Msg : Type u) (Chal : ℕ → Type) (T D : Type) :
    SpongeQuery Msg D (HashQuery T D) → Type :=
  SpongeAnswer (Msg := Msg) Chal D (fun _ : HashQuery T D => D)

/-- Sponge chaining states (`prev` and `nextState`) introduced by a log entry. -/
def spongeStates {X' : Type w} {Y' : X' → Type} :
    (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → List D
  | .chal _ prev _, (next, _) => [prev, next]
  | .other _, _ => []

/-- A sponge state `s` is present in `l` if `s = s₀` or `s` appears as the
input or output chaining state of some `.chal` entry in `l`. -/
def SpongePresent {X' : Type w} {Y' : X' → Type} (s₀ : D)
    (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) (s : D) : Prop :=
  s = s₀ ∨ ∃ e ∈ l, s ∈ spongeStates e.1 e.2

/-- Sponge collision / cycle / init-hit bad event: a `.chal` query's output
state `next` hits an already-present sponge state. -/
def SpongeHit {X' : Type w} {Y' : X' → Type} (s₀ : D)
    (l : Log (SpongeAnswer (Msg := Msg) Chal D Y')) :
    (x : SpongeQuery Msg D X') → SpongeAnswer Chal D Y' x → Prop
  | .chal _ _ _, (next, _) => SpongePresent s₀ l next
  | .other _, _ => False

/-- Merkle digests brought into play by a hash entry of a sponge log. -/
def spongeHashDigests :
    (x : SpongeQuery Msg D (HashQuery T D)) → SpongeMerkleAnswer Msg Chal T D x → List D
  | .chal _ _ _, _ => []
  | .other (.rows _), y => [y]
  | .other (.node a b), y => [a, b, y]

/-- Merkle digests brought into play by a single incremental sponge step `i < r`. -/
def spongeChalDigests (stepDigestsOf : ℕ → Msg → List D) (r : ℕ) :
    SpongeQuery Msg D (HashQuery T D) → List D
  | .chal i _ m => if i < r then stepDigestsOf i m else []
  | .other _ => []

/-- Merkle digests brought into play by an entry of a sponge-Merkle log. -/
def spongeEntryDigests (stepDigestsOf : ℕ → Msg → List D) (r : ℕ)
    (e : Sigma (SpongeMerkleAnswer Msg Chal T D)) : List D :=
  spongeChalDigests stepDigestsOf r e.1 ++ spongeHashDigests e.1 e.2

/-- A Merkle digest `d` is present in a sponge-Merkle log `l`. -/
def SpongeMerklePresent (stepDigestsOf : ℕ → Msg → List D) (r : ℕ)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) (d : D) : Prop :=
  ∃ e ∈ l, d ∈ spongeEntryDigests stepDigestsOf r e

/-- Merkle hit in a sponge-Merkle log (only on `.other` hash queries). -/
def SpongeMerkleHit (stepDigestsOf : ℕ → Msg → List D) (r : ℕ)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    (x : SpongeQuery Msg D (HashQuery T D)) → SpongeMerkleAnswer Msg Chal T D x → Prop
  | .chal _ _ _, _ => False
  | .other _, y => SpongeMerklePresent stepDigestsOf r l y

/-- Joint bad event for incremental sponge chaining + frozen Merkle trees:
`SpongeHit` on `.chal` queries and `SpongeMerkleHit` on `.other` hash queries. -/
def JointHit (s₀ : D) (stepDigestsOf : ℕ → Msg → List D) (r : ℕ)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    (x : SpongeQuery Msg D (HashQuery T D)) → SpongeMerkleAnswer Msg Chal T D x → Prop
  | .chal _ _ _, (next, _) => SpongePresent s₀ l next
  | .other _, y => SpongeMerklePresent stepDigestsOf r l y

theorem SpongePresent.mono {X' : Type w} {Y' : X' → Type} {s₀ : D}
    {l l' : Log (SpongeAnswer (Msg := Msg) Chal D Y')} {s : D}
    (h : SpongePresent s₀ l s) (hl : l ⊆ l') : SpongePresent s₀ l' s :=
  h.imp id fun ⟨e, he, hs⟩ => ⟨e, hl he, hs⟩

theorem SpongeMerklePresent.mono {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l l' : Log (SpongeMerkleAnswer Msg Chal T D)} {d : D}
    (h : SpongeMerklePresent stepDigestsOf r l d) (hl : l ⊆ l') :
    SpongeMerklePresent stepDigestsOf r l' d := by
  obtain ⟨e, he, hd⟩ := h
  exact ⟨e, hl he, hd⟩

theorem jointHit_of_spongeHit {s₀ : D} {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    {x : SpongeQuery Msg D (HashQuery T D)} {y : SpongeMerkleAnswer Msg Chal T D x}
    (h : SpongeHit s₀ l x y) : JointHit s₀ stepDigestsOf r l x y := by
  cases x with
  | chal i prev m => exact h
  | other q => exact False.elim h

theorem jointHit_of_spongeMerkleHit {s₀ : D} {stepDigestsOf : ℕ → Msg → List D} {r : ℕ}
    {l : Log (SpongeMerkleAnswer Msg Chal T D)}
    {x : SpongeQuery Msg D (HashQuery T D)} {y : SpongeMerkleAnswer Msg Chal T D x}
    (h : SpongeMerkleHit stepDigestsOf r l x y) : JointHit s₀ stepDigestsOf r l x y := by
  cases x with
  | chal i prev m => exact False.elim h
  | other q => exact h

namespace MerkleRO

/-- Per-entry Merkle digest cap under incremental sponge chaining: `M` for a
challenge step (specifically `M = 1` for single-root absorption) and `3` for a
Merkle hash query. -/
def spongeMerkleEntryCap (M : ℕ) (x : SpongeQuery Msg D (HashQuery T D)) : ℕ :=
  match x with
  | .chal _ _ _ => M
  | .other _ => 3

/-- Upper bound on the number of Merkle digests present in a sponge-Merkle log. -/
def spongeMerkleCap (M : ℕ) (l : Log (SpongeMerkleAnswer Msg Chal T D)) : ℕ :=
  (l.map fun e => spongeMerkleEntryCap M e.1).sum

/-- Per-entry sponge state cap: `2` (`prev` and `next`) for a challenge step,
`0` for a Merkle hash query. -/
def spongeStateEntryCap (x : SpongeQuery Msg D (HashQuery T D)) : ℕ :=
  match x with
  | .chal _ _ _ => 2
  | .other _ => 0

/-- Upper bound on the number of sponge states present in a sponge-Merkle log
(`1` for the initial state `s₀`, plus `2` per challenge entry). -/
def spongeStateCap (l : Log (SpongeMerkleAnswer Msg Chal T D)) : ℕ :=
  1 + (l.map fun e => spongeStateEntryCap e.1).sum

@[simp] theorem spongeMerkleCap_nil (M : ℕ) :
    spongeMerkleCap (Msg := Msg) (Chal := Chal) (T := T) (D := D) M [] = 0 := rfl

@[simp] theorem spongeStateCap_nil :
    spongeStateCap (Msg := Msg) (Chal := Chal) (T := T) (D := D) [] = 1 := rfl

theorem spongeMerkleCap_append_singleton (M : ℕ) (l : Log (SpongeMerkleAnswer Msg Chal T D))
    (e : Sigma (SpongeMerkleAnswer Msg Chal T D)) :
    spongeMerkleCap M (l ++ [e]) = spongeMerkleCap M l + spongeMerkleEntryCap M e.1 := by
  simp [spongeMerkleCap]

theorem spongeStateCap_append_singleton (l : Log (SpongeMerkleAnswer Msg Chal T D))
    (e : Sigma (SpongeMerkleAnswer Msg Chal T D)) :
    spongeStateCap (l ++ [e]) = spongeStateCap l + spongeStateEntryCap e.1 := by
  simp [spongeStateCap, Nat.add_assoc]

/-- Joint Bellman potential (multiplied by `|D|`) for `JointHit`:
starting with at most `pM` Merkle digests and `pS` sponge states in play and
at most `q` queries remaining, where each `.chal` query hits with probability
`≤ pS / |D|` and adds `(M, 2)` while each `.other` hash query hits with
probability `≤ pM / |D|` and adds `(3, 0)`. -/
noncomputable def jointHitPotential (M pM pS q : ℕ) : ℝ :=
  (Finset.range (q + 1)).sup' Finset.nonempty_range_add_one fun h =>
    (h : ℝ) * ((pM : ℝ) + M * (q - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2
      + ((q - h : ℕ) : ℝ) * (pS : ℝ) + ((q - h : ℕ) : ℝ) * ((q - h - 1 : ℕ) : ℝ)

theorem jointHitPotential_nonneg (M pM pS q : ℕ) : 0 ≤ jointHitPotential M pM pS q := by
  unfold jointHitPotential
  have h0 : (0 : ℕ) ∈ Finset.range (q + 1) := Finset.mem_range.mpr (Nat.succ_pos q)
  have hle := Finset.le_sup' (f := fun h : ℕ =>
    (h : ℝ) * ((pM : ℝ) + M * (q - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2
      + ((q - h : ℕ) : ℝ) * (pS : ℝ) + ((q - h : ℕ) : ℝ) * ((q - h - 1 : ℕ) : ℝ)) h0
  refine le_trans ?_ hle
  positivity

theorem jointHitPotential_mono_q (M pM pS q : ℕ) :
    jointHitPotential M pM pS q ≤ jointHitPotential M pM pS (q + 1) := by
  unfold jointHitPotential
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h : ℕ =>
    (h : ℝ) * ((pM : ℝ) + M * (q + 1 - h : ℕ)) + (3 : ℝ) * h * (h - 1 : ℕ) / 2
      + ((q + 1 - h : ℕ) : ℝ) * (pS : ℝ) + ((q + 1 - h : ℕ) : ℝ) * ((q + 1 - h - 1 : ℕ) : ℝ)) hmem)
  have hsub1 : ((q - h : ℕ) : ℝ) ≤ ((q + 1 - h : ℕ) : ℝ) := by
    exact_mod_cast (by omega : q - h ≤ q + 1 - h)
  have hsub2 : ((q - h - 1 : ℕ) : ℝ) ≤ ((q + 1 - h - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : q - h - 1 ≤ q + 1 - h - 1)
  gcongr

theorem jointHitPotential_chal_step (M pM pS q : ℕ) :
    (pS : ℝ) + jointHitPotential M (pM + M) (pS + 2) q ≤ jointHitPotential M pM pS (q + 1) := by
  unfold jointHitPotential
  rw [add_comm, Finset.sup'_add]
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h' : ℕ =>
    (h' : ℝ) * ((pM : ℝ) + M * (q + 1 - h' : ℕ)) + (3 : ℝ) * h' * (h' - 1 : ℕ) / 2
      + ((q + 1 - h' : ℕ) : ℝ) * (pS : ℝ) + ((q + 1 - h' : ℕ) : ℝ) * ((q + 1 - h' - 1 : ℕ) : ℝ)) hmem)
  have hsub1 : ((q + 1 - h : ℕ) : ℝ) = ((q - h : ℕ) : ℝ) + 1 := by
    exact_mod_cast (by omega : q + 1 - h = q - h + 1)
  have hsub2 : q + 1 - h - 1 = q - h := by omega
  have hc : (2 : ℝ) * ((q - h : ℕ) : ℝ) + ((q - h : ℕ) : ℝ) * ((q - h - 1 : ℕ) : ℝ) =
      (((q - h : ℕ) : ℝ) + 1) * ((q - h : ℕ) : ℝ) := by
    generalize q - h = c
    cases c with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  rw [hsub1, hsub2]
  push_cast
  linarith

theorem jointHitPotential_hash_step (M pM pS q : ℕ) :
    (pM : ℝ) + jointHitPotential M (pM + 3) pS q ≤ jointHitPotential M pM pS (q + 1) := by
  unfold jointHitPotential
  rw [add_comm, Finset.sup'_add]
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hlt : h < q + 1 := Finset.mem_range.mp hh
  have hmem : h + 1 ∈ Finset.range (q + 2) := Finset.mem_range.mpr (by omega)
  refine le_trans ?_ (Finset.le_sup' (f := fun h' : ℕ =>
    (h' : ℝ) * ((pM : ℝ) + M * (q + 1 - h' : ℕ)) + (3 : ℝ) * h' * (h' - 1 : ℕ) / 2
      + ((q + 1 - h' : ℕ) : ℝ) * (pS : ℝ) + ((q + 1 - h' : ℕ) : ℝ) * ((q + 1 - h' - 1 : ℕ) : ℝ)) hmem)
  have hsub1 : q + 1 - (h + 1) = q - h := by omega
  have hsub2 : h + 1 - 1 = h := by omega
  rw [hsub1, hsub2]
  have h3 : (3 : ℝ) * (h : ℝ) + 3 * (h : ℝ) * ((h - 1 : ℕ) : ℝ) / 2 =
      3 * ((h + 1 : ℕ) : ℝ) * (h : ℝ) / 2 := by
    cases h with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hM : (0 : ℝ) ≤ (M : ℝ) * ((q - h : ℕ) : ℝ) := by positivity
  push_cast at h3 ⊢
  nlinarith

/-- **Optimal closed-form bound (`c = 3 / 2`) for incremental sponge chaining.**
Whenever each sponge step brings at most `M ≤ 3` Merkle digests into play
(in particular `M = 1`, `entryCap = 1`),
`jointHitPotential M 0 1 Q ≤ 3 * Q ^ 2 / 2`. -/
theorem jointHitPotential_zero_one_le {M : ℕ} (hM : M ≤ 3) (Q : ℕ) :
    jointHitPotential M 0 1 Q ≤ 3 * (Q : ℝ) ^ 2 / 2 := by
  unfold jointHitPotential
  refine Finset.sup'_le _ _ fun h hh => ?_
  have hle : h ≤ Q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hh)
  have hMr : (M : ℝ) ≤ 3 := by exact_mod_cast hM
  have hsub : ((Q - h : ℕ) : ℝ) = (Q : ℝ) - (h : ℝ) := Nat.cast_sub hle
  have hh1 : ((h - 1 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast Nat.sub_le h 1
  have hc_eq : ((Q - h : ℕ) : ℝ) * 1 + ((Q - h : ℕ) : ℝ) * ((Q - h - 1 : ℕ) : ℝ) =
      ((Q - h : ℕ) : ℝ) ^ 2 := by
    generalize Q - h = c
    cases c with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
  have hnn_c : (0 : ℝ) ≤ (Q : ℝ) - (h : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr hle)
  have h1 : (h : ℝ) * ((0 : ℕ) + (M : ℝ) * ((Q - h : ℕ) : ℝ)) ≤
      3 * (h : ℝ) * ((Q : ℝ) - (h : ℝ)) := by
    rw [Nat.cast_zero, zero_add, hsub]
    have hmul : (0 : ℝ) ≤ (h : ℝ) * ((Q : ℝ) - (h : ℝ)) := mul_nonneg (Nat.cast_nonneg h) hnn_c
    nlinarith
  have h2 : (3 : ℝ) * (h : ℝ) * ((h - 1 : ℕ) : ℝ) / 2 ≤ 3 * (h : ℝ) ^ 2 / 2 := by
    have : (3 : ℝ) * (h : ℝ) * ((h - 1 : ℕ) : ℝ) ≤ 3 * (h : ℝ) * (h : ℝ) := by gcongr
    linarith [sq (h : ℝ)]
  have hquad : 3 * (h : ℝ) * ((Q : ℝ) - (h : ℝ)) + 3 * (h : ℝ) ^ 2 / 2 +
      ((Q : ℝ) - (h : ℝ)) ^ 2 ≤ 3 * (Q : ℝ) ^ 2 / 2 := by
    have hsq : 0 ≤ ((Q : ℝ) - (h : ℝ)) ^ 2 := sq_nonneg _
    linarith
  rw [Nat.cast_one, add_assoc _ (((Q - h : ℕ) : ℝ) * 1), hc_eq, hsub]
  rw [hsub] at h1
  exact (add_le_add (add_le_add h1 h2) le_rfl).trans hquad

/-- Specialization of `jointHitPotential_zero_one_le` to single-root incremental
absorption (`entryCap = 1`). -/
theorem jointHitPotential_entryCap_one_le (Q : ℕ) :
    jointHitPotential 1 0 1 Q ≤ 3 * (Q : ℝ) ^ 2 / 2 :=
  jointHitPotential_zero_one_le (by decide) Q

end MerkleRO

section SpongeCount

variable {s₀ : D} {stepDigestsOf : ℕ → Msg → List D} {r M : ℕ}

theorem length_spongeEntryDigests_le
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    (e : Sigma (SpongeMerkleAnswer Msg Chal T D)) :
    (spongeEntryDigests stepDigestsOf r e).length ≤ spongeMerkleEntryCap M e.1 := by
  obtain ⟨x, y⟩ := e
  cases x with
  | chal i prev m =>
    simp only [spongeEntryDigests, spongeHashDigests, List.append_nil, spongeChalDigests,
      spongeMerkleEntryCap]
    split_ifs with hi
    · exact hM i hi m
    · exact Nat.zero_le M
  | other q =>
    simp only [spongeEntryDigests, spongeChalDigests, List.nil_append, spongeMerkleEntryCap]
    cases q with
    | rows _ => exact show 1 ≤ 3 by decide
    | node _ _ => exact le_refl 3

theorem exists_finset_spongeMerklePresent
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    ∃ S : Finset D, S.card ≤ spongeMerkleCap M l ∧
      ∀ d, SpongeMerklePresent stepDigestsOf r l d → d ∈ S := by
  classical
  refine ⟨(l.flatMap (spongeEntryDigests stepDigestsOf r)).toFinset, ?_, fun d hd => ?_⟩
  · refine (List.toFinset_card_le _).trans ?_
    induction l with
    | nil => simp [spongeMerkleCap]
    | cons e l ih =>
      rw [List.flatMap_cons, List.length_append, spongeMerkleCap, List.map_cons, List.sum_cons]
      have he := length_spongeEntryDigests_le hM e
      change (spongeEntryDigests stepDigestsOf r e).length +
          (l.flatMap (spongeEntryDigests stepDigestsOf r)).length ≤
        spongeMerkleEntryCap M e.1 + spongeMerkleCap M l
      omega
  · rw [List.mem_toFinset, List.mem_flatMap]
    exact hd

theorem exists_finset_spongePresent (s₀ : D) (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    ∃ S : Finset D, S.card ≤ spongeStateCap l ∧ ∀ s, SpongePresent s₀ l s → s ∈ S := by
  classical
  refine ⟨(s₀ :: l.flatMap fun e => spongeStates e.1 e.2).toFinset, ?_, fun s hs => ?_⟩
  · refine (List.toFinset_card_le _).trans ?_
    rw [List.length_cons, spongeStateCap]
    suffices h : (l.flatMap fun e => spongeStates e.1 e.2).length ≤
        (l.map fun e => spongeStateEntryCap e.1).sum by omega
    induction l with
    | nil => simp
    | cons e l ih =>
      rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons]
      have he : (spongeStates e.1 e.2).length ≤ spongeStateEntryCap e.1 := by
        obtain ⟨x, y⟩ := e
        cases x with
        | chal i prev m =>
          obtain ⟨next, c⟩ := y
          simp [spongeStates, spongeStateEntryCap]
        | other q => simp [spongeStates, spongeStateEntryCap]
      omega
  · rw [List.mem_toFinset, List.mem_cons]
    rcases hs with rfl | ⟨e, he, hs⟩
    · exact Or.inl rfl
    · exact Or.inr (List.mem_flatMap.mpr ⟨e, he, hs⟩)

variable [Fintype D] [Nonempty D]

theorem fractionLE_spongeMerklePresent
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    FractionLE (fun y : D => SpongeMerklePresent stepDigestsOf r l y)
      ((spongeMerkleCap M l : ℝ) / Fintype.card D) := by
  obtain ⟨S, hS, hmem⟩ := exists_finset_spongeMerklePresent (r := r) hM l
  refine ⟨S, ?_, hmem⟩
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]
  exact_mod_cast hS

theorem fractionLE_spongePresent [∀ i, Fintype (Chal i)] [∀ i, Nonempty (Chal i)]
    (s₀ : D) (l : Log (SpongeMerkleAnswer Msg Chal T D)) (i : ℕ) :
    FractionLE (fun y : D × Chal i => SpongePresent s₀ l y.1)
      ((spongeStateCap l : ℝ) / Fintype.card D) := by
  obtain ⟨S, hS, hmem⟩ := exists_finset_spongePresent s₀ l
  refine ⟨S ×ˢ (Finset.univ : Finset (Chal i)), ?_, fun y hy =>
    Finset.mem_product.mpr ⟨hmem y.1 hy, Finset.mem_univ y.2⟩⟩
  rw [Finset.card_product, Finset.card_univ, Fintype.card_prod]
  have hDne : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hScast : (S.card : ℝ) ≤ (spongeStateCap l : ℝ) := by exact_mod_cast hS
  have hC0 : (0 : ℝ) ≤ Fintype.card (Chal i) := Nat.cast_nonneg _
  calc ((S.card * Fintype.card (Chal i) : ℕ) : ℝ)
      = (S.card : ℝ) * (Fintype.card (Chal i) : ℝ) := by push_cast; ring
    _ ≤ (spongeStateCap l : ℝ) * (Fintype.card (Chal i) : ℝ) :=
        mul_le_mul_of_nonneg_right hScast hC0
    _ = ((spongeStateCap l : ℝ) / Fintype.card D) *
          ((Fintype.card D * Fintype.card (Chal i) : ℕ) : ℝ) := by
        push_cast
        field_simp

variable [DecidableEq (SpongeQuery Msg D (HashQuery T D))] [∀ i, Fintype (Chal i)]
  [∀ i, Nonempty (Chal i)] {α : Type w}

/-- **Joint hit probability from any log, via the joint Bellman potential.** -/
theorem prob_hasBadFrom_jointHit_le
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    {c : OracleComp (SpongeMerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q)
    (l : Log (SpongeMerkleAnswer Msg Chal T D)) :
    prob (fun _ l' => HasBadFrom (JointHit s₀ stepDigestsOf r) l.length l') c l
      ≤ jointHitPotential M (spongeMerkleCap M l) (spongeStateCap l) Q / Fintype.card D := by
  classical
  have hDpos : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  induction c generalizing l Q with
  | pure a =>
    rw [prob_pure, ite_eq_right (not_hasBadFrom_of_length_le le_rfl)]
    exact div_nonneg (jointHitPotential_nonneg M _ _ Q) hDpos.le
  | queryBind x k ih =>
    cases Q with
    | zero => exact absurd hc (queryBound_queryBind_zero x k)
    | succ Q =>
      cases hx : l.dlookup x with
      | some y =>
        rw [prob_queryBind_of_lookup hx]
        exact (ih y (hc y) l).trans
          (div_le_div_of_nonneg_right (jointHitPotential_mono_q M _ _ Q) hDpos.le)
      | none =>
        have hYpos : (0 : ℝ) < Fintype.card (SpongeMerkleAnswer Msg Chal T D x) :=
          Nat.cast_pos.mpr Fintype.card_pos
        set B := jointHitPotential M (spongeMerkleCap M l + spongeMerkleEntryCap M x)
            (spongeStateCap l + spongeStateEntryCap x) Q / Fintype.card D with hBdef
        have hB0 : 0 ≤ B := div_nonneg (jointHitPotential_nonneg M _ _ Q) hDpos.le
        have hstep : ∀ y : SpongeMerkleAnswer Msg Chal T D x,
            prob (fun _ l' => HasBadFrom (JointHit s₀ stepDigestsOf r) l.length l') (k y)
                (l ++ [⟨x, y⟩])
              ≤ (if JointHit s₀ stepDigestsOf r l x y then 1 else 0) + B := by
          intro y
          by_cases hb : JointHit s₀ stepDigestsOf r l x y
          · rw [ite_eq_left hb]
            exact (prob_le_one _ _ _).trans (le_add_of_nonneg_right hB0)
          · rw [ite_eq_right hb, zero_add]
            refine le_trans (prob_mono_of_outcome fun a l' ha h => ?_)
              ((ih y (hc y) (l ++ [⟨x, y⟩])).trans (le_of_eq ?_))
            · obtain ⟨t, rfl⟩ := ha.prefix
              rw [List.append_assoc, List.singleton_append] at h ⊢
              rw [List.length_append, List.length_singleton]
              exact (hasBadFrom_length_cons h).resolve_left hb
            · rw [spongeMerkleCap_append_singleton, spongeStateCap_append_singleton]
        rw [prob_queryBind_of_fresh hx, div_le_iff₀ hYpos]
        cases x with
        | chal i prev m =>
          have hfrac : FractionLE (JointHit s₀ stepDigestsOf r l (.chal i prev m))
              ((spongeStateCap l : ℝ) / Fintype.card D) :=
            fractionLE_spongePresent s₀ l i
          calc ∑ y : D × Chal i,
                prob (fun _ l' => HasBadFrom (JointHit s₀ stepDigestsOf r) l.length l') (k y)
                  (l ++ [⟨.chal i prev m, y⟩])
              ≤ ∑ y : D × Chal i,
                  ((if JointHit s₀ stepDigestsOf r l (.chal i prev m) y then (1 : ℝ) else 0) + B) :=
                Finset.sum_le_sum fun y _ => hstep y
            _ = (∑ y : D × Chal i,
                    if JointHit s₀ stepDigestsOf r l (.chal i prev m) y then (1 : ℝ) else 0) +
                  Fintype.card (D × Chal i) * B := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ ≤ ((spongeStateCap l : ℝ) / Fintype.card D) * Fintype.card (D × Chal i) +
                  Fintype.card (D × Chal i) * B :=
                add_le_add_left hfrac.sum_ite_le _
            _ = ((spongeStateCap l : ℝ) +
                    jointHitPotential M (spongeMerkleCap M l + M) (spongeStateCap l + 2) Q) /
                  Fintype.card D * Fintype.card (D × Chal i) := by
                rw [hBdef, spongeMerkleEntryCap, spongeStateEntryCap]
                field_simp
            _ ≤ (jointHitPotential M (spongeMerkleCap M l) (spongeStateCap l) (Q + 1) /
                  Fintype.card D) * Fintype.card (D × Chal i) :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right
                    (jointHitPotential_chal_step M (spongeMerkleCap M l) (spongeStateCap l) Q)
                    hDpos.le)
                  hYpos.le
        | other q =>
          have hfrac : FractionLE (JointHit s₀ stepDigestsOf r l (.other q))
              ((spongeMerkleCap M l : ℝ) / Fintype.card D) :=
            fractionLE_spongeMerklePresent hM l
          calc ∑ y : D,
                prob (fun _ l' => HasBadFrom (JointHit s₀ stepDigestsOf r) l.length l') (k y)
                  (l ++ [⟨.other q, y⟩])
              ≤ ∑ y : D,
                  ((if JointHit s₀ stepDigestsOf r l (.other q) y then (1 : ℝ) else 0) + B) :=
                Finset.sum_le_sum fun y _ => hstep y
            _ = (∑ y : D, if JointHit s₀ stepDigestsOf r l (.other q) y then (1 : ℝ) else 0) +
                  Fintype.card D * B := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            _ ≤ ((spongeMerkleCap M l : ℝ) / Fintype.card D) * Fintype.card D +
                  Fintype.card D * B :=
                add_le_add_left hfrac.sum_ite_le _
            _ = ((spongeMerkleCap M l : ℝ) +
                    jointHitPotential M (spongeMerkleCap M l + 3) (spongeStateCap l) Q) /
                  Fintype.card D * Fintype.card D := by
                simp only [hBdef, spongeMerkleEntryCap, spongeStateEntryCap, Nat.add_zero]
                field_simp
            _ ≤ (jointHitPotential M (spongeMerkleCap M l) (spongeStateCap l) (Q + 1) /
                  Fintype.card D) * Fintype.card D :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right
                    (jointHitPotential_hash_step M (spongeMerkleCap M l) (spongeStateCap l) Q)
                    hDpos.le)
                  hDpos.le

/-- **Joint hit probability from the empty log, via the Bellman potential.** -/
theorem prob_hasBad_jointHit_le_potential
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    {c : OracleComp (SpongeMerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (JointHit s₀ stepDigestsOf r) l) c []
      ≤ jointHitPotential M 0 1 Q / Fintype.card D := by
  simpa only [HasBad, List.length_nil, spongeMerkleCap_nil, spongeStateCap_nil] using
    prob_hasBadFrom_jointHit_le (s₀ := s₀) hM hc []

/-- **Tight incremental sponge BCS collision bound (`c = 3 / 2`).**
When each sponge challenge step brings at most `M ≤ 3` Merkle digests into play
(in particular **`M = 1`**, `entryCap = 1`), any `Q`-query computation from the
empty log triggers a Merkle or sponge hit with probability at most
`3 * Q ^ 2 / (2 * card D)`. -/
theorem prob_hasBad_jointHit_le {M : ℕ} (hM3 : M ≤ 3)
    (hM : ∀ i < r, ∀ m, (stepDigestsOf i m).length ≤ M)
    {c : OracleComp (SpongeMerkleAnswer Msg Chal T D) α} {Q : ℕ} (hc : c.QueryBound Q) :
    prob (fun _ l => HasBad (JointHit s₀ stepDigestsOf r) l) c []
      ≤ 3 * (Q : ℝ) ^ 2 / (2 * Fintype.card D) := by
  refine (prob_hasBad_jointHit_le_potential (s₀ := s₀) hM hc).trans ?_
  have hle := jointHitPotential_zero_one_le hM3 Q
  have hD : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  calc jointHitPotential M 0 1 Q / Fintype.card D
      ≤ (3 * (Q : ℝ) ^ 2 / 2) / Fintype.card D := div_le_div_of_nonneg_right hle hD
    _ = 3 * (Q : ℝ) ^ 2 / (2 * Fintype.card D) := by ring

end SpongeCount

end CertiFri.Oracle
