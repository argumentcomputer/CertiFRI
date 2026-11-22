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

end CertiFri.Oracle
