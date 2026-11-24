import Mathlib
import CertiFriProofs.Theory.Stark.Logup

/-!
# The degree of the lookup constraints

When the lookup constraints (`logupValues`, `Theory/Stark/Logup.lean`) are
computed on polynomials, each value is a polynomial. This file bounds its
degree: if the structure constants, the public values and the scaled difference
are constants, and every other input has degree at most `E`, every value has
degree at most `(max groupSize 1 + 1) * E`.

A group of lookups holds at most `max groupSize 1` messages. Each coordinate of
a message has degree at most `E`: it is a combination, with constant
coefficients, of values of nodes. The constraint of the group is a product of
its messages and of one difference of entries of the lookup trace, minus
products of all but one message and a multiplicity.

An array "has degree at most `n`" when each of its entries does; an entry out
of range reads zero, of degree zero. The lemmas follow the computation:
`natDegree_coordMul_le` for a product of tuples, `natDegree_lookupMessage_le`
for a message, `natDegree_groupConstraint_le` for the constraint of a group and
`natDegree_logupValues_le` for all of them.

Nothing here is about a protocol.
-/

namespace CertiFri.Stark.Model

open Polynomial

variable {R : Type} [CommRing R]

/-! ## Arrays -/

/-- An entry of `Array.ofFn f` is a value of `f`, or zero. -/
private theorem natDegree_getD_ofFn_le {n : ℕ} (f : Fin n → R[X]) (D : ℕ)
    (hf : ∀ k, (f k).natDegree ≤ D) (i : ℕ) : ((Array.ofFn f).getD i 0).natDegree ≤ D := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  split
  · simpa using hf _
  · simp

/-- An entry of `a ++ b` is an entry of `a` or an entry of `b`. -/
private theorem natDegree_getD_append_le (a b : Array R[X]) (D : ℕ)
    (ha : ∀ i, (a.getD i 0).natDegree ≤ D) (hb : ∀ i, (b.getD i 0).natDegree ≤ D) (i : ℕ) :
    ((a ++ b).getD i 0).natDegree ≤ D := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split
  · rw [← Array.getD_eq_getD_getElem?]
    exact ha i
  · rw [← Array.getD_eq_getD_getElem?]
    exact hb _

/-- An entry of a slice of an array of constants is a constant. -/
private theorem natDegree_getD_extract (a : Array R[X]) (start stop : ℕ)
    (ha : ∀ i, (a.getD i 0).natDegree = 0) (i : ℕ) :
    ((a.extract start stop).getD i 0).natDegree = 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rw [← Array.getD_eq_getD_getElem?]
    exact ha _
  · simp

/-- An entry of an entry of `messages`, read with defaults, is an entry of one
of its elements, or zero. -/
private theorem natDegree_getD_getD_le (messages : Array (Array R[X])) (E : ℕ)
    (hmsg : ∀ m ∈ messages, ∀ i, (m.getD i 0).natDegree ≤ E) (j i : ℕ) :
    ((messages.getD j #[]).getD i 0).natDegree ≤ E := by
  by_cases hj : j < messages.size
  · have h : messages.getD j #[] = messages[j] := by simp [Array.getD, hj]
    rw [h]
    exact hmsg _ (Array.getElem_mem hj) i
  · have h : messages.getD j #[] = #[] := by simp [Array.getD, hj]
    rw [h]
    simp

/-- Appending arrays of degree at most `D` gives an array of degree at most
`D`. -/
private theorem natDegree_foldl_append_le {α : Type} (f : α → Array R[X]) (D : ℕ)
    (hf : ∀ g i, ((f g).getD i 0).natDegree ≤ D) (l : List α) (out : Array R[X])
    (hout : ∀ i, (out.getD i 0).natDegree ≤ D) (i : ℕ) :
    ((l.foldl (fun out g => out ++ f g) out).getD i 0).natDegree ≤ D := by
  induction l generalizing out with
  | nil => exact hout i
  | cons g l ih =>
    rw [List.foldl_cons]
    exact ih _ (natDegree_getD_append_le _ _ D hout (hf g))

/-! ## Sums and products of tuples -/

/-- The fold of `sumRange` keeps a bound on the degree. -/
private theorem natDegree_foldl_add_le (f : ℕ → R[X]) (D : ℕ) (hf : ∀ i, (f i).natDegree ≤ D)
    (l : List ℕ) (acc : R[X]) (hacc : acc.natDegree ≤ D) :
    (l.foldl (fun acc i => acc + f i) acc).natDegree ≤ D := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons i l ih =>
    rw [List.foldl_cons]
    exact ih _ ((natDegree_add_le _ _).trans (max_le hacc (hf i)))

/-- A sum of polynomials of degree at most `D` has degree at most `D`. -/
private theorem natDegree_sumRange_le (n : ℕ) (f : ℕ → R[X]) (D : ℕ)
    (hf : ∀ i, (f i).natDegree ≤ D) : (sumRange n f).natDegree ≤ D :=
  natDegree_foldl_add_le f D hf _ 0 (by simp)

/-- The product of tuples of degrees at most `da` and `db`, with constant
structure constants, has degree at most `da + db`. -/
private theorem natDegree_coordMul_le (d : ℕ) (table a b : Array R[X]) (da db : ℕ)
    (htable : ∀ i, (table.getD i 0).natDegree = 0)
    (ha : ∀ i, (a.getD i 0).natDegree ≤ da) (hb : ∀ i, (b.getD i 0).natDegree ≤ db) (i : ℕ) :
    ((coordMul d table a b).getD i 0).natDegree ≤ da + db := by
  unfold coordMul
  refine natDegree_getD_ofFn_le _ _ (fun k => ?_) i
  refine natDegree_sumRange_le _ _ _ fun i => natDegree_sumRange_le _ _ _ fun j => ?_
  refine (natDegree_mul_le ..).trans ?_
  rw [htable, add_zero]
  exact (natDegree_mul_le ..).trans (add_le_add (ha i) (hb j))

/-- The coordinates of one are constants. -/
private theorem natDegree_coordOne_le (d D i : ℕ) :
    ((coordOne d : Array R[X]).getD i 0).natDegree ≤ D := by
  unfold coordOne
  refine natDegree_getD_ofFn_le _ _ (fun k => ?_) i
  split <;> simp

/-- Each product by a tuple of degree at most `E` adds at most `E` to the
degree. -/
private theorem natDegree_foldl_coordMul_le (d : ℕ) (table : Array R[X]) (E : ℕ)
    (htable : ∀ i, (table.getD i 0).natDegree = 0) (l : List (Array R[X]))
    (hl : ∀ m ∈ l, ∀ i, (m.getD i 0).natDegree ≤ E) (acc : Array R[X]) (n : ℕ)
    (hacc : ∀ i, (acc.getD i 0).natDegree ≤ n) (i : ℕ) :
    ((l.foldl (coordMul d table) acc).getD i 0).natDegree ≤ n + l.length * E := by
  induction l generalizing acc n with
  | nil => simpa using hacc i
  | cons m l ih =>
    rw [List.foldl_cons, List.length_cons, Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm]
    exact ih (fun m' hm' => hl m' (List.mem_cons_of_mem _ hm')) _ _
      (natDegree_coordMul_le d table acc m n E htable hacc (hl m List.mem_cons_self))

/-- The product of the messages other than message `j`, taken over a list of
indices, has degree at most `E` per index. -/
private theorem natDegree_foldl_others_le (d : ℕ) (table : Array R[X]) (E : ℕ)
    (htable : ∀ i, (table.getD i 0).natDegree = 0) (messages : Array (Array R[X]))
    (hmsg : ∀ m ∈ messages, ∀ i, (m.getD i 0).natDegree ≤ E) (j : ℕ) (l : List ℕ)
    (acc : Array R[X]) (n : ℕ) (hacc : ∀ i, (acc.getD i 0).natDegree ≤ n) (i : ℕ) :
    ((l.foldl (fun product i =>
        if i = j then product else coordMul d table product (messages.getD i #[]))
      acc).getD i 0).natDegree ≤ n + l.length * E := by
  induction l generalizing acc n with
  | nil => simpa using hacc i
  | cons m l ih =>
    rw [List.foldl_cons, List.length_cons, Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm]
    refine ih _ _ fun i => ?_
    split
    · exact (hacc i).trans (Nat.le_add_right _ _)
    · exact natDegree_coordMul_le d table acc _ n E htable hacc
        (natDegree_getD_getD_le messages E hmsg m) i

/-! ## Messages and constraints -/

/-- A message has degree at most `E`, when the challenges are constants and the
values of the nodes have degree at most `E`. -/
private theorem natDegree_lookupMessage_le (d : ℕ) (table beta gamma buf : Array R[X])
    (lookup : Lookup) (E : ℕ) (htable : ∀ i, (table.getD i 0).natDegree = 0)
    (hbeta : ∀ i, (beta.getD i 0).natDegree = 0) (hgamma : ∀ i, (gamma.getD i 0).natDegree = 0)
    (hbuf : ∀ i, (buf.getD i 0).natDegree ≤ E) (i : ℕ) :
    ((lookupMessage d table beta gamma buf lookup).getD i 0).natDegree ≤ E := by
  simp only [lookupMessage]
  refine natDegree_getD_ofFn_le _ _ (fun k => ?_) i
  refine (natDegree_add_le _ _).trans (max_le ?_ (by rw [hbeta]; exact Nat.zero_le _))
  generalize k.val = k
  rw [← Array.foldr_toList]
  induction lookup.args.toList generalizing k with
  | nil => exact natDegree_getD_ofFn_le _ _ (fun _ => by simp) k
  | cons arg l ih =>
    rw [List.foldr_cons]
    have hshift := fun k => natDegree_coordMul_le d table _ gamma E 0 htable ih
      (fun j => (hgamma j).le) k
    refine natDegree_getD_ofFn_le _ _ (fun k => ?_) k
    split
    · exact (natDegree_add_le _ _).trans (max_le (hshift 0) (hbuf arg))
    · exact hshift k

/-- Subtracting, for each index of a list, the product of the other messages
and a multiplicity keeps the bound `(messages.size + 1) * E`. -/
private theorem natDegree_foldl_sub_le (d : ℕ) (table : Array R[X])
    (messages : Array (Array R[X])) (multiplicities : Array R[X]) (E : ℕ)
    (htable : ∀ i, (table.getD i 0).natDegree = 0)
    (hmsg : ∀ m ∈ messages, ∀ i, (m.getD i 0).natDegree ≤ E)
    (hmult : ∀ i, (multiplicities.getD i 0).natDegree ≤ E) (l : List ℕ) (acc : Array R[X])
    (hacc : ∀ i, (acc.getD i 0).natDegree ≤ (messages.size + 1) * E) (i : ℕ) :
    ((l.foldl
      (fun acc j =>
        Array.ofFn (n := d) fun k =>
          acc.getD k.val 0 -
            ((List.range messages.size).foldl
              (fun product i =>
                if i = j then product else coordMul d table product (messages.getD i #[]))
              (coordOne d)).getD k.val 0 * multiplicities.getD j 0)
      acc).getD i 0).natDegree ≤ (messages.size + 1) * E := by
  induction l generalizing acc with
  | nil => exact hacc i
  | cons j l ih =>
    rw [List.foldl_cons]
    refine ih _ fun i => natDegree_getD_ofFn_le _ _ (fun k => ?_) i
    refine (natDegree_sub_le _ _).trans (max_le (hacc _) ((natDegree_mul_le ..).trans ?_))
    rw [Nat.succ_mul]
    refine add_le_add ?_ (hmult j)
    simpa using natDegree_foldl_others_le d table E htable messages hmsg j
      (List.range messages.size) (coordOne d) 0 (natDegree_coordOne_le d 0) k.val

/-- The constraint of a group of messages of degree at most `E`, with
multiplicities and a difference of degree at most `E`, has degree at most
`(messages.size + 1) * E`. -/
private theorem natDegree_groupConstraint_le (d : ℕ) (table : Array R[X])
    (messages : Array (Array R[X])) (multiplicities diff : Array R[X]) (E : ℕ)
    (htable : ∀ i, (table.getD i 0).natDegree = 0)
    (hmsg : ∀ m ∈ messages, ∀ i, (m.getD i 0).natDegree ≤ E)
    (hmult : ∀ i, (multiplicities.getD i 0).natDegree ≤ E)
    (hdiff : ∀ i, (diff.getD i 0).natDegree ≤ E) (i : ℕ) :
    ((groupConstraint d table messages multiplicities diff).getD i 0).natDegree ≤
      (messages.size + 1) * E := by
  simp only [groupConstraint]
  refine natDegree_foldl_sub_le d table messages multiplicities E htable hmsg hmult _ _
    (fun i => ?_) i
  rw [Nat.succ_mul]
  refine natDegree_coordMul_le d table _ diff _ E htable (fun i => ?_) hdiff i
  rw [← Array.foldl_toList]
  simpa using natDegree_foldl_coordMul_le d table E htable messages.toList
    (fun m hm => hmsg m (Array.mem_toList_iff.mp hm)) (coordOne d) 0
    (natDegree_coordOne_le d 0) i

/-- **The degree of the lookup constraints.** On polynomial inputs, with
constant structure constants, public values and scaled difference, and all
other inputs of degree at most `E`, every lookup constraint has degree at most
`(max groupSize 1 + 1) * E`. -/
theorem natDegree_logupValues_le (d : ℕ) (table : Array R[X]) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array R[X]) (isLastRow : R[X])
    (groupSize E : ℕ) (htable : ∀ i, (table.getD i 0).natDegree = 0)
    (hpublics : ∀ i, (publics.getD i 0).natDegree = 0)
    (hdelta : ∀ i, (deltaScaled.getD i 0).natDegree = 0)
    (hbuf : ∀ i, (buf.getD i 0).natDegree ≤ E) (hstage2 : ∀ i, (stage2.getD i 0).natDegree ≤ E)
    (hstage2Next : ∀ i, (stage2Next.getD i 0).natDegree ≤ E) (hlast : isLastRow.natDegree ≤ E)
    (i : ℕ) :
    ((logupValues d table lookups buf stage2 stage2Next publics deltaScaled isLastRow
      groupSize).getD i 0).natDegree ≤ (max groupSize 1 + 1) * E := by
  simp only [logupValues]
  refine natDegree_foldl_append_le _ _ (fun g i => ?_) _ #[] (fun i => by simp) i
  have hsize : ((lookups.extract (g * max groupSize 1) ((g + 1) * max groupSize 1)).map
      (lookupMessage d table (publics.extract 0 d) (publics.extract d (2 * d)) buf)).size + 1 ≤
      max groupSize 1 + 1 := by
    rw [Array.size_map, Array.size_extract, Nat.succ_mul]
    omega
  refine le_trans ?_ (Nat.mul_le_mul_right E hsize)
  refine natDegree_groupConstraint_le d table _ _ _ E htable ?_ (fun j => ?_) (fun j => ?_) i
  · intro m hm j
    obtain ⟨lookup, -, rfl⟩ := Array.mem_map.mp hm
    exact natDegree_lookupMessage_le d table _ _ buf lookup E htable
      (natDegree_getD_extract publics 0 d hpublics)
      (natDegree_getD_extract publics d (2 * d) hpublics) hbuf j
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases (lookups.extract (g * max groupSize 1) ((g + 1) * max groupSize 1))[j]? with
    | none => simp
    | some lookup => simpa using hbuf lookup.multiplicity
  · refine natDegree_getD_ofFn_le _ _ (fun k => ?_) j
    refine (natDegree_sub_le _ _).trans (max_le ?_ (hstage2 _))
    split
    · exact hstage2 _
    · refine natDegree_getD_ofFn_le _ _ (fun k => ?_) k.val
      refine (natDegree_add_le _ _).trans (max_le (hstage2Next _) ?_)
      refine (natDegree_mul_le ..).trans ?_
      rw [hdelta, add_zero]
      exact hlast

end CertiFri.Stark.Model
