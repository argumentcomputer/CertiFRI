import CertiFriProofs.Theory.Stark.Balance

/-!
# Balance over the integers, and equal multisets of messages

A lookup argument proves that a list of messages with multiplicities is
balanced *in the field* (`Balanced`, in `Balance.lean`): for every
fingerprint, the multiplicities add up to zero in the field, so a sum that is
a multiple of the characteristic counts as zero. This file says what that
means when the multiplicities are small integers: the sums are zero in the
integers, and for multiplicities `1` and `-1` the messages sent and the
messages received are the same, as multisets.

## Contents

* `balanced_int_of_balanced`: a list with integer multiplicities that is
  balanced in the field is balanced over the integers, when the absolute
  values of the multiplicities add up to less than the characteristic.
* `map_fpPoly_eq_of_balanced`: when the list of the messages sent, each with
  multiplicity `1`, followed by the messages received, each with multiplicity
  `-1`, is balanced in the field, and there are fewer messages than the
  characteristic, the multiset of the fingerprint polynomials of the messages
  sent is that of the messages received.

## Assumptions

The field has characteristic `p` (`CharP K p`), and `p = 0` is allowed: in
characteristic zero there is no condition on the multiplicities. Otherwise the
bound is on the whole list, not on each fingerprint: the absolute values of all
the multiplicities add up to less than `p`.

## What is not covered

* That the multiplicities of an actual circuit are small integers, and that
  there are fewer of them than the characteristic, is the business of the
  application: here both are hypotheses.
* Messages are compared by their fingerprint polynomials (`fpPoly`). Two
  messages that differ by trailing zeros have the same fingerprint polynomial
  and are identified: the conclusion is an equality of multisets of
  polynomials, not of multisets of lists.
-/

namespace CertiFri.Stark.Model

open Polynomial

variable {K : Type} [Field K]

/-! ## Small integers in a field -/

/-- An integer that is zero in a field of characteristic `p`, and whose
absolute value is below `p`, is zero. In characteristic zero there is no
condition on the absolute value. -/
private theorem int_eq_zero_of_cast_eq_zero {p : ℕ} [CharP K p] {n : ℤ} (h : (n : K) = 0)
    (hp : p = 0 ∨ n.natAbs < p) : n = 0 := by
  rw [CharP.intCast_eq_zero_iff K p] at h
  rcases hp with rfl | hp
  · rw [Nat.cast_zero] at h
    exact zero_dvd_iff.mp h
  · refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
    rw [Int.natAbs_natCast]
    exact hp

/-- The absolute value of a sum of integers is at most the sum of the absolute
values. -/
private theorem natAbs_sum_le (l : List ℤ) : l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => rw [List.sum_nil, List.map_nil, List.sum_nil, Int.natAbs_zero]
  | cons a l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (Int.natAbs_add_le a l.sum).trans (Nat.add_le_add_left ih _)

/-- A sum of natural numbers over the members of a list that pass a test is at
most the sum over the whole list. -/
private theorem sum_map_filter_le {α : Type*} (l : List α) (t : α → Bool) (f : α → ℕ) :
    ((l.filter t).map f).sum ≤ (l.map f).sum := by
  induction l with
  | nil => rw [List.filter_nil]
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.filter_cons]
    split
    · rw [List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _
    · exact ih.trans (Nat.le_add_left _ _)

/-! ## Balance over the integers -/

open Classical in
/-- **Balance over the integers.** A list of messages with integer
multiplicities that is balanced in a field of characteristic `p` is balanced
over the integers, when the absolute values of the multiplicities add up to
less than `p`: for every fingerprint, the multiplicities of the items with that
fingerprint add up to zero in the integers. In characteristic zero there is no
condition on the multiplicities. -/
theorem balanced_int_of_balanced {p : ℕ} [CharP K p] {items : List (ℤ × List K)}
    (hbal : Balanced (items.map fun it => ((it.1 : K), it.2)))
    (hsmall : p = 0 ∨ (items.map fun it => it.1.natAbs).sum < p) (q : K[X]) :
    ((items.filter fun it => fpPoly it.2 = q).map Prod.fst).sum = 0 := by
  refine int_eq_zero_of_cast_eq_zero (K := K) ?_ (hsmall.imp_right fun h => lt_of_le_of_lt ?_ h)
  · have h := hbal q
    rw [List.filter_map, List.map_map] at h
    rw [Int.cast_list_sum, List.map_map]
    exact h
  · refine (natAbs_sum_le _).trans ?_
    rw [List.map_map]
    exact sum_map_filter_le items _ _

/-! ## Messages sent and messages received -/

/-- In a list of messages that all have the same integer multiplicity `c`, the
multiplicities of the items with a given fingerprint add up to `c` times the
number of messages with that fingerprint. -/
private theorem sum_filter_map_const [DecidableEq K[X]] (c : ℤ) (l : List (List K))
    (q : K[X]) :
    (((l.map fun m => (c, m)).filter fun it => fpPoly it.2 = q).map Prod.fst).sum
      = (l.map fpPoly).count q * c := by
  induction l with
  | nil => simp
  | cons m l ih =>
    by_cases h : fpPoly m = q <;> simp [h, ih, add_mul, add_comm]

/-- **Messages sent are the messages received.** When the list of the messages
sent, each with multiplicity `1`, followed by the messages received, each with
multiplicity `-1`, is balanced in a field of characteristic `p`, and there are
fewer than `p` messages in all, every fingerprint is sent as many times as it
is received: the multiset of the fingerprint polynomials of the messages sent
is that of the messages received. In characteristic zero there is no condition
on the number of messages. -/
theorem map_fpPoly_eq_of_balanced {p : ℕ} [CharP K p] {sent received : List (List K)}
    (hbal : Balanced
      ((sent.map fun m => ((1 : K), m)) ++ (received.map fun m => ((-1 : K), m))))
    (hsmall : p = 0 ∨ sent.length + received.length < p) :
    ((sent.map fpPoly : List K[X]) : Multiset K[X]) = (received.map fpPoly : List K[X]) := by
  classical
  refine Multiset.ext.mpr fun q => ?_
  rw [Multiset.coe_count, Multiset.coe_count]
  have h := balanced_int_of_balanced (p := p)
    (items := (sent.map fun m => ((1 : ℤ), m)) ++ (received.map fun m => ((-1 : ℤ), m)))
    (by simpa [Function.comp_def] using hbal) (by simpa [Function.comp_def] using hsmall) q
  rw [List.filter_append, List.map_append, List.sum_append, sum_filter_map_const,
    sum_filter_map_const] at h
  omega

end CertiFri.Stark.Model
