import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import CertiFriProofs.Refines

/-!
# Executable field computations under the abstraction map

Generic facts about a refinement `r : Refines F K`: what the abstraction map
`r.toModel` makes of the computations the executable verifier builds from the
field operations.

* `toModel_fieldPow`: exponentiation by squaring is the power in `K`.
* `toModel_getD_list_map`, `toModel_getD_array_map`, `toModel_getD_toList_map`:
  reading an entry with the default zero commutes with the map.
* `toModel_foldl_powers`: a left fold that adds each term of a list with a
  running power of a fixed element is, in `K`, the sum of the terms with the
  powers of that element.

Nothing here is about the verifier itself. The lemmas assume only the laws of
`Refines`: they hold for any representation, redundant or not.
-/

namespace CertiFri.Exec

variable {F K : Type} [FieldOps F] [Field K] (r : Refines F K)

/-! ## Powers -/

/-- Exponentiation by squaring over `bits` bits computes the power, for an
exponent below `2 ^ bits`. -/
theorem toModel_fieldPowBits (x : F) (bits : ℕ) :
    ∀ n, n < 2 ^ bits → r.toModel (fieldPowBits x bits n) = r.toModel x ^ n := by
  induction bits with
  | zero =>
    intro n h
    obtain rfl : n = 0 := by simpa using h
    rw [fieldPowBits, r.map_one, pow_zero]
  | succ bits ih =>
    intro n h
    have hhalf : n / 2 < 2 ^ bits := by
      rw [pow_succ] at h
      omega
    have e := ih (n / 2) hhalf
    simp only [fieldPowBits]
    split
    · rw [r.map_mul, e, ← pow_add]
      congr 1
      omega
    · rw [r.map_mul, r.map_mul, e, ← pow_add, ← pow_succ]
      congr 1
      omega

/-- The executable power is the power in the model. -/
theorem toModel_fieldPow (x : F) (n : ℕ) : r.toModel (fieldPow x n) = r.toModel x ^ n :=
  toModel_fieldPowBits r x _ n Nat.lt_log2_self

/-! ## Entries of lists and arrays -/

/-- An entry of a mapped list, with default zero, is the image of the entry of
the list with default zero. -/
theorem toModel_getD_list_map (l : List F) (i : ℕ) :
    (l.map r.toModel).getD i 0 = r.toModel (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? with
  | none => exact r.map_zero.symm
  | some a => rfl

/-- An entry of a mapped array, with default zero, is the image of the entry of
the array with default zero. -/
theorem toModel_getD_array_map (a : Array F) (i : ℕ) :
    (a.map r.toModel).getD i 0 = r.toModel (a.getD i 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? with
  | none => exact r.map_zero.symm
  | some a => rfl

/-- An entry of the mapped list of an array, with default zero, is the image of
the entry of the array with default zero. -/
theorem toModel_getD_toList_map (a : Array F) (i : ℕ) :
    (a.toList.map r.toModel).getD i 0 = r.toModel (a.getD i 0) := by
  rw [toModel_getD_list_map, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]

/-! ## Sums with powers of a fixed element -/

/-- A left fold over a list that keeps a sum and a running power: each element
`c` adds `f c` times the running power, and the running power is multiplied by
`alpha`. Started from the sum `a` and the power `p`, the sum it ends with is,
in the model, `a + p * ∑ k, alpha ^ k * f (l[k])`. -/
theorem toModel_foldl_powers {β : Type} (alpha : F) (f : β → F) (l : List β) (a p : F) :
    r.toModel (l.foldl (fun (acc : F × F) c => (acc.1 + acc.2 * f c, acc.2 * alpha)) (a, p)).1 =
      r.toModel a + r.toModel p *
        ∑ k : Fin l.length, r.toModel alpha ^ (k : ℕ) * r.toModel (f (l.get k)) := by
  induction l generalizing a p with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, r.map_add, r.map_mul, Fin.val_zero, pow_zero,
      one_mul, List.get_cons_zero, Fin.val_succ, pow_succ, Finset.mul_sum, mul_add, add_assoc]
    refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun k _ => ?_))
    have e : (c :: l).get k.succ = l.get k := rfl
    rw [e]
    ring

end CertiFri.Exec
