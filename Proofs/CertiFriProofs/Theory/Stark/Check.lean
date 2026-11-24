import Mathlib
import CertiFriProofs.Theory.Stark.Air

/-!
# The verifier's check of one circuit, over the model field

The verifier opens the columns of a circuit at an out-of-domain point `ζ` and
at its successor, evaluates the constraints on the opened rows, folds them with
`α`, and compares the result, divided by the vanishing polynomial of the trace
domain at `ζ`, with the quotient reassembled from its opened chunks. This file
states that check over a field `K` and relates it to the polynomials of
`Theory/Stark/Air.lean`.

## Contents

* `ExtData K`: what the check uses of the extension structure of `K` over its
  base field: the degree `d`, a basis, and the coordinates of an element. Only
  two laws are asked: the first basis element is one, and an element is the
  combination of the basis with its coordinates. `ExtData.table` holds the
  structure constants (`ExtData.isTable`).
* `ExtData.publics`: the public values of a circuit, that is the coordinates
  of the two lookup challenges and of the lookup sums entering and leaving the
  circuit. `asm_publics_*`: the four elements they assemble to.
* `openedRow`: the row the constraints are evaluated on, from the opened rows,
  with the selectors as the verifier computes them at `ζ`.
* `circuitCheck`: the check.
* `circuitCheck_iff_eval`: if the opened rows are the values of column
  polynomials at `ζ` and at `ζ * g`, and `ζ` is outside the trace domain, the
  check holds exactly when the folded constraints at `ζ` are the vanishing
  polynomial times the quotient at `ζ`.

Nothing here is about a protocol or a commitment.
-/

namespace CertiFri.Stark.Model

open Polynomial

variable {F K : Type} [Field K]

/-- A read of an array given by a function, inside the array. -/
private theorem getD_ofFn {w : ℕ} (f : Fin w → K) {i : ℕ} (hi : i < w) :
    (Array.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hi]
  rfl

/-- A read of a segment of an array is a read of the array. -/
private theorem getD_extract (a : Array K) {i j k : ℕ} (hk : i + k < j) :
    (a.extract i j).getD k 0 = a.getD (i + k) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · next h => rw [Array.getElem?_eq_none (by omega)]

/-- Entry `m * d + k` of the concatenation of the `d` values `f x 0, …,
f x (d - 1)` for each `x` of a list is `f x k`, for the entry `x` of the list
at position `m`. -/
private theorem getElem?_flatMap_range {α β : Type} (f : α → ℕ → β) (d : ℕ) {k : ℕ}
    (hk : k < d) (l : List α) (m : ℕ) {x : α} (hm : l[m]? = some x) :
    (l.flatMap fun y => (List.range d).map (f y))[m * d + k]? = some (f x k) := by
  induction l generalizing m with
  | nil => exact absurd hm (by simp)
  | cons y l ih =>
    rw [List.flatMap_cons]
    cases m with
    | zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at hm
      rw [Nat.zero_mul, Nat.zero_add, List.getElem?_append_left (by simpa using hk),
        List.getElem?_map, List.getElem?_range hk, hm]
      rfl
    | succ m =>
      rw [List.getElem?_cons_succ] at hm
      rw [List.getElem?_append_right (by simp [Nat.succ_mul]; omega), List.length_map,
        List.length_range, show (m + 1) * d + k - d = m * d + k by rw [Nat.succ_mul]; omega]
      exact ih m hm

/-- The extension structure the checks use: the degree, a basis, and the
coordinates of an element in it. -/
structure ExtData (K : Type) [Field K] where
  /-- The degree of the extension. -/
  d : ℕ
  /-- The basis. -/
  basis : ℕ → K
  /-- The coordinates of an element. -/
  coord : K → ℕ → K
  /-- The degree is positive. -/
  d_pos : 0 < d
  /-- The first basis element is one. -/
  basis_zero : basis 0 = 1
  /-- An element is the combination of the basis with its coordinates. -/
  sum_coord : ∀ y : K, ∑ k ∈ Finset.range d, coord y k * basis k = y

namespace ExtData

variable (E : ExtData K)

/-- The structure constants of the basis: entry `(i * d + j) * d + k` is
coordinate `k` of the product of the basis elements `i` and `j`. -/
def table : Array K :=
  Array.ofFn (n := E.d * E.d * E.d) fun t =>
    E.coord (E.basis (t.val / (E.d * E.d)) * E.basis (t.val / E.d % E.d)) (t.val % E.d)

/-- `table` holds the structure constants of the basis. -/
theorem isTable : IsTable E.basis E.d E.table := by
  intro i hi j hj
  rw [← E.sum_coord (E.basis i * E.basis j)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hd := E.d_pos
  have hjk : j * E.d + k < E.d * E.d :=
    calc j * E.d + k < (j + 1) * E.d := by rw [Nat.succ_mul]; omega
      _ ≤ E.d * E.d := Nat.mul_le_mul_right E.d hj
  have hidx : (i * E.d + j) * E.d + k = j * E.d + k + i * (E.d * E.d) := by ring
  have hlt : (i * E.d + j) * E.d + k < E.d * E.d * E.d :=
    calc (i * E.d + j) * E.d + k < (i + 1) * (E.d * E.d) := by rw [hidx, Nat.succ_mul]; omega
      _ ≤ E.d * (E.d * E.d) := Nat.mul_le_mul_right _ hi
      _ = E.d * E.d * E.d := (Nat.mul_assoc _ _ _).symm
  have h1 : ((i * E.d + j) * E.d + k) / (E.d * E.d) = i := by
    rw [hidx, Nat.add_mul_div_right _ _ (Nat.mul_pos hd hd), Nat.div_eq_of_lt hjk, Nat.zero_add]
  have h2 : ((i * E.d + j) * E.d + k) / E.d % E.d = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hk', Nat.zero_add,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  have h3 : ((i * E.d + j) * E.d + k) % E.d = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk']
  rw [table, getD_ofFn _ hlt]
  simp only [h1, h2, h3]

/-- The public values of a circuit: the coordinates of `β`, of `γ`, of the
lookup sum entering the circuit and of the one leaving it. -/
def publics (β γ acc next : K) : Array K :=
  ([β, γ, acc, next].flatMap fun x => (List.range E.d).map (E.coord x)).toArray

/-- The group of public values at position `m` assembles to the element at
position `m` of `β`, `γ` and the two lookup sums. -/
private theorem asm_publics_extract (β γ acc next : K) (m : ℕ) {x : K}
    (hm : [β, γ, acc, next][m]? = some x) {s t : ℕ} (hs : s = m * E.d) (ht : t = s + E.d) :
    asm E.basis E.d ((E.publics β γ acc next).extract s t) = x := by
  rw [asm, ← E.sum_coord x]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [getD_extract _ (by omega), publics, Array.getD_eq_getD_getElem?, List.getElem?_toArray, hs,
    getElem?_flatMap_range E.coord E.d hk' _ m hm]
  rfl

/-- The first group of public values assembles to `β`. -/
theorem asm_publics_beta (β γ acc next : K) :
    asm E.basis E.d ((E.publics β γ acc next).extract 0 E.d) = β :=
  E.asm_publics_extract β γ acc next 0 rfl (by omega) (by omega)

/-- The second group of public values assembles to `γ`. -/
theorem asm_publics_gamma (β γ acc next : K) :
    asm E.basis E.d ((E.publics β γ acc next).extract E.d (2 * E.d)) = γ :=
  E.asm_publics_extract β γ acc next 1 rfl (by omega) (by omega)

/-- The third group of public values assembles to the entering lookup sum. -/
theorem asm_publics_acc (β γ acc next : K) :
    asm E.basis E.d ((E.publics β γ acc next).extract (2 * E.d) (3 * E.d)) = acc :=
  E.asm_publics_extract β γ acc next 2 rfl (by omega) (by omega)

/-- The fourth group of public values assembles to the leaving lookup sum. -/
theorem asm_publics_next (β γ acc next : K) :
    asm E.basis E.d ((E.publics β γ acc next).extract (3 * E.d) (4 * E.d)) = next :=
  E.asm_publics_extract β γ acc next 3 rfl (by omega) (by omega)

end ExtData

/-- The row the constraints of a circuit are evaluated on, built from the rows
opened at `ζ` (position `0`) and at its successor (position `1`): the public
values, and the selectors of the trace domain of order `n` generated by `g`, as
the verifier computes them at `ζ`. -/
def openedRow (n : ℕ) (g : K) (publics : Array K) (ζ : K) (pre main s2 : Array (Array K)) :
    RowValues K where
  preprocessed := pre.getD 0 #[]
  preprocessedNext := pre.getD 1 #[]
  main := main.getD 0 #[]
  mainNext := main.getD 1 #[]
  stage2 := s2.getD 0 #[]
  stage2Next := s2.getD 1 #[]
  publics := publics
  isFirstRow := (ζ ^ n - 1) * (ζ - 1)⁻¹
  isLastRow := (ζ ^ n - 1) * (ζ - g⁻¹)⁻¹
  isTransition := ζ - g⁻¹

/-- **The verifier's check of one circuit** with a trace domain of order `n`
generated by `g`: the constraint values on the opened rows, folded with `α` and
divided by the vanishing polynomial at `ζ`, are the quotient reassembled from
its opened chunks. `ι` reads the constants of the graph; `acc` and `next` are
the lookup sums entering and leaving the circuit. -/
def circuitCheck (ι : F → K) (E : ExtData K) (c : Circuit F) (n : ℕ) (g β γ acc next α ζ : K)
    (pre main s2 : Array (Array K)) (quot : Array K) : Prop :=
  foldAlpha α (constraintVals ι E.d E.table c
      (openedRow n g (E.publics β γ acc next) ζ pre main s2)
      (deltaScaled E.d n g (E.publics β γ acc next))) * (ζ ^ n - 1)⁻¹ =
    ∑ i ∈ Finset.range c.quotientDegree, (ζ ^ n) ^ i *
      ∑ j ∈ Finset.range E.d, quot.getD (i * E.d + j) 0 * E.basis j

/-- **The check, on evaluations of polynomials.** Let the opened rows be the
values of the columns `cols` at `ζ` and at `ζ * g`, and `ζ` be outside the
trace domain. Then the check holds exactly when the folded constraints at `ζ`
are the vanishing polynomial of the domain times the quotient at `ζ`. -/
theorem circuitCheck_iff_eval (ι : F → K) (E : ExtData K) (c : Circuit F) {n : ℕ} {g : K}
    (hg : g ^ n = 1) (hg0 : g ≠ 0) (β γ acc next α : K) {ζ : K} (hζ : ζ ^ n ≠ 1)
    (cols : Columns K) {pre main s2 : Array (Array K)} {quot : Array K}
    (hpre : pre.getD 0 #[] = Array.ofFn (n := c.preprocessedWidth) fun j =>
      (cols.pre j.val).eval ζ)
    (hpreNext : pre.getD 1 #[] = Array.ofFn (n := c.preprocessedWidth) fun j =>
      (cols.pre j.val).eval (ζ * g))
    (hmain : main.getD 0 #[] = Array.ofFn (n := c.mainWidth) fun j => (cols.main j.val).eval ζ)
    (hmainNext : main.getD 1 #[] = Array.ofFn (n := c.mainWidth) fun j =>
      (cols.main j.val).eval (ζ * g))
    (hs2 : s2.getD 0 #[] = Array.ofFn (n := c.stage2Width) fun j => (cols.stage2 j.val).eval ζ)
    (hs2Next : s2.getD 1 #[] = Array.ofFn (n := c.stage2Width) fun j =>
      (cols.stage2 j.val).eval (ζ * g))
    (hquot : ∀ i < c.quotientDegree * E.d, quot.getD i 0 = (cols.quotient i).eval ζ) :
    circuitCheck ι E c n g β γ acc next α ζ pre main s2 quot ↔
      (compPoly ι E.d E.table c n g cols (E.publics β γ acc next)
          (deltaScaled E.d n g (E.publics β γ acc next)) α).eval ζ =
        (ζ ^ n - 1) * (quotientPoly E.basis E.d n c.quotientDegree cols).eval ζ := by
  have hζ1 : ζ ≠ 1 := fun h => hζ (by rw [h, one_pow])
  have hζg : ζ ≠ g⁻¹ := fun h => hζ (by rw [h, inv_pow, hg, inv_one])
  have hv : ζ ^ n - 1 ≠ 0 := sub_ne_zero.mpr hζ
  -- The row the verifier builds is the row of the columns at `ζ`.
  have hrow : openedRow n g (E.publics β γ acc next) ζ pre main s2 =
      pointRow c n g cols (E.publics β γ acc next) ζ := by
    rw [openedRow, pointRow, hpre, hpreNext, hmain, hmainNext, hs2, hs2Next,
      selector_first hζ1, selector_last hg hg0 hζg]
  -- The quotient the verifier reassembles is the quotient at `ζ`.
  have hq : ∑ i ∈ Finset.range c.quotientDegree, (ζ ^ n) ^ i *
      ∑ j ∈ Finset.range E.d, quot.getD (i * E.d + j) 0 * E.basis j =
      (quotientPoly E.basis E.d n c.quotientDegree cols).eval ζ := by
    rw [eval_quotientPoly]
    refine Finset.sum_congr rfl fun i hi => ?_
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rw [hquot _
      (calc i * E.d + j < (i + 1) * E.d := by rw [Nat.succ_mul]; omega
        _ ≤ c.quotientDegree * E.d := Nat.mul_le_mul_right E.d hi')]
  rw [circuitCheck, hrow, ← eval_compPoly, hq, ← div_eq_mul_inv, div_eq_iff hv, mul_comm]

end CertiFri.Stark.Model
