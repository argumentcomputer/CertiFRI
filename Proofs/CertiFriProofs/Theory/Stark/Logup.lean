import Mathlib
import CertiFri.Stark.Graph
import CertiFri.Stark.Logup

/-!
# The lookup constraints over a commutative ring, and what they say

The executable verifier computes the lookup constraints of a circuit in
coordinates (`logupConstraintValues`, `CertiFri/Stark/Logup.lean`): an element
of the extension is a tuple of `d` coordinates, and tuples are multiplied with
the structure constants of the basis. Here the same computation is defined over
any commutative ring `R`, with the degree `d` and the table of structure
constants as arguments, and its meaning is proved.

## Contents

* `sumRange`, `coordMul`, `coordOne`, `lookupMessage`, `groupConstraint`,
  `logupValues`: the computation, written as in the executable code.
* `size_groupConstraint`, `size_logupValues`, `getD_logupValues`: there are
  `d` values per group, and the values of group `g`, at the positions
  `g * d, …, g * d + d - 1`, are the coordinates of the constraint of the group.
* `map_logupValues`: a ring homomorphism commutes with it, as it does with
  each step (`map_coordMul`, `map_coordOne`, `map_lookupMessage`,
  `map_groupConstraint`).
* `asm e d a`: the element with the coordinates `a` in a basis `e`, that is
  `∑ k < d, a[k] * e k`. `IsTable e d T` says that `T` holds the structure
  constants of `e`.
* `asm_coordMul`, `asm_coordOne`, `asm_lookupMessage`, `asm_groupConstraint`:
  what the tuples computed here are the coordinates of.
* `asm_diff_eq_of_groupConstraint_eq_zero`: over a field, if the constraint of
  a group is zero and none of its messages is zero, the step of the group is
  `∑ multiplicity / message`.
* `le_lookupGroups_mul`: the groups cover the lookups.
* `logup_row_eq`: over a field, if every lookup constraint of a row is zero
  and no message of the row is zero, the lookup sum grows over the row by
  `∑ multiplicity / message`.

## Assumptions

`e 0 = 1` and `0 < d` (the first basis element is one), and `IsTable e d T`.
Nothing is assumed about linear independence: the statements are identities
between assembled elements, for any coordinates.
-/

namespace CertiFri.Stark.Model

variable {R S : Type}

section Ring

variable [CommRing R] [CommRing S]

/-! ## The computation -/

/-- `f 0 + ⋯ + f (n - 1)`, as the executable code computes it. -/
def sumRange (n : ℕ) (f : ℕ → R) : R :=
  (List.range n).foldl (fun acc i => acc + f i) 0

/-- The product of two tuples of `d` coordinates, with the structure constants
`table` of the basis. -/
def coordMul (d : ℕ) (table a b : Array R) : Array R :=
  Array.ofFn (n := d) fun k =>
    sumRange d fun i => sumRange d fun j =>
      a.getD i 0 * b.getD j 0 * table.getD ((i * d + j) * d + k.val) 0

/-- The coordinates of one. -/
def coordOne (d : ℕ) : Array R :=
  Array.ofFn (n := d) fun k => if k.val = 0 then 1 else 0

/-- The message of a lookup: `β + ∑_i γ^i * arg_i`, in coordinates. -/
def lookupMessage (d : ℕ) (table beta gamma buf : Array R) (lookup : Lookup) : Array R :=
  let fingerprint := lookup.args.foldr
    (fun arg acc =>
      let shifted := coordMul d table acc gamma
      Array.ofFn (n := d) fun k =>
        if k.val = 0 then shifted.getD 0 0 + buf.getD arg 0 else shifted.getD k.val 0)
    (Array.ofFn (n := d) fun _ => 0)
  Array.ofFn (n := d) fun k => fingerprint.getD k.val 0 + beta.getD k.val 0

/-- The constraint of one group, in coordinates:
`(∏_j m_j) * diff - ∑_j c_j * ∏_{j' ≠ j} m_{j'}`. -/
def groupConstraint (d : ℕ) (table : Array R) (messages : Array (Array R))
    (multiplicities diff : Array R) : Array R :=
  let all := messages.foldl (coordMul d table) (coordOne d)
  (List.range messages.size).foldl
    (fun acc j =>
      let others := (List.range messages.size).foldl
        (fun product i => if i = j then product else coordMul d table product (messages.getD i #[]))
        (coordOne d)
      Array.ofFn (n := d) fun k =>
        acc.getD k.val 0 - others.getD k.val 0 * multiplicities.getD j 0)
    (coordMul d table all diff)

/-- The values of the lookup constraints at one evaluation point: for each
group of lookups, in order, the `d` coordinates of its constraint. The
arguments are those of the executable `logupConstraintValues`, with the degree
`d` and the structure constants `table` made explicit. -/
def logupValues (d : ℕ) (table : Array R) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array R) (isLastRow : R) (groupSize : ℕ) :
    Array R :=
  let size := max groupSize 1
  let beta := publics.extract 0 d
  let gamma := publics.extract d (2 * d)
  let groups := lookupGroups lookups.size groupSize
  let wrap : Array R := Array.ofFn (n := d) fun k =>
    stage2Next.getD k.val 0 + isLastRow * deltaScaled.getD k.val 0
  (List.range groups).foldl
    (fun out g =>
      let chunk := lookups.extract (g * size) ((g + 1) * size)
      let diff : Array R := Array.ofFn (n := d) fun k =>
        (if g + 1 < groups then stage2.getD ((g + 1) * d + k.val) 0 else wrap.getD k.val 0)
          - stage2.getD (g * d + k.val) 0
      out ++ groupConstraint d table (chunk.map (lookupMessage d table beta gamma buf))
        (chunk.map fun lookup => buf.getD lookup.multiplicity 0) diff)
    #[]

/-! ## Shape -/

/-- `sumRange` is the sum over the range. -/
theorem sumRange_eq (n : ℕ) (f : ℕ → R) : sumRange n f = ∑ i ∈ Finset.range n, f i := by
  unfold sumRange
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

/-- A property of the start of a left fold that every step keeps holds of the
result. -/
private theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ b a, P b → P (f b a)) (l : List α) (b : β) (hb : P b) : P (l.foldl f b) := by
  induction l generalizing b with
  | nil => exact hb
  | cons a l ih => exact ih _ (hf b a hb)

/-- A left fold that appends the `d` entries of `c g` for each `g < n`: the
result has `n * d` entries, and entry `g * d + k` is entry `k` of `c g`. -/
private theorem foldl_append_spec {α : Type} (d : ℕ) (c : ℕ → Array α)
    (hc : ∀ g, (c g).size = d) (x : α) (n : ℕ) :
    ((List.range n).foldl (fun out g => out ++ c g) #[]).size = n * d ∧
      ∀ g < n, ∀ k < d,
        ((List.range n).foldl (fun out g => out ++ c g) #[]).getD (g * d + k) x =
          (c g).getD k x := by
  induction n with
  | zero => exact ⟨by simp, fun g hg => absurd hg (Nat.not_lt_zero g)⟩
  | succ n ih =>
    obtain ⟨hs, hget⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.size_append, hs, hc, Nat.succ_mul], fun g hg k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hg with hlt | rfl
    · have hlt' : g * d + k < n * d :=
        calc g * d + k < (g + 1) * d := by rw [Nat.succ_mul]; omega
          _ ≤ n * d := Nat.mul_le_mul_right d hlt
      rw [← hget g hlt k hk, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_append_left (by rw [hs]; exact hlt')]
    · rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
        Array.getElem?_append_right (by rw [hs]; omega), hs, Nat.add_sub_cancel_left]

/-- A group constraint has `d` coordinates. -/
theorem size_groupConstraint (d : ℕ) (table : Array R) (messages : Array (Array R))
    (multiplicities diff : Array R) :
    (groupConstraint d table messages multiplicities diff).size = d := by
  unfold groupConstraint
  exact foldl_invariant (fun a : Array R => a.size = d) _ (fun _ _ _ => Array.size_ofFn) _ _
    Array.size_ofFn

/-- There are `d` values per group of lookups. -/
theorem size_logupValues (d : ℕ) (table : Array R) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array R) (isLastRow : R) (groupSize : ℕ) :
    (logupValues d table lookups buf stage2 stage2Next publics deltaScaled isLastRow
      groupSize).size = lookupGroups lookups.size groupSize * d := by
  unfold logupValues
  exact (foldl_append_spec d _ (fun _ => size_groupConstraint ..) 0 _).1

/-- The values of group `g` are the coordinates of the constraint of the group:
that of the lookups `g * size, …, (g + 1) * size - 1`, where `size` is
`max groupSize 1`, with the step from slot `g` of `stage2` to slot `g + 1`, or
for the last group to the first slot of the next row with the last-row term. -/
theorem getD_logupValues (d : ℕ) (table : Array R) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array R) (isLastRow : R) (groupSize : ℕ)
    {g k : ℕ} (hg : g < lookupGroups lookups.size groupSize) (hk : k < d) :
    (logupValues d table lookups buf stage2 stage2Next publics deltaScaled isLastRow
        groupSize).getD (g * d + k) 0 =
      (groupConstraint d table
        ((lookups.extract (g * max groupSize 1) ((g + 1) * max groupSize 1)).map
          (lookupMessage d table (publics.extract 0 d) (publics.extract d (2 * d)) buf))
        ((lookups.extract (g * max groupSize 1) ((g + 1) * max groupSize 1)).map
          fun lookup => buf.getD lookup.multiplicity 0)
        (Array.ofFn (n := d) fun k =>
          (if g + 1 < lookupGroups lookups.size groupSize
            then stage2.getD ((g + 1) * d + k.val) 0
            else (Array.ofFn (n := d) fun k =>
              stage2Next.getD k.val 0 + isLastRow * deltaScaled.getD k.val 0).getD k.val 0)
            - stage2.getD (g * d + k.val) 0)).getD k 0 := by
  unfold logupValues
  exact (foldl_append_spec d _ (fun _ => size_groupConstraint ..) 0 _).2 g hg k hk

/-! ## Ring homomorphisms -/

/-- An entry of a mapped array, with default zero, is the image of the entry. -/
private theorem getD_map (φ : R →+* S) (a : Array R) (i : ℕ) :
    (a.map φ).getD i 0 = φ (a.getD i 0) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? with
  | none => exact (map_zero φ).symm
  | some a => rfl

/-- An entry of an array of mapped arrays, with the empty array as default. -/
private theorem getD_map_map {α β : Type} (φ : α → β) (ms : Array (Array α)) (i : ℕ) :
    (ms.map (Array.map φ)).getD i #[] = (ms.getD i #[]).map φ := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases ms[i]? with
  | none => exact Array.map_empty.symm
  | some a => rfl

/-- Mapping a left fold that appends arrays maps each of them. -/
private theorem map_foldl_append {α β : Type} (φ : α → β) (c : ℕ → Array α)
    (c' : ℕ → Array β) (h : ∀ g, (c g).map φ = c' g) (l : List ℕ) :
    (l.foldl (fun out g => out ++ c g) #[]).map φ = l.foldl (fun out g => out ++ c' g) #[] := by
  have key := List.foldl_hom (Array.map φ) (g₁ := fun out g => out ++ c g)
    (g₂ := fun out g => out ++ c' g) (l := l) (init := #[])
    fun x y => by rw [Array.map_append, h]
  rw [Array.map_empty] at key
  exact key.symm

/-- A ring homomorphism commutes with `sumRange`. -/
theorem map_sumRange (φ : R →+* S) (n : ℕ) (f : ℕ → R) :
    φ (sumRange n f) = sumRange n fun i => φ (f i) := by
  rw [sumRange_eq, sumRange_eq, map_sum]

/-- A ring homomorphism commutes with the product of tuples. -/
theorem map_coordMul (φ : R →+* S) (d : ℕ) (table a b : Array R) :
    (coordMul d table a b).map φ = coordMul d (table.map φ) (a.map φ) (b.map φ) := by
  unfold coordMul
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, map_sumRange, map_mul, getD_map]

/-- A ring homomorphism maps the coordinates of one to the coordinates of one. -/
theorem map_coordOne (φ : R →+* S) (d : ℕ) : (coordOne d : Array R).map φ = coordOne d := by
  unfold coordOne
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply]
  split
  · exact map_one φ
  · exact map_zero φ

/-- A ring homomorphism commutes with the message of a lookup. -/
theorem map_lookupMessage (φ : R →+* S) (d : ℕ) (table beta gamma buf : Array R)
    (lookup : Lookup) :
    (lookupMessage d table beta gamma buf lookup).map φ =
      lookupMessage d (table.map φ) (beta.map φ) (gamma.map φ) (buf.map φ) lookup := by
  unfold lookupMessage
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, map_add, ← getD_map]
  congr 2
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  have hinit : (Array.ofFn (n := d) fun _ => (0 : R)).map φ = Array.ofFn (n := d) fun _ => 0 := by
    rw [Array.map_ofFn]
    congr 1
    funext _
    exact map_zero φ
  rw [← hinit]
  refine (List.foldr_hom (Array.map φ) fun arg acc => ?_).symm
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, ← map_coordMul, getD_map, ← map_add]
  split <;> rfl

/-- A ring homomorphism commutes with the constraint of a group. -/
theorem map_groupConstraint (φ : R →+* S) (d : ℕ) (table : Array R)
    (messages : Array (Array R)) (multiplicities diff : Array R) :
    (groupConstraint d table messages multiplicities diff).map φ =
      groupConstraint d (table.map φ) (messages.map (Array.map φ)) (multiplicities.map φ)
        (diff.map φ) := by
  have hall : (messages.map (Array.map φ)).foldl (coordMul d (table.map φ)) (coordOne d) =
      (messages.foldl (coordMul d table) (coordOne d)).map φ := by
    rw [Array.foldl_map, ← Array.foldl_toList, ← Array.foldl_toList, ← map_coordOne φ]
    exact List.foldl_hom (Array.map φ) fun x y => (map_coordMul φ d table x y).symm
  simp only [groupConstraint]
  rw [hall, ← map_coordMul]
  simp only [Array.size_map]
  refine (List.foldl_hom (Array.map φ) fun acc j => ?_).symm
  rw [Array.map_ofFn]
  congr 1
  funext k
  have hothers : (List.range messages.size).foldl
      (fun product i => if i = j then product
        else coordMul d (table.map φ) product ((messages.map (Array.map φ)).getD i #[]))
      (coordOne d) =
      ((List.range messages.size).foldl
        (fun product i => if i = j then product
          else coordMul d table product (messages.getD i #[]))
        (coordOne d)).map φ := by
    rw [← map_coordOne φ]
    refine List.foldl_hom (Array.map φ) fun x i => ?_
    split
    · rfl
    · rw [getD_map_map, map_coordMul]
  simp only [Function.comp_apply, hothers, getD_map, map_sub, map_mul]

/-- A ring homomorphism commutes with the lookup constraints. -/
theorem map_logupValues (φ : R →+* S) (d : ℕ) (table : Array R) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array R) (isLastRow : R) (groupSize : ℕ) :
    (logupValues d table lookups buf stage2 stage2Next publics deltaScaled isLastRow
        groupSize).map φ =
      logupValues d (table.map φ) lookups (buf.map φ) (stage2.map φ) (stage2Next.map φ)
        (publics.map φ) (deltaScaled.map φ) (φ isLastRow) groupSize := by
  simp only [logupValues]
  refine map_foldl_append φ _ _ (fun g => ?_) _
  simp only [map_groupConstraint, Array.map_map]
  congr 2
  · funext lookup
    simp only [Function.comp_apply, map_lookupMessage, Array.map_extract]
  · funext lookup
    simp only [Function.comp_apply, getD_map]
  · rw [Array.map_ofFn]
    congr 1
    funext k
    simp only [Function.comp_apply, map_sub, getD_map, apply_ite φ]
    congr 2
    rw [← getD_map, Array.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply, map_add, map_mul]

/-! ## Assembling coordinates -/

/-- The element with the coordinates `a` in the basis `e`: `∑ k < d, a[k] * e k`. -/
def asm (e : ℕ → R) (d : ℕ) (a : Array R) : R :=
  ∑ k ∈ Finset.range d, a.getD k 0 * e k

/-- `T` holds the structure constants of the basis `e`: entry
`(i * d + j) * d + k` is coordinate `k` of `e i * e j`. -/
def IsTable (e : ℕ → R) (d : ℕ) (T : Array R) : Prop :=
  ∀ i < d, ∀ j < d, ∑ k ∈ Finset.range d, T.getD ((i * d + j) * d + k) 0 * e k = e i * e j

variable {e : ℕ → R} {d : ℕ} {T : Array R}

/-- An entry of `Array.ofFn`, with default zero. -/
private theorem getD_ofFn {n : ℕ} (f : Fin n → R) {k : ℕ} (hk : k < n) :
    (Array.ofFn f).getD k 0 = f ⟨k, hk⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hk]
  rfl

/-- An entry of the list of an array is the entry of the array. -/
private theorem getD_toList {α : Type} (a : Array α) (i : ℕ) (x : α) :
    a.toList.getD i x = a.getD i x := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- The element that a tuple given by a function assembles to. -/
theorem asm_ofFn (f : ℕ → R) :
    asm e d (Array.ofFn (n := d) fun k => f k.val) = ∑ k ∈ Finset.range d, f k * e k :=
  Finset.sum_congr rfl fun k hk => by rw [getD_ofFn _ (Finset.mem_range.mp hk)]

/-- A tuple whose first `d` entries are zero assembles to zero. -/
theorem asm_eq_zero {a : Array R} (h : ∀ k < d, a.getD k 0 = 0) : asm e d a = 0 :=
  Finset.sum_eq_zero fun k hk => by rw [h k (Finset.mem_range.mp hk), zero_mul]

/-- The product of two tuples is the tuple of the product. -/
theorem asm_coordMul (hT : IsTable e d T) (a b : Array R) :
    asm e d (coordMul d T a b) = asm e d a * asm e d b := by
  unfold coordMul
  rw [asm_ofFn fun k => sumRange d fun i => sumRange d fun j =>
    a.getD i 0 * b.getD j 0 * T.getD ((i * d + j) * d + k) 0]
  unfold asm
  calc ∑ k ∈ Finset.range d, (sumRange d fun i => sumRange d fun j =>
        a.getD i 0 * b.getD j 0 * T.getD ((i * d + j) * d + k) 0) * e k
      = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d, a.getD i 0 * b.getD j 0 *
          ∑ k ∈ Finset.range d, T.getD ((i * d + j) * d + k) 0 * e k := by
        simp only [sumRange_eq, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ i ∈ Finset.range d, ∑ j ∈ Finset.range d, a.getD i 0 * b.getD j 0 * (e i * e j) :=
        Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by
          rw [hT i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
    _ = (∑ k ∈ Finset.range d, a.getD k 0 * e k) * ∑ k ∈ Finset.range d, b.getD k 0 * e k := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The coordinates of one assemble to one. -/
theorem asm_coordOne (h0 : e 0 = 1) (hd : 0 < d) : asm e d (coordOne d : Array R) = 1 := by
  unfold coordOne
  rw [asm_ofFn fun k => if k = 0 then 1 else 0, Finset.sum_eq_single 0, ite_eq_left rfl, one_mul,
    h0]
  · intro k _ hk
    rw [ite_eq_right hk, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hd) h

/-- Adding a value to coordinate zero adds it to the element. -/
private theorem asm_add_zeroth (h0 : e 0 = 1) (hd : 0 < d) (a : Array R) (x : R) :
    asm e d (Array.ofFn (n := d) fun k =>
      if k.val = 0 then a.getD 0 0 + x else a.getD k.val 0) = asm e d a + x := by
  rw [asm_ofFn fun k => if k = 0 then a.getD 0 0 + x else a.getD k 0]
  have h : ∀ k ∈ Finset.range d, (if k = 0 then a.getD 0 0 + x else a.getD k 0) * e k =
      a.getD k 0 * e k + if k = 0 then x else 0 := by
    intro k _
    split
    · next hk => rw [hk, h0, mul_one, mul_one]
    · rw [add_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr hd)]
  rfl

/-- The sum of two tuples assembles to the sum of the elements. -/
private theorem asm_ofFn_add (a b : Array R) :
    asm e d (Array.ofFn (n := d) fun k => a.getD k.val 0 + b.getD k.val 0) =
      asm e d a + asm e d b := by
  rw [asm_ofFn fun k => a.getD k 0 + b.getD k 0]
  simp only [add_mul, Finset.sum_add_distrib]
  rfl

/-- A tuple minus a multiple of another assembles to the same of the elements. -/
private theorem asm_ofFn_sub_mul (a b : Array R) (c : R) :
    asm e d (Array.ofFn (n := d) fun k => a.getD k.val 0 - b.getD k.val 0 * c) =
      asm e d a - c * asm e d b := by
  rw [asm_ofFn fun k => a.getD k 0 - b.getD k 0 * c]
  simp only [sub_mul, Finset.sum_sub_distrib, asm, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The fingerprint of the arguments of a lookup assembles to `∑_i γ^i * arg_i`. -/
private theorem asm_fingerprint (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d)
    (gamma buf : Array R) (args : List ℕ) :
    asm e d (args.foldr
        (fun arg acc => Array.ofFn (n := d) fun k =>
          if k.val = 0 then (coordMul d T acc gamma).getD 0 0 + buf.getD arg 0
          else (coordMul d T acc gamma).getD k.val 0)
        (Array.ofFn (n := d) fun _ => 0)) =
      ∑ i ∈ Finset.range args.length, asm e d gamma ^ i * buf.getD (args.getD i 0) 0 := by
  induction args with
  | nil =>
    rw [List.foldr_nil, asm_ofFn fun _ => 0]
    simp only [zero_mul, Finset.sum_const_zero, List.length_nil, Finset.range_zero,
      Finset.sum_empty]
  | cons arg args ih =>
    rw [List.foldr_cons, asm_add_zeroth h0 hd, asm_coordMul hT, ih, List.length_cons,
      Finset.sum_range_succ', Finset.sum_mul]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, one_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The message of a lookup assembles to `β + ∑_i γ^i * arg_i`, for the
elements `β` and `γ` that `beta` and `gamma` assemble to. -/
theorem asm_lookupMessage (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d)
    (beta gamma buf : Array R) (lookup : Lookup) :
    asm e d (lookupMessage d T beta gamma buf lookup) =
      asm e d beta + ∑ i ∈ Finset.range lookup.args.size,
        asm e d gamma ^ i * buf.getD (lookup.args.getD i 0) 0 := by
  simp only [lookupMessage]
  rw [asm_ofFn_add, ← Array.foldr_toList, asm_fingerprint hT h0 hd, add_comm]
  simp only [Array.length_toList, getD_toList]

/-- A left fold of products of tuples assembles to the product of the elements. -/
private theorem asm_foldl_coordMul (hT : IsTable e d T) (l : List (Array R)) (init : Array R) :
    asm e d (l.foldl (coordMul d T) init) =
      asm e d init * ∏ j ∈ Finset.range l.length, asm e d (l.getD j #[]) := by
  induction l generalizing init with
  | nil => simp only [List.foldl_nil, List.length_nil, Finset.range_zero, Finset.prod_empty,
      mul_one]
  | cons m l ih =>
    rw [List.foldl_cons, ih, asm_coordMul hT, List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The product of the tuples `ms i` for `i < n` other than `j` assembles to
the product of the elements. -/
private theorem asm_foldl_others (hT : IsTable e d T) (ms : ℕ → Array R) (j n : ℕ)
    (init : Array R) :
    asm e d ((List.range n).foldl
        (fun product i => if i = j then product else coordMul d T product (ms i)) init) =
      asm e d init * ∏ i ∈ (Finset.range n).erase j, asm e d (ms i) := by
  rw [← Finset.filter_ne', Finset.prod_filter]
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.prod_empty,
      mul_one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.prod_range_succ, ← mul_assoc, ← ih]
    by_cases h : n = j
    · rw [ite_eq_left h, ite_eq_right (not_not.mpr h), mul_one]
    · rw [ite_eq_right h, ite_eq_left h, asm_coordMul hT]

/-- Subtracting from a tuple, for each `j < n`, the tuple `o j` times `c j`
subtracts the same of the elements. -/
private theorem asm_foldl_sub (o : ℕ → Array R) (c : ℕ → R) (n : ℕ) (init : Array R) :
    asm e d ((List.range n).foldl
        (fun acc j => Array.ofFn (n := d) fun k => acc.getD k.val 0 - (o j).getD k.val 0 * c j)
        init) =
      asm e d init - ∑ j ∈ Finset.range n, c j * asm e d (o j) := by
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty,
      sub_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, asm_ofFn_sub_mul,
      ih, Finset.sum_range_succ]
    ring

/-- The constraint of a group assembles to
`(∏_j m_j) * diff - ∑_j c_j * ∏_{j' ≠ j} m_{j'}`. -/
theorem asm_groupConstraint (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d)
    (messages : Array (Array R)) (multiplicities diff : Array R) :
    asm e d (groupConstraint d T messages multiplicities diff) =
      (∏ j ∈ Finset.range messages.size, asm e d (messages.getD j #[])) * asm e d diff
        - ∑ j ∈ Finset.range messages.size, multiplicities.getD j 0 *
            ∏ i ∈ (Finset.range messages.size).erase j, asm e d (messages.getD i #[]) := by
  simp only [groupConstraint]
  rw [asm_foldl_sub, asm_coordMul hT, ← Array.foldl_toList, asm_foldl_coordMul hT]
  simp only [asm_foldl_others hT fun i => messages.getD i #[], asm_coordOne h0 hd, one_mul,
    Array.length_toList, getD_toList]

/-- The step of group `g` assembles to the lookup sum leaving the group minus
the one entering it. -/
private theorem asm_logupDiff (stage2 stage2Next deltaScaled : Array R) (isLastRow : R)
    (g : ℕ) (p : Prop) [Decidable p] :
    asm e d (Array.ofFn (n := d) fun k =>
        (if p then stage2.getD ((g + 1) * d + k.val) 0
          else (Array.ofFn (n := d) fun k =>
            stage2Next.getD k.val 0 + isLastRow * deltaScaled.getD k.val 0).getD k.val 0)
          - stage2.getD (g * d + k.val) 0) =
      (if p then ∑ k ∈ Finset.range d, stage2.getD ((g + 1) * d + k) 0 * e k
          else asm e d stage2Next + isLastRow * asm e d deltaScaled)
        - ∑ k ∈ Finset.range d, stage2.getD (g * d + k) 0 * e k := by
  rw [asm_ofFn fun k =>
    (if p then stage2.getD ((g + 1) * d + k) 0
      else (Array.ofFn (n := d) fun k =>
        stage2Next.getD k.val 0 + isLastRow * deltaScaled.getD k.val 0).getD k 0)
      - stage2.getD (g * d + k) 0]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  by_cases hp : p
  · simp only [ite_eq_left hp]
  · simp only [ite_eq_right hp]
    unfold asm
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [getD_ofFn _ (Finset.mem_range.mp hk)]
    ring

end Ring

/-! ## What the constraints of a row say -/

section Field

variable {K : Type} [Field K] {e : ℕ → K} {d : ℕ} {T : Array K}

/-- The message of a lookup on a row, as an element: `β + ∑_i γ^i * arg_i`,
where the arguments are the values `buf` of their nodes. -/
def messageVal (β γ : K) (buf : Array K) (lookup : Lookup) : K :=
  β + ∑ i ∈ Finset.range lookup.args.size, γ ^ i * buf.getD (lookup.args.getD i 0) 0

/-- An entry of a mapped segment of an array. -/
private theorem getD_map_extract {α β : Type} [Inhabited α] (f : α → β) (a : Array α)
    (s t j : ℕ) (x : β) (hj : j < min t a.size - s) :
    ((a.extract s t).map f).getD j x = f (a.getD (s + j) default) := by
  have hlt : s + j < a.size := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_extract, ite_eq_left hj,
    Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
  rfl

/-- The groups cover the lookups. -/
theorem le_lookupGroups_mul (numLookups groupSize : ℕ) :
    numLookups ≤ lookupGroups numLookups groupSize * max groupSize 1 := by
  unfold lookupGroups
  have hpos : 0 < max groupSize 1 := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
  have h1 := Nat.lt_div_mul_add (a := numLookups + (max groupSize 1 - 1)) hpos
  have h2 := Nat.mul_le_mul_right (max groupSize 1)
    (Nat.le_max_left ((numLookups + (max groupSize 1 - 1)) / max groupSize 1) 1)
  omega

/-- Summing over the groups, and in each over its lookups, is summing over the
lookups that the groups cover. -/
private theorem sum_chunks {M : Type} [AddCommMonoid M] (F : ℕ → M) (size L G : ℕ) :
    ∑ g ∈ Finset.range G, ∑ j ∈ Finset.range (min ((g + 1) * size) L - g * size),
        F (g * size + j) =
      ∑ j ∈ Finset.range (min (G * size) L), F j := by
  induction G with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.zero_mul, Nat.zero_min]
  | succ G ih =>
    rw [Finset.sum_range_succ, ih]
    have hs : (G + 1) * size = G * size + size := Nat.succ_mul G size
    rcases Nat.le_total (G * size) L with h | h
    · rw [Nat.min_eq_left h, ← Finset.sum_range_add]
      congr 2
      omega
    · rw [Nat.min_eq_right h, show min ((G + 1) * size) L - G * size = 0 by omega,
        Finset.range_zero, Finset.sum_empty, add_zero, show min ((G + 1) * size) L = L by omega]

/-- A sum of steps, each from one term of a sequence to the next and the last
one to `w`, is `w` minus the first term. -/
private theorem sum_step_sub {M : Type} [AddCommGroup M] (src : ℕ → M) (w : M) {G : ℕ}
    (hG : 0 < G) :
    ∑ g ∈ Finset.range G, ((if g + 1 < G then src (g + 1) else w) - src g) = w - src 0 := by
  have h := Finset.sum_range_sub (fun g => if g < G then src g else w) G
  rw [ite_eq_right (Nat.lt_irrefl G), ite_eq_left hG] at h
  rw [← h]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [ite_eq_left (Finset.mem_range.mp hg)]

/-- With the denominators cleared: if `(∏_j m_j) * D = ∑_j c_j * ∏_{i ≠ j} m_i`
and no `m_j` is zero, then `D = ∑_j c_j / m_j`. -/
private theorem eq_sum_div_of_cleared {ι : Type} [DecidableEq ι] (s : Finset ι) (m c : ι → K)
    (D : K) (hm : ∀ j ∈ s, m j ≠ 0)
    (h : (∏ j ∈ s, m j) * D - ∑ j ∈ s, c j * ∏ i ∈ s.erase j, m i = 0) :
    D = ∑ j ∈ s, c j / m j := by
  apply mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr hm)
  rw [sub_eq_zero.mp h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.mul_prod_erase s m hj]
  field_simp [hm j hj]

/-- **The constraint of one group.** If the constraint of a group is zero and
none of its messages is zero, its step is `∑ multiplicity / message`. -/
theorem asm_diff_eq_of_groupConstraint_eq_zero (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d)
    (messages : Array (Array K)) (multiplicities diff : Array K)
    (hzero : ∀ k < d, (groupConstraint d T messages multiplicities diff).getD k 0 = 0)
    (hne : ∀ j < messages.size, asm e d (messages.getD j #[]) ≠ 0) :
    asm e d diff = ∑ j ∈ Finset.range messages.size,
      multiplicities.getD j 0 / asm e d (messages.getD j #[]) := by
  have h := asm_eq_zero (e := e) hzero
  rw [asm_groupConstraint hT h0 hd] at h
  exact eq_sum_div_of_cleared _ _ _ _ (fun j hj => hne j (Finset.mem_range.mp hj)) h

/-- The constraints of group `g` of a row: the lookup sum leaving the group is
the one entering it plus `∑ multiplicity / message` over its lookups. -/
private theorem logup_group_eq (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d)
    (lookups : Array Lookup) (buf stage2 stage2Next publics deltaScaled : Array K)
    (isLastRow : K) (groupSize : ℕ)
    (hzero : ∀ i, (logupValues d T lookups buf stage2 stage2Next publics deltaScaled isLastRow
      groupSize).getD i 0 = 0)
    (hne : ∀ j < lookups.size,
      messageVal (asm e d (publics.extract 0 d)) (asm e d (publics.extract d (2 * d))) buf
        (lookups.getD j default) ≠ 0)
    {g : ℕ} (hg : g < lookupGroups lookups.size groupSize) :
    (if g + 1 < lookupGroups lookups.size groupSize
          then ∑ k ∈ Finset.range d, stage2.getD ((g + 1) * d + k) 0 * e k
          else asm e d stage2Next + isLastRow * asm e d deltaScaled)
        - ∑ k ∈ Finset.range d, stage2.getD (g * d + k) 0 * e k =
      ∑ j ∈ Finset.range (min ((g + 1) * max groupSize 1) lookups.size - g * max groupSize 1),
        buf.getD (lookups.getD (g * max groupSize 1 + j) default).multiplicity 0 /
          messageVal (asm e d (publics.extract 0 d)) (asm e d (publics.extract d (2 * d))) buf
            (lookups.getD (g * max groupSize 1 + j) default) := by
  have hz := fun k (hk : k < d) =>
    (getD_logupValues d T lookups buf stage2 stage2Next publics deltaScaled isLastRow groupSize
      hg hk).symm.trans (hzero _)
  have h := asm_diff_eq_of_groupConstraint_eq_zero hT h0 hd _ _ _ hz
  rw [Array.size_map, Array.size_extract, asm_logupDiff] at h
  rw [h fun j hj => by
    rw [getD_map_extract _ _ _ _ _ _ hj, asm_lookupMessage hT h0 hd]
    exact hne _ (by omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [getD_map_extract _ _ _ _ _ _ (Finset.mem_range.mp hj),
    getD_map_extract _ _ _ _ _ _ (Finset.mem_range.mp hj), asm_lookupMessage hT h0 hd]
  rfl

/-- **The lookup constraints of one row.** Let every lookup constraint of the
row be zero, and no message of the row be zero. Then the lookup sum after the
row, with the last-row term, is the lookup sum before the row plus
`∑ multiplicity / message` over the lookups: with `s` and `s'` the elements
that the first `d` entries of `stage2` and of `stage2Next` assemble to, and
`δ` the one of `deltaScaled`,

    s' + isLastRow * δ - s = ∑_j multiplicity_j / message_j.

`β` and `γ` are the elements that the entries `0, …, d - 1` and
`d, …, 2 * d - 1` of `publics` assemble to. -/
theorem logup_row_eq (hT : IsTable e d T) (h0 : e 0 = 1) (hd : 0 < d) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array K) (isLastRow : K) (groupSize : ℕ)
    (hzero : ∀ i, (logupValues d T lookups buf stage2 stage2Next publics deltaScaled isLastRow
      groupSize).getD i 0 = 0)
    (hne : ∀ j < lookups.size,
      messageVal (asm e d (publics.extract 0 d)) (asm e d (publics.extract d (2 * d))) buf
        (lookups.getD j default) ≠ 0) :
    asm e d stage2Next + isLastRow * asm e d deltaScaled - asm e d stage2 =
      ∑ j ∈ Finset.range lookups.size,
        buf.getD (lookups.getD j default).multiplicity 0 /
          messageVal (asm e d (publics.extract 0 d)) (asm e d (publics.extract d (2 * d))) buf
            (lookups.getD j default) := by
  have hG : 0 < lookupGroups lookups.size groupSize :=
    Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_right _ _)
  have hsum := Finset.sum_congr (s₂ := Finset.range (lookupGroups lookups.size groupSize)) rfl
    fun g hg => logup_group_eq hT h0 hd lookups buf stage2 stage2Next publics deltaScaled
      isLastRow groupSize hzero hne (Finset.mem_range.mp hg)
  rw [sum_step_sub (fun g => ∑ k ∈ Finset.range d, stage2.getD (g * d + k) 0 * e k) _ hG,
    sum_chunks (fun j => buf.getD (lookups.getD j default).multiplicity 0 /
      messageVal (asm e d (publics.extract 0 d)) (asm e d (publics.extract d (2 * d))) buf
        (lookups.getD j default)),
    min_eq_right (le_lookupGroups_mul _ _)] at hsum
  simp only [Nat.zero_mul, Nat.zero_add] at hsum
  exact hsum

end Field

end CertiFri.Stark.Model
