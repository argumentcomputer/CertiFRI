import CertiFri.Stark.Graph

/-!
# The lookup constraints

multi-stark's lookup argument is a chained logUp accumulator. Every row of a
circuit sends its lookups as messages; the lookup trace holds, for each group
of lookups, the running sum entering that group. The constraints of one group
with messages `m_0, …, m_{s-1}` and multiplicities `c_0, …, c_{s-1}` say

```
(∏_j m_j) * (acc' - acc) - ∑_j c_j * ∏_{j' ≠ j} m_{j'} = 0
```

that is `acc' = acc + ∑_j c_j / m_j` with the denominators cleared, where
`m_j = β + ∑_i γ^i * arg_i` is the fingerprint of the arguments of lookup `j`,
`acc` is the group's own column and `acc'` is the column of the next group. For
the last group `acc'` is the first column of the next row, plus, on the last
row, the public difference between the sums leaving and entering the circuit.

This file is a port of `logup_constraint_values` (`src/lookup.rs`) of
multi-stark at revision `3515632`: the values of these constraints at one
evaluation point.

## Coordinates

The accumulators and the challenges are extension-field elements, but the
committed columns hold base-field elements, so each of them is stored as its
coordinates in the basis of the extension, one column per coordinate. The
constraints are therefore identities between tuples of coordinates, multiplied
as the basis prescribes. Evaluated at an out-of-domain point, each coordinate
is itself an extension-field element. `coordMul` is that product: its structure
constants are read off the basis (`basisTable`).

## Differences from multi-stark

* multi-stark has three code paths: one for an extension of degree one, one
  for degree two that multiplies by Karatsuba's formula with the nonresidue of
  a binomial extension, and a general one. Here a single formula covers every
  degree and every basis. In a field the results are the same; that is tested
  for the quadratic extension of Goldilocks, not proved.
* A missing column or node reads zero, where multi-stark panics.

Nothing is proved here. What these values mean is proved in the proofs
package (`Proofs/CertiFriProofs/Theory/Stark/Logup.lean`, and
`Exec/Stark/Arith.lean` for this executable code).
-/

namespace CertiFri.Stark

section Coordinates

variable (F : Type) {EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]

/-- The `i`-th element of the basis of the extension. -/
def basisElem (i : Nat) : EF :=
  ExtensionOps.ofBasis
    (Array.ofFn (n := ExtensionOps.degree (F := F) (EF := EF)) fun j =>
      if j.val = i then (1 : F) else 0)

/-- The structure constants of the basis, embedded in the extension: with `d`
the degree, entry `(i * d + j) * d + k` is coordinate `k` of the product of the
basis elements `i` and `j`. -/
def basisTable : Array EF :=
  let d := ExtensionOps.degree (F := F) (EF := EF)
  Array.ofFn (n := d * d * d) fun t =>
    let product : EF := basisElem F (t.val / (d * d)) * basisElem F (t.val / d % d)
    ExtensionOps.embed ((ExtensionOps.toBasis (F := F) product).getD (t.val % d) 0)

/-- The element with coordinates `coords`, where the coordinates themselves
are extension elements: `∑_j coords[j] * basis_j` (`from_ext_basis`). -/
def fromExtBasis (coords : Array EF) : EF :=
  (List.range coords.size).foldl (fun acc j => acc + coords.getD j 0 * basisElem F j) 0

end Coordinates

section Arithmetic

variable {EF : Type} [FieldOps EF]

/-- `f 0 + ⋯ + f (n - 1)`. -/
def sumRange (n : Nat) (f : Nat → EF) : EF :=
  (List.range n).foldl (fun acc i => acc + f i) 0

/-- The product of two tuples of `d` coordinates, with the structure constants
`table` of the basis. -/
def coordMul (d : Nat) (table a b : Array EF) : Array EF :=
  Array.ofFn (n := d) fun k =>
    sumRange d fun i => sumRange d fun j =>
      a.getD i 0 * b.getD j 0 * table.getD ((i * d + j) * d + k.val) 0

/-- The coordinates of one. -/
def coordOne (d : Nat) : Array EF :=
  Array.ofFn (n := d) fun k => if k.val = 0 then 1 else 0

/-- The message of a lookup: `β + ∑_i γ^i * arg_i`, in coordinates. The
arguments are base-field values, so each enters coordinate zero. -/
def lookupMessage (d : Nat) (table beta gamma buf : Array EF) (lookup : Lookup) : Array EF :=
  let fingerprint := lookup.args.foldr
    (fun arg acc =>
      let shifted := coordMul d table acc gamma
      Array.ofFn (n := d) fun k =>
        if k.val = 0 then shifted.getD 0 0 + buf.getD arg 0 else shifted.getD k.val 0)
    (Array.ofFn (n := d) fun _ => 0)
  Array.ofFn (n := d) fun k => fingerprint.getD k.val 0 + beta.getD k.val 0

/-- The constraint of one group, in coordinates:
`(∏_j m_j) * diff - ∑_j c_j * ∏_{j' ≠ j} m_{j'}`, for the messages `m`, the
multiplicities `c` and the step `diff = acc' - acc`. -/
def groupConstraint (d : Nat) (table : Array EF) (messages : Array (Array EF))
    (multiplicities diff : Array EF) : Array EF :=
  let all := messages.foldl (coordMul d table) (coordOne d)
  (List.range messages.size).foldl
    (fun acc j =>
      let others := (List.range messages.size).foldl
        (fun product i => if i = j then product else coordMul d table product (messages.getD i #[]))
        (coordOne d)
      Array.ofFn (n := d) fun k =>
        acc.getD k.val 0 - others.getD k.val 0 * multiplicities.getD j 0)
    (coordMul d table all diff)

/-- The number of groups of `numLookups` lookups taken `groupSize` at a time,
and at least one (`lookup_groups`). -/
def lookupGroups (numLookups groupSize : Nat) : Nat :=
  max ((numLookups + (max groupSize 1 - 1)) / max groupSize 1) 1

end Arithmetic

section Constraints

variable (F : Type) {EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]

/-- **The values of the lookup constraints** at one evaluation point: for each
group of lookups, in order, the coordinates of its constraint.

* `buf` holds the values of the nodes of the graph;
* `stage2` and `stage2Next` are the current and the next row of the lookup
  trace: the coordinates of the sum entering group `g` are at positions
  `g * d` to `g * d + d - 1`;
* `publics` holds the coordinates of `β`, then those of `γ`;
* `deltaScaled` holds the coordinates of the difference between the sums
  leaving and entering the circuit, divided by the value the last-row selector
  takes on the last row;
* `isLastRow` is the value of the last-row selector.

A circuit without lookups has one group with no message: its constraint is
`acc' - acc`, with the last-row term. -/
def logupConstraintValues (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array EF) (isLastRow : EF) (groupSize : Nat) :
    Array EF :=
  let d := ExtensionOps.degree (F := F) (EF := EF)
  let table : Array EF := basisTable F
  let size := max groupSize 1
  let beta := publics.extract 0 d
  let gamma := publics.extract d (2 * d)
  let groups := lookupGroups lookups.size groupSize
  let wrap : Array EF := Array.ofFn (n := d) fun k =>
    stage2Next.getD k.val 0 + isLastRow * deltaScaled.getD k.val 0
  (List.range groups).foldl
    (fun out g =>
      let chunk := lookups.extract (g * size) ((g + 1) * size)
      let diff : Array EF := Array.ofFn (n := d) fun k =>
        (if g + 1 < groups then stage2.getD ((g + 1) * d + k.val) 0 else wrap.getD k.val 0)
          - stage2.getD (g * d + k.val) 0
      out ++ groupConstraint d table (chunk.map (lookupMessage d table beta gamma buf))
        (chunk.map fun lookup => buf.getD lookup.multiplicity 0) diff)
    #[]

end Constraints

end CertiFri.Stark
