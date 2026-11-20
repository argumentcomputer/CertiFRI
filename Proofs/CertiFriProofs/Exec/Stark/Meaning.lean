import CertiFriProofs.Exec.Stark.Shard

/-!
# What vanishing constraints say

The soundness theorems of the STARK conclude that no constraint value of a
proof fails (`ConstraintFail`, `Exec/Stark/Shard.lean`): the zeros of every
graph and the lookup constraints vanish on every row, for the polynomials the
committed columns decode to. This file spells out what that means.

## Contents

* `Circuit.LookupsPlain`: the lookups of a circuit only read a prefix of nodes
  none of which reads the lookup trace or a public value. Then the messages of
  the circuit are functions of the fixed trace, the main trace and the row
  selectors. The zeros may read anything.
* `Circuit.ZerosPlain`: the zeros of a circuit are in such a prefix. Then they
  are functions of the fixed trace, the main trace and the row selectors. The
  lookups may read anything.
* `Circuit.PlainOk`: one such prefix holds the zeros and what the lookups
  read. It gives the two properties above (`Circuit.PlainOk.lookupsPlain`,
  `Circuit.PlainOk.zerosPlain`).
* `zeros_of_not_constraintFail`: if no constraint fails, every zero of every
  active circuit whose zeros are plain (`ZerosPlain`) vanishes on every row, on
  the values of its fixed and main columns alone.
* `shardLookupItems`: the messages the active circuits of a proof send on the
  rows of their traces, read off the fixed and main columns.
* `lookupSum_of_not_constraintFail`: if no constraint fails, the lookups of
  the active circuits are plain (`LookupsPlain`), and no message has a zero
  denominator at the lookup challenges, then the lookup sum leaving the last
  active circuit is the sum entering the first plus the lookup sum of these
  messages. Nothing is asked of the zeros.
* `coeff_shardCols_mem_base`: the main and fixed columns of a proof have
  base-field coefficients, for base-field rows and under the margin of unique
  decoding.

## Assumptions

The characteristic is not two (`h2`), so that the number of rows of a trace is
not zero in the field.

`LookupsPlain`, `ZerosPlain` and `PlainOk` are properties of the system:
multi-stark compiles lookups and base constraints from expressions without the
lookup trace. The two theorems ask for different things:

* `lookupSum_of_not_constraintFail` needs `LookupsPlain`: the multiplicities
  and the arguments of the lookups read only the fixed trace, the main trace
  and the row selectors. The zeros may read anything, so a system with
  extension constraints (zeros that read the lookup trace), or with a public
  value in a constraint, is covered, as long as the nodes its lookups refer to
  come before the first node that reads the lookup trace or a public value.
* `zeros_of_not_constraintFail` needs `ZerosPlain` of the circuit: its zeros
  read only the fixed trace, the main trace and the row selectors. A circuit
  with an extension constraint, or with a public value in a constraint, does
  not have it.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model CertiFri.Fri Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K]

/-- The zeros and the lookups of the circuit only read a prefix of its nodes,
none of which reads the lookup trace or a public value. -/
def _root_.CertiFri.Stark.Circuit.PlainOk (c : Circuit F) : Prop :=
  ∃ k, (∀ i < k, ∀ node, c.graph.nodes[i]? = some node → node.Plain) ∧
    (∀ z ∈ c.graph.zeros, z < k) ∧
    ∀ l ∈ c.graph.lookups, l.multiplicity < k ∧ ∀ a ∈ l.args, a < k

/-- The lookups of the circuit only read a prefix of its nodes, none of which
reads the lookup trace or a public value: the first `k` nodes are plain, and
the multiplicity and the arguments of every lookup are among them. The zeros
may read anything. -/
def _root_.CertiFri.Stark.Circuit.LookupsPlain (c : Circuit F) : Prop :=
  ∃ k, (∀ i < k, ∀ node, c.graph.nodes[i]? = some node → node.Plain) ∧
    ∀ l ∈ c.graph.lookups, l.multiplicity < k ∧ ∀ a ∈ l.args, a < k

/-- The zeros of the circuit are in a prefix of its nodes, none of which reads
the lookup trace or a public value: the first `k` nodes are plain, and every
zero is one of them. The lookups may read anything. -/
def _root_.CertiFri.Stark.Circuit.ZerosPlain (c : Circuit F) : Prop :=
  ∃ k, (∀ i < k, ∀ node, c.graph.nodes[i]? = some node → node.Plain) ∧
    ∀ z ∈ c.graph.zeros, z < k

omit [FieldOps F] [TwoAdicOps F] in
/-- A circuit whose zeros and lookups are plain has plain lookups. -/
theorem _root_.CertiFri.Stark.Circuit.PlainOk.lookupsPlain {c : Circuit F} (h : c.PlainOk) :
    c.LookupsPlain := by
  obtain ⟨k, hnodes, -, hlookups⟩ := h
  exact ⟨k, hnodes, hlookups⟩

omit [FieldOps F] [TwoAdicOps F] in
/-- A circuit whose zeros and lookups are plain has plain zeros. -/
theorem _root_.CertiFri.Stark.Circuit.PlainOk.zerosPlain {c : Circuit F} (h : c.PlainOk) :
    c.ZerosPlain := by
  obtain ⟨k, hnodes, hzeros, -⟩ := h
  exact ⟨k, hnodes, hzeros⟩

variable (M : StarkModel F EF K) (sys : System F D) (θ : ℝ) (com : Compiled.Committed K D)

/-- The row `r` of the active circuit `ci`, at position `pos`: the values of
its fixed and main columns on rows `r` and `r + 1` of its trace domain, with
the row selectors, and neither lookup trace nor public values. -/
noncomputable def plainRow (active : Array Bool) (logDegrees : Array ℕ) (stage1 : D)
    (pos ci r : ℕ) : RowValues K :=
  pointRow (sys.circuits.getD ci default) (2 ^ logDegrees.getD pos 0)
    (M.gen (logDegrees.getD pos 0))
    { pre := (shardCols M sys θ com active logDegrees stage1 stage1 stage1 pos ci).pre
      main := (shardCols M sys θ com active logDegrees stage1 stage1 stage1 pos ci).main
      stage2 := fun _ => 0
      quotient := fun _ => 0 }
    #[] (M.gen (logDegrees.getD pos 0) ^ r)

/-- The row of a proof on row `r` of the trace domain agrees with `plainRow` on
the fixed trace, the main trace and the selectors: the fixed and main columns
depend neither on the commitments to the lookup traces and the quotients nor on
the public values. -/
private theorem rowAgree_plainRow (active : Array Bool) (logDegrees : Array ℕ)
    (stage1 stage2 quot : D) (publics : Array K) (pos ci r : ℕ) :
    RowAgree
      (pointRow (sys.circuits.getD ci default) (2 ^ logDegrees.getD pos 0)
        (M.gen (logDegrees.getD pos 0))
        (shardCols M sys θ com active logDegrees stage1 stage2 quot pos ci) publics
        (M.gen (logDegrees.getD pos 0) ^ r))
      (plainRow M sys θ com active logDegrees stage1 pos ci r) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {M sys θ com}

/-- **Plain zeros hold on every row.** If no constraint of a proof fails, every
zero of the graph of every active circuit whose zeros are plain vanishes on
every row of its trace domain, on the values of the fixed and main columns. -/
theorem zeros_of_not_constraintFail {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} {β γ acc0 : K} {accs : Array K}
    (h : ¬ ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs)
    {p : ℕ × ℕ} (hp : p ∈ (activeIndices active).zipIdx)
    (hplain : (sys.circuits.getD p.1 default).ZerosPlain) {r : ℕ}
    (hr : r < 2 ^ logDegrees.getD p.2 0) {z : ℕ}
    (hz : z ∈ (sys.circuits.getD p.1 default).graph.zeros) :
    (sweep M.base.toModel (sys.circuits.getD p.1 default).graph.nodes
      (plainRow M sys θ com active logDegrees stage1 p.2 p.1 r)).getD z 0 = 0 := by
  obtain ⟨k, hnodes, hzeros⟩ := hplain
  have hzk := hzeros z hz
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hz
  -- The constraint value `i` of the row is the value of the zero `i`.
  have hval : (rowVals M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs p.2 p.1
      (M.gen (logDegrees.getD p.2 0) ^ r)).getD i 0 = 0 := by
    by_contra hne
    exact h ⟨p, hp, r, hr, i, hne⟩
  rw [rowVals, getD_constraintVals_zero _ _ _ _ _ _ hi,
    Array.getD_eq_getD_getElem? (xs := (sys.circuits.getD p.1 default).graph.zeros),
    Array.getElem?_eq_getElem hi, Option.getD_some] at hval
  -- The zero is a plain node: it has the same value on the plain row.
  exact (getD_sweep_congr_of_plain _ _ k hnodes
    (rowAgree_plainRow M sys θ com active logDegrees stage1 stage2 quot
      (shardPublics M β γ acc0 accs p.2) p.2 p.1 r) hzk).symm.trans hval

variable (M sys θ com)

/-- The messages the active circuits of a proof send on the rows of their
traces, with their multiplicities, read off the fixed and main columns. -/
noncomputable def shardLookupItems (active : Array Bool) (logDegrees : Array ℕ) (stage1 : D) :
    List (K × List K) :=
  (activeIndices active).zipIdx.flatMap fun p =>
    circuitItems M.base.toModel (sys.circuits.getD p.1 default)
      (fun r => plainRow M sys θ com active logDegrees stage1 p.2 p.1 r)
      (2 ^ logDegrees.getD p.2 0)

variable {M sys θ com}

omit [FieldOps F] [TwoAdicOps F] [DecidableEq K] in
/-- The messages of a circuit with plain lookups are the same on rows that
agree on the fixed trace, the main trace and the selectors. -/
private theorem circuitItems_congr_of_plain (ι : F → K) {c : Circuit F}
    (hplain : c.LookupsPlain) {rows rows' : ℕ → RowValues K}
    (h : ∀ r, RowAgree (rows r) (rows' r)) (n : ℕ) :
    circuitItems ι c rows n = circuitItems ι c rows' n := by
  obtain ⟨k, hnodes, hlookups⟩ := hplain
  rw [circuitItems, circuitItems]
  refine List.flatMap_congr fun r _ => List.map_congr_left fun l hl => ?_
  obtain ⟨hm, hargs⟩ := hlookups l (Array.mem_toList_iff.mp hl)
  rw [getD_sweep_congr_of_plain ι _ k hnodes (h r) hm]
  refine congrArg _ (List.map_congr_left fun a ha => ?_)
  exact getD_sweep_congr_of_plain ι _ k hnodes (h r) (hargs a (Array.mem_toList_iff.mp ha))

omit [DecidableEq K] in
/-- Lookup sums telescope over positions. If the difference of `a` between the
positions `pos + 1` and `pos` is the lookup sum of the messages of the element
at position `pos`, for the elements of a list at the positions from `n`, then
the difference of `a` between the end of the list and `n` is the lookup sum of
all these messages. -/
private theorem lookupSum_flatMap_zipIdx {α : Type} (β γ : K) (a : ℕ → K)
    (f : α × ℕ → List (K × List K)) (l : List α) (n : ℕ)
    (h : ∀ p ∈ l.zipIdx n, a (p.2 + 1) - a p.2 = lookupSum β γ (f p)) :
    a (n + l.length) - a n = lookupSum β γ ((l.zipIdx n).flatMap f) := by
  induction l generalizing n with
  | nil =>
    rw [List.length_nil, Nat.add_zero, sub_self]
    rfl
  | cons x l ih =>
    have hx := h (x, n) (by rw [List.zipIdx_cons]; exact List.mem_cons_self)
    have hl := ih (n + 1) fun p hp =>
      h p (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hp)
    rw [List.zipIdx_cons, List.flatMap_cons, lookupSum_append, ← hx, ← hl, List.length_cons,
      show n + (l.length + 1) = n + 1 + l.length by omega]
    ring

omit [DecidableEq K] in
/-- The lookup sum entering the circuit after position `pos` is the one leaving
the circuit at position `pos`. -/
private theorem accIn_succ (acc0 : K) (accs : Array K) (pos : ℕ) :
    accIn acc0 accs (pos + 1) = accOut accs pos := by
  rw [accIn, ite_eq_right (Nat.succ_ne_zero pos), Nat.add_sub_cancel, accOut]

omit [DecidableEq K] in
/-- The lookup sum entering the position after the last lookup sum is the last
one, and the sum entering the first circuit if there is none. -/
private theorem accIn_size (acc0 : K) (accs : Array K) :
    accIn acc0 accs accs.size = accs.back?.getD acc0 := by
  rw [accIn, Array.back?_eq_getElem?]
  split
  · next h0 =>
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  · next h0 =>
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    rfl

/-- **The lookup sums of a proof add up.** If no constraint of a proof fails,
the lookups of its active circuits are plain, no message they send has a zero
denominator at the lookup challenges, and there is one lookup sum per active
circuit, then the lookup sum leaving the last active circuit is the sum
entering the first plus the lookup sum of the messages the circuits send. The
zeros of the circuits may read anything. -/
theorem lookupSum_of_not_constraintFail (h2 : (2 : K) ≠ 0) {active : Array Bool}
    {logDegrees : Array ℕ} {stage1 stage2 quot : D} {β γ acc0 : K} {accs : Array K}
    (h : ¬ ConstraintFail M sys θ com active logDegrees stage1 stage2 quot β γ acc0 accs)
    (hplain : ∀ p ∈ (activeIndices active).zipIdx,
      (sys.circuits.getD p.1 default).LookupsPlain)
    (htwo : ∀ p ∈ (activeIndices active).zipIdx,
      logDegrees.getD p.2 0 ≤ TwoAdicOps.twoAdicity (F := F))
    (hsize : accs.size = (activeIndices active).length)
    (hne : ∀ it ∈ shardLookupItems M sys θ com active logDegrees stage1,
      β + (fpPoly it.2).eval γ ≠ 0) :
    (accs.back?.getD acc0) =
      acc0 + lookupSum β γ (shardLookupItems M sys θ com active logDegrees stage1) := by
  -- One circuit: the lookup sum grows by the lookup sum of its messages.
  have hstep : ∀ p ∈ (activeIndices active).zipIdx,
      accIn acc0 accs (p.2 + 1) - accIn acc0 accs p.2 =
        lookupSum β γ (circuitItems M.base.toModel (sys.circuits.getD p.1 default)
          (fun r => plainRow M sys θ com active logDegrees stage1 p.2 p.1 r)
          (2 ^ logDegrees.getD p.2 0)) := by
    intro p hp
    have hg : IsPrimitiveRoot (M.gen (logDegrees.getD p.2 0)) (2 ^ logDegrees.getD p.2 0) :=
      M.generator _ (htwo p hp)
    have hn : ((2 ^ logDegrees.getD p.2 0 : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact pow_ne_zero _ h2
    have hcirc := logup_circuit_eq M.extData.isTable M.extData.basis_zero M.extData.d_pos
      M.base.toModel (sys.circuits.getD p.1 default) hg hn
      (shardCols M sys θ com active logDegrees stage1 stage2 quot p.2 p.1)
      (shardPublics M β γ acc0 accs p.2)
    rw [show asm M.extData.basis M.extData.d
          ((shardPublics M β γ acc0 accs p.2).extract 0 M.extData.d) = β from
        M.extData.asm_publics_beta _ _ _ _,
      show asm M.extData.basis M.extData.d
          ((shardPublics M β γ acc0 accs p.2).extract M.extData.d (2 * M.extData.d)) = γ from
        M.extData.asm_publics_gamma _ _ _ _,
      show asm M.extData.basis M.extData.d
          ((shardPublics M β γ acc0 accs p.2).extract (2 * M.extData.d) (3 * M.extData.d)) =
          accIn acc0 accs p.2 from M.extData.asm_publics_acc _ _ _ _,
      show asm M.extData.basis M.extData.d
          ((shardPublics M β γ acc0 accs p.2).extract (3 * M.extData.d) (4 * M.extData.d)) =
          accOut accs p.2 from M.extData.asm_publics_next _ _ _ _,
      circuitItems_congr_of_plain M.base.toModel (hplain p hp) (fun r =>
        rowAgree_plainRow M sys θ com active logDegrees stage1 stage2 quot
          (shardPublics M β γ acc0 accs p.2) p.2 p.1 r)] at hcirc
    rw [accIn_succ]
    refine hcirc (fun r hr i => ?_) fun it hit => hne it (List.mem_flatMap.mpr ⟨p, hp, hit⟩)
    -- The lookup constraints are the constraint values after the zeros.
    by_contra hval
    refine h ⟨p, hp, r, hr, (sys.circuits.getD p.1 default).graph.zeros.size + i, ?_⟩
    rw [rowVals, getD_constraintVals_logup]
    exact hval
  -- Over the circuits the lookup sums cancel.
  have htel := lookupSum_flatMap_zipIdx β γ (accIn acc0 accs)
    (fun p : ℕ × ℕ => circuitItems M.base.toModel (sys.circuits.getD p.1 default)
      (fun r => plainRow M sys θ com active logDegrees stage1 p.2 p.1 r)
      (2 ^ logDegrees.getD p.2 0)) (activeIndices active) 0 hstep
  rw [Nat.zero_add, ← hsize, accIn_size, show accIn acc0 accs 0 = acc0 from ite_eq_left rfl] at htel
  exact eq_add_of_sub_eq' htel

/-- A coset of a height that exists in the field has `2 ^ h` points. -/
private theorem card_coset (M : StarkModel F EF K) {h : ℕ}
    (hh : h ≤ TwoAdicOps.twoAdicity (F := F)) : (M.coset h).card = 2 ^ h := by
  rw [StarkModel.coset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact (M.generator h hh).pow_inj (by simpa using ha) (by simpa using hb)
    (mul_left_cancel₀ M.shift_ne hab)

/-- **The main and fixed columns have base-field coefficients**, for committed
rows of base-field elements, at a height that exists in the field, for an
agreement of at most one and under the margin of unique decoding. -/
theorem coeff_shardCols_mem_base (hθ : θ ≤ 1) {active : Array Bool} {logDegrees : Array ℕ}
    {stage1 stage2 quot : D} {pos ci : ℕ}
    (htwo : logDegrees.getD pos 0 + sys.fri.logBlowup ≤ TwoAdicOps.twoAdicity (F := F))
    (hmargin : DecodeMargin (M.coset (logDegrees.getD pos 0 + sys.fri.logBlowup))
      (2 ^ logDegrees.getD pos 0) θ) (j n : ℕ) :
    ((shardCols M sys θ (M.baseRows com) active logDegrees stage1 stage2 quot pos ci).main
        j).coeff n ∈ Set.range M.base.toModel ∧
      ((shardCols M sys θ (M.baseRows com) active logDegrees stage1 stage2 quot pos ci).pre
        j).coeff n ∈ Set.range M.base.toModel := by
  -- The margin leaves more points than the degree bound.
  have hmar : ((2 ^ (logDegrees.getD pos 0 + sys.fri.logBlowup - sys.fri.logBlowup) + 2 : ℕ) : ℝ)
      ≤ θ * 2 ^ (logDegrees.getD pos 0 + sys.fri.logBlowup) := by
    rw [DecodeMargin, card_coset M htwo] at hmargin
    rw [Nat.add_sub_cancel]
    have hle : θ * (2 : ℝ) ^ (logDegrees.getD pos 0 + sys.fri.logBlowup)
        ≤ 2 ^ (logDegrees.getD pos 0 + sys.fri.logBlowup) :=
      mul_le_of_le_one_left (by positivity) hθ
    push_cast at hmargin ⊢
    linarith
  refine ⟨M.coeff_colPoly_mem_base _ _ _ _ _ _ htwo hmar n, ?_⟩
  rw [shardCols]
  split
  · exact M.coeff_colPoly_mem_base _ _ _ _ _ _ htwo hmar n
  · rw [coeff_zero]
    exact ⟨0, M.base.map_zero⟩

end CertiFri.Exec.Stark
