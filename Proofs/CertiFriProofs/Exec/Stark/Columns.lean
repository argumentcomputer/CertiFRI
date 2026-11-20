import CertiFriProofs.Exec.Stark.Model
import CertiFriProofs.Exec.Extract
import CertiFriProofs.Theory.PcsRbr.DecodeTight

/-!
# Committed columns and the polynomials they decode to

A column of a committed matrix is a word on a coset of a two-adic subgroup,
read off the rows a commitment opens to. Inside the unique-decoding radius it
determines a polynomial: the one the opening proof makes claims about, when the
opening points are outside the coset. This file defines that polynomial for the
columns of the STARK, from a `StarkModel` alone, and relates it to the claims
of the opening protocol.

## Contents

* `StarkModel.cosetPoint`, `StarkModel.coset`: the point of an index on the
  coset of `2 ^ h` points, in the order the rows are committed, and the coset.
* `StarkModel.colWord com root dims mi col h`: the word of column `col` of
  matrix `mi` under `root`, of `2 ^ h` entries, for the committed rows `com`.
* `StarkModel.colPoly lb θ …`: the polynomial of degree at most
  `2 ^ (h - lb)` it decodes to at agreement `θ` (`decodeT`,
  `Theory/PcsRbr/DecodeTight.lean`): one that agrees with the word on a
  fraction `θ` of the coset; zero if there is none.
* `StarkModel.baseRows com`: the committed rows `com`, without the rows that
  have an entry outside the base field.
* `claims_f_eq_colWord`, `coset_eq`, `ldt_degree_eq`: the functions, cosets and
  degree bounds of the claims of the opening protocol (`Compiled.Params.claims`
  for `modelParams`) are these.
* `eval_colPoly_of_not_claimsFail`: if the claims of an opening do not fail
  and no opening point lies in the coset of a column it is claimed for, every
  claimed value is the value of the decoded polynomial of its column at its
  opening point.
* `natDegree_colPoly_le`, `coeff_colPoly_mem_base`: the decoded polynomial has
  degree at most `2 ^ (h - lb)`, and base-field coefficients when the rows are
  base-field rows.
* `StarkModel.card_coset`, `StarkModel.strictMargin_coset`: a coset of a height
  that exists in the field has `2 ^ h` points, and the margin of unique
  decoding holds on it, for every height, as soon as
  `1 + 2 ^ (-lb) < 2 * θ`.

## Assumptions

The margin of unique decoding (`StrictMargin`,
`|D| + d < 2 * θ * |D|`) at the heights of the matrices of the shape, where it
is used. It does not depend on the height: `strictMargin_coset` derives it from
the blowup and `θ` alone.

`eval_colPoly_of_not_claimsFail` asks that no opening point lies in the coset
of a column it is claimed for. The opening protocol says nothing about a
committed word at an opening point (`PcsRbr.ClaimsHoldOff`), and the decoder
leaves no point out: the hypothesis gives the agreement on the whole dense set.
The verifier does not check it: the STARK pays for it with the probability that
its random opening point lands in a coset (`fractionLE_offCosets`,
`Exec/Stark/Shard.lean`). Of the shape checks of the opening proof, the theorem
asks only for the numbers of opening points and that no column is shorter than
the final height.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Fri CertiFri.Oracle Polynomial

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K]

namespace StarkModel

variable (M : StarkModel F EF K)

/-- The point of `index` on the coset of `2 ^ h` points, in the order the rows
of a matrix are committed. -/
def cosetPoint (h index : ℕ) : K := M.shift * M.gen h ^ reverseBitsLen index h

/-- The coset of `2 ^ h` points the columns of log-height `h` are committed
on. -/
def coset (h : ℕ) : Finset K := (Finset.range (2 ^ h)).image fun i => M.shift * M.gen h ^ i

/-- The word of column `col` of matrix `mi` under `root`, of `2 ^ h` entries:
its value at the point of index `i` is entry `col` of row `i`. It is zero where
no row is committed, where the row is too short, and off the coset. -/
noncomputable def colWord (com : Compiled.Committed K D) (root : D) (dims : Array Dimensions)
    (mi col h : ℕ) : K → K :=
  Compiled.ofIndexed (2 ^ h) (M.cosetPoint h) fun i => Compiled.entry (com root dims mi i) col

/-- The polynomial a column decodes to at agreement `θ`: of degree at most
`2 ^ (h - lb)`, for a blowup of `2 ^ lb`, agreeing with the word of the column
on a fraction `θ` of the coset. -/
noncomputable def colPoly (lb : ℕ) (θ : ℝ) (com : Compiled.Committed K D) (root : D)
    (dims : Array Dimensions) (mi col h : ℕ) : K[X] :=
  decodeT (M.coset h) (2 ^ (h - lb)) θ (M.colWord com root dims mi col h)

open Classical in
/-- The committed rows `com`, without the rows that have an entry outside the
base field. The executable verifier only ever opens rows of base-field
elements. -/
noncomputable def baseRows (com : Compiled.Committed K D) : Compiled.Committed K D :=
  fun root dims mi i =>
    (com root dims mi i).bind fun row =>
      if ∀ x ∈ row.toList, x ∈ Set.range M.base.toModel then some row else none

/-- The decoded polynomial of a column has degree at most `2 ^ (h - lb)`. -/
theorem natDegree_colPoly_le (lb : ℕ) (θ : ℝ) (com : Compiled.Committed K D) (root : D)
    (dims : Array Dimensions) (mi col h : ℕ) :
    (M.colPoly lb θ com root dims mi col h).natDegree ≤ 2 ^ (h - lb) := by
  have hlt := degree_decodeT_lt (M.coset h) (2 ^ (h - lb)) θ (M.colWord com root dims mi col h)
  exact natDegree_le_iff_degree_le.mpr (Order.le_of_lt_succ (by exact_mod_cast hlt))

/-! ### The base field -/

/-- The base field, as a subfield of `K`: the values of the executable base
field. -/
private def baseSubfield : Subfield K where
  carrier := Set.range M.base.toModel
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, M.base.map_mul a b⟩
  one_mem' := ⟨1, M.base.map_one⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, M.base.map_add a b⟩
  zero_mem' := ⟨0, M.base.map_zero⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, M.base.map_neg a⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, M.base.map_inv a⟩

omit [DecidableEq K] in
/-- The elements of the base subfield are the values of the executable base
field. -/
private theorem mem_baseSubfield {x : K} : x ∈ M.baseSubfield ↔ x ∈ Set.range M.base.toModel :=
  Iff.rfl

/-- A polynomial of degree below the number of points of a set, whose points
are in a subfield and whose values at them are in the subfield, has its
coefficients in the subfield: it is the Lagrange interpolant of its values. -/
private theorem coeff_mem_of_eval_mem (L : Subfield K) {P : K[X]} {s : Finset K}
    (hdeg : P.degree < s.card) (hs : ∀ x ∈ s, x ∈ L) (hP : ∀ x ∈ s, P.eval x ∈ L) (n : ℕ) :
    P.coeff n ∈ L := by
  have hC : ∀ {a : K}, a ∈ L → C a ∈ lifts L.subtype := fun ha => C'_mem_lifts ⟨⟨_, ha⟩, rfl⟩
  have hlift : P ∈ lifts L.subtype := by
    rw [Lagrange.eq_interpolate (v := id) (Set.injOn_id _) hdeg, Lagrange.interpolate_apply]
    refine Subsemiring.sum_mem _ fun i hi => Subsemiring.mul_mem _ (hC (hP i hi)) ?_
    rw [Lagrange.basis]
    refine Subsemiring.prod_mem _ fun j hj => ?_
    have hj' := hs j (Finset.mem_of_mem_erase hj)
    rw [Lagrange.basisDivisor]
    refine Subsemiring.mul_mem _ (hC (L.inv_mem (L.sub_mem (hs i hi) hj'))) ?_
    rw [lifts_iff_liftsRing]
    exact Subring.sub_mem _ ((lifts_iff_liftsRing _ _).mp (X_mem_lifts _))
      ((lifts_iff_liftsRing _ _).mp (hC hj'))
  obtain ⟨a, ha⟩ := (lifts_iff_coeff_lifts P).mp hlift n
  rw [← ha]
  exact a.2

/-- A coset of a height that exists in the field has `2 ^ h` points. -/
theorem card_coset {h : ℕ} (hh : h ≤ TwoAdicOps.twoAdicity (F := F)) :
    (M.coset h).card = 2 ^ h := by
  rw [coset, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  exact (M.generator h hh).pow_inj (by simpa using ha) (by simpa using hb)
    (mul_left_cancel₀ M.shift_ne hab)

/-- **The margin of unique decoding, for every height.** On the coset of
`2 ^ (k + lb)` points of a height that exists in the field, with the degree
bound `2 ^ k` of a blowup of `2 ^ lb`, the strict margin holds as soon as
`1 + 2 ^ (-lb) < 2 * θ`. The condition does not mention `k`. -/
theorem strictMargin_coset {k lb : ℕ} {θ : ℝ} (hh : k + lb ≤ TwoAdicOps.twoAdicity (F := F))
    (hθ : 1 + (1 / 2 : ℝ) ^ lb < 2 * θ) : StrictMargin (M.coset (k + lb)) (2 ^ k) θ := by
  have hpos : (0 : ℝ) < 2 ^ (k + lb) := by positivity
  have hk : (1 / 2 : ℝ) ^ lb * 2 ^ (k + lb) = 2 ^ k := by
    rw [pow_add, one_div, inv_pow]
    field_simp
  have hmul := mul_lt_mul_of_pos_right hθ hpos
  rw [add_mul, one_mul, hk] at hmul
  unfold StrictMargin
  rw [M.card_coset hh]
  push_cast
  linarith

/-- The points of a coset are in the base field. -/
private theorem mem_baseSubfield_of_mem_coset {h : ℕ} {x : K} (hx : x ∈ M.coset h) :
    x ∈ M.baseSubfield := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
  exact M.baseSubfield.mul_mem (M.mem_baseSubfield.mpr (Set.mem_range_self _))
    (M.baseSubfield.pow_mem (M.mem_baseSubfield.mpr (Set.mem_range_self _)) i)

omit [DecidableEq K] in
/-- An entry of a base-field row is in the base field. -/
private theorem entry_baseRows_mem (com : Compiled.Committed K D) (root : D)
    (dims : Array Dimensions) (mi i col : ℕ) :
    Compiled.entry (M.baseRows com root dims mi i) col ∈ M.baseSubfield := by
  have hall : ∀ x ∈ ((M.baseRows com root dims mi i).getD #[]).toList, x ∈ M.baseSubfield := by
    unfold baseRows
    cases com root dims mi i with
    | none =>
      intro x hx
      simp at hx
    | some row =>
      rw [Option.bind_some]
      split_ifs with hrow
      · exact hrow
      · intro x hx
        simp at hx
  rw [Compiled.entry, Array.getD_eq_getD_getElem?]
  cases hx : ((M.baseRows com root dims mi i).getD #[])[col]? with
  | none => exact M.baseSubfield.zero_mem
  | some x => exact hall x (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx))

/-- The word of a column of base-field rows takes its values in the base
field. -/
private theorem colWord_baseRows_mem (com : Compiled.Committed K D) (root : D)
    (dims : Array Dimensions) (mi col h : ℕ) (x : K) :
    M.colWord (M.baseRows com) root dims mi col h x ∈ M.baseSubfield := by
  unfold colWord Compiled.ofIndexed
  split
  · exact M.entry_baseRows_mem com root dims mi _ col
  · exact M.baseSubfield.zero_mem

/-- **Base-field rows decode to base-field polynomials.** For a height that
exists in the field and an agreement that leaves more points than the degree
bound, the decoded polynomial of a column of base-field rows has base-field
coefficients. -/
theorem coeff_colPoly_mem_base (lb : ℕ) {θ : ℝ} (com : Compiled.Committed K D) (root : D)
    (dims : Array Dimensions) (mi col : ℕ) {h : ℕ} (hh : h ≤ TwoAdicOps.twoAdicity (F := F))
    (hθ : ((2 ^ (h - lb) : ℕ) : ℝ) < θ * 2 ^ h) (n : ℕ) :
    (M.colPoly lb θ (M.baseRows com) root dims mi col h).coeff n ∈ Set.range M.base.toModel := by
  rw [← mem_baseSubfield]
  unfold colPoly decodeT
  split
  · next hex =>
    obtain ⟨hdeg, B, hB, hcard, hf⟩ := Classical.choose_spec hex
    refine coeff_mem_of_eval_mem M.baseSubfield (s := B) ?_
      (fun x hx => M.mem_baseSubfield_of_mem_coset (hB hx)) (fun x hx => ?_) n
    · rw [M.card_coset hh] at hcard
      have hlt : ((2 ^ (h - lb) : ℕ) : ℝ) < (B.card : ℝ) := by
        push_cast at hθ hcard ⊢
        linarith
      have hle : 2 ^ (h - lb) + 1 ≤ B.card := Nat.cast_lt.mp hlt
      exact hdeg.trans_le (by exact_mod_cast hle)
    · rw [← hf x hx]
      exact M.colWord_baseRows_mem com root dims mi col h x
  · rw [coeff_zero]
    exact M.baseSubfield.zero_mem

/-! ### Compatible generators -/

omit [DecidableEq K] in
/-- The generator of the height `n - j` is the `2 ^ j`-th power of the generator
of the height `n`, for a height `n` that exists in the field. -/
private theorem gen_sub {n j : ℕ} (hn : n ≤ TwoAdicOps.twoAdicity (F := F)) (hj : j ≤ n) :
    M.gen (n - j) = M.gen n ^ 2 ^ j := by
  have h := Domain.generator_eq_pow (g := M.gen) (fun h hh => M.generator_sq h (hh.trans_le hn))
    (Nat.sub_le n j)
  rwa [Nat.sub_sub_self hj] at h

end StarkModel

/-! ## The claims of the opening protocol -/

section Claims

variable [Inhabited D] (M : StarkModel F EF K) (params : FriParams) (shape : ClaimShape)
  (hshape : logMaxHeight params.logBlowup shape ≤ TwoAdicOps.twoAdicity (F := F))

omit [Inhabited D] in
/-- The function of a claim of the opening protocol is the word of its
column. -/
theorem claims_f_eq_colWord (msg : Compiled.Msg K D shape.length) (com : Compiled.Committed K D)
    {j : ℕ} (hj : j ≤ logMaxHeight params.logBlowup shape)
    (k : Fin ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).numClaims
      j)) :
    ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).claims msg com j
        k).f =
      M.colWord com
        (msg.inputRoots ((modelParams M.toFieldModel params shape
          (M.wellFormed params shape hshape)).slot j k).batch)
        ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).dims
          ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).slot j
            k).batch)
        ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).slot j
          k).matrix
        ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).slot j k).col
        (logMaxHeight params.logBlowup shape - j) := by
  have hpt : (fun i => M.shift * pointOfIndex (M.gen (logMaxHeight params.logBlowup shape))
      (logMaxHeight params.logBlowup shape) (logMaxHeight params.logBlowup shape - j) i) =
      M.cosetPoint (logMaxHeight params.logBlowup shape - j) := by
    funext i
    rw [pointOfIndex, Nat.sub_sub_self hj, ← M.gen_sub hshape hj]
    rfl
  unfold Compiled.Params.claims StarkModel.colWord
  dsimp only
  exact congrFun (congrArg (Compiled.ofIndexed _) hpt) _

/-- The coset of a level of the opening protocol is the coset of its height. -/
theorem coset_eq {j : ℕ} (hj : j ≤ logMaxHeight params.logBlowup shape) :
    (twoAdicDomain
        (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).ω
        (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).n j).image
      ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).shift * ·) =
      M.coset (logMaxHeight params.logBlowup shape - j) := by
  show (twoAdicDomain (M.gen (logMaxHeight params.logBlowup shape))
    (logMaxHeight params.logBlowup shape) j).image (M.shift * ·) = _
  rw [twoAdicDomain, StarkModel.coset, Finset.image_image, M.gen_sub hshape hj]
  rfl

/-- The degree bound of a level of the opening protocol, for a first domain not
below the final height: the size of the coset divided by the blowup. -/
theorem ldt_degree_eq (hfinal : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape)
    {j : ℕ} (hj : j ≤ numRounds params shape) :
    (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).ldt.degree j =
      2 ^ (logMaxHeight params.logBlowup shape - j - params.logBlowup) := by
  show 2 ^ (numRounds params shape - j) * 2 ^ params.logFinalPolyLen = _
  rw [← pow_add]
  congr 1
  unfold numRounds FriParams.logFinalHeight at *
  omega

omit [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K] [DecidableEq K]
  [Inhabited D] in
/-- A claim of a shape is about a column of a matrix of the shape, of the
committed height of that matrix. -/
private theorem exists_matrix_of_mem_claimRefs {lb : ℕ} {c : ClaimRef}
    (hc : c ∈ claimRefs lb shape) : ∃ m ∈ shape.flatten, c.logHeight = m.logDegree + lb := by
  obtain ⟨p, hp, -, -, hh, -⟩ := mem_claimRefs hc
  obtain ⟨mats, ms, hmats, hms, hph, -⟩ := mem_pointRefs (List.mem_of_getElem? hp)
  exact ⟨ms, List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩,
    hh.trans hph⟩

omit [DecidableEq K] in
/-- The root of an input batch in the statement, read through `view`, is the
commitment of the batch. -/
private theorem inputRoots_firstMessage (commitments : Array D) (points values : Array EF)
    (b : Fin (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).batches) :
    (view M.toFieldModel params shape
        (firstMessage (F := F) commitments points values)).inputRoots b =
      commitments.getD b.val default := by
  simp only [view, Checks.digestsIn_firstMessage, List.getD_eq_getElem?_getD,
    Array.getElem?_toList, Array.getD_eq_getD_getElem?]

omit [DecidableEq K] in
/-- The opening point of a claim of a level, in the statement read through
`view`, is the entry of `points` the claim refers to. -/
private theorem point_firstMessage (commitments : Array D) (points values : Array EF)
    (hpoints : points.size = (pointRefs params.logBlowup shape).length) {j : ℕ}
    (hj : j ≤ numRounds params shape)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length) :
    (view M.toFieldModel params shape (firstMessage (F := F) commitments points values)).point j
        k =
      M.ext.toModel (points.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).pointIdx 0) := by
  have hk : ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
      k).pointIdx < (points.toList.map M.ext.toModel).length := by
    rw [List.length_map, Array.length_toList, hpoints]
    exact Arith.pointIdx_lt_of_mem_levelClaims (List.get_mem _ k)
  rw [Arith.view_point M.toFieldModel params shape _ hj k, Arith.extsIn_firstMessage,
    List.getD_append _ _ _ _ hk, toModel_getD_toList_map]

omit [DecidableEq K] in
/-- The claimed value of a claim of a level, in the statement read through
`view`, is the entry of `values` the claim refers to. -/
private theorem value_firstMessage (commitments : Array D) (points values : Array EF)
    (hpoints : points.size = (pointRefs params.logBlowup shape).length) {j : ℕ}
    (hj : j ≤ numRounds params shape)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length) :
    (view M.toFieldModel params shape (firstMessage (F := F) commitments points values)).value j
        k =
      M.ext.toModel (values.getD
        ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).get
          k).valueIdx 0) := by
  have hlen : (points.toList.map M.ext.toModel).length =
      (pointRefs params.logBlowup shape).length := by
    rw [List.length_map, Array.length_toList, hpoints]
  rw [Arith.view_value M.toFieldModel params shape _ hj k, Arith.extsIn_firstMessage, ← hlen,
    List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    toModel_getD_toList_map]

/-- **Claims that do not fail are evaluations of the decoded polynomials.** Let
the statement of an opening have one opening point per point of the shape, and
no column shorter than the final height; let the strict margin of unique
decoding hold at the height of every column of the shape, and let no opening
point lie in the coset of a column it is claimed for. If the claims, read from
the committed rows `com`, do not fail at agreement `θ`, then for every claim of
the shape the claimed value is the value, at the opening point of the claim, of
the polynomial its column decodes to. -/
theorem eval_colPoly_of_not_claimsFail {θ : ℝ} (commitments : Array D) (points values : Array EF)
    (com : Compiled.Committed K D)
    (hpoints : points.size = (pointRefs params.logBlowup shape).length)
    (hfinal : ∀ m ∈ shape.flatten, params.logFinalHeight ≤ m.logDegree + params.logBlowup)
    (hmargin : ∀ m ∈ shape.flatten,
      StrictMargin (M.coset (m.logDegree + params.logBlowup)) (2 ^ m.logDegree) θ)
    (hoff : ∀ c ∈ claimRefs params.logBlowup shape,
      M.ext.toModel (points.getD c.pointIdx 0) ∉ M.coset c.logHeight)
    (h : ¬ PcsRbr.ClaimsFail
      (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).ldt
      (modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).shift θ
      ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).claims
        (view M.toFieldModel params shape (firstMessage commitments points values)) com))
    {c : ClaimRef} (hc : c ∈ claimRefs params.logBlowup shape) :
    (M.colPoly params.logBlowup θ com (commitments.getD c.batch default)
        (batchDims params.logBlowup (shape.getD c.batch [])) c.matrix c.col c.logHeight).eval
        (M.ext.toModel (points.getD c.pointIdx 0)) =
      M.ext.toModel (values.getD c.valueIdx 0) := by
  obtain ⟨ms, hms, hcms⟩ := exists_matrix_of_mem_claimRefs shape hc
  have hle : ms.logDegree + params.logBlowup ≤ logMaxHeight params.logBlowup shape :=
    le_logMaxHeight hms
  have hfin := hfinal ms hms
  have hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape := hfin.trans hle
  obtain ⟨j, hlog⟩ : ∃ j, c.logHeight + j = logMaxHeight params.logBlowup shape :=
    ⟨logMaxHeight params.logBlowup shape - c.logHeight, by omega⟩
  have hjn : j ≤ logMaxHeight params.logBlowup shape := by omega
  have hn : logMaxHeight params.logBlowup shape - j = c.logHeight := by omega
  have hj : j ≤ numRounds params shape := by
    unfold numRounds
    omega
  have hmem : c ∈ levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j :=
    List.mem_filter.mpr ⟨hc, beq_iff_eq.mpr hlog⟩
  obtain ⟨k, rfl⟩ := List.mem_iff_get.mp hmem
  have hhold : PcsRbr.ClaimsHoldOff
      (((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).ldt.domain
        j).image
          ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).shift * ·))
      ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).ldt.degree j)
      θ
      ((modelParams M.toFieldModel params shape (M.wellFormed params shape hshape)).claims
        (view M.toFieldModel params shape (firstMessage commitments points values)) com j) :=
    not_not.mp fun hn => h ⟨j, hj, hn⟩
  have hword := claims_f_eq_colWord M params shape hshape
    (view M.toFieldModel params shape (firstMessage commitments points values)) com hjn k
  rw [inputRoots_firstMessage M params shape hshape, hn] at hword
  rw [Compiled.Params.ldt_domain, coset_eq M params shape hshape hjn,
    ldt_degree_eq M params shape hshape hheight hj, hn] at hhold
  have hm : StrictMargin (M.coset ((levelClaims params.logBlowup shape
      (logMaxHeight params.logBlowup shape) j).get k).logHeight)
      (2 ^ (((levelClaims params.logBlowup shape
        (logMaxHeight params.logBlowup shape) j).get k).logHeight - params.logBlowup)) θ := by
    rw [hcms, Nat.add_sub_cancel]
    exact hmargin ms hms
  have hz := hoff _ hc
  rw [← point_firstMessage M params shape commitments points values hpoints hj k] at hz
  have hext := eval_decodeT_of_claimsHoldOff hm hhold k hz
  rw [hword] at hext
  rw [← point_firstMessage M params shape commitments points values hpoints hj k,
    ← value_firstMessage M params shape commitments points values hpoints hj k]
  exact hext

end Claims

end CertiFri.Exec.Stark
