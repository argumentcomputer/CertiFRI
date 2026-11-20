import CertiFriProofs.Exec.Stark.Model
import CertiFriProofs.Exec.Field

/-!
# The arithmetic of the STARK verifier, in the model

What the abstraction map of a `StarkModel` makes of the computations of the
STARK verifier (`CertiFri/Stark`): each executable function is carried to the
function of `Theory/Stark` over the model field `K`.

## Contents

* `toModel_fieldOfNat`, `toModel_fieldPowTwo`: a natural number and a repeated
  square, for any refinement.
* `toModel_basisElem`, `map_basisTable`, `toModel_fromExtBasis`,
  `map_lookupPublics`: the basis, its structure constants, an element given by
  coordinates, and the public values of a circuit.
* `map_sweep_exec`, `map_logup_exec`: the values of the nodes of a graph and
  the lookup constraints.
* `circuitOk_iff`: the constraint check of one circuit is `circuitCheck`
  (`Theory/Stark/Check.lean`) on the modelled values.
* `toModel_fingerprint`, `messagesAccumulator_model`: the fingerprint of a
  message, and the lookup sum of messages given with their multiplicities.
* `zetaOk_model`: a usable out-of-domain point is not zero and lies outside the
  trace domain of every active circuit.

## Assumptions

The laws of `StarkModel`. Nothing is assumed about the shape of the arrays: a
read outside an array gives zero on both sides.
-/

namespace CertiFri.Exec.Stark

open CertiFri.Stark CertiFri.Stark.Model Polynomial

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] [Field K]

/-! ## Arrays -/

/-- A read of an array given by a function, inside the array. -/
private theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (x : α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f).getD i x = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dite_eq_left hi]
  rfl

/-- A read of a segment of an array is a read of the array. -/
private theorem getD_extract {α : Type} (a : Array α) (x : α) {i j k : ℕ} (hk : i + k < j) :
    (a.extract i j).getD k x = a.getD (i + k) x := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_extract]
  split
  · rfl
  · next h => rw [Array.getElem?_eq_none (by omega)]

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

/-! ## Numbers and powers -/

omit [TwoAdicOps F] in
/-- A natural number below `2 ^ bits`, computed by doubling over `bits` bits, is
that number in the field. -/
private theorem toModel_fieldOfNatBits (r : Refines F K) (bits : ℕ) :
    ∀ n, n < 2 ^ bits → r.toModel (fieldOfNatBits bits n) = (n : K) := by
  induction bits with
  | zero =>
    intro n h
    obtain rfl : n = 0 := by simpa using h
    rw [fieldOfNatBits, r.map_zero, Nat.cast_zero]
  | succ bits ih =>
    intro n h
    have hhalf : n / 2 < 2 ^ bits := by
      rw [pow_succ] at h
      omega
    have e := ih (n / 2) hhalf
    simp only [fieldOfNatBits]
    split
    · rw [r.map_add, e, ← Nat.cast_add]
      congr 1
      omega
    · rw [r.map_add, r.map_add, r.map_one, e, ← Nat.cast_add, ← Nat.cast_succ]
      congr 1
      omega

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] in
/-- A natural number computed by doubling is that number in the field. -/
theorem toModel_fieldOfNat (r : Refines F K) (n : ℕ) : r.toModel (fieldOfNat n) = (n : K) :=
  toModel_fieldOfNatBits r _ n Nat.lt_log2_self

omit [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF] in
/-- `k` squarings give the power `2 ^ k`. -/
theorem toModel_fieldPowTwo (r : Refines F K) (x : F) (k : ℕ) :
    r.toModel (fieldPowTwo x k) = r.toModel x ^ 2 ^ k := by
  induction k with
  | zero => rw [fieldPowTwo, pow_zero, pow_one]
  | succ k ih =>
    simp only [fieldPowTwo]
    rw [r.map_mul, ih, ← pow_add, ← two_mul, ← pow_succ']

/-- The abstraction map commutes with `sumRange`. -/
private theorem toModel_sumRange (r : Refines EF K) (n : ℕ) (f : ℕ → EF) :
    r.toModel (Stark.sumRange n f) = Model.sumRange n fun i => r.toModel (f i) := by
  have key := List.foldl_hom r.toModel (g₁ := fun acc i => acc + f i)
    (g₂ := fun acc i => acc + r.toModel (f i)) (l := List.range n) (init := 0)
    fun x y => (r.map_add x (f y)).symm
  rw [r.map_zero] at key
  exact key.symm

variable (M : StarkModel F EF K)

/-! ## The basis of the extension -/

/-- The executable basis elements are the basis of the model. -/
theorem toModel_basisElem {i : ℕ} (hi : i < M.extData.d) :
    M.ext.toModel (basisElem F i) = M.extData.basis i := by
  have hd := M.degree_eq
  rw [basisElem, M.ofBasis _ (by rw [Array.size_ofFn, hd]), Finset.sum_eq_single i]
  · rw [getD_ofFn _ _ (hd ▸ hi), ite_eq_left rfl, M.base.map_one, one_mul]
  · intro k hk hki
    rw [getD_ofFn _ _ (hd ▸ Finset.mem_range.mp hk), ite_eq_right hki, M.base.map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hi) h

/-- The executable structure constants are those of the model. -/
theorem map_basisTable : (basisTable F : Array EF).map M.ext.toModel = M.extData.table := by
  have hd := M.degree_eq
  have hpos := M.extData.d_pos
  refine Array.ext ?_ fun t h₁ h₂ => ?_
  · simp only [basisTable, ExtData.table, Array.size_map, Array.size_ofFn, hd]
  · have ht : t < M.extData.d * (M.extData.d * M.extData.d) := by
      simpa only [ExtData.table, Array.size_ofFn, Nat.mul_assoc] using h₂
    have h1 : t / (M.extData.d * M.extData.d) < M.extData.d :=
      (Nat.div_lt_iff_lt_mul (Nat.mul_pos hpos hpos)).mpr ht
    have h2 : t / M.extData.d % M.extData.d < M.extData.d := Nat.mod_lt _ hpos
    have h3 : t % M.extData.d < M.extData.d := Nat.mod_lt _ hpos
    simp only [basisTable, ExtData.table, Array.getElem_map, Array.getElem_ofFn]
    rw [M.embed, ← hd, M.toBasis _ _ h3, M.ext.map_mul, toModel_basisElem M h1,
      toModel_basisElem M h2]

/-- An element given by at most `d` coordinates, themselves extension elements,
is the combination of the basis with the modelled coordinates. -/
theorem toModel_fromExtBasis (coords : Array EF) (h : coords.size ≤ M.extData.d) :
    M.ext.toModel (fromExtBasis F coords) =
      ∑ j ∈ Finset.range coords.size, M.ext.toModel (coords.getD j 0) * M.extData.basis j := by
  rw [show fromExtBasis F coords =
      Stark.sumRange coords.size fun j => coords.getD j 0 * basisElem F j from rfl,
    toModel_sumRange, Model.sumRange_eq]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [M.ext.map_mul, toModel_basisElem M (lt_of_lt_of_le (Finset.mem_range.mp hj) h)]

/-- The embedded coordinates of an element are, in the model, the coordinates
of the modelled element. -/
private theorem map_toBasis (e : EF) :
    ((ExtensionOps.toBasis (F := F) e).toList.map ExtensionOps.embed).map M.ext.toModel =
      (List.range M.extData.d).map (M.extData.coord (M.ext.toModel e)) := by
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_map, Array.length_toList, List.length_range, M.toBasis_size]
  · have hi : i < M.extData.d := by simpa using h₂
    have hi' : i < (ExtensionOps.toBasis (F := F) e).size := by rw [M.toBasis_size]; exact hi
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [M.embed, ← M.toBasis e i hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi',
      Option.getD_some]

/-- The public values of a circuit are the coordinates of the modelled lookup
challenges and lookup sums. -/
theorem map_lookupPublics (β γ acc next : EF) :
    (lookupPublics (F := F) β γ acc next).map M.ext.toModel =
      M.extData.publics (M.ext.toModel β) (M.ext.toModel γ) (M.ext.toModel acc)
        (M.ext.toModel next) := by
  simp only [lookupPublics, ExtData.publics, List.map_toArray, List.flatMap_cons,
    List.flatMap_nil, List.map_append, List.map_nil, map_toBasis]

/-! ## Graphs -/

/-- The value of a column variable, in the model. -/
private theorem toModel_var (r : Refines EF K) (v : RowValues EF) (col : ColRef) :
    r.toModel (v.var col) = varVal (mapRow r.toModel v) col := by
  obtain ⟨source, next, index⟩ := col
  cases source <;> cases next <;> exact (toModel_getD_array_map r _ index).symm

/-- The value of one node, in the model, given the modelled values of the nodes
before it. -/
private theorem toModel_evalNode (v : RowValues EF) (buf : Array EF) (node : Node F) :
    M.ext.toModel (evalNode v buf node) =
      nodeVal M.base.toModel (mapRow M.ext.toModel v) (buf.map M.ext.toModel) node := by
  cases node with
  | const c => exact M.embed c
  | var col => exact toModel_var M.ext v col
  | pub index => exact (toModel_getD_array_map M.ext v.publics index).symm
  | isFirstRow => rfl
  | isLastRow => rfl
  | isTransition => rfl
  | add a b => simp only [evalNode, nodeVal, toModel_getD_array_map, M.ext.map_add]
  | sub a b => simp only [evalNode, nodeVal, toModel_getD_array_map, M.ext.map_sub]
  | mul a b => simp only [evalNode, nodeVal, toModel_getD_array_map, M.ext.map_mul]
  | neg a => simp only [evalNode, nodeVal, toModel_getD_array_map, M.ext.map_neg]

/-- `map_sweep_exec`, for the fold over a list of nodes from any buffer. -/
private theorem map_foldl_evalNode (v : RowValues EF) (l : List (Node F)) (buf : Array EF) :
    (l.foldl (fun buf node => buf.push (evalNode v buf node)) buf).map M.ext.toModel =
      l.foldl
        (fun buf node => buf.push (nodeVal M.base.toModel (mapRow M.ext.toModel v) buf node))
        (buf.map M.ext.toModel) := by
  induction l generalizing buf with
  | nil => rfl
  | cons node l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, Array.map_push, toModel_evalNode]

/-- The values of the nodes of a graph, in the model. -/
theorem map_sweep_exec (g : Graph F) (v : RowValues EF) :
    (g.sweep v).map M.ext.toModel =
      Model.sweep M.base.toModel g.nodes (mapRow M.ext.toModel v) := by
  rw [Graph.sweep, Model.sweep, ← Array.foldl_toList, ← Array.foldl_toList, map_foldl_evalNode,
    Array.mkEmpty_eq, Array.map_empty]

/-! ## The lookup constraints -/

/-- The product of tuples of coordinates, in the model. -/
private theorem map_coordMul_exec (r : Refines EF K) (d : ℕ) (table a b : Array EF) :
    (Stark.coordMul d table a b).map r.toModel =
      Model.coordMul d (table.map r.toModel) (a.map r.toModel) (b.map r.toModel) := by
  unfold Stark.coordMul Model.coordMul
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, toModel_sumRange, r.map_mul, toModel_getD_array_map]

/-- The coordinates of one, in the model. -/
private theorem map_coordOne_exec (r : Refines EF K) (d : ℕ) :
    (Stark.coordOne d : Array EF).map r.toModel = Model.coordOne d := by
  unfold Stark.coordOne Model.coordOne
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply]
  split
  · exact r.map_one
  · exact r.map_zero

/-- The message of a lookup, in the model. -/
private theorem map_lookupMessage_exec (r : Refines EF K) (d : ℕ)
    (table beta gamma buf : Array EF) (lookup : Lookup) :
    (Stark.lookupMessage d table beta gamma buf lookup).map r.toModel =
      Model.lookupMessage d (table.map r.toModel) (beta.map r.toModel) (gamma.map r.toModel)
        (buf.map r.toModel) lookup := by
  unfold Stark.lookupMessage Model.lookupMessage
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, r.map_add, ← toModel_getD_array_map]
  congr 2
  rw [← Array.foldr_toList, ← Array.foldr_toList]
  have hinit : (Array.ofFn (n := d) fun _ => (0 : EF)).map r.toModel =
      Array.ofFn (n := d) fun _ => 0 := by
    rw [Array.map_ofFn]
    congr 1
    funext _
    exact r.map_zero
  rw [← hinit]
  refine (List.foldr_hom (Array.map r.toModel) fun arg acc => ?_).symm
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_apply, ← map_coordMul_exec, toModel_getD_array_map, ← r.map_add]
  split <;> rfl

/-- The constraint of a group, in the model. -/
private theorem map_groupConstraint_exec (r : Refines EF K) (d : ℕ) (table : Array EF)
    (messages : Array (Array EF)) (multiplicities diff : Array EF) :
    (Stark.groupConstraint d table messages multiplicities diff).map r.toModel =
      Model.groupConstraint d (table.map r.toModel) (messages.map (Array.map r.toModel))
        (multiplicities.map r.toModel) (diff.map r.toModel) := by
  have hall : (messages.map (Array.map r.toModel)).foldl
      (Model.coordMul d (table.map r.toModel)) (Model.coordOne d) =
      (messages.foldl (Stark.coordMul d table) (Stark.coordOne d)).map r.toModel := by
    rw [Array.foldl_map, ← Array.foldl_toList, ← Array.foldl_toList, ← map_coordOne_exec r]
    exact List.foldl_hom (Array.map r.toModel) fun x y => (map_coordMul_exec r d table x y).symm
  simp only [Stark.groupConstraint, Model.groupConstraint]
  rw [hall, ← map_coordMul_exec]
  simp only [Array.size_map]
  refine (List.foldl_hom (Array.map r.toModel) fun acc j => ?_).symm
  rw [Array.map_ofFn]
  congr 1
  funext k
  have hothers : (List.range messages.size).foldl
      (fun product i => if i = j then product
        else Model.coordMul d (table.map r.toModel) product
          ((messages.map (Array.map r.toModel)).getD i #[]))
      (Model.coordOne d) =
      ((List.range messages.size).foldl
        (fun product i => if i = j then product
          else Stark.coordMul d table product (messages.getD i #[]))
        (Stark.coordOne d)).map r.toModel := by
    rw [← map_coordOne_exec r]
    refine List.foldl_hom (Array.map r.toModel) fun x i => ?_
    split
    · rfl
    · rw [getD_map_map, map_coordMul_exec]
  simp only [Function.comp_apply, hothers, toModel_getD_array_map, r.map_sub, r.map_mul]

omit [TwoAdicOps F] in
/-- `map_logup_exec`, for any refinement, with the degree as a variable. -/
private theorem map_logup_aux (r : Refines EF K) {d : ℕ}
    (hd : d = ExtensionOps.degree (F := F) (EF := EF)) (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array EF) (isLastRow : EF) (groupSize : ℕ) :
    (logupConstraintValues F lookups buf stage2 stage2Next publics deltaScaled isLastRow
        groupSize).map r.toModel =
      logupValues d ((basisTable F : Array EF).map r.toModel) lookups (buf.map r.toModel)
        (stage2.map r.toModel) (stage2Next.map r.toModel) (publics.map r.toModel)
        (deltaScaled.map r.toModel) (r.toModel isLastRow) groupSize := by
  subst hd
  simp only [logupConstraintValues, logupValues]
  refine map_foldl_append r.toModel _ _ (fun g => ?_) _
  simp only [map_groupConstraint_exec, Array.map_map]
  congr 2
  · funext lookup
    simp only [Function.comp_apply, map_lookupMessage_exec, Array.map_extract]
  · funext lookup
    simp only [Function.comp_apply, toModel_getD_array_map]
  · rw [Array.map_ofFn]
    congr 1
    funext k
    simp only [Function.comp_apply, r.map_sub, toModel_getD_array_map, apply_ite r.toModel]
    congr 2
    rw [← toModel_getD_array_map, Array.map_ofFn]
    congr 2
    funext k
    simp only [Function.comp_apply, r.map_add, r.map_mul]

/-- The lookup constraints, in the model. -/
theorem map_logup_exec (lookups : Array Lookup)
    (buf stage2 stage2Next publics deltaScaled : Array EF) (isLastRow : EF) (groupSize : ℕ) :
    (logupConstraintValues F lookups buf stage2 stage2Next publics deltaScaled isLastRow
        groupSize).map M.ext.toModel =
      logupValues M.extData.d M.extData.table lookups (buf.map M.ext.toModel)
        (stage2.map M.ext.toModel) (stage2Next.map M.ext.toModel) (publics.map M.ext.toModel)
        (deltaScaled.map M.ext.toModel) (M.ext.toModel isLastRow) groupSize := by
  rw [← map_basisTable M]
  exact map_logup_aux M.ext M.degree_eq lookups buf stage2 stage2Next publics deltaScaled
    isLastRow groupSize

/-! ## The constraint check of one circuit -/

/-- The row the executable check evaluates the constraints on is, in the
model, the opened row with the modelled public values. -/
private theorem mapRow_opened (k : ℕ) (publics : Array EF) (ζ : EF)
    (pre main s2 : Array (Array EF)) :
    mapRow M.ext.toModel
        { preprocessed := pre.getD 0 #[]
          preprocessedNext := pre.getD 1 #[]
          main := main.getD 0 #[]
          mainNext := main.getD 1 #[]
          stage2 := s2.getD 0 #[]
          stage2Next := s2.getD 1 #[]
          publics := publics
          isFirstRow := (selectorsAt (F := F) k ζ).isFirstRow
          isLastRow := (selectorsAt (F := F) k ζ).isLastRow
          isTransition := (selectorsAt (F := F) k ζ).isTransition } =
      openedRow (2 ^ k) (M.gen k) (publics.map M.ext.toModel) (M.ext.toModel ζ)
        (pre.map fun row => row.map M.ext.toModel) (main.map fun row => row.map M.ext.toModel)
        (s2.map fun row => row.map M.ext.toModel) := by
  have hlast : M.ext.toModel (ExtensionOps.embed (TwoAdicOps.twoAdicGenerator (F := F) k)⁻¹) =
      (M.gen k)⁻¹ := by
    rw [M.embed, M.base.map_inv, StarkModel.gen]
  simp only [mapRow, openedRow, selectorsAt, M.ext.map_mul, M.ext.map_inv, M.ext.map_sub,
    M.ext.map_one, toModel_fieldPowTwo, hlast, getD_map_map]

/-- The inverse of the vanishing polynomial at the point, in the model. -/
private theorem toModel_invVanishing (k : ℕ) (ζ : EF) :
    M.ext.toModel (selectorsAt (F := F) k ζ).invVanishing = (M.ext.toModel ζ ^ 2 ^ k - 1)⁻¹ := by
  simp only [selectorsAt, M.ext.map_inv, M.ext.map_sub, M.ext.map_one, toModel_fieldPowTwo]

/-- The coordinates of the difference of the lookup sums leaving and entering
a circuit, divided by the value of the last-row selector on the last row, in
the model. -/
private theorem map_deltaScaled (k : ℕ) (publics : Array EF) :
    (Array.ofFn (n := ExtensionOps.degree (F := F) (EF := EF)) fun j =>
        (publics.getD (3 * ExtensionOps.degree (F := F) (EF := EF) + j.val) 0
            - publics.getD (2 * ExtensionOps.degree (F := F) (EF := EF) + j.val) 0)
          * ExtensionOps.embed
            (fieldOfNat (2 ^ k) * TwoAdicOps.twoAdicGenerator (F := F) k)⁻¹).map M.ext.toModel =
      deltaScaled M.extData.d (2 ^ k) (M.gen k) (publics.map M.ext.toModel) := by
  rw [deltaScaled, M.degree_eq, Array.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, M.ext.map_mul, M.ext.map_sub, toModel_getD_array_map, M.embed,
    M.base.map_inv, M.base.map_mul, toModel_fieldOfNat, StarkModel.gen]

/-- The constraint values of a circuit on a row, in the model. -/
private theorem map_constraintValues (c : Circuit F) (v : RowValues EF) (ds : Array EF) :
    (c.graph.constraintValues (c.graph.sweep v) ++
        logupConstraintValues F c.graph.lookups (c.graph.sweep v) v.stage2 v.stage2Next v.publics
          ds v.isLastRow c.lookupGroupSize).map M.ext.toModel =
      constraintVals M.base.toModel M.extData.d M.extData.table c (mapRow M.ext.toModel v)
        (ds.map M.ext.toModel) := by
  rw [constraintVals, Array.map_append, map_logup_exec, map_sweep_exec, Graph.constraintValues,
    Array.map_map]
  congr 2
  funext z
  rw [Function.comp_apply, ← toModel_getD_array_map, map_sweep_exec]

/-- The fold of values with a challenge, in the model. -/
private theorem toModel_foldAlpha (r : Refines EF K) (α : EF) (vals : Array EF) :
    r.toModel (vals.foldl (fun folded v => folded * α + v) 0) =
      foldAlpha (r.toModel α) (vals.map r.toModel) := by
  rw [foldAlpha, ← Array.foldl_toList, ← Array.foldl_toList, Array.toList_map, List.foldl_map,
    ← r.map_zero]
  exact (List.foldl_hom r.toModel fun x y => by rw [r.map_add, r.map_mul]).symm

/-- A left fold over `0, …, n - 1` that keeps a sum and a running power of `z`:
in the model, the sum is `∑ i < n, z ^ i * f i` and the power is `z ^ n`. -/
private theorem toModel_foldl_range_powers (r : Refines EF K) (z : EF) (f : ℕ → EF) (n : ℕ) :
    r.toModel ((List.range n).foldl
        (fun (acc : EF × EF) i => (acc.1 + acc.2 * f i, acc.2 * z)) (0, 1)).1 =
        ∑ i ∈ Finset.range n, r.toModel z ^ i * r.toModel (f i) ∧
      r.toModel ((List.range n).foldl
        (fun (acc : EF × EF) i => (acc.1 + acc.2 * f i, acc.2 * z)) (0, 1)).2 =
        r.toModel z ^ n := by
  induction n with
  | zero =>
    rw [List.range_zero, List.foldl_nil, Finset.sum_range_zero, pow_zero]
    exact ⟨r.map_zero, r.map_one⟩
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨by rw [r.map_add, r.map_mul, ih.1, ih.2, Finset.sum_range_succ],
      by rw [r.map_mul, ih.2, pow_succ]⟩

/-- A chunk of `d` entries of a row, read as coordinates, is the combination
of the basis with the modelled entries: a missing entry reads zero on both
sides. -/
private theorem toModel_fromExtBasis_extract (row : Array EF) (i : ℕ) :
    M.ext.toModel (fromExtBasis F (row.extract (i * M.extData.d) ((i + 1) * M.extData.d))) =
      ∑ j ∈ Finset.range M.extData.d,
        (row.map M.ext.toModel).getD (i * M.extData.d + j) 0 * M.extData.basis j := by
  have hsize : (row.extract (i * M.extData.d) ((i + 1) * M.extData.d)).size ≤ M.extData.d := by
    rw [Array.size_extract, Nat.succ_mul]
    omega
  rw [toModel_fromExtBasis M _ hsize]
  refine (Finset.sum_subset (Finset.range_mono hsize) fun j _ hj => ?_).trans
    (Finset.sum_congr rfl fun j hj => ?_)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using hj),
      Option.getD_none, M.ext.map_zero, zero_mul]
  · have hj' := Finset.mem_range.mp hj
    rw [toModel_getD_array_map, getD_extract _ _ (by rw [Nat.succ_mul]; omega)]

/-- The quotient reassembled from its opened chunks, in the model. -/
private theorem toModel_quotientValue (chunks : ℕ) (z : EF) (row : Array EF) :
    M.ext.toModel (quotientValue (F := F) chunks z row) =
      ∑ i ∈ Finset.range chunks, M.ext.toModel z ^ i *
        ∑ j ∈ Finset.range M.extData.d,
          (row.map M.ext.toModel).getD (i * M.extData.d + j) 0 * M.extData.basis j := by
  simp only [quotientValue]
  rw [(toModel_foldl_range_powers M.ext z _ chunks).1, ← M.degree_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [toModel_fromExtBasis_extract]

/-- **The constraint check of one circuit, in the model.** The executable check
accepts exactly when `circuitCheck` holds of the modelled challenges and opened
values, for the trace domain of order `2 ^ k` and its generator. -/
theorem circuitOk_iff (c : Circuit F) (k : ℕ) (β γ acc next α ζ : EF)
    (pre main s2 : Array (Array EF)) (quot : Array EF) :
    circuitOk c k β γ acc next α ζ pre main s2 quot = true ↔
      circuitCheck M.base.toModel M.extData c (2 ^ k) (M.gen k) (M.ext.toModel β)
        (M.ext.toModel γ) (M.ext.toModel acc) (M.ext.toModel next) (M.ext.toModel α)
        (M.ext.toModel ζ) (pre.map fun row => row.map M.ext.toModel)
        (main.map fun row => row.map M.ext.toModel) (s2.map fun row => row.map M.ext.toModel)
        (quot.map M.ext.toModel) := by
  refine (M.ext.beq_iff _ _).trans ?_
  rw [M.ext.map_mul, toModel_invVanishing, toModel_quotientValue, toModel_foldAlpha,
    map_constraintValues, mapRow_opened, map_deltaScaled, map_lookupPublics, toModel_fieldPowTwo,
    circuitCheck]

/-- The fingerprint of a message is the value of its fingerprint polynomial at
the modelled challenge. -/
theorem toModel_fingerprint (γ : EF) (args : Array F) :
    M.ext.toModel (fingerprint γ args) =
      (fpPoly (args.toList.map M.base.toModel)).eval (M.ext.toModel γ) := by
  rw [eval_fpPoly, fingerprint, ← Array.foldr_toList]
  induction args.toList with
  | nil => exact M.ext.map_zero
  | cons a l ih =>
    rw [List.foldr_cons, List.map_cons, List.foldr_cons, M.ext.map_add, M.ext.map_mul, ih,
      M.embed]

/-- `messagesAccumulator_model`, for the fold from any accumulator: if the fold
ends with a true flag, the flag was true, every denominator is nonzero in the
model, and the lookup sum of the messages was added to the value. -/
private theorem foldl_messages_model (β γ : EF) (messages : List (Array F × F))
    (acc : Bool × EF)
    (h : (messages.foldl
      (fun (acc : Bool × EF) m =>
        (acc.1 && !(β + fingerprint γ m.1 == 0),
          acc.2 + (β + fingerprint γ m.1)⁻¹ * ExtensionOps.embed m.2)) acc).1 = true) :
    acc.1 = true ∧
      (∀ msg ∈ messages, M.ext.toModel β
        + (fpPoly (msg.1.toList.map M.base.toModel)).eval (M.ext.toModel γ) ≠ 0) ∧
      M.ext.toModel (messages.foldl
        (fun (acc : Bool × EF) m =>
          (acc.1 && !(β + fingerprint γ m.1 == 0),
            acc.2 + (β + fingerprint γ m.1)⁻¹ * ExtensionOps.embed m.2)) acc).2 =
        M.ext.toModel acc.2 + lookupSum (M.ext.toModel β) (M.ext.toModel γ)
          (messages.map fun msg =>
            (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) := by
  induction messages generalizing acc with
  | nil =>
    refine ⟨h, fun _ hm => absurd hm List.not_mem_nil, ?_⟩
    rw [List.foldl_nil, List.map_nil, lookupSum, List.map_nil, List.sum_nil, add_zero]
  | cons m l ih =>
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2, h3⟩ := ih _ h
    rw [Bool.and_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨hacc, hden⟩ := h1
    have hden' : M.ext.toModel β
        + (fpPoly (m.1.toList.map M.base.toModel)).eval (M.ext.toModel γ) ≠ 0 := by
      intro h0
      have hb : (β + fingerprint γ m.1 == 0) = true :=
        (M.ext.beq_iff _ _).mpr
          (by rw [M.ext.map_add, toModel_fingerprint, M.ext.map_zero, h0])
      rw [hb] at hden
      cases hden
    refine ⟨hacc, fun msg hmsg => ?_, ?_⟩
    · rcases List.mem_cons.mp hmsg with rfl | hmsg
      · exact hden'
      · exact h2 msg hmsg
    · rw [h3, M.ext.map_add, M.ext.map_mul, M.ext.map_inv, M.ext.map_add, toModel_fingerprint,
        M.embed, List.map_cons, lookupSum, lookupSum, List.map_cons, List.sum_cons,
        div_eq_mul_inv]
      ring

/-- **The lookup sum of public messages, in the model.** If the executable
accumulator reports that every denominator is nonzero, every denominator is
nonzero in the model and the accumulated value is the lookup sum of the
modelled messages. -/
theorem messagesAccumulator_model (β γ : EF) (messages : List (Array F × F))
    (h : (messagesAccumulator β γ messages).1 = true) :
    (∀ msg ∈ messages, M.ext.toModel β
        + (fpPoly (msg.1.toList.map M.base.toModel)).eval (M.ext.toModel γ) ≠ 0) ∧
      M.ext.toModel (messagesAccumulator β γ messages).2 =
        lookupSum (M.ext.toModel β) (M.ext.toModel γ)
          (messages.map fun msg => (M.base.toModel msg.2, msg.1.toList.map M.base.toModel)) := by
  obtain ⟨-, h2, h3⟩ := foldl_messages_model M β γ messages (true, 0) h
  refine ⟨h2, h3.trans ?_⟩
  rw [M.ext.map_zero, zero_add]

/-- A usable out-of-domain point is not zero and lies outside the trace domain
of every active circuit. -/
theorem zetaOk_model {D InputProof CommitProof : Type}
    (proof : Proof F EF D InputProof CommitProof) (ζ : EF) (h : zetaOk proof ζ = true) :
    M.ext.toModel ζ ≠ 0 ∧ ∀ pos < (activeIndices proof.active).length,
      M.ext.toModel ζ ^ 2 ^ proof.logDegrees.getD pos 0 ≠ 1 := by
  rw [zetaOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  refine ⟨fun hz => ?_, fun pos hpos hz => ?_⟩
  · have hb : (ζ == 0) = true := (M.ext.beq_iff _ _).mpr (by rw [hz, M.ext.map_zero])
    rw [hb] at h0
    cases h0
  · have h1 := hall pos (List.mem_range.mpr hpos)
    rw [Bool.not_eq_true'] at h1
    have hb : (fieldPowTwo ζ (proof.logDegrees.getD pos 0) == 1) = true :=
      (M.ext.beq_iff _ _).mpr (by rw [toModel_fieldPowTwo, hz, M.ext.map_one])
    rw [hb] at h1
    cases h1

end CertiFri.Exec.Stark
