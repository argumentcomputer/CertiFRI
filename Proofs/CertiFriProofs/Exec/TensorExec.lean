import CertiFri.TensorBatching
import CertiFriProofs.Exec.Arith
import CertiFriProofs.Exec.Checks
import CertiFriProofs.Exec.Transcript
import CertiFriProofs.Exec.SoundnessUnconditional
import CertiFriProofs.Theory.Compiled.Tensor

/-!
# Executable `Fri.verifyTensor` refinement and chained-ROM soundness

Bridges the executable tensor-batched FRI verifier (`CertiFri.Fri.verifyTensor`
in `CertiFri/Verifier.lean`, matching `multi-stark` `v6`'s `FriBatching::Tensor`)
to the compiled tensor protocol (`Theory/Compiled/Tensor.lean`) and proves
chained-ROM soundness (`Exec.soundnessTensor`, `Exec.soundnessTensor_uniqueDecoding`).

## Contents

1. **Weight and opening refinement (`WeightRefinement`, `OpeningRefinement`):**
   * `length_tensorWeightsList`, `toModel_tensorWeightsList_getD`,
     `toModel_tensorWeights_getD`, `toModel_tensorWeightExplicit`
   * `toModel_tensorColAcc`, `toModel_tensorOpeningTerm`,
     `toModel_reducedOpeningTensor`, `toModel_reducedOpeningTensor_tensorWeights`
2. **Shape coordinate bijection (`TensorShape`):**
   * `expandOpening`, `flatMap_expandOpening_openingRefs`,
     `flatMap_expandOpening_levelOpenings`
   * `openingCoords`, `tensorCoord`, `tensorCoord_injective`
   * `width_le_maxWidth_of_mem_openingRefs`,
     `length_levelOpenings_le_maxOpeningsPerHeight`
3. **Query arithmetic and commitment checks (`TensorChecks`):**
   * `AgreesTensor`, `toModel_reducedOpeningsTensor`, `finalCheckTensor_of_queryResultTensor`,
     `rows_queryResultTensor`, `modelChecksTensor_of_verifyWithTensor_aux`
4. **Idealised tensor challenger and transcript (`TensorTranscript`):**
   * `freeChallengerTensor` (handling both `kCol + kOpen > 0` and `kCol + kOpen = 0`)
   * `transcriptTensor_free`
5. **Chained-ROM executable soundness (`TensorSoundness`):**
   * `acceptsTensor`, `run_model_of_acceptsTensor`, `experimentTensor`
   * `Exec.soundnessTensor` (generic `Tensor2DMCA` + `StepMCA`)
   * `Exec.soundnessTensor_uniqueDecoding` (unconditional up to unique decoding,
     error linear in `kCol + kOpen`)
-/

namespace CertiFri.Exec

open Fri

/-! ## 1. Tensor weight and reduced-opening refinement -/

section WeightRefinement

variable {EF K : Type} [FieldOps EF] [Field K] (r : Refines EF K)

/-- Unrolled (untruncated) tensor weight list of length `2 ^ chals.length`. -/
private def tensorWeightsFull : List EF → List EF
  | [] => [1]
  | chals => chals.foldl (fun acc x => acc ++ acc.map (fun w => x * w)) [1]

private theorem tensorWeightsFull_nil : tensorWeightsFull (EF := EF) [] = [1] := rfl

private theorem tensorWeightsFull_snoc (chals : List EF) (x : EF) :
    tensorWeightsFull (chals ++ [x]) =
      tensorWeightsFull chals ++ (tensorWeightsFull chals).map (fun w => x * w) := by
  cases chals with
  | nil => simp [tensorWeightsFull]
  | cons c cs =>
    simp [tensorWeightsFull, List.foldl_append]

private theorem length_tensorWeightsFull :
    ∀ chals : List EF, (tensorWeightsFull chals).length = 2 ^ chals.length := by
  intro chals
  induction chals using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs x ih =>
    rw [tensorWeightsFull_snoc, List.length_append, List.length_map, ih, List.length_append,
      List.length_singleton, pow_succ, mul_two]

private theorem tensorStep_take_comm (len : ℕ) (acc : List EF) (x : EF) :
    tensorStep len (acc.take len) x = (acc ++ acc.map (fun w => x * w)).take len := by
  unfold tensorStep
  rw [List.take_append, List.take_append, List.take_take, Nat.min_self, List.length_take]
  by_cases h : len ≤ acc.length
  · rw [Nat.min_eq_left h, Nat.sub_self, List.take_zero, List.append_nil,
      Nat.sub_eq_zero_of_le h, List.take_zero, List.append_nil]
  · have hlt : acc.length < len := Nat.lt_of_not_ge h
    rw [Nat.min_eq_right (Nat.le_of_lt hlt), List.take_of_length_le (Nat.le_of_lt hlt)]

private theorem tensorWeightsList_eq_take (chals : List EF) (len : ℕ) :
    tensorWeightsList chals len = (tensorWeightsFull chals).take len := by
  by_cases h0 : len = 0
  · subst h0; simp [tensorWeightsList]
  · unfold tensorWeightsList
    rw [ite_eq_right h0]
    induction chals using List.reverseRecOn with
    | nil =>
      simp only [List.foldl_nil, tensorWeightsFull_nil]
      have h1 : 1 ≤ len := Nat.pos_of_ne_zero h0
      rw [List.take_of_length_le (by simpa using h1)]
    | append_singleton cs x ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, tensorStep_take_comm,
        tensorWeightsFull_snoc]

/-- Exact length of `Fri.tensorWeightsList chals len`: `min len (2 ^ chals.length)`. -/
theorem length_tensorWeightsList (chals : List EF) (len : ℕ) :
    (tensorWeightsList chals len).length = min len (2 ^ chals.length) := by
  rw [tensorWeightsList_eq_take, List.length_take, length_tensorWeightsFull]

private theorem toModel_tensorWeightsFull_getElem :
    ∀ (chals : List EF) (j : ℕ) (hj : j < 2 ^ chals.length),
      r.toModel ((tensorWeightsFull chals)[j]'(by rw [length_tensorWeightsFull]; exact hj)) =
        tensorWeight (fun b : Fin chals.length => r.toModel chals[b.val]) ⟨j, hj⟩ := by
  intro chals
  induction chals using List.reverseRecOn with
  | nil =>
    intro j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simp [tensorWeightsFull, r.map_one, tensorWeight]
  | append_singleton cs x ih =>
    intro j hj
    have hlen : (cs ++ [x]).length = cs.length + 1 := by simp
    have hj' : j < 2 ^ (cs.length + 1) := by rwa [hlen] at hj
    have hlen_full : (tensorWeightsFull cs).length = 2 ^ cs.length := length_tensorWeightsFull cs
    let rVec : Fin (cs.length + 1) → K := fun b =>
      r.toModel ((cs ++ [x])[b.val]'(by rw [hlen]; exact b.isLt))
    have hcast : tensorWeight (fun b : Fin (cs ++ [x]).length => r.toModel (cs ++ [x])[b.val]) ⟨j, hj⟩ =
        tensorWeight rVec ⟨j, hj'⟩ := by
      unfold tensorWeight
      refine Finset.prod_bij (fun b _ => ⟨b.val, by rw [← hlen]; exact b.isLt⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun b _ => ⟨⟨b.val, by rw [hlen]; exact b.isLt⟩, Finset.mem_univ _, rfl⟩)
        (fun b _ => rfl)
    rw [hcast]
    have hlo_vec : rVec ∘ Fin.castSucc = fun b : Fin cs.length => r.toModel cs[b.val] := by
      funext b
      simp only [Function.comp_apply, rVec, Fin.val_castSucc]
      rw [List.getElem_append_left b.isLt]
    have hlast_vec : rVec (Fin.last cs.length) = r.toModel x := by
      simp only [rVec, Fin.val_last]
      rw [List.getElem_append_right le_rfl]
      simp
    by_cases hlt : j < 2 ^ cs.length
    · have hget : (tensorWeightsFull (cs ++ [x]))[j]'(by rw [length_tensorWeightsFull]; exact hj) =
          (tensorWeightsFull cs)[j]'(by rw [hlen_full]; exact hlt) := by
        simp only [tensorWeightsFull_snoc]
        exact List.getElem_append_left (by rw [hlen_full]; exact hlt)
      rw [hget, ih j hlt]
      have hw := tensorWeight_succ_lo rVec ⟨j, hlt⟩
      rw [hlo_vec] at hw
      exact hw.symm
    · have hge : 2 ^ cs.length ≤ j := Nat.le_of_not_lt hlt
      have hsub_lt : j - 2 ^ cs.length < 2 ^ cs.length := by
        rw [pow_succ, mul_two] at hj'; omega
      have hget : (tensorWeightsFull (cs ++ [x]))[j]'(by rw [length_tensorWeightsFull]; exact hj) =
          x * (tensorWeightsFull cs)[j - 2 ^ cs.length]'(by rw [hlen_full]; exact hsub_lt) := by
        simp only [tensorWeightsFull_snoc]
        rw [List.getElem_append_right (by rw [hlen_full]; exact hge), List.getElem_map]
        congr 2
        omega
      rw [hget, r.map_mul, ih (j - 2 ^ cs.length) hsub_lt]
      have hw := tensorWeight_succ_hi rVec ⟨j - 2 ^ cs.length, hsub_lt⟩
      rw [hlo_vec, hlast_vec] at hw
      have hidx : (⟨j - 2 ^ cs.length + 2 ^ cs.length,
          by rw [pow_succ, mul_two]; exact Nat.add_lt_add_right hsub_lt _⟩ :
          Fin (2 ^ (cs.length + 1))) = ⟨j, hj'⟩ := by
        ext; dsimp only; omega
      rw [hidx] at hw
      exact hw.symm

/-- **Exact refinement of executable `Fri.tensorWeightsList` to mathematical `tensorWeight`.** -/
theorem toModel_tensorWeightsList_getD (chals : List EF) (len j : ℕ)
    (hj_len : j < len) (hj_pow : j < 2 ^ chals.length) :
    r.toModel ((tensorWeightsList chals len).getD j 0) =
      tensorWeight (fun b : Fin chals.length => r.toModel chals[b.val]) ⟨j, hj_pow⟩ := by
  have hlt : j < (tensorWeightsList chals len).length := by
    rw [length_tensorWeightsList]
    exact lt_min hj_len hj_pow
  rw [List.getD_eq_getElem _ _ hlt]
  have hget : (tensorWeightsList chals len)[j]'hlt =
      (tensorWeightsFull chals)[j]'(by rw [length_tensorWeightsFull]; exact hj_pow) := by
    simp only [tensorWeightsList_eq_take]
    exact List.getElem_take
  rw [hget]
  exact toModel_tensorWeightsFull_getElem r chals j hj_pow

/-- **Exact refinement of executable `Fri.tensorWeights` (Array) to mathematical `tensorWeight`.** -/
theorem toModel_tensorWeights_getD (chals : Array EF) (len j : ℕ)
    (hj_len : j < len) (hj_pow : j < 2 ^ chals.size) :
    r.toModel ((tensorWeights chals len).getD j 0) =
      tensorWeight (fun b : Fin chals.size => r.toModel chals[b.val]) ⟨j, hj_pow⟩ := by
  have hget : (tensorWeights chals len).getD j 0 = (tensorWeightsList chals.toList len).getD j 0 := by
    unfold tensorWeights
    by_cases hlt : j < (tensorWeightsList chals.toList len).length <;>
      simp [Array.getD, List.getD_eq_getElem?_getD, hlt]
  rw [hget]
  exact toModel_tensorWeightsList_getD r chals.toList len j hj_len (by simpa using hj_pow)

/-- **Exact refinement of executable `Fri.tensorWeightExplicit` to mathematical `tensorWeight`.** -/
theorem toModel_tensorWeightExplicit (chals : List EF) (j : ℕ) (hj : j < 2 ^ chals.length) :
    r.toModel (tensorWeightExplicit chals j) =
      tensorWeight (fun b : Fin chals.length => r.toModel chals[b.val]) ⟨j, hj⟩ := by
  have hgo : ∀ (cs : List EF) (idx : ℕ) (hidx : idx < 2 ^ cs.length) (acc : EF),
      r.toModel (tensorWeightExplicit.go cs idx acc) =
        r.toModel acc * tensorWeight (fun b : Fin cs.length => r.toModel cs[b.val]) ⟨idx, hidx⟩ := by
    intro cs
    induction cs with
    | nil =>
      intro idx hidx acc
      simp [tensorWeightExplicit.go, tensorWeight]
    | cons c cs ih =>
      intro idx hidx acc
      have hdiv : idx / 2 < 2 ^ cs.length := by
        simp only [List.length_cons, pow_succ'] at hidx
        omega
      simp only [tensorWeightExplicit.go]
      rw [ih (idx / 2) hdiv]
      have hprod : tensorWeight (fun b : Fin (c :: cs).length => r.toModel (c :: cs)[b.val]) ⟨idx, hidx⟩ =
          (if idx % 2 = 1 then r.toModel c else 1) *
            tensorWeight (fun b : Fin cs.length => r.toModel cs[b.val]) ⟨idx / 2, hdiv⟩ := by
        change (∏ b : Fin (cs.length + 1),
            if idx.testBit b.val then r.toModel (c :: cs)[b.val] else 1) = _
        rw [Fin.prod_univ_succ]
        congr 1
        · have hbit0 : idx.testBit 0 = decide (idx % 2 = 1) := by
            simp only [Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
            cases hmod : idx % 2 with
            | zero => rfl
            | succ m =>
              have hm : m = 0 := by omega
              subst hm; rfl
          simp only [Fin.val_zero, hbit0, decide_eq_true_eq, List.getElem_cons_zero]
        · refine Finset.prod_congr rfl fun b _ => ?_
          have hbit : idx.testBit (b.val + 1) = (idx / 2).testBit b.val := by
            rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
              pow_succ', ← Nat.div_div_eq_div_mul]
          simp [Fin.val_succ, hbit]
      rw [hprod]
      split_ifs with hodd
      · rw [r.map_mul, mul_assoc]
      · rw [one_mul]
  unfold tensorWeightExplicit
  rw [hgo chals j hj 1, r.map_one, one_mul]

end WeightRefinement

section OpeningRefinement

variable {F EF K : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF] [Field K]
  (m : FieldModel F EF K)

/-- `tensorColAcc` refines to the exact column-weighted sum in `K`. -/
theorem toModel_tensorColAcc (colWeights : Array EF) (claimed : Array EF) (opened : Array F)
    (W : ℕ) (hW_c : claimed.size = W) (hW_o : opened.size = W) :
    m.ext.toModel (tensorColAcc colWeights claimed opened) =
      ∑ c : Fin W, m.ext.toModel (colWeights.getD c.val 0) *
        (m.ext.toModel (claimed.getD c.val 0) - m.base.toModel (opened.getD c.val 0)) := by
  unfold tensorColAcc
  have hmin : min claimed.size opened.size = W := by rw [hW_c, hW_o, Nat.min_self]
  rw [hmin]
  have hfold : ∀ (n : ℕ) (init : EF),
      m.ext.toModel ((List.range n).foldl (fun acc c =>
          acc + colWeights.getD c 0 * (claimed.getD c 0 - ExtensionOps.embed (opened.getD c 0))) init) =
        m.ext.toModel init +
          ∑ c : Fin n, m.ext.toModel (colWeights.getD c.val 0) *
            (m.ext.toModel (claimed.getD c.val 0) - m.base.toModel (opened.getD c.val 0)) := by
    intro n
    induction n with
    | zero => intro init; simp
    | succ n ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        m.ext.map_add, ih, m.ext.map_mul, m.ext.map_sub, m.embed, Fin.sum_univ_castSucc,
        add_assoc]
      rfl
  rw [hfold W 0, m.ext.map_zero, zero_add]

/-- `tensorOpeningTerm` refines to the exact opening-weighted quotient sum in `K`. -/
theorem toModel_tensorOpeningTerm (colWeights : Array EF) (openWeight z x : EF)
    (claimed : Array EF) (opened : Array F) (W : ℕ) (hW_c : claimed.size = W)
    (hW_o : opened.size = W) :
    m.ext.toModel (tensorOpeningTerm colWeights openWeight z x claimed opened) =
      m.ext.toModel openWeight *
        (∑ c : Fin W, m.ext.toModel (colWeights.getD c.val 0) *
          ((m.ext.toModel (claimed.getD c.val 0) - m.base.toModel (opened.getD c.val 0)) *
            (m.ext.toModel z - m.ext.toModel x)⁻¹)) := by
  unfold tensorOpeningTerm
  rw [m.ext.map_mul, m.ext.map_mul, m.ext.map_inv, m.ext.map_sub,
    toModel_tensorColAcc m colWeights claimed opened W hW_c hW_o,
    mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => by ring

/-- `reducedOpeningTensor` refines to the exact opening- and column-weighted quotient sum in `K`. -/
theorem toModel_reducedOpeningTensor (sched : TensorSchedule EF) (x : EF)
    (openings : List (ℕ × EF × Array EF × Array F))
    (hsize : ∀ item ∈ openings, item.2.2.1.size = item.2.2.2.size) :
    m.ext.toModel (reducedOpeningTensor sched x openings) =
      (openings.map fun (oIdx, z, claimed, opened) =>
        m.ext.toModel (sched.openWeights.getD oIdx 0) *
          ∑ c : Fin claimed.size, m.ext.toModel (sched.colWeights.getD c.val 0) *
            ((m.ext.toModel (claimed.getD c.val 0) - m.base.toModel (opened.getD c.val 0)) *
              (m.ext.toModel z - m.ext.toModel x)⁻¹)).sum := by
  unfold reducedOpeningTensor
  have hfold : ∀ (l : List (ℕ × EF × Array EF × Array F)) (init : EF),
      (∀ item ∈ l, item.2.2.1.size = item.2.2.2.size) →
      m.ext.toModel (l.foldl (fun acc (oIdx, z, claimed, opened) =>
          acc + tensorOpeningTerm sched.colWeights (sched.openWeights.getD oIdx 0) z x claimed opened)
        init) =
        m.ext.toModel init +
          (l.map fun (oIdx, z, claimed, opened) =>
            m.ext.toModel (sched.openWeights.getD oIdx 0) *
              ∑ c : Fin claimed.size, m.ext.toModel (sched.colWeights.getD c.val 0) *
                ((m.ext.toModel (claimed.getD c.val 0) - m.base.toModel (opened.getD c.val 0)) *
                  (m.ext.toModel z - m.ext.toModel x)⁻¹)).sum := by
    intro l
    induction l with
    | nil => intro init _; simp
    | cons hd tl ih =>
      intro init hsz
      rcases hd with ⟨oIdx, z, claimed, opened⟩
      have hhd : claimed.size = opened.size := hsz _ (List.mem_cons_self ..)
      have htl : ∀ item ∈ tl, item.2.2.1.size = item.2.2.2.size :=
        fun item hm => hsz item (List.mem_cons_of_mem _ hm)
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih _ htl, m.ext.map_add,
        toModel_tensorOpeningTerm m sched.colWeights (sched.openWeights.getD oIdx 0) z x
          claimed opened claimed.size rfl hhd.symm,
        add_assoc]
  rw [hfold openings 0 hsize, m.ext.map_zero, zero_add]

/-- When `sched` holds `tensorWeights` expanded from `colChals` and `openChals` with
enough capacity for the openings `ops`, `reducedOpeningTensor` refines to the exact
2D `tensorWeight` quotient sum in `K` (matching `Tensor2DMCA`). -/
theorem toModel_reducedOpeningTensor_tensorWeights
    (colChals openChals : Array EF) (maxW maxM : ℕ)
    (hmaxW : maxW ≤ 2 ^ colChals.size) (hmaxM : maxM ≤ 2 ^ openChals.size)
    (x : EF) (ops : List (EF × Array EF × Array F))
    (hM : ops.length ≤ maxM)
    (hW : ∀ item ∈ ops, item.2.1.size ≤ maxW ∧ item.2.1.size = item.2.2.size) :
    let sched : TensorSchedule EF :=
      { colChallenges := colChals
        openChallenges := openChals
        colWeights := tensorWeights colChals maxW
        openWeights := tensorWeights openChals maxM }
    let rCol : Fin colChals.size → K := fun b => m.ext.toModel colChals[b.val]
    let rOpen : Fin openChals.size → K := fun b => m.ext.toModel openChals[b.val]
    m.ext.toModel (reducedOpeningTensor sched x
        (ops.zipIdx.map fun ((z, claimed, opened), oIdx) => (oIdx, z, claimed, opened))) =
      ∑ o : Fin ops.length,
        tensorWeight rOpen ⟨o.val, lt_of_lt_of_le o.isLt (le_trans hM hmaxM)⟩ *
          ∑ c : Fin (ops[o.val].2.1.size),
            tensorWeight rCol ⟨c.val, lt_of_lt_of_le c.isLt
              (le_trans (hW _ (List.getElem_mem o.isLt)).1 hmaxW)⟩ *
              ((m.ext.toModel (ops[o.val].2.1.getD c.val 0) -
                  m.base.toModel (ops[o.val].2.2.getD c.val 0)) *
                (m.ext.toModel ops[o.val].1 - m.ext.toModel x)⁻¹) := by
  intro sched rCol rOpen
  have hsize : ∀ item ∈ (ops.zipIdx.map fun ((z, claimed, opened), oIdx) =>
      (oIdx, z, claimed, opened)), item.2.2.1.size = item.2.2.2.size := by
    intro item hm
    rcases List.mem_map.mp hm with ⟨⟨⟨z, claimed, opened⟩, oIdx⟩, hmem, rfl⟩
    have hget := List.mem_zipIdx_iff_getElem?.mp hmem
    exact (hW (z, claimed, opened) (List.mem_of_getElem? hget)).2
  rw [toModel_reducedOpeningTensor m sched x _ hsize, List.map_map]
  have hsum_map : ∀ {α : Type} (l : List α) (g : α → K),
      (l.map g).sum = ∑ i : Fin l.length, g l[i.val] := by
    intro α l g
    induction l with
    | nil => simp
    | cons a as ih =>
      rw [List.map_cons, List.sum_cons, ih]
      exact (Fin.sum_univ_succ (f := fun i : Fin (as.length + 1) => g (a :: as)[i.val])).symm
  rw [hsum_map]
  refine Finset.sum_bij (fun (i : Fin ops.zipIdx.length) _ =>
      (⟨i.val, by simpa using i.isLt⟩ : Fin ops.length))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun o _ => ⟨⟨o.val, by simp⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun i _ => ?_)
  have hi : i.val < ops.length := by simpa using i.isLt
  simp only [Function.comp_apply, List.getElem_zipIdx, zero_add]
  have ho_m : i.val < maxM := lt_of_lt_of_le hi hM
  have ho_pow : i.val < 2 ^ openChals.size := lt_of_lt_of_le ho_m hmaxM
  rw [toModel_tensorWeights_getD m.ext openChals maxM i.val ho_m ho_pow]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc_w : c.val < maxW := lt_of_lt_of_le c.isLt (hW _ (List.getElem_mem hi)).1
  have hc_pow : c.val < 2 ^ colChals.size := lt_of_lt_of_le hc_w hmaxW
  rw [toModel_tensorWeights_getD m.ext colChals maxW c.val hc_w hc_pow]

end OpeningRefinement

/-! ## 2. Shape bijection between `levelOpenings` and `levelClaims` -/

section TensorShape

/-- Expand one `OpeningRef` into its `o.width` individual `ClaimRef`s in column order. -/
def expandOpening (o : OpeningRef) : List ClaimRef :=
  (List.range o.width).map fun col =>
    ⟨o.batch, o.matrix, col, o.logHeight, o.pointIdx, o.valueStart + col⟩

private theorem zipIdx_range_map {α : Type} (f : ℕ → α) (w s : ℕ) :
    ((List.range w).map f).zipIdx s = (List.range w).map fun col => (f col, s + col) := by
  refine List.ext_getElem (by simp) fun i hi _ => ?_
  simp

private theorem openingRefs_go_flatMap (ps : List PointRef) :
    ∀ (pi vs : ℕ),
      (openingRefs.go ps pi vs).flatMap expandOpening =
        (((ps.zipIdx pi).flatMap fun (p, pIdx) =>
            (List.range p.width).map fun col => (p, pIdx, col)).zipIdx vs).map
          fun ((p, pIdx, col), vi) => ⟨p.batch, p.matrix, col, p.logHeight, pIdx, vi⟩ := by
  induction ps with
  | nil => intro pi vs; rfl
  | cons p ps ih =>
    intro pi vs
    simp only [openingRefs.go, List.flatMap_cons, List.zipIdx_cons, List.zipIdx_append,
      List.map_append, List.length_map, List.length_range]
    rw [ih (pi + 1) (vs + p.width)]
    congr 1
    rw [zipIdx_range_map, List.map_map]
    rfl

/-- Expanding every `OpeningRef` of a shape yields `claimRefs` identically. -/
theorem flatMap_expandOpening_openingRefs (lb : ℕ) (shape : ClaimShape) :
    (openingRefs lb shape).flatMap expandOpening = claimRefs lb shape :=
  openingRefs_go_flatMap (pointRefs lb shape) 0 0

/-- Expanding every `OpeningRef` at level `j` yields `levelClaims` at level `j` identically. -/
theorem flatMap_expandOpening_levelOpenings (lb : ℕ) (shape : ClaimShape) (n j : ℕ) :
    (levelOpenings lb shape n j).flatMap expandOpening = levelClaims lb shape n j := by
  unfold levelOpenings levelClaims
  rw [← flatMap_expandOpening_openingRefs lb shape, List.filter_flatMap]
  induction (openingRefs lb shape) with
  | nil => rfl
  | cons o os ih =>
    simp only [List.filter_cons, List.flatMap_cons]
    by_cases h : (o.logHeight + j == n) = true
    · simp only [h, ↓reduceIte, List.flatMap_cons, ih]
      congr 1
      have hfil : (expandOpening o).filter (fun c => c.logHeight + j == n) = expandOpening o := by
        rw [List.filter_eq_self]
        intro c hc
        simp only [expandOpening, List.mem_map] at hc
        obtain ⟨col, -, rfl⟩ := hc
        exact h
      exact hfil.symm
    · have hf : (o.logHeight + j == n) = false := Bool.eq_false_iff.mpr h
      simp only [hf, Bool.false_eq_true, ↓reduceIte, ih]
      have hfil : (expandOpening o).filter (fun c => c.logHeight + j == n) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp only [expandOpening, List.mem_map] at hc
        obtain ⟨col, -, rfl⟩ := hc
        exact h
      rw [hfil, List.nil_append]

private theorem le_foldr_max_nat {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

private theorem map_openingRefs_go (ps : List PointRef) :
    ∀ (pi vs : ℕ),
      (openingRefs.go ps pi vs).map (fun o => (o.batch, o.matrix, o.logHeight, o.width)) =
        ps.map (fun p => (p.batch, p.matrix, p.logHeight, p.width)) := by
  induction ps with
  | nil => intro _ _; rfl
  | cons p ps ih =>
    intro pi vs
    simp only [openingRefs.go, List.map_cons, ih]

/-- Every `OpeningRef` comes from some `PointRef` of the shape with the same fields. -/
theorem mem_pointRefs_of_mem_openingRefs {lb : ℕ} {shape : ClaimShape} {o : OpeningRef}
    (h : o ∈ openingRefs lb shape) :
    ⟨o.batch, o.matrix, o.logHeight, o.width⟩ ∈ pointRefs lb shape := by
  have h1 : (o.batch, o.matrix, o.logHeight, o.width) ∈
      (openingRefs lb shape).map (fun o => (o.batch, o.matrix, o.logHeight, o.width)) :=
    List.mem_map_of_mem h
  rw [openingRefs, map_openingRefs_go] at h1
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp h1
  rcases p with ⟨b, mat, lh, w⟩
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
  exact hp

/-- Every opening group's width is bounded by `maxWidth shape`. -/
theorem width_le_maxWidth_of_mem_openingRefs {lb : ℕ} {shape : ClaimShape} {o : OpeningRef}
    (h : o ∈ openingRefs lb shape) : o.width ≤ maxWidth shape := by
  obtain ⟨mats, ms, hmats, hms, -, hw⟩ := mem_pointRefs (mem_pointRefs_of_mem_openingRefs h)
  have hmem : ms ∈ shape.flatten :=
    List.mem_flatten.mpr ⟨mats, List.mem_of_getElem? hmats, List.mem_of_getElem? hms⟩
  dsimp only at hw
  rw [hw]
  exact le_foldr_max_nat (List.mem_map_of_mem (f := (·.width)) hmem)

/-- The number of opening groups at any level `j` is bounded by `maxOpeningsPerHeight`. -/
theorem length_levelOpenings_le_maxOpeningsPerHeight (lb : ℕ) (shape : ClaimShape) (n j : ℕ) :
    (levelOpenings lb shape n j).length ≤ maxOpeningsPerHeight lb shape := by
  cases hlo : levelOpenings lb shape n j with
  | nil => exact Nat.zero_le _
  | cons o os =>
    have ho_mem : o ∈ levelOpenings lb shape n j := by rw [hlo]; exact List.mem_cons_self
    have ho_open : o ∈ openingRefs lb shape := (List.mem_filter.mp ho_mem).1
    have ho_lh : o.logHeight + j = n := by simpa using (List.mem_filter.mp ho_mem).2
    let p₀ : PointRef := ⟨o.batch, o.matrix, o.logHeight, o.width⟩
    have hp₀ : p₀ ∈ pointRefs lb shape := mem_pointRefs_of_mem_openingRefs ho_open
    have hmap_lh : (openingRefs lb shape).map (·.logHeight) = (pointRefs lb shape).map (·.logHeight) := by
      have h := map_openingRefs_go (pointRefs lb shape) 0 0
      have hproj := congrArg (List.map fun t => t.2.2.1) h
      simpa [openingRefs, List.map_map, Function.comp_def] using hproj
    have hlen_eq : (levelOpenings lb shape n j).length =
        ((pointRefs lb shape).filter fun q => q.logHeight == p₀.logHeight).length := by
      unfold levelOpenings
      have h1 : ∀ {α : Type} (l : List α) (f : α → ℕ) (P : ℕ → Bool),
          (l.filter fun x => P (f x)).length = ((l.map f).filter P).length := by
        intro α l f P
        induction l with
        | nil => rfl
        | cons a l ih =>
          simp only [List.filter_cons, List.map_cons]
          split <;> simp [ih]
      rw [h1 (openingRefs lb shape) (·.logHeight) (fun lh => lh + j == n),
        h1 (pointRefs lb shape) (·.logHeight) (fun lh => lh == p₀.logHeight), hmap_lh]
      congr 1
      refine List.filter_congr fun lh _ => ?_
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      dsimp only [p₀]
      exact ⟨fun h => by omega, fun h => by omega⟩
    rw [← hlo, hlen_eq]
    exact le_foldr_max_nat (List.mem_map_of_mem (f := fun p : PointRef =>
      ((pointRefs lb shape).filter fun q => q.logHeight == p.logHeight).length) hp₀)

/-- Flat list of `(openingIdx, colIdx)` 2D coordinates in the exact expansion order
of `ops.flatMap expandOpening`. -/
def openingCoords (ops : List OpeningRef) (start : ℕ := 0) : List (ℕ × ℕ) :=
  (ops.zipIdx start).flatMap fun (o, oIdx) => (List.range o.width).map fun col => (oIdx, col)

theorem length_openingCoords (ops : List OpeningRef) :
    ∀ start, (openingCoords ops start).length = (ops.flatMap expandOpening).length := by
  induction ops with
  | nil => intro _; rfl
  | cons o os ih =>
    intro start
    simp only [openingCoords, List.zipIdx_cons, List.flatMap_cons, List.length_append,
      List.length_map, List.length_range, expandOpening]
    exact congrArg (o.width + ·) (ih (start + 1))

theorem mem_openingCoords_bounds (ops : List OpeningRef) :
    ∀ start p, p ∈ openingCoords ops start →
      start ≤ p.1 ∧ p.1 < start + ops.length ∧
        ∃ (h : p.1 - start < ops.length), p.2 < ops[p.1 - start].width := by
  induction ops with
  | nil => intro _ _ hp; simp [openingCoords] at hp
  | cons o os ih =>
    intro start p hp
    simp only [openingCoords, List.zipIdx_cons, List.flatMap_cons, List.mem_append,
      List.mem_map, List.mem_range] at hp
    rcases hp with ⟨col, hcol, rfl⟩ | hp
    · refine ⟨le_rfl, by simp, by simp, by simpa using hcol⟩
    · obtain ⟨hge, hlt, hidx, hcol⟩ := ih (start + 1) p hp
      refine ⟨by omega, by simp; omega, by simp; omega, ?_⟩
      have hsub : p.1 - start = (p.1 - (start + 1)) + 1 := by omega
      simpa [hsub] using hcol

theorem nodup_openingCoords (ops : List OpeningRef) :
    ∀ start, (openingCoords ops start).Nodup := by
  induction ops with
  | nil => intro _; exact List.nodup_nil
  | cons o os ih =>
    intro start
    simp only [openingCoords, List.zipIdx_cons, List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨?_, ih (start + 1), ?_⟩
    · exact List.Nodup.map (fun _ _ h => (Prod.mk.inj h).2) List.nodup_range
    · intro a ha b hb hab
      subst hab
      simp only [List.mem_map, List.mem_range] at ha
      obtain ⟨col, -, rfl⟩ := ha
      obtain ⟨hge, -, -, -⟩ := mem_openingCoords_bounds os (start + 1) _ hb
      omega

/-- The 2D tensor slot `(openingIdx, colIdx) : Fin M × Fin W` of flat claim `k` at
level `j` for shape `shape`. -/
def tensorCoord (params : FriParams) (shape : ClaimShape) (j : ℕ)
    (k : Fin (levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).length) :
    Fin (maxOpeningsPerHeight params.logBlowup shape) × Fin (maxWidth shape) :=
  let n := logMaxHeight params.logBlowup shape
  let ops := levelOpenings params.logBlowup shape n j
  have hlen : k.val < (openingCoords ops).length := by
    rw [length_openingCoords, flatMap_expandOpening_levelOpenings]
    exact k.isLt
  let p := (openingCoords ops)[k.val]'hlen
  have hmem : p ∈ openingCoords ops := List.getElem_mem hlen
  have hbd := mem_openingCoords_bounds ops 0 p hmem
  have ho_lt : p.1 < maxOpeningsPerHeight params.logBlowup shape :=
    lt_of_lt_of_le (by simpa using hbd.2.1)
      (length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n j)
  have hc_lt : p.2 < maxWidth shape := by
    obtain ⟨hidx, hcol⟩ := hbd.2.2
    have ho_mem : ops[p.1 - 0]'hidx ∈ openingRefs params.logBlowup shape :=
      (List.mem_filter.mp (List.getElem_mem hidx)).1
    exact lt_of_lt_of_le hcol (width_le_maxWidth_of_mem_openingRefs ho_mem)
  (⟨p.1, ho_lt⟩, ⟨p.2, hc_lt⟩)

/-- `tensorCoord` is injective on every level `j`: distinct flat claims occupy
distinct `(openingIdx, colIdx)` slots. -/
theorem tensorCoord_injective (params : FriParams) (shape : ClaimShape) (j : ℕ) :
    Function.Injective (tensorCoord params shape j) := by
  intro a b hab
  let n := logMaxHeight params.logBlowup shape
  let ops := levelOpenings params.logBlowup shape n j
  have ha : a.val < (openingCoords ops).length := by
    rw [length_openingCoords, flatMap_expandOpening_levelOpenings]; exact a.isLt
  have hb : b.val < (openingCoords ops).length := by
    rw [length_openingCoords, flatMap_expandOpening_levelOpenings]; exact b.isLt
  have hpeq : (openingCoords ops)[a.val]'ha = (openingCoords ops)[b.val]'hb := by
    have h1 := congrArg (fun x => x.1.val) hab
    have h2 := congrArg (fun x => x.2.val) hab
    exact Prod.ext h1 h2
  exact Fin.ext ((List.Nodup.getElem_inj_iff (nodup_openingCoords ops 0)).mp hpeq)

/-- Relating a flat sum over `ops.flatMap expandOpening` (indexed with `openingCoords`)
to the nested sum over `o : Fin ops.length` and `c : Fin ops[o.val].width`. -/
theorem sum_flatMap_expandOpening_eq_sum_nested {K : Type} [AddCommMonoid K]
    (ops : List OpeningRef) (g : ℕ → ℕ → ClaimRef → K) :
    ∀ start,
      (∑ k : Fin (ops.flatMap expandOpening).length,
          g ((openingCoords ops start)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).1
            ((openingCoords ops start)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).2
            (ops.flatMap expandOpening)[k.val]) =
        ∑ o : Fin ops.length, ∑ c : Fin ops[o.val].width,
          g (start + o.val) c.val
            ⟨ops[o.val].batch, ops[o.val].matrix, c.val,
              ops[o.val].logHeight, ops[o.val].pointIdx, ops[o.val].valueStart + c.val⟩ := by
  have hsum_zip : ∀ (l₁ : List (ℕ × ℕ)) (l₂ : List ClaimRef) (hlen : l₁.length = l₂.length),
      (∑ k : Fin l₂.length, g (l₁[k.val]'(by omega)).1 (l₁[k.val]'(by omega)).2 l₂[k.val]) =
        ((l₁.zip l₂).map fun (p, c) => g p.1 p.2 c).sum := by
    intro l₁
    induction l₁ with
    | nil =>
      intro l₂ hlen
      cases l₂ with
      | nil => simp
      | cons _ _ => simp at hlen
    | cons a as ih =>
      intro l₂ hlen
      cases l₂ with
      | nil => simp at hlen
      | cons b bs =>
        simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons]
        rw [Fin.sum_univ_succ]
        congr 1
        exact ih bs (by simpa using hlen)
  induction ops with
  | nil => intro _; simp
  | cons o os ih =>
    intro start
    rw [hsum_zip (openingCoords (o :: os) start) ((o :: os).flatMap expandOpening)
      (length_openingCoords (o :: os) start)]
    simp only [openingCoords, List.zipIdx_cons, List.flatMap_cons]
    have hlen_head : ((List.range o.width).map fun col => (start, col)).length =
        (expandOpening o).length := by simp [expandOpening]
    rw [List.zip_append hlen_head, List.map_append, List.sum_append]
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    congr 1
    · rw [← hsum_zip ((List.range o.width).map fun col => (start, col)) (expandOpening o) hlen_head]
      refine Finset.sum_bij
        (fun (k : Fin (expandOpening o).length) _ =>
          (⟨k.val, by simpa [expandOpening] using k.isLt⟩ : Fin (o :: os)[0].width))
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
        (fun c _ => ⟨⟨c.val, by simpa [expandOpening] using c.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        (fun k _ => ?_)
      simp [expandOpening]
    · change ((List.zip (openingCoords os (start + 1)) (os.flatMap expandOpening)).map
        fun (p, c) => g p.1 p.2 c).sum = _
      rw [← hsum_zip (openingCoords os (start + 1)) (os.flatMap expandOpening)
        (length_openingCoords os (start + 1)), ih (start + 1)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Nat.add_assoc, Nat.add_comm 1 j.val]

end TensorShape

/-! ## 3. Query arithmetic and check refinement for `Fri.verifyTensor` -/

section TensorChecks

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- Opening-group levels as `verifyWithTensor` hands them to `checkQueryTensor`. -/
def levelOpeningsOf (params : FriParams) (shape : ClaimShape) : ℕ → List OpeningRef := fun j =>
  (Array.ofFn (n := numRounds params shape + 1) fun j =>
    levelOpenings params.logBlowup shape (logMaxHeight params.logBlowup shape) j.val).getD j []

theorem levelOpeningsOf_eq {j : ℕ} (hj : j ≤ numRounds params shape) :
    levelOpeningsOf params shape j =
      levelOpenings params.logBlowup shape (logMaxHeight params.logBlowup shape) j := by
  have h : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  simp [levelOpeningsOf, h]

/-- What `verifyWithTensor` computes for query `t`. -/
def queryResultTensor (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof) (ch : TensorChallenges EF) (t : ℕ) :
    QueryResult EF :=
  checkQueryTensor (F := F) params shape (levelOpeningsOf params shape) points values proof ch t
    (ch.indices.getD t 0)

/-- The model messages, tensor schedule, folding challenges, and query indices agree
with a tensor-batched executable run. -/
structure AgreesTensor (commitments : Array D) (points values : Array EF)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof)
    (ch : TensorChallenges EF) (msg : ℕ → Compiled.Msg K D shape.length)
    (r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape))
    (β : ℕ → K) (index : Fin params.numQueries → ℕ) : Prop where
  msg : ∀ j ≤ numRounds params shape + 1,
    msg j = view m params shape (messages params shape commitments points values proof j)
  colSize : ch.schedule.colChallenges.size = tensorNumChallenges (maxWidth shape)
  openSize : ch.schedule.openChallenges.size =
    tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)
  colWeights : ch.schedule.colWeights =
    tensorWeights ch.schedule.colChallenges (maxWidth shape)
  openWeights : ch.schedule.openWeights =
    tensorWeights ch.schedule.openChallenges (maxOpeningsPerHeight params.logBlowup shape)
  colChals : ∀ b : Fin (tensorNumChallenges (maxWidth shape)),
    r.1 b = m.ext.toModel (ch.schedule.colChallenges[b.val]'(by rw [colSize]; exact b.isLt))
  openChals : ∀ b : Fin (tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)),
    r.2 b = m.ext.toModel (ch.schedule.openChallenges[b.val]'(by rw [openSize]; exact b.isLt))
  beta : ∀ i < numRounds params shape, β i = m.ext.toModel (ch.betas.getD i 0)
  index : ∀ t, index t = ch.indices.getD t.val 0

omit [TwoAdicOps F] in
/-- Helper: `AgreesTensor` projects to a dummy `Agrees` (with `α = 0`) so all
message-only lemmas from `Exec/Arith.lean` and `Exec/Checks.lean` apply verbatim. -/
private theorem AgreesTensor.toDummyAgrees {commitments : Array D} {points values : Array EF}
    {InputProof CommitProof : Type} {proof : FriProof F EF D InputProof CommitProof}
    {ch : TensorChallenges EF} {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index) :
    Agrees m params shape commitments points values proof
      ⟨0, ch.betas, ch.powOk, ch.indices⟩ msg 0 β index where
  msg := hag.msg
  alpha := m.ext.map_zero.symm
  beta := hag.beta
  index := hag.index

private theorem maxWidth_le_two_pow (shape : ClaimShape) :
    maxWidth shape ≤ 2 ^ tensorNumChallenges (maxWidth shape) := by
  cases h : maxWidth shape with
  | zero => exact Nat.zero_le _
  | succ w => exact lt_two_pow_tensorNumChallenges (Nat.lt_succ_self w)

private theorem maxOpenings_le_two_pow (lb : ℕ) (shape : ClaimShape) :
    maxOpeningsPerHeight lb shape ≤ 2 ^ tensorNumChallenges (maxOpeningsPerHeight lb shape) := by
  cases h : maxOpeningsPerHeight lb shape with
  | zero => exact Nat.zero_le _
  | succ w => exact lt_two_pow_tensorNumChallenges (Nat.lt_succ_self w)

/-- **Tensor reduced openings refine to `Compiled.Params.reducedTensor`.** -/
theorem toModel_reducedOpeningsTensor {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    {j : ℕ} (hj : j ≤ numRounds params shape) (t : Fin params.numQueries) (idx : ℕ)
    (hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width) :
    m.ext.toModel ((reducedOpeningsTensor (F := F) (logMaxHeight params.logBlowup shape)
        (numRounds params shape) (levelOpeningsOf params shape) ch.schedule points values
        (queryRows proof t.val) idx).getD j 0) =
      (modelParams m params shape wf).reducedTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape) (msg 0)
        ((modelParams m params shape wf).opened (modelProof m params shape proof) t) r idx j := by
  let n := logMaxHeight params.logBlowup shape
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  let ops := levelOpenings params.logBlowup shape n j
  have hlt : j < numRounds params shape + 1 := Nat.lt_succ_of_le hj
  have hjn : j ≤ n := hj.trans (Nat.sub_le _ _)
  let x : EF := cosetPoint (F := F) n j (idx >>> j)
  let rawOps : List (EF × Array EF × Array F) :=
    ops.map fun o => (points.getD o.pointIdx 0, claimedRow values o,
      openedRow (queryRows proof t.val) o.batch o.matrix)
  have hget : (reducedOpeningsTensor (F := F) n (numRounds params shape)
      (levelOpeningsOf params shape) ch.schedule points values (queryRows proof t.val) idx).getD j 0 =
      Fri.reducedOpeningTensor ch.schedule x
        (rawOps.zipIdx.map fun ((z, cl, op), oIdx) => (oIdx, z, cl, op)) := by
    simp only [reducedOpeningsTensor, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt,
      ↓reduceDIte, Option.getD_some, levelOpeningsOf_eq params shape hj, rawOps, x]
    congr 1
    have hzip : ∀ (l : List OpeningRef) (s : ℕ),
        (l.zipIdx s).map (fun (o, oIdx) =>
          (oIdx, points.getD o.pointIdx 0, claimedRow values o,
            openedRow (queryRows proof t.val) o.batch o.matrix)) =
        ((l.map fun o => (points.getD o.pointIdx 0, claimedRow values o,
            openedRow (queryRows proof t.val) o.batch o.matrix)).zipIdx s).map
          fun ((z, cl, op), oIdx) => (oIdx, z, cl, op) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro s
        simp only [List.zipIdx_cons, List.map_cons]
        exact congrArg (List.cons _) (ih (s + 1))
    simpa only [Array.getD_eq_getD_getElem?] using hzip ops 0
  rw [hget]
  have hsched : ch.schedule =
      { colChallenges := ch.schedule.colChallenges
        openChallenges := ch.schedule.openChallenges
        colWeights := tensorWeights ch.schedule.colChallenges W
        openWeights := tensorWeights ch.schedule.openChallenges M } := by
    cases hs : ch.schedule
    have hcW := hag.colWeights; have hoW := hag.openWeights
    rw [hs] at hcW hoW
    simp only [TensorSchedule.mk.injEq, true_and]
    exact ⟨hcW, hoW⟩
  rw [hsched]
  have hmaxW : W ≤ 2 ^ ch.schedule.colChallenges.size := by
    rw [hag.colSize]; exact maxWidth_le_two_pow shape
  have hmaxM : M ≤ 2 ^ ch.schedule.openChallenges.size := by
    rw [hag.openSize]; exact maxOpenings_le_two_pow params.logBlowup shape
  have hM : rawOps.length ≤ M := by
    rw [List.length_map]
    exact length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n j
  have hW : ∀ item ∈ rawOps, item.2.1.size ≤ W ∧ item.2.1.size = item.2.2.size := by
    intro item hm
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hm
    have ho_open : o ∈ openingRefs params.logBlowup shape := (List.mem_filter.mp ho).1
    refine ⟨?_, ?_⟩
    · simp only [claimedRow, Array.size_ofFn]
      exact width_le_maxWidth_of_mem_openingRefs ho_open
    · simp only [claimedRow, Array.size_ofFn]
      exact (hwidths o ho_open).symm
  rw [toModel_reducedOpeningTensor_tensorWeights m ch.schedule.colChallenges
    ch.schedule.openChallenges W M hmaxW hmaxM x rawOps hM hW]
  -- Rewrite the RHS `Compiled.Params.reducedTensor` using `sum_flatMap_expandOpening_eq_sum_nested`.
  unfold Compiled.Params.reducedTensor
  have hdum := hag.toDummyAgrees m params shape
  let g : ℕ → ℕ → ClaimRef → K := fun oIdx cIdx c =>
    (if ho : oIdx < M then
      if hc : cIdx < W then
        PcsRbr.tensorCoordWeight r (⟨oIdx, ho⟩, ⟨cIdx, hc⟩)
      else 0
    else 0) *
    ((m.ext.toModel (values.getD c.valueIdx 0) -
        m.base.toModel (openedEntry (queryRows proof t.val) c)) *
      (m.ext.toModel (points.getD c.pointIdx 0) - m.ext.toModel x)⁻¹)
  have hrhs :
      (∑ k : Fin ((modelParams m params shape wf).numClaims j),
          PcsRbr.tensorCoordWeight r (tensorCoord params shape j k) *
            (((msg 0).value j k -
                (modelParams m params shape wf).opened (modelProof m params shape proof) t j k) /
              ((msg 0).point j k -
                (modelParams m params shape wf).shift *
                  pointOfIndex (modelParams m params shape wf).ω
                    (modelParams m params shape wf).n
                    ((modelParams m params shape wf).n - j) (idx >>> j)))) =
        ∑ k : Fin (ops.flatMap expandOpening).length,
          g ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).1
            ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords]; exact k.isLt)).2
            (ops.flatMap expandOpening)[k.val] := by
    have hfl : ops.flatMap expandOpening = levelClaims params.logBlowup shape n j :=
      flatMap_expandOpening_levelOpenings params.logBlowup shape n j
    refine Finset.sum_bij
      (fun (k : Fin ((modelParams m params shape wf).numClaims j)) _ =>
        (⟨k.val, by rw [hfl]; exact k.isLt⟩ : Fin (ops.flatMap expandOpening).length))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun k _ => ⟨⟨k.val, by show k.val < (levelClaims params.logBlowup shape n j).length; rw [← hfl]; exact k.isLt⟩,
        Finset.mem_univ _, Fin.ext rfl⟩)
      (fun k _ => ?_)
    have htc : tensorCoord params shape j k =
        (⟨((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).1,
            lt_of_lt_of_le (by simpa using (mem_openingCoords_bounds ops 0 _ (List.getElem_mem _)).2.1)
              (length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n j)⟩,
          ⟨((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).2, by
            obtain ⟨hidx, hcol⟩ := (mem_openingCoords_bounds ops 0 _ (List.getElem_mem _)).2.2
            exact lt_of_lt_of_le hcol
              (width_le_maxWidth_of_mem_openingRefs (List.mem_filter.mp (List.getElem_mem hidx)).1)⟩) := rfl
    have hbd := mem_openingCoords_bounds ops 0 _
      (List.getElem_mem (show k.val < (openingCoords ops 0).length by rw [length_openingCoords, hfl]; exact k.isLt))
    have ho_lt : ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).1 < M :=
      lt_of_lt_of_le (by simpa using hbd.2.1)
        (length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n j)
    have hc_lt : ((openingCoords ops 0)[k.val]'(by rw [length_openingCoords, hfl]; exact k.isLt)).2 < W := by
      obtain ⟨hidx, hcol⟩ := hbd.2.2
      exact lt_of_lt_of_le hcol
        (width_le_maxWidth_of_mem_openingRefs (List.mem_filter.mp (List.getElem_mem hidx)).1)
    dsimp only [g]
    simp only [dite_eq_left ho_lt, dite_eq_left hc_lt]
    have hcelem : (ops.flatMap expandOpening)[k.val]'(by rw [hfl]; exact k.isLt) =
        (levelClaims params.logBlowup shape n j).get
          ⟨k.val, k.isLt⟩ := by
      simp only [List.get_eq_getElem]
      exact List.getElem_of_eq hfl (by rw [hfl]; exact k.isLt)
    have hcos : (modelParams m params shape wf).shift *
          pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            ((modelParams m params shape wf).n - j) (idx >>> j) = m.ext.toModel x :=
      (toModel_cosetPoint m params shape wf hjn (index := idx >>> j)).symm
    rw [hcelem, htc, div_eq_mul_inv,
      value_msg_zero m params shape wf hshape hdum hj k,
      point_msg_zero m params shape wf hshape hdum hj k,
      opened_modelProof m params shape wf t j k, hcos]
    rfl
  change _ = ∑ k : Fin ((modelParams m params shape wf).numClaims j),
      PcsRbr.tensorCoordWeight r (tensorCoord params shape j k) *
        (((msg 0).value j k -
            (modelParams m params shape wf).opened (modelProof m params shape proof) t j k) /
          ((msg 0).point j k -
            (modelParams m params shape wf).shift *
              pointOfIndex (modelParams m params shape wf).ω
                (modelParams m params shape wf).n
                ((modelParams m params shape wf).n - j) (idx >>> j)))
  rw [hrhs, sum_flatMap_expandOpening_eq_sum_nested ops g 0]
  dsimp only [g]
  -- Match the two nested sums `Fin rawOps.length` vs `Fin ops.length`!
  refine Finset.sum_bij
    (fun (o : Fin rawOps.length) _ => (⟨o.val, by simpa [rawOps] using o.isLt⟩ : Fin ops.length))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun o _ => ⟨⟨o.val, by simp [rawOps]⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun o _ => ?_)
  have ho_ops : o.val < ops.length := by simpa [rawOps] using o.isLt
  have ho_M : o.val < M := lt_of_lt_of_le ho_ops
    (length_levelOpenings_le_maxOpeningsPerHeight params.logBlowup shape n j)
  have hwt_open :
      tensorWeight (fun b : Fin ch.schedule.openChallenges.size =>
          m.ext.toModel ch.schedule.openChallenges[b.val]) ⟨o.val, lt_of_lt_of_le o.isLt (le_trans hM hmaxM)⟩ =
        tensorWeight r.2 ⟨o.val, lt_two_pow_tensorNumChallenges ho_M⟩ := by
    unfold tensorWeight
    refine Finset.prod_bij
      (fun b _ => ⟨b.val, by rw [← hag.openSize]; exact b.isLt⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun b _ => ⟨⟨b.val, by rw [hag.openSize]; exact b.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun b _ => ?_)
    simp [hag.openChals]
  rw [hwt_open, Finset.mul_sum]
  have hraw_w : (rawOps[o.val]).2.1.size = ops[o.val].width := by
    simp [rawOps, claimedRow]
  refine Finset.sum_bij
    (fun (c : Fin (rawOps[o.val]).2.1.size) _ =>
      (⟨c.val, by rw [← hraw_w]; exact c.isLt⟩ : Fin ops[o.val].width))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun c _ => ⟨⟨c.val, by rw [hraw_w]; exact c.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun c _ => ?_)
  have hc_w : c.val < ops[o.val].width := by rw [← hraw_w]; exact c.isLt
  have hc_W : c.val < W := lt_of_lt_of_le hc_w
    (width_le_maxWidth_of_mem_openingRefs (List.mem_filter.mp (List.getElem_mem ho_ops)).1)
  have hwt_col :
      tensorWeight (fun b : Fin ch.schedule.colChallenges.size =>
          m.ext.toModel ch.schedule.colChallenges[b.val])
        ⟨c.val, lt_of_lt_of_le c.isLt (le_trans (hW _ (List.getElem_mem o.isLt)).1 hmaxW)⟩ =
        tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges hc_W⟩ := by
    unfold tensorWeight
    refine Finset.prod_bij
      (fun b _ => ⟨b.val, by rw [← hag.colSize]; exact b.isLt⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Fin.ext (by simpa using congrArg Fin.val h))
      (fun b _ => ⟨⟨b.val, by rw [hag.colSize]; exact b.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      (fun b _ => ?_)
    simp [hag.colChals]
  simp only [Nat.zero_add, dite_eq_left ho_M, dite_eq_left hc_W, PcsRbr.tensorCoordWeight,
    rawOps, List.getElem_map, claimedRow, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn,
    hc_w, ↓reduceDIte, Option.getD_some, openedRow, openedEntry]
  rw [hwt_col]
  ring

/-- The tensor fold chain refines to `Compiled.Params.foldedTensor`. -/
theorem toModel_foldChain_tensor_fst {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    (t : Fin params.numQueries) (idx : ℕ)
    (hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width)
    {i : ℕ} (hi : i ≤ numRounds params shape) :
    m.ext.toModel (Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpeningsTensor (F := F) (logMaxHeight params.logBlowup shape)
          (numRounds params shape) (levelOpeningsOf params shape) ch.schedule points values
          (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).1 =
      (modelParams m params shape wf).foldedTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
        (modelProof m params shape proof) (msg 0) r β idx t i :=
  Arith.toModel_foldChain m params shape wf _ _ _ _ β idx (Nat.sub_le _ _)
    (fun _ hj => toModel_reducedOpeningsTensor m params shape wf hshape hag hj t idx hwidths)
    hag.beta hi

/-- Reconstructed rows of the tensor fold chain refine to `Compiled.Params.commitRowTensor`. -/
theorem toModel_foldChain_tensor_row {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    (t : Fin params.numQueries) (idx : ℕ)
    (hwidths : ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t.val) o.batch o.matrix).size = o.width)
    {i' i : ℕ} (hi' : i' < i) (hi : i ≤ numRounds params shape) :
    (m.ext.toModel (((Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpeningsTensor (F := F) (logMaxHeight params.logBlowup shape)
          (numRounds params shape) (levelOpeningsOf params shape) ch.schedule points values
          (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).2.getD i' (0, 0)).1),
      m.ext.toModel (((Fri.foldChain (F := F) (logMaxHeight params.logBlowup shape)
        (reducedOpeningsTensor (F := F) (logMaxHeight params.logBlowup shape)
          (numRounds params shape) (levelOpeningsOf params shape) ch.schedule points values
          (queryRows proof t.val) idx)
        (fun i => sibling proof i t.val) ch.betas idx i).2.getD i' (0, 0)).2)) =
      (modelParams m params shape wf).commitRowTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
        (modelProof m params shape proof) (msg 0) r β idx t i' := by
  rw [List.getD_eq_getElem?_getD, Arith.getElem?_foldChain_snd _ _ _ _ _ hi', Option.getD_some,
    Arith.toModel_placeRow,
    toModel_foldChain_tensor_fst m params shape wf hshape hag t idx hwidths (hi'.le.trans hi)]
  rfl

omit [Inhabited D] in
private theorem widths_of_queryResultTensor_ok {points values : Array EF}
    {InputProof CommitProof : Type} {proof : FriProof F EF D InputProof CommitProof}
    {ch : TensorChallenges EF} {t : ℕ}
    (hok : (queryResultTensor (F := F) params shape points values proof ch t).ok = true) :
    ∀ o ∈ openingRefs params.logBlowup shape,
      (openedRow (queryRows proof t) o.batch o.matrix).size = o.width := by
  simp only [queryResultTensor, checkQueryTensor, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq] at hok
  exact hok.1.1.1

/-- Passing `checkQueryTensor` implies `Compiled.Params.FinalCheckTensor` for query `t`. -/
theorem finalCheckTensor_of_queryResultTensor {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    (t : Fin params.numQueries)
    (hok : (queryResultTensor (F := F) params shape points values proof ch t.val).ok = true) :
    (modelParams m params shape wf).foldedTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
        (modelProof m params shape proof) (msg 0) r β (index t) t
        (modelParams m params shape wf).rounds =
      Compiled.hornerEval
        ((msg ((modelParams m params shape wf).rounds + 1)).finalCoeffs.take
          (modelParams m params shape wf).finalDegree)
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          ((modelParams m params shape wf).n - (modelParams m params shape wf).rounds)
          (index t >>> (modelParams m params shape wf).rounds)) := by
  have hwidths := widths_of_queryResultTensor_ok params shape hok
  simp only [queryResultTensor, checkQueryTensor, Bool.and_eq_true] at hok
  have hfinal := hok.2
  have hdum := hag.toDummyAgrees m params shape
  rw [m.ext.beq_iff, toModel_foldChain_tensor_fst m params shape wf hshape hag t _ hwidths le_rfl,
    m.ext.horner_eq_eval, m.embed,
    toModel_domainPoint m params shape wf (j := numRounds params shape) (Nat.sub_le _ _),
    ← Compiled.hornerEval_eq_eval, ← take_finalCoeffs_msg_last m params shape wf hshape hdum,
    ← hag.index t] at hfinal
  exact hfinal

/-- Passing `checkQueryTensor` identifies the reconstructed folding rows of query `t`. -/
theorem rows_queryResultTensor {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    (t : Fin params.numQueries)
    (hok : (queryResultTensor (F := F) params shape points values proof ch t.val).ok = true)
    {i : ℕ} (hi : i < numRounds params shape) :
    (m.ext.toModel (((queryResultTensor (F := F) params shape points values proof ch t.val).rows.getD i
        (0, 0)).1),
      m.ext.toModel (((queryResultTensor (F := F) params shape points values proof ch t.val).rows.getD i
        (0, 0)).2)) =
      (modelParams m params shape wf).commitRowTensor (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
        (modelProof m params shape proof) (msg 0) r β (index t) t i := by
  rw [hag.index t]
  exact toModel_foldChain_tensor_row m params shape wf hshape hag t _
    (widths_of_queryResultTensor_ok params shape hok) hi le_rfl

/-- Verdict of the compiled tensor verifier against a fixed hasher `H`. -/
def modelChecksTensor [DecidableEq K] [DecidableEq D] (P : Compiled.Params K) (W M : ℕ)
    (coord : ∀ j, Fin (P.numClaims j) → Fin M × Fin W) (H : MerkleHasher K D)
    (pf : Compiled.Proof K D P.batches P.queries) (msg : ℕ → Compiled.Msg K D P.batches)
    (r : PcsRbr.TensorChal K W M) (β : ℕ → K) (index : Fin P.queries → ℕ) : Bool :=
  ((List.finRange P.batches).all fun b =>
      Merkle.verifyOpenings H ((msg 0).inputRoots b) (P.dims b)
        (Array.ofFn fun t => index t >>> (P.n - Merkle.maxLogHeight (P.dims b).toList))
        (Array.ofFn (pf.inputRows b)) (Array.ofFn (pf.inputPaths b))) &&
    decide (P.FinalCheckTensor W M coord pf msg r β index) &&
    (List.range P.rounds).all fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot (P.commitDims i)
        (Array.ofFn fun t => index t >>> (i + 1))
        (Array.ofFn fun t => #[#[(P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).1,
          (P.commitRowTensor W M coord pf (msg 0) r β (index t) t i).2]])
        (Array.ofFn (pf.commitPaths i))

/-- Executable `verifyWithTensor` implies `ch.powOk = true` and `modelChecksTensor = true`. -/
theorem modelChecksTensor_of_verifyWithTensor [DecidableEq K] [DecidableEq D] (H : MerkleHasher K D)
    {commitments : Array D} {points values : Array EF}
    {proof : FriProof F EF D (Array (List D)) (Array (List D))} {ch : TensorChallenges EF}
    {msg : ℕ → Compiled.Msg K D shape.length}
    {r : PcsRbr.TensorChal K (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape)}
    {β : ℕ → K} {index : Fin params.numQueries → ℕ}
    (hshape : shapeOk (F := F) params shape commitments points values proof = true)
    (hag : AgreesTensor m params shape commitments points values proof ch msg r β index)
    (h : verifyWithTensor (merkleMmcs (inputHasher m H)) (merkleMmcs (friHasher m H))
      params shape commitments points values proof ch = true) :
    ch.powOk = true ∧
      modelChecksTensor (modelParams m params shape wf) (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape) H
        (modelProof m params shape proof) msg r β index = true := by
  have h' : (ch.powOk && ch.indices.size == params.numQueries
      && (List.range params.numQueries).all (fun t =>
        decide (ch.indices.getD t 0 < 2 ^ logMaxHeight params.logBlowup shape))
      && inputChecks (merkleMmcs (inputHasher m H)) params shape commitments
        proof.inputOpenings ch.indices
      && (Array.ofFn fun t : Fin params.numQueries =>
        queryResultTensor (F := F) params shape points values proof ch t.val).all (·.ok)
      && commitChecks (merkleMmcs (friHasher m H)) params.numQueries
        (logMaxHeight params.logBlowup shape) (numRounds params shape) proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices
        ((Array.ofFn fun t : Fin params.numQueries =>
          queryResultTensor (F := F) params shape points values proof ch t.val).map (·.rows)))
      = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨hpow, -⟩, -⟩, hin⟩, hok⟩, hcommit⟩ := h'
  have hok_all : ∀ t : Fin params.numQueries,
      (queryResultTensor (F := F) params shape points values proof ch t.val).ok = true := fun t => by
    have := Array.all_eq_true.mp hok t.val (by rw [Array.size_ofFn]; exact t.isLt)
    simpa using this
  refine ⟨hpow, ?_⟩
  have hdum := hag.toDummyAgrees m params shape
  have hfin : (modelParams m params shape wf).FinalCheckTensor (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
      (modelProof m params shape proof) msg r β index :=
    fun t => finalCheckTensor_of_queryResultTensor m params shape wf hshape hag t (hok_all t)
  have hcm : (List.range (modelParams m params shape wf).rounds).all (fun i =>
      Merkle.verifyOpenings H (msg (i + 1)).commitRoot
        ((modelParams m params shape wf).commitDims i)
        (Array.ofFn fun t => index t >>> (i + 1))
        (Array.ofFn fun t =>
          #[#[((modelParams m params shape wf).commitRowTensor (maxWidth shape)
              (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
              (modelProof m params shape proof) (msg 0) r β (index t) t i).1,
            ((modelParams m params shape wf).commitRowTensor (maxWidth shape)
              (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
              (modelProof m params shape proof) (msg 0) r β (index t) t i).2]])
        (Array.ofFn ((modelProof m params shape proof).commitPaths i))) = true := by
    rw [List.all_eq_true]
    intro i hi
    have hi : i < numRounds params shape := List.mem_range.mp hi
    obtain ⟨root, opening, hroot, ho, hv⟩ := Checks.commitChecks_merkle _ hcommit hi
    obtain ⟨-, hpaths⟩ := Checks.size_of_verifyOpenings hv
    rw [Array.size_ofFn] at hpaths
    rw [Checks.verifyOpenings_friHasher, Checks.map_ofFn_pair] at hv
    simp only [Checks.getD_map_ofFn] at hv
    rw [Checks.commitRoot_eq m params shape hdum hi hroot,
      Checks.ofFn_commitPaths m params shape i ho hpaths]
    have hrows_eq : ∀ t : Fin params.numQueries,
        (m.ext.toModel (((queryResultTensor (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).1),
          m.ext.toModel (((queryResultTensor (F := F) params shape points values proof ch t.val).rows.getD i
            (0, 0)).2)) =
          (modelParams m params shape wf).commitRowTensor (maxWidth shape)
            (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
            (modelProof m params shape proof) (msg 0) r β (index t) t i :=
      fun t => rows_queryResultTensor m params shape wf hshape hag t (hok_all t) hi
    simp only [← hrows_eq]
    simp only [hag.index]
    exact hv
  simp only [modelChecksTensor, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨inputChecks_model m params shape wf H hdum hin, hfin⟩, hcm⟩

end TensorChecks

/-! ## 4. Idealised tensor challenger and transcript refinement -/

/-- `sampleExtMany` always returns a list of length `cnt`. -/
theorem length_sampleExtMany {σ F EF D : Type} (chal : Challenger σ F EF D) :
    ∀ (cnt : ℕ) (s : σ), (sampleExtMany chal cnt s).1.length = cnt
  | 0, _ => rfl
  | cnt + 1, s => by
    simp only [sampleExtMany, List.length_cons, length_sampleExtMany chal cnt]

section TensorTranscript

open Oracle
open PcsRbr (TensorChal ChalTensor GrindChal)

variable {F EF D K : Type} [Field K] [DecidableEq K]

/-- Public length of `firstMessage` determined by `params` and `shape`. -/
def firstMessageLen (params : FriParams) (shape : ClaimShape) : ℕ :=
  shape.length + (pointRefs params.logBlowup shape).length +
    (claimRefs params.logBlowup shape).length

/-- Oracle answer for the current round of `s` under `ChalTensor`. -/
def freeAnswerTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries)) K D x)
    (s : FreeState F EF D) : GrindChal bits (ChalTensor P.ldt W M P.queries) s.round :=
  f (.chal (fsTranscript f s.hist s.round) s.cur)

/-- The `k`-th query point of a `ChalTensor` challenge; zero when out of range. -/
def queryPointTensor (P : Compiled.Params K) {W M i : ℕ}
    (c : ChalTensor P.ldt W M P.queries i) (k : ℕ) : K :=
  if h : k < P.queries then c.points ⟨k, h⟩ else 0

/-- **Idealised challenger for `Fri.verifyTensor`.**
In round `0`, `sampleExt` returns the `kCol` column challenges followed by the
`kOpen` opening-group challenges of `(freeAnswerTensor ...).2.tensor`. When
`kCol + kOpen = 0`, absorbing the first observation after `firstLen` closes
round `0` and starts round `1`. Rounds `≥ 1` match `freeChallenger` identically. -/
noncomputable def freeChallengerTensor [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    (P : Compiled.Params K) (W M firstLen : ℕ) (bits : ℕ → ℕ)
    (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries)) K D x)
    (m : FieldModel F EF K) :
    Challenger (FreeState F EF D) F EF D where
  observe s o :=
    if s.nsamp = 0 then
      if s.round = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
          s.cur.length = firstLen then
        ⟨1, Function.update s.hist 0 s.cur, [o], 0⟩
      else { s with cur := s.cur ++ [o] }
    else ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩
  sampleExt s :=
    let ans := freeAnswerTensor P W M bits f s
    let val : K :=
      if s.round = 0 then
        let kCol := Fri.tensorNumChallenges W
        let kOpen := Fri.tensorNumChallenges M
        if h1 : s.nsamp < kCol then ans.2.tensor.1 ⟨s.nsamp, h1⟩
        else if h2 : s.nsamp - kCol < kOpen then ans.2.tensor.2 ⟨s.nsamp - kCol, h2⟩
        else 0
      else ans.2.field
    (Function.surjInv m.surj val, { s with nsamp := s.nsamp + 1 })
  sampleBits s _ :=
    let ans := freeAnswerTensor P W M bits f s
    (if s.nsamp = 0 ∧ bits s.round ≠ 0 then (ans.1 : ℕ)
      else P.indexOf (queryPointTensor P ans.2
        (s.nsamp - if bits s.round = 0 then 0 else 1)),
      { s with nsamp := s.nsamp + 1 })

namespace TensorTranscript

variable (P : Compiled.Params K) (W M firstLen : ℕ) (bits : ℕ → ℕ)
  (f : ∀ x : FSQuery (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries))
      (HashQuery K D),
    MerkleAnswer (RawMsg F EF D) (GrindChal bits (ChalTensor P.ldt W M P.queries)) K D x)
  {ms : ℕ → RawMsg F EF D}

private theorem freeAnswerTensor_mk {i : ℕ} {hist : ℕ → RawMsg F EF D}
    (hh : ∀ j < i, hist j = ms j) (k : ℕ) :
    freeAnswerTensor P W M bits f ⟨i, hist, ms i, k⟩ = Transcript.answer f ms i := by
  unfold freeAnswerTensor Transcript.answer
  rw [Transcript.fsTranscript_congr f hh]

variable [FieldOps F] [FieldOps EF] [ExtensionOps F EF] (m : FieldModel F EF K)

private theorem observe_extend {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0)
    (hno : i ≠ 0 ∨ cur.length < firstLen) (o : Observation F EF D) :
    Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).observe s o)
      i (cur ++ [o]) 0 := by
  have hcond : ¬ (s.round = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0 ∧
      s.cur.length = firstLen) := by
    rw [h.round, h.cur]
    rintro ⟨rfl, -, hlen⟩
    rcases hno with hne | hlt
    · exact hne rfl
    · omega
  have hs : (freeChallengerTensor P W M firstLen bits f m).observe s o =
      { s with cur := s.cur ++ [o] } := by
    unfold freeChallengerTensor
    dsimp only
    rw [ite_eq_left h.nsamp, ite_eq_right hcond]
  rw [hs]
  exact ⟨h.round, h.hist, by rw [← h.cur], h.nsamp⟩

private theorem observeAll_round0 {s : FreeState F EF D} {cur : RawMsg F EF D}
    (h : Transcript.At ms s 0 cur 0) (l : List (Observation F EF D))
    (hlen : cur.length + l.length ≤ firstLen) :
    Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).observeAll s l)
      0 (cur ++ l) 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have hlt : cur.length < firstLen := by simp at hlen; omega
    have h1 := observe_extend P W M firstLen bits f m h (Or.inr hlt) o
    have h2 := ih h1 (by simp at hlen ⊢; omega)
    rwa [List.append_assoc] at h2

private theorem observeAll_pos {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0) (hi : i ≠ 0) (l : List (Observation F EF D)) :
    Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).observeAll s l)
      i (cur ++ l) 0 := by
  induction l generalizing s cur with
  | nil => rwa [List.append_nil]
  | cons o l ih =>
    have h1 := observe_extend P W M firstLen bits f m h (Or.inl hi) o
    have h2 := ih h1
    rwa [List.append_assoc] at h2

/-- Ready to advance to round `i + 1` on the next `observe`: either a squeeze has
already occurred (`1 ≤ k`) or we are at the end of round `0` with `0` tensor
challenges (`kCol + kOpen = 0`). -/
private def ReadyToAdvance (W M i k : ℕ) : Prop :=
  1 ≤ k ∨ (i = 0 ∧ Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0)

private theorem observe_next_tensor {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hr : ReadyToAdvance W M i k)
    (hlen0 : i = 0 → (ms 0).length = firstLen) (o : Observation F EF D) :
    Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).observe s o)
      (i + 1) [o] 0 := by
  have hs : (freeChallengerTensor P W M firstLen bits f m).observe s o =
      ⟨s.round + 1, Function.update s.hist s.round s.cur, [o], 0⟩ := by
    unfold freeChallengerTensor
    dsimp only
    rcases hr with hk | ⟨rfl, hzero⟩
    · rw [ite_eq_right (by rw [h.nsamp]; omega)]
    · by_cases hk0 : s.nsamp = 0
      · rw [ite_eq_left hk0, ite_eq_left ⟨h.round, hzero, by rw [h.cur]; exact hlen0 rfl⟩]
        simp [h.round]
      · rw [ite_eq_right hk0]
  rw [hs]
  refine ⟨by rw [← h.round], fun j hj => ?_, rfl, rfl⟩
  show Function.update s.hist s.round s.cur j = ms j
  rw [h.round, h.cur]
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · rw [Function.update_of_ne hj.ne]
    exact h.hist j hj
  · rw [Function.update_self]

private theorem observeAll_next_tensor {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hr : ReadyToAdvance W M i k)
    (hlen0 : i = 0 → (ms 0).length = firstLen)
    {l : List (Observation F EF D)} (hl : l ≠ []) :
    Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).observeAll s l)
      (i + 1) l 0 := by
  cases l with
  | nil => exact absurd rfl hl
  | cons o l =>
    exact observeAll_pos P W M firstLen bits f m
      (observe_next_tensor P W M firstLen bits f m h hr hlen0 o) (Nat.succ_ne_zero i) l

private theorem sampleExt_round0_col {s : FreeState F EF D} {k : ℕ}
    (h : Transcript.At ms s 0 (ms 0) k) (hk : k < Fri.tensorNumChallenges W) :
    ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.1 ⟨k, hk⟩) ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).2
        0 (ms 0) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensor, ↓reduceIte, hk, ↓reduceDIte,
    freeAnswerTensor_mk P W M bits f hh]

private theorem sampleExt_round0_open {s : FreeState F EF D} {k : ℕ}
    (h : Transcript.At ms s 0 (ms 0) (Fri.tensorNumChallenges W + k))
    (hk : k < Fri.tensorNumChallenges M) :
    ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.2 ⟨k, hk⟩) ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).2
        0 (ms 0) (Fri.tensorNumChallenges W + k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  have hnot : ¬ (Fri.tensorNumChallenges W + k < Fri.tensorNumChallenges W) := by omega
  have hsub : Fri.tensorNumChallenges W + k - Fri.tensorNumChallenges W = k :=
    Nat.add_sub_cancel_left _ _
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensor, ↓reduceIte, hnot, ↓reduceDIte, hsub, hk,
    freeAnswerTensor_mk P W M bits f hh]

private theorem sampleExtMany_col :
    ∀ (cnt start : ℕ) (hbound : start + cnt ≤ Fri.tensorNumChallenges W) {s : FreeState F EF D},
      Transcript.At ms s 0 (ms 0) start →
      (sampleExtMany (freeChallengerTensor P W M firstLen bits f m) cnt s).1 =
          List.ofFn (fun j : Fin cnt =>
            Function.surjInv m.surj
              ((Transcript.answer f ms 0).2.tensor.1 ⟨start + j.val, by omega⟩)) ∧
        Transcript.At ms (sampleExtMany (freeChallengerTensor P W M firstLen bits f m) cnt s).2
          0 (ms 0) (start + cnt) := by
  intro cnt
  induction cnt with
  | zero =>
    intro start _ s h
    exact ⟨rfl, by simpa [sampleExtMany] using h⟩
  | succ cnt ih =>
    intro start hbound s h
    have hlt : start < Fri.tensorNumChallenges W := by omega
    obtain ⟨h1, hs1⟩ := sampleExt_round0_col P W M firstLen bits f m h hlt
    obtain ⟨hrest, hs2⟩ := ih (start + 1) (by omega) hs1
    refine ⟨?_, by rwa [show start + 1 + cnt = start + (cnt + 1) by omega] at hs2⟩
    simp only [sampleExtMany, h1, hrest, List.ofFn_succ]
    refine congrArg₂ List.cons ?_ ?_
    · congr 1
    · congr 1; funext j; congr 1; apply congrArg; ext; simp only [Fin.val_succ]; omega

private theorem sampleExtMany_open :
    ∀ (cnt start : ℕ) (hbound : start + cnt ≤ Fri.tensorNumChallenges M) {s : FreeState F EF D},
      Transcript.At ms s 0 (ms 0) (Fri.tensorNumChallenges W + start) →
      (sampleExtMany (freeChallengerTensor P W M firstLen bits f m) cnt s).1 =
          List.ofFn (fun j : Fin cnt =>
            Function.surjInv m.surj
              ((Transcript.answer f ms 0).2.tensor.2 ⟨start + j.val, by omega⟩)) ∧
        Transcript.At ms (sampleExtMany (freeChallengerTensor P W M firstLen bits f m) cnt s).2
          0 (ms 0) (Fri.tensorNumChallenges W + (start + cnt)) := by
  intro cnt
  induction cnt with
  | zero =>
    intro start _ s h
    exact ⟨rfl, by simpa [sampleExtMany] using h⟩
  | succ cnt ih =>
    intro start hbound s h
    have hlt : start < Fri.tensorNumChallenges M := by omega
    obtain ⟨h1, hs1⟩ := sampleExt_round0_open P W M firstLen bits f m h hlt
    obtain ⟨hrest, hs2⟩ := ih (start + 1) (by omega) (by rwa [Nat.add_assoc] at hs1)
    refine ⟨?_, by rwa [show start + 1 + cnt = start + (cnt + 1) by omega] at hs2⟩
    simp only [sampleExtMany, h1, hrest, List.ofFn_succ]
    refine congrArg₂ List.cons ?_ ?_
    · congr 1
    · congr 1; funext j; congr 1; apply congrArg; ext; simp only [Fin.val_succ]; omega

private theorem sampleExt_pos {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hi : i ≠ 0) :
    ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).1 =
        Function.surjInv m.surj (Transcript.answer f ms i).2.field ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).sampleExt s).2
        i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensor, hi, ↓reduceIte, freeAnswerTensor_mk P W M bits f hh]

private theorem sampleBits_pow_tensor {s : FreeState F EF D} {i : ℕ}
    (h : Transcript.At ms s i (ms i) 0) (hb : bits i ≠ 0) (b : ℕ) :
    ((freeChallengerTensor P W M firstLen bits f m).sampleBits s b).1 =
        ((Transcript.answer f ms i).1 : ℕ) ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).sampleBits s b).2
        i (ms i) 1 := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  simp only [freeChallengerTensor, true_and, freeAnswerTensor_mk P W M bits f hh]
  rw [ite_eq_left hb]

private theorem sampleBits_query_tensor {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (hk : k = 0 → bits i = 0) (b : ℕ) :
    ((freeChallengerTensor P W M firstLen bits f m).sampleBits s b).1 =
        P.indexOf (queryPointTensor P (Transcript.answer f ms i).2
          (k - if bits i = 0 then 0 else 1)) ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).sampleBits s b).2
        i (ms i) (k + 1) := by
  obtain ⟨r, hist, cur, n⟩ := s
  obtain ⟨hr, hh, hc, hn⟩ := h
  dsimp only at hr hh hc hn
  subst hr hc hn
  refine ⟨?_, rfl, hh, rfl, rfl⟩
  have hcond : ¬ (n = 0 ∧ bits r ≠ 0) := fun hn => hn.2 (hk hn.1)
  simp only [freeChallengerTensor, hcond, ↓reduceIte, freeAnswerTensor_mk P W M bits f hh]

private theorem checkWitness_pos_tensor {s : FreeState F EF D} {i : ℕ} {cur : RawMsg F EF D}
    (h : Transcript.At ms s i cur 0) (hi : i ≠ 0) (b : ℕ) (w : F)
    (hms : ms i = cur ++ if b = 0 then [] else [.base w]) (hbits : bits i = b) :
    (((freeChallengerTensor P W M firstLen bits f m).checkWitness s b w).1 = true →
        ((Transcript.answer f ms i).1 : ℕ) = 0) ∧
      Transcript.At ms ((freeChallengerTensor P W M firstLen bits f m).checkWitness s b w).2
        i (ms i) (if b = 0 then 0 else 1) := by
  have hok : ∀ st, (freeChallengerTensor P W M firstLen bits f m).ok st = true := fun _ => rfl
  by_cases hb : b = 0
  · rw [ite_eq_left hb, List.append_nil] at hms
    rw [Challenger.checkWitness, hok, Bool.not_true, ite_eq_right (by simp), ite_eq_left hb,
      ite_eq_left hb, hms]
    exact ⟨fun _ => Transcript.fin_val_eq_zero (hbits.trans hb) _, hms ▸ h⟩
  · rw [ite_eq_right hb] at hms
    have h' := observe_extend P W M firstLen bits f m h (Or.inl hi) (.base w)
    rw [← hms] at h'
    obtain ⟨hv, hs⟩ := sampleBits_pow_tensor P W M firstLen bits f m h' (hbits ▸ hb) b
    rw [Challenger.checkWitness, hok, Bool.not_true, ite_eq_right (by simp), ite_eq_right hb,
      ite_eq_right hb]
    simp only [hok, Bool.true_and]
    refine ⟨fun hz => ?_, hs⟩
    rw [← hv]
    exact eq_of_beq hz

private theorem sampleIndices_tensor {s : FreeState F EF D} {i k : ℕ}
    (h : Transcript.At ms s i (ms i) k) (j : ℕ)
    (hk : k = j + if bits i = 0 then 0 else 1) (b count : ℕ) :
    (freeChallengerTensor P W M firstLen bits f m).sampleIndices b count s =
      (List.range count).map fun t =>
        P.indexOf (queryPointTensor P (Transcript.answer f ms i).2 (j + t)) := by
  induction count generalizing s k j with
  | zero => rfl
  | succ count ih =>
    obtain ⟨hv, hs⟩ :=
      sampleBits_query_tensor P W M firstLen bits f m h (by intro h0; split at hk <;> omega) b
    have hj : k - (if bits i = 0 then 0 else 1) = j := by omega
    rw [hj] at hv
    rw [Challenger.sampleIndices, hv, ih hs (j + 1) (by omega), List.range_succ_eq_map,
      List.map_cons, List.map_map]
    refine congrArg₂ _ rfl (List.map_congr_left fun t _ => ?_)
    rw [Function.comp_apply, Nat.add_right_comm, Nat.add_assoc]

private theorem commitPhase_free_tensor [Inhabited D] (cpb : ℕ) (commits : Array D)
    (witnesses : Array F) (r : ℕ)
    (hms : ∀ i < r, ms (i + 1) = .digest (commits.getD i default) ::
      (if cpb = 0 then [] else [.base (witnesses.getD i 0)]))
    (hbits : ∀ i < r, bits (i + 1) = cpb) (hlen0 : (ms 0).length = firstLen)
    {s : FreeState F EF D} {k : ℕ}
    (h : Transcript.At ms s 0 (ms 0) k) (hr : ReadyToAdvance W M 0 k) :
    (commitPhase (freeChallengerTensor P W M firstLen bits f m) cpb commits witnesses r s).1 =
        ((List.range r).map fun i =>
          Function.surjInv m.surj (Transcript.answer f ms (i + 1)).2.field).toArray ∧
      ((commitPhase (freeChallengerTensor P W M firstLen bits f m) cpb commits witnesses r s).2.1 = true →
        ∀ i < r, ((Transcript.answer f ms (i + 1)).1 : ℕ) = 0) ∧
      ∃ k', Transcript.At ms
          (commitPhase (freeChallengerTensor P W M firstLen bits f m) cpb commits witnesses r s).2.2
          r (ms r) k' ∧
        ReadyToAdvance W M r k' := by
  induction r with
  | zero => exact ⟨rfl, fun _ _ hi => absurd hi (Nat.not_lt_zero _), k, h, hr⟩
  | succ r ih =>
    obtain ⟨hβ, hpow, k', hs, hr'⟩ := ih (fun i hi => hms i (Nat.lt_succ_of_lt hi))
      (fun i hi => hbits i (Nat.lt_succ_of_lt hi))
    have h1 := observe_next_tensor P W M firstLen bits f m hs hr' (fun _ => hlen0)
      (.digest (commits.getD r default))
    obtain ⟨hw, h2⟩ := checkWitness_pos_tensor P W M firstLen bits f m h1 (Nat.succ_ne_zero r)
      cpb (witnesses.getD r 0) (hms r (Nat.lt_succ_self r)) (hbits r (Nat.lt_succ_self r))
    obtain ⟨hv, h3⟩ := sampleExt_pos P W M firstLen bits f m h2 (Nat.succ_ne_zero r)
    refine ⟨?_, fun hok i hi => ?_, _, h3, Or.inl (Nat.succ_pos _)⟩
    · rw [commitPhase, hβ, hv, List.push_toArray, List.range_succ, List.map_append,
        List.map_singleton]
    · rw [commitPhase] at hok
      obtain ⟨hok₁, hok₂⟩ := Bool.and_eq_true_iff.mp hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact hpow hok₁ i hi
      · exact hw hok₂

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem tensorOf_ungrind_fsTranscript (r : ℕ) :
    PcsRbr.tensorOf (PcsRbr.ungrind (fsTranscript f ms (r + 1))) =
      (Transcript.answer f ms 0).2.tensor := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Transcript.fsTranscript_succ, PcsRbr.ungrind_snoc, PcsRbr.tensorOf_snoc_succ, ih]

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem betasOfTensor_ungrind_fsTranscript (r i : ℕ) :
    PcsRbr.betasOfTensor (PcsRbr.ungrind (fsTranscript f ms r)) i =
      if i + 1 < r then (Transcript.answer f ms (i + 1)).2.field else 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    cases r with
    | zero => rfl
    | succ r =>
      rw [Transcript.fsTranscript_succ, PcsRbr.ungrind_snoc, PcsRbr.betasOfTensor_snoc_succ]
      by_cases hi : i = r
      · subst hi
        rw [Function.update_self, ite_eq_left (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hi, ih]
        by_cases hlt : i + 1 < r + 1
        · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]

omit [FieldOps F] [FieldOps EF] [ExtensionOps F EF] in
private theorem queriesOfTensor_ungrind_fsTranscript (r : ℕ) :
    PcsRbr.queriesOfTensor (PcsRbr.ungrind (fsTranscript f ms (r + 1))) =
      (Transcript.answer f ms r).2.points :=
  rfl

/-- **Full transcript refinement for `Fri.transcriptTensor` under `freeChallengerTensor`.** -/
theorem transcriptTensor_free [TwoAdicOps F] [Inhabited D] (params : FriParams) (shape : ClaimShape)
    (wf : WellFormed m params shape)
    (f : ∀ x : FSQuery (RawMsg F EF D)
        (GrindChal (powBits params shape)
          (ChalTensor (modelParams m params shape wf).ldt (maxWidth shape)
            (maxOpeningsPerHeight params.logBlowup shape) (modelParams m params shape wf).queries))
        (HashQuery K D),
      MerkleAnswer (RawMsg F EF D)
        (GrindChal (powBits params shape)
          (ChalTensor (modelParams m params shape wf).ldt (maxWidth shape)
            (maxOpeningsPerHeight params.logBlowup shape) (modelParams m params shape wf).queries))
        K D x)
    (commitments : Array D) (points values : Array EF) {InputProof CommitProof : Type}
    (proof : FriProof F EF D InputProof CommitProof)
    (hshape : shapeOk (F := F) params shape commitments points values proof = true) :
    let P := modelParams m params shape wf
    let W := maxWidth shape
    let M := maxOpeningsPerHeight params.logBlowup shape
    let ms := messages params shape commitments points values proof
    let t := fsTranscript f ms (P.rounds + 2)
    let ch := transcriptTensor
      (freeChallengerTensor P W M (firstMessageLen params shape) (powBits params shape) f m)
      FreeState.init params shape commitments points values proof
    ch.schedule.colChallenges.size = tensorNumChallenges W ∧
      ch.schedule.openChallenges.size = tensorNumChallenges M ∧
      ch.schedule.colWeights = tensorWeights ch.schedule.colChallenges W ∧
      ch.schedule.openWeights = tensorWeights ch.schedule.openChallenges M ∧
      (∀ b : Fin (tensorNumChallenges W),
        (PcsRbr.tensorOf (PcsRbr.ungrind t)).1 b =
          m.ext.toModel (ch.schedule.colChallenges[b.val]'(by
            simp only [ch, transcriptTensor, transcriptTailTensor, TensorSchedule.sample,
              List.size_toArray, length_sampleExtMany]; exact b.isLt))) ∧
      (∀ b : Fin (tensorNumChallenges M),
        (PcsRbr.tensorOf (PcsRbr.ungrind t)).2 b =
          m.ext.toModel (ch.schedule.openChallenges[b.val]'(by
            simp only [ch, transcriptTensor, transcriptTailTensor, TensorSchedule.sample,
              List.size_toArray, length_sampleExtMany]; exact b.isLt))) ∧
      (∀ i < P.rounds,
        m.ext.toModel (ch.betas.getD i 0) = PcsRbr.betasOfTensor (PcsRbr.ungrind t) i) ∧
      (ch.powOk = true → PcsRbr.PowPasses t) ∧
      (∀ k : Fin params.numQueries,
        ch.indices.getD k.val 0 = P.indexOf (PcsRbr.queriesOfTensor (PcsRbr.ungrind t) k)) := by
  intro P W M ms t ch
  have hlen_first : (ms 0).length = firstMessageLen params shape := by
    simp only [ms, messages, ↓reduceIte, firstMessage, firstMessageLen, List.length_append,
      List.length_map, Array.length_toList]
    simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
    have hc := hshape.1.1.1.1.1.1.1.1.1.2
    have hp := hshape.1.1.1.1.1.1.1.1.2
    have hv := hshape.1.1.1.1.1.1.1.2
    omega
  have hfinal_ne : finalMessage (F := F) (D := D) (numRounds params shape) proof.finalPoly ≠ [] := by
    simp only [shapeOk, Bool.and_eq_true, beq_iff_eq] at hshape
    have hfp : proof.finalPoly.size = 2 ^ params.logFinalPolyLen := hshape.1.1.2
    have hpos : 0 < proof.finalPoly.size := by rw [hfp]; exact Nat.two_pow_pos _
    intro heq
    have hlen := congrArg List.length heq
    simp only [finalMessage, List.length_append, List.length_map, Array.length_toList,
      List.length_nil] at hlen
    omega
  let chal := freeChallengerTensor P W M (firstMessageLen params shape) (powBits params shape) f m
  have h0 : Transcript.At ms (chal.observeAll FreeState.init (firstMessage commitments points values))
      0 (ms 0) 0 := by
    have h := observeAll_round0 P W M (firstMessageLen params shape) (powBits params shape) f m
      (Transcript.At.init (ms := ms)) (firstMessage commitments points values)
      (by simp only [List.length_nil, zero_add]; exact le_of_eq hlen_first)
    simpa [ms, messages] using h
  obtain ⟨hcol_list, h1⟩ :=
    sampleExtMany_col P W M (firstMessageLen params shape) (powBits params shape) f m
      (tensorNumChallenges W) 0 (by omega) h0
  obtain ⟨hopen_list, h2⟩ :=
    sampleExtMany_open P W M (firstMessageLen params shape) (powBits params shape) f m
      (tensorNumChallenges M) 0 (by omega) (by simpa using h1)
  have hready0 : ReadyToAdvance W M 0 (tensorNumChallenges W + tensorNumChallenges M) := by
    by_cases hz : tensorNumChallenges W + tensorNumChallenges M = 0
    · exact Or.inr ⟨rfl, hz⟩
    · exact Or.inl (by omega)
  have hms_commit : ∀ i < P.rounds,
      ms (i + 1) = .digest (proof.commitPhaseCommits.getD i default) ::
        (if params.commitPowBits = 0 then [] else [.base (proof.commitPowWitnesses.getD i 0)]) := by
    intro i hi
    have hi' : i + 1 ≤ numRounds params shape := hi
    simp [ms, messages, hi']
  have hbits_commit : ∀ i < P.rounds, powBits params shape (i + 1) = params.commitPowBits := by
    intro i hi
    have hi' : i + 1 ≤ numRounds params shape := hi
    simp [powBits, hi']
  obtain ⟨hbetas, hpow_c, k', h3, hr3⟩ :=
    commitPhase_free_tensor P W M (firstMessageLen params shape) (powBits params shape) f m
      params.commitPowBits proof.commitPhaseCommits proof.commitPowWitnesses P.rounds
      hms_commit hbits_commit hlen_first (by simpa using h2) hready0
  have h4 := observeAll_next_tensor P W M (firstMessageLen params shape) (powBits params shape) f m
    h3 hr3 (fun _ => hlen_first) hfinal_ne
  have hms_last : ms (P.rounds + 1) =
      finalMessage (numRounds params shape) proof.finalPoly ++
        (if params.queryPowBits = 0 then [] else [.base proof.queryPowWitness]) := by
    simp [ms, messages, show ¬ (P.rounds + 1 ≤ numRounds params shape) by show ¬ (numRounds params shape + 1 ≤ numRounds params shape); omega]
  have hbits_last : powBits params shape (P.rounds + 1) = params.queryPowBits := by
    simp [powBits, show ¬ (P.rounds + 1 ≤ numRounds params shape) by show ¬ (numRounds params shape + 1 ≤ numRounds params shape); omega]
  obtain ⟨hpow_q, h5⟩ := checkWitness_pos_tensor P W M (firstMessageLen params shape)
    (powBits params shape) f m h4 (Nat.succ_ne_zero _) params.queryPowBits proof.queryPowWitness
    hms_last hbits_last
  have hidx_list := sampleIndices_tensor P W M (firstMessageLen params shape)
    (powBits params shape) f m h5 0 (by simp [hbits_last])
    (logMaxHeight params.logBlowup shape) params.numQueries
  have hcol_arr : ch.schedule.colChallenges =
      (List.ofFn fun j : Fin (tensorNumChallenges W) =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.1
          ⟨0 + j.val, by dsimp only [W]; omega⟩)).toArray := by
    show (TensorSchedule.sample chal _ W M).1.colChallenges = _
    simp only [TensorSchedule.sample]
    exact congrArg List.toArray hcol_list
  have hopen_arr : ch.schedule.openChallenges =
      (List.ofFn fun j : Fin (tensorNumChallenges M) =>
        Function.surjInv m.surj ((Transcript.answer f ms 0).2.tensor.2
          ⟨0 + j.val, by dsimp only [M]; omega⟩)).toArray := by
    show (TensorSchedule.sample chal _ W M).1.openChallenges = _
    simp only [TensorSchedule.sample]
    exact congrArg List.toArray hopen_list
  refine ⟨by rw [hcol_arr]; simp, by rw [hopen_arr]; simp, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [tensorOf_ungrind_fsTranscript]
    simp only [hcol_arr, List.getElem_toArray, List.getElem_ofFn]
    rw [Function.surjInv_eq m.surj]
    have hb : (⟨0 + b.val, by omega⟩ : Fin (tensorNumChallenges W)) = b := by ext; simp
    rw [hb]
  · intro b
    rw [tensorOf_ungrind_fsTranscript]
    simp only [hopen_arr, List.getElem_toArray, List.getElem_ofFn]
    rw [Function.surjInv_eq m.surj]
    have hb : (⟨0 + b.val, by omega⟩ : Fin (tensorNumChallenges M)) = b := by ext; simp
    rw [hb]
  · intro i hi
    have hbi : ch.betas = ((List.range P.rounds).map fun i =>
        Function.surjInv m.surj (Transcript.answer f ms (i + 1)).2.field).toArray := hbetas
    rw [hbi, Transcript.getD_map_range, ite_eq_left hi, Function.surjInv_eq m.surj,
      betasOfTensor_ungrind_fsTranscript, ite_eq_left (by omega)]
  · intro hpowOk
    rw [Transcript.powPasses_fsTranscript]
    dsimp only [ch, transcriptTensor, transcriptTailTensor, TensorSchedule.sample] at hpowOk
    rw [Bool.and_eq_true] at hpowOk
    intro i hi
    rcases i with _ | k
    · exact Transcript.fin_val_eq_zero (by simp [powBits]) _
    · rcases Nat.lt_or_ge k P.rounds with hk | hk
      · exact hpow_c hpowOk.1 k hk
      · have hk_eq : k = P.rounds := by omega
        subst hk_eq
        exact hpow_q hpowOk.2
  · intro k
    have hind : ch.indices = ((List.range params.numQueries).map fun t =>
        P.indexOf (queryPointTensor P (Transcript.answer f ms (P.rounds + 1)).2 (0 + t))).toArray := by
      show (chal.sampleIndices (logMaxHeight params.logBlowup shape) params.numQueries _).toArray = _
      exact congrArg List.toArray hidx_list
    rw [hind, Transcript.getD_map_range, ite_eq_left k.isLt, queriesOfTensor_ungrind_fsTranscript]
    have hkq : k.val < P.queries := k.isLt
    simp only [Nat.zero_add, queryPointTensor, dite_eq_left hkq]
    rfl

end TensorTranscript

end TensorTranscript

/-! ## 5. Chained-ROM soundness of executable `Fri.verifyTensor` -/

section TensorSoundness

open Oracle OracleComp
open PcsRbr (TensorChal ChalTensor GrindChal ClaimsFail PowPasses ungrind
  tensorOf betasOfTensor queriesOfTensor)

variable {F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- Oracle answer type for tensor-batched FRI in the chained random-oracle model. -/
abbrev TensorOracleAnswer :=
  MerkleAnswer (RawMsg F EF D)
    (GrindChal (powBits params shape)
      (ChalTensor (modelParams m params shape wf).ldt (maxWidth shape)
        (maxOpeningsPerHeight params.logBlowup shape) (modelParams m params shape wf).queries))
    K D

/-- **Executable `Fri.verifyTensor` against an idealised tensor oracle `f`.** -/
noncomputable def acceptsTensor
    (f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D) : Bool :=
  Fri.verifyTensor (merkleMmcs (inputHasher m (hasherOf f)))
    (merkleMmcs (friHasher m (hasherOf f)))
    (freeChallengerTensor (modelParams m params shape wf) (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (firstMessageLen params shape)
      (powBits params shape) f m)
    FreeState.init params shape a.commitments a.points a.values a.proof

omit [DecidableEq D] in
theorem msgAt_fsTranscript_tensor
    (f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    {j : ℕ} (hj : j ≤ numRounds params shape + 1) :
    Compiled.msgAt (ungrind (fsTranscript f (a.messages params shape)
      ((modelParams m params shape wf).rounds + 2))) j = a.messages params shape j := by
  refine Compiled.msgAt_eq_of_getElem? ?_
  rw [Compiled.msgs_ungrind, fsTranscript_msgs, List.getElem?_map,
    List.getElem?_range (show j < (modelParams m params shape wf).rounds + 2 from
      Nat.lt_succ_of_le hj)]
  rfl

/-- **Refinement of `Fri.verifyTensor`:** if executable `Fri.verifyTensor` accepts
against oracle `f`, the compiled tensor model verifier accepts the corresponding
Fiat–Shamir transcript against `f`. -/
theorem run_model_of_acceptsTensor
    (f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x) (a : Attempt F EF D)
    (h : acceptsTensor m params shape wf f a = true) :
    ((modelParams m params shape wf).verifyGrindViewTensor (maxWidth shape)
      (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
      (powBits params shape) (view m params shape) (modelProof m params shape a.proof)
      (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))).run f = true := by
  unfold acceptsTensor Fri.verifyTensor at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hshape, hwith⟩ := h
  obtain ⟨hcolSz, hopenSz, hcolW, hopenW, hcolC, hopenC, hβ, hpow, hidx⟩ :=
    TensorTranscript.transcriptTensor_free m params shape wf f a.commitments a.points a.values
      a.proof hshape
  have hag : AgreesTensor m params shape a.commitments a.points a.values a.proof
      (transcriptTensor
        (freeChallengerTensor (modelParams m params shape wf) (maxWidth shape)
          (maxOpeningsPerHeight params.logBlowup shape) (firstMessageLen params shape)
          (powBits params shape) f m)
        FreeState.init params shape a.commitments a.points a.values a.proof)
      (fun j => view m params shape (Compiled.msgAt (ungrind (fsTranscript f
        (a.messages params shape) ((modelParams m params shape wf).rounds + 2))) j))
      (tensorOf (ungrind (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))))
      (betasOfTensor (ungrind (fsTranscript f (a.messages params shape)
        ((modelParams m params shape wf).rounds + 2))))
      (fun k => (modelParams m params shape wf).indexOf
        (queriesOfTensor (ungrind (fsTranscript f (a.messages params shape)
          ((modelParams m params shape wf).rounds + 2))) k)) :=
    { msg := fun j hj => by rw [msgAt_fsTranscript_tensor m params shape wf f a hj]; rfl
      colSize := hcolSz
      openSize := hopenSz
      colWeights := hcolW
      openWeights := hopenW
      colChals := fun b => hcolC b
      openChals := fun b => hopenC b
      beta := fun i hi => (hβ i hi).symm
      index := fun k => (hidx k).symm }
  obtain ⟨hpowOk, hchecks⟩ := modelChecksTensor_of_verifyWithTensor m params shape wf (hasherOf f)
    hshape hag hwith
  refine ((modelParams m params shape wf).run_verifyGrindViewTensor _ _ _ _ _ f _ _).mpr
    ⟨hpow hpowOk, ?_⟩
  exact ((modelParams m params shape wf).run_verifyWithTensor _ _ _ f _ _ _ _ _).trans hchecks

variable [DecidableEq F] [DecidableEq EF] [Fintype K] [Fintype D]

/-- Chained-ROM soundness experiment for executable `Fri.verifyTensor`. -/
noncomputable def experimentTensor {A : Type*}
    (adv : OracleComp (TensorOracleAnswer (D := D) m params shape wf) A)
    (attempt : A → Attempt F EF D) :
    OracleComp (TensorOracleAnswer (D := D) m params shape wf) (A × Bool) :=
  (modelParams m params shape wf).experimentGrindViewTensor (maxWidth shape)
    (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
    (powBits params shape) (view m params shape) adv
    (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)

/-- **Generic chained-ROM soundness of executable `Fri.verifyTensor`** from
`Tensor2DMCA` and `StepMCA`. -/
theorem soundnessTensor {θ : ℝ} (hθ : 0 ≤ θ) {εα εβ : ℕ → ℝ} {ε₀ εmax : ℝ}
    (hmca : ∀ j ≤ (modelParams m params shape wf).rounds,
      Tensor2DMCA ((twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n j).image
          ((modelParams m params shape wf).shift * ·))
        (2 ^ ((modelParams m params shape wf).rounds - j) *
          (modelParams m params shape wf).finalDegree)
        (maxWidth shape) (maxOpeningsPerHeight params.logBlowup shape) θ (εα j))
    (hε₀ : ∀ j ≤ (modelParams m params shape wf).rounds, εα j ≤ ε₀)
    (hstep : ∀ i < (modelParams m params shape wf).rounds,
      StepMCA (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n i)
        (twoAdicDomain (modelParams m params shape wf).ω
          (modelParams m params shape wf).n (i + 1))
        (2 ^ ((modelParams m params shape wf).rounds - (i + 1)) *
          (modelParams m params shape wf).finalDegree) θ (εβ i))
    (hα : ε₀ ≤ εmax)
    (hβ : ∀ i < (modelParams m params shape wf).rounds, εβ i / 2 ^ params.commitPowBits ≤ εmax)
    (hq : θ ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (TensorOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsTensor m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift θ
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experimentTensor m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  refine (modelParams m params shape wf).soundness_grind_view_tensor_of_imp (maxWidth shape)
    (maxOpeningsPerHeight params.logBlowup shape) (tensorCoord params shape)
    (fun j _ => tensorCoord_injective params shape j) (powBits params shape)
    (view m params shape) hθ hmca hε₀ hstep
    (by simpa [powBits] using hα)
    (fun i hi => by
      have hi' : i + 1 ≤ numRounds params shape := hi
      simpa [powBits, hi'] using hβ i hi)
    (by
      show θ ^ params.numQueries / 2 ^ (powBits params shape (numRounds params shape + 1)) ≤ εmax
      rw [powBits_last params shape]
      exact hq)
    hadv (fun a => (attempt a).messages params shape)
    (fun a => modelProof m params shape (attempt a).proof)
    (fun a l => ∃ f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x,
      (∀ x y, l.dlookup x = some y → f x = y) ∧
        acceptsTensor m params shape wf f (attempt a) = true)
    fun out l b l' hexp hver ⟨f, hf, hacc⟩ => by
      have hrun := (modelParams m params shape wf).run_verifyGrindViewTensor_of_outcome hexp hver f
      rw [toFun_eq_self hf] at hrun
      exact hrun.symm.trans (run_model_of_acceptsTensor m params shape wf f (attempt out.1) hacc)

/-- **Unconditional unique-decoding soundness of executable `Fri.verifyTensor`
(chained ROM).**

Under `2 * δ + (1 / 2) ^ logBlowup ≤ 1` (zero unproven proximity assumptions),
the tensor batching error is linear in `kCol + kOpen` (logarithmic in total
claims `W * M`):

    (kCol + kOpen) * ((1 + δ) * 2 ^ n) / |K|

where `kCol = tensorNumChallenges (maxWidth shape)` and
`kOpen = tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape)`. -/
theorem soundnessTensor_uniqueDecoding
    (hheight : params.logFinalHeight ≤ logMaxHeight params.logBlowup shape) {δ : ℝ} (hδ : 0 ≤ δ)
    (hrate : 2 * δ + (1 / 2) ^ params.logBlowup ≤ 1) {εmax : ℝ}
    (hα : ((tensorNumChallenges (maxWidth shape) +
          tensorNumChallenges (maxOpeningsPerHeight params.logBlowup shape) : ℕ) : ℝ) *
        ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K ≤ εmax)
    (hβ : ((1 + δ) * (2 : ℝ) ^ logMaxHeight params.logBlowup shape) / Fintype.card K /
        2 ^ params.commitPowBits ≤ εmax)
    (hq : (1 - δ) ^ params.numQueries / 2 ^ params.queryPowBits ≤ εmax) {A : Type*}
    {adv : OracleComp (TensorOracleAnswer (D := D) m params shape wf) A} {Q : ℕ}
    (hadv : adv.QueryBound Q) (attempt : A → Attempt F EF D) :
    prob (fun res l =>
        (∃ f : ∀ x, TensorOracleAnswer (D := D) m params shape wf x,
          (∀ x y, l.dlookup x = some y → f x = y) ∧
            acceptsTensor m params shape wf f (attempt res.1) = true) ∧
        ClaimsFail (modelParams m params shape wf).ldt (modelParams m params shape wf).shift
          (1 - δ)
          ((modelParams m params shape wf).claims
            (view m params shape (firstMessage (attempt res.1).commitments
              (attempt res.1).points (attempt res.1).values)) (committedRow l)))
      (experimentTensor m params shape wf adv attempt) [] ≤
      (Q + ((modelParams m params shape wf).rounds + 2) +
          (modelParams m params shape wf).verifierQueries) * εmax +
        ((max ((modelParams m params shape wf).batches +
            (modelParams m params shape wf).rounds) 3 + 3 : ℕ) : ℝ) *
          (Q + ((modelParams m params shape wf).rounds + 2) +
            (modelParams m params shape wf).verifierQueries) ^ 2 / (4 * Fintype.card D) := by
  let P := modelParams m params shape wf
  let W := maxWidth shape
  let M := maxOpeningsPerHeight params.logBlowup shape
  have hn : P.n = P.rounds + params.logBlowup + params.logFinalPolyLen := by
    show logMaxHeight params.logBlowup shape =
      numRounds params shape + params.logBlowup + params.logFinalPolyLen
    unfold numRounds FriParams.logFinalHeight at *
    omega
  have hθ : 0 ≤ 1 - δ := by
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ params.logBlowup := by positivity
    linarith
  have hmca : ∀ j ≤ P.rounds,
      Tensor2DMCA ((twoAdicDomain P.ω P.n j).image (P.shift * ·))
        (2 ^ (P.rounds - j) * P.finalDegree) W M (1 - δ)
        (((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K)) := by
    intro j hj
    refine tensor2DMCA_ud _ _ W M hδ ?_
    have hcard : ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card =
        2 ^ params.logBlowup * (2 ^ (P.rounds - j) * P.finalDegree) := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne)]
      exact Compose.card_twoAdicDomain_eq_mul_degree hn P.prim hj
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ params.logBlowup := by positivity
    have hinv : (2 : ℝ) ^ params.logBlowup * (1 / 2 : ℝ) ^ params.logBlowup = 1 := by
      rw [← mul_pow]; norm_num
    have hdeg_le : ((2 ^ (P.rounds - j) * P.finalDegree : ℕ) : ℝ) =
        (1 / 2 : ℝ) ^ params.logBlowup *
          (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) := by
      rw [hcard]; push_cast
      linear_combination -((2 : ℝ) ^ (P.rounds - j) * (P.finalDegree : ℝ)) * hinv
    rw [hdeg_le]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card]
  have hε₀ : ∀ j ≤ P.rounds,
      ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K) ≤
        ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K := by
    intro j hj
    have hcard_le : (((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card : ℝ) ≤ (2 : ℝ) ^ P.n := by
      rw [Finset.card_image_of_injective _ (mul_right_injective₀ P.shift_ne),
        card_twoAdicDomain P.prim (hj.trans P.rounds_le)]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le P.n j) :
        2 ^ (P.n - j) ≤ 2 ^ P.n)
    have hmul : ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) ≤
        ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
          ((1 + δ) * (2 : ℝ) ^ P.n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard_le (by linarith))
        (Nat.cast_nonneg _)
    calc ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            (((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K)
        = ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            ((1 + δ) * ((twoAdicDomain P.ω P.n j).image (P.shift * ·)).card) / Fintype.card K := by
          ring
      _ ≤ ((tensorNumChallenges W + tensorNumChallenges M : ℕ) : ℝ) *
            ((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K :=
          div_le_div_of_nonneg_right hmul (Nat.cast_nonneg _)
  have hstep : ∀ i < P.rounds,
      StepMCA (twoAdicDomain P.ω P.n i) (twoAdicDomain P.ω P.n (i + 1))
        (2 ^ (P.rounds - (i + 1)) * P.finalDegree) (1 - δ)
        (((1 + δ) * (2 : ℝ) ^ P.n) / Fintype.card K) :=
    fun i hi => P.stepMCA_of_rate_of_curveCA (curveCA_udThreshold (F := K)) hn rfl hδ hrate hi
  exact soundnessTensor m params shape wf hθ hmca hε₀ hstep hα (fun _ _ => hβ) hq hadv attempt

end TensorSoundness

end CertiFri.Exec
