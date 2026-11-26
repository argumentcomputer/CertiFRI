import CertiFri.TensorBatching
import CertiFriProofs.Theory.ProximityGap.TensorMCA
import CertiFriProofs.Exec.SoundnessSponge

/-!
# Executable `FriBatching::Tensor` Refinement & 128-Bit `GoldilocksExt3` Soundness

Bridges the executable `FriBatching::Tensor` implementation
(`CertiFri/TensorBatching.lean`, matching `multi-stark` `v6`'s
`src/p3_adapter/fri_batching.rs`) to the mathematical soundness theorems in
`Proofs/CertiFriProofs/Theory/ProximityGap/TensorMCA.lean`:

1. **Exact executable refinement (`CertiFri.Exec`):**
   * `length_tensorWeightsList`: `(Fri.tensorWeightsList chals len).length = min len (2 ^ chals.length)`.
   * `toModel_tensorWeightsList_getD`: every entry `j < len` (`len ≤ 2 ^ chals.length`)
     of executable `Fri.tensorWeightsList` refines to the exact mathematical
     multilinear monomial `tensorWeight (fun b => r.toModel chals[b]) j`.
   * `toModel_tensorWeightExplicit`: executable `Fri.tensorWeightExplicit` refines
     to the exact same `tensorWeight`.
   * `toModel_tensorColAcc`, `toModel_tensorOpeningTerm`, `toModel_reducedOpeningTensor`,
     `toModel_reducedOpeningTensor_tensorWeights`: the executable column
     accumulation, single-opening term, and full level reduced opening
     `Fri.reducedOpeningTensor` refine to the exact mathematical 2D tensor sum
     `∑_o w_open[o] * (∑_c w_col[c] * (y_{o,c} - f_{o,c}(x)) * (z_o - x)⁻¹)`.

2. **Concrete `GoldilocksExt3` 128-bit Tensor batching soundness (`CertiFri.P3.Exec`):**
   * `goldilocksExt3_tensor2DMCA_ud`: unconditional 2D tensor MCA over `Fp3Model`
     with error `(kCol + kOpen) * ((1 + δ) * |D|) / Goldilocks.order ^ 3`.
   * `goldilocksExt3_tensor2DMCA_ud_128`: for ANY width `W ≤ 2 ^ 16`, ANY opening
     count `M ≤ 2 ^ 16` (up to `2 ^ 32` claims!), ANY domain `|D| ≤ 2 ^ 32`, and
     blowup `4` (`δ = 3 / 8`), the tensor batching error is strictly `≤ (3 / 4) / 2 ^ 128`
     (in fact `< 2 ^ (-153)`), with **zero** unproven assumptions.
   * `goldilocksExt3_tensor2DMCA_johnson_128`: Johnson-regime 2D tensor MCA over
     `Fp3Model` under `BatchedLineListCA Fp3Model T`, with concrete `≤ (3 / 4) / 2 ^ 128`
     corollary at `θ = 65 / 128` (`logBlowup = 2`).
-/

namespace CertiFri.Exec

open Fri

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

/-- Under `r : Refines EF K`, every entry `j < 2 ^ chals.length` of `tensorWeightsFull chals`
equals the mathematical multilinear monomial `tensorWeight (fun b => r.toModel chals[b]) j`. -/
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
    -- Compare via `tensorWeight_succ_lo` / `tensorWeight_succ_hi`.
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

end CertiFri.Exec

/-! ## Concrete `GoldilocksExt3` 128-bit Tensor batching soundness -/

namespace CertiFri.P3.Exec

open CertiFri CertiFri.P3 CertiFri.Exec

/-- **Unconditional `Tensor2DMCA` over `GoldilocksExt3` (`Fp3Model`) in the
unique-decoding regime (`2 * δ + ρ ≤ 1`).** -/
theorem goldilocksExt3_tensor2DMCA_ud (D : Finset Fp3Model) (d W M : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hrate : 2 * (δ * D.card) + d ≤ D.card) :
    Tensor2DMCA D d W M (1 - δ)
      (((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        (((1 + δ) * D.card) / ((Goldilocks.order : ℝ) ^ 3))) := by
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  simpa only [hcard] using tensor2DMCA_ud (F := Fp3Model) D d W M hδ hrate

/-- Helper bound: if `n ≤ 2 ^ k`, then `tensorNumChallenges n ≤ k`. -/
theorem tensorNumChallenges_le_of_le_pow {n k : ℕ} (h : n ≤ 2 ^ k) :
    Fri.tensorNumChallenges n ≤ k := by
  unfold Fri.tensorNumChallenges
  split_ifs with hle
  · exact Nat.zero_le _
  · have hlt : n - 1 < 2 ^ k := by omega
    have hlog : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).mpr hlt
    omega

/-- **Concrete 128-bit unconditional `GoldilocksExt3` Tensor batching theorem:**
for ANY width `W ≤ 2 ^ 16` (`≤ 65,536` columns), ANY opening count `M ≤ 2 ^ 16`
(up to **4.29 billion** claims!), ANY evaluation domain `|D| ≤ 2 ^ 32`, and
unique-decoding blowup `4` (`δ = 3 / 8`, `d / |D| ≤ 1 / 4`), the 2D Tensor
batching error is strictly `≤ (3 / 4) / 2 ^ 128` (leaving `> 25` bits of margin
above 128 bits, with ZERO unproven assumptions!). -/
theorem goldilocksExt3_tensor2DMCA_ud_128 (D : Finset Fp3Model) (d W M : ℕ)
    (hD : D.card ≤ 2 ^ 32) (hW : W ≤ 2 ^ 16) (hM : M ≤ 2 ^ 16)
    (hrate : 2 * ((3 / 8 : ℝ) * D.card) + d ≤ D.card) :
    Tensor2DMCA D d W M (5 / 8) ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  have hbase := goldilocksExt3_tensor2DMCA_ud D d W M (δ := 3 / 8) (by norm_num) hrate
  rw [show (1 - 3 / 8 : ℝ) = 5 / 8 by norm_num] at hbase
  have hkCol : Fri.tensorNumChallenges W ≤ 16 := tensorNumChallenges_le_of_le_pow hW
  have hkOpen : Fri.tensorNumChallenges M ≤ 16 := tensorNumChallenges_le_of_le_pow hM
  have hkSum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) ≤ 32 := by
    exact_mod_cast (by omega : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ 32)
  have hD_real : (D.card : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hD
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have herr : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
      (((1 + (3 / 8 : ℝ)) * D.card) / ((Goldilocks.order : ℝ) ^ 3)) ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    have hnum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        ((1 + (3 / 8 : ℝ)) * D.card) ≤ 32 * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) := by
      have h1 : (1 + (3 / 8 : ℝ)) * D.card ≤ (11 / 8 : ℝ) * (2 : ℝ) ^ 32 := by nlinarith
      exact mul_le_mul hkSum h1 (by positivity) (by norm_num)
    have hdiv : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
        (((1 + (3 / 8 : ℝ)) * D.card) / ((Goldilocks.order : ℝ) ^ 3)) ≤
        (32 * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32)) / (2 : ℝ) ^ 191 := by
      rw [← mul_div_assoc]
      exact div_le_div₀ (by positivity) hnum (by positivity) h191
    refine hdiv.trans ?_
    have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
    rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
    have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
    have hconst : (32 : ℝ) * ((11 / 8 : ℝ) * (2 : ℝ) ^ 32) ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by
      norm_num
    rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
    exact mul_le_mul_of_nonneg_right hconst hpos128.le
  intro u
  obtain ⟨bad, hbad_card, hbad⟩ := hbase u
  refine ⟨bad, hbad_card.trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)), hbad⟩

/-- **Johnson-regime `Tensor2DMCA` over `GoldilocksExt3` (`Fp3Model`)** under
`BatchedLineListCA Fp3Model T`, at agreement `θ = 65 / 128` (`logBlowup = 2`). -/
theorem goldilocksExt3_tensor2DMCA_johnson_128 {T : ℕ → ℕ → ℕ → ℕ → ℕ}
    (hca : BatchedLineListCA Fp3Model T)
    (D : Finset Fp3Model) (hDne : D.Nonempty) (d W M : ℕ)
    (hD : D.card ≤ 2 ^ 32) (hW : W ≤ 2 ^ 16) (hM : M ≤ 2 ^ 16)
    (hrate : (d : ℝ) / D.card ≤ 1 / 4)
    {cT : ℝ} (hcT : cT ≤ (2 : ℝ) ^ 56)
    (hT : ∀ i < Fri.tensorNumChallenges W + Fri.tensorNumChallenges M,
      (T D.card d ⌈(65 / 128 : ℝ) * D.card⌉₊ (2 ^ i) : ℝ) ≤ cT) :
    Tensor2DMCA D d W M (65 / 128) ((3 / 4 : ℝ) / (2 : ℝ) ^ 128) := by
  have hgap : (d : ℝ) / D.card < (65 / 128 : ℝ) ^ 2 := lt_of_le_of_lt hrate (by norm_num)
  have hbase := tensor2DMCA_johnson hca D hDne d W M (θ := 65 / 128) (cT := cT)
    (by norm_num) (by norm_num) hgap hT
  have hcard : (Fintype.card Fp3Model : ℝ) = (Goldilocks.order : ℝ) ^ 3 := by
    rw [Fp3Model.card_fp3Model, Nat.cast_pow]
  rw [hcard] at hbase
  have hkCol : Fri.tensorNumChallenges W ≤ 16 := tensorNumChallenges_le_of_le_pow hW
  have hkOpen : Fri.tensorNumChallenges M ≤ 16 := tensorNumChallenges_le_of_le_pow hM
  have hkSum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) ≤ 32 := by
    exact_mod_cast (by omega : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ 32)
  have hD_real : (D.card : ℝ) ≤ (2 : ℝ) ^ 32 := by exact_mod_cast hD
  have h191 : (2 : ℝ) ^ 191 ≤ (Goldilocks.order : ℝ) ^ 3 := two_pow_191_le_goldilocks_cube
  have hLJ : ((65 / 128 : ℝ) - (d : ℝ) / D.card) /
      ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card) * (1 - 65 / 128) ≤ 17 := by
    have hden_pos : (0 : ℝ) < (65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card := by linarith
    have hmono : ((65 / 128 : ℝ) - (d : ℝ) / D.card) /
        ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card) ≤
        ((65 / 128 : ℝ) - 1 / 4) / ((65 / 128 : ℝ) ^ 2 - 1 / 4) := by
      rw [div_le_div_iff₀ hden_pos (by norm_num)]
      linarith
    have hbound : ((65 / 128 : ℝ) - 1 / 4) / ((65 / 128 : ℝ) ^ 2 - 1 / 4) * (1 - 65 / 128) ≤ 17 := by
      norm_num
    linarith
  have herr : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
      ((cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
        ((1 - 65 / 128) * D.card)) / ((Goldilocks.order : ℝ) ^ 3)) ≤
      (3 / 4 : ℝ) / (2 : ℝ) ^ 128 := by
    by_cases h0 : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M = 0
    · rw [h0, Nat.cast_zero, zero_mul]
      exact div_nonneg (by norm_num) (pow_pos (by norm_num) 128).le
    · have hpos0 : 0 < Fri.tensorNumChallenges W + Fri.tensorNumChallenges M := Nat.pos_of_ne_zero h0
      have hcT_nn : 0 ≤ cT := (Nat.cast_nonneg _).trans (hT 0 hpos0)
      have hterm : ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
          ((1 - 65 / 128) * D.card) ≤ 17 * (2 : ℝ) ^ 32 := by
        rw [← mul_assoc]
        exact mul_le_mul hLJ hD_real (Nat.cast_nonneg _) (by norm_num)
      have hden_pos : (0 : ℝ) < (65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card := by linarith
      have hnum_nn : 0 ≤ (65 / 128 : ℝ) - (d : ℝ) / D.card := by linarith
      have hterm_nn : 0 ≤ ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
          ((1 - 65 / 128) * D.card) :=
        mul_nonneg (div_nonneg hnum_nn hden_pos.le) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      have hinner_nn : 0 ≤ cT + ((65 / 128 - (d : ℝ) / D.card) /
          ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) * ((1 - 65 / 128) * D.card) := by linarith
      have hnum : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
          (cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
            ((1 - 65 / 128) * D.card)) ≤ 32 * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32) := by
        exact mul_le_mul hkSum (by linarith) hinner_nn (by norm_num)
      have hdiv : ((Fri.tensorNumChallenges W + Fri.tensorNumChallenges M : ℕ) : ℝ) *
          ((cT + ((65 / 128 - (d : ℝ) / D.card) / ((65 / 128 : ℝ) ^ 2 - (d : ℝ) / D.card)) *
            ((1 - 65 / 128) * D.card)) / ((Goldilocks.order : ℝ) ^ 3)) ≤
          (32 * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32)) / (2 : ℝ) ^ 191 := by
        rw [← mul_div_assoc]
        exact div_le_div₀ (by positivity) hnum (by positivity) h191
      refine hdiv.trans ?_
      have h191e : (2 : ℝ) ^ 191 = (2 : ℝ) ^ 63 * (2 : ℝ) ^ 128 := by rw [← pow_add]
      rw [h191e, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpos128 : (0 : ℝ) < (2 : ℝ) ^ 128 := pow_pos (by norm_num) 128
      have hconst : (32 : ℝ) * ((2 : ℝ) ^ 56 + 17 * (2 : ℝ) ^ 32) ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ 63 := by
        norm_num
      rw [← mul_assoc (3 / 4 : ℝ) ((2 : ℝ) ^ 63)]
      exact mul_le_mul_of_nonneg_right hconst hpos128.le
  intro u
  obtain ⟨bad, hbad_card, hbad⟩ := hbase u
  refine ⟨bad, hbad_card.trans (mul_le_mul_of_nonneg_right herr (Nat.cast_nonneg _)), hbad⟩

end CertiFri.P3.Exec
