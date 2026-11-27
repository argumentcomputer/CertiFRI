import Mathlib
import CertiFriProofs.Theory.Oracle.Balanced
import CertiFriProofs.Theory.PcsRbrTensor
import CertiFriProofs.Theory.Compiled.Verifier

/-!
# Shape-independent uniform challenge answers for tensor-batched STARKs

Generalizes `Theory/Stark/Uniform.lean` (`UAns K slots width`) to support
tensor-batched FRI (`FriBatching::Tensor`), where the opening batching round
draws `kCol + kOpen` independent extension-field challenges (`TensorChal K W M`)
whose count depends on the prover-chosen active circuits and trace heights.

* `UTensorAns K fslots slots width` holds `fslots` independent field elements
  and `slots` numbers below `2 ^ width`. `UTensorAns.fieldAt u k` is the `k`-th
  field element (and `UTensorAns.field u := u.fieldAt 0` is the single challenge
  used by rounds `0..3` and the FRI folding rounds); `UTensorAns.bits u k b` is
  the `k`-th bit sample reduced to `b` bits.
* `pcsChalTensor P W M bits j u` reads the challenge of round `j` of the
  tensor-batched opening protocol (`GrindChal bits (ChalTensor P.ldt W M P.queries) j`)
  off a uniform answer `u`.
* `fractionLE_pcsChalTensor` and `fractionLE_tensorField`: every fraction bound
  on `ChalTensor` (with PoW grinding) or on `K` pulls back cleanly to
  `UTensorAns K fslots slots width` whenever `kCol + kOpen ≤ fslots`, `0 < fslots`,
  `P.queries + 1 ≤ slots`, `bits j ≤ width`, and `P.n ≤ width`.
-/

namespace CertiFri.Stark

open CertiFri.Oracle CertiFri.PcsRbr

/-- A shape-independent uniform answer to a challenge query for a tensor-batched
STARK: `fslots` independent field elements and `slots` numbers below `2 ^ width`. -/
abbrev UTensorAns (K : Type) (fslots slots width : ℕ) : Type :=
  (Fin fslots → K) × (Fin slots → Fin (2 ^ width))

namespace UTensorAns

variable {K : Type} {fslots slots width : ℕ}

/-- The `k`-th field challenge of an answer, or `0` if out of range. -/
def fieldAt [Zero K] (u : UTensorAns K fslots slots width) (k : ℕ) : K :=
  if h : k < fslots then u.1 ⟨k, h⟩ else 0

/-- The primary (`0`-th) field challenge of an answer. -/
def field [Zero K] (u : UTensorAns K fslots slots width) : K :=
  u.fieldAt 0

/-- The `k`-th number of an answer, reduced to `b` bits; zero if out of range. -/
def bits (u : UTensorAns K fslots slots width) (k b : ℕ) : ℕ :=
  if h : k < slots then (u.2 ⟨k, h⟩ : ℕ) % 2 ^ b else 0

/-- A number reduced to `b` bits is below `2 ^ b`. -/
theorem bits_lt (u : UTensorAns K fslots slots width) (k b : ℕ) : u.bits k b < 2 ^ b := by
  unfold bits
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos b)
  · exact Nat.two_pow_pos b

/-- The `k`-th number of an answer that has one, reduced to `b` bits. -/
theorem bits_of_lt (u : UTensorAns K fslots slots width) {k : ℕ} (h : k < slots) (b : ℕ) :
    u.bits k b = (u.2 ⟨k, h⟩ : ℕ) % 2 ^ b :=
  dite_eq_left h

/-- The `k`-th field challenge of an answer that has one. -/
theorem fieldAt_of_lt [Zero K] (u : UTensorAns K fslots slots width) {k : ℕ} (h : k < fslots) :
    u.fieldAt k = u.1 ⟨k, h⟩ :=
  dite_eq_left h

end UTensorAns

section PcsTensor

variable {K : Type} [Field K] [DecidableEq K] {fslots slots width : ℕ}

/-- The challenge of round `j` of the tensor-batched opening protocol with
parameters `P`, tensor dimensions `(W, M)`, and proof-of-work bits `bits`,
read off a uniform answer `u : UTensorAns K fslots slots width`. -/
noncomputable def pcsChalTensor (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (j : ℕ)
    (u : UTensorAns K fslots slots width) :
    GrindChal bits (ChalTensor P.ldt W M P.queries) j :=
  (⟨u.bits 0 (bits j), u.bits_lt 0 (bits j)⟩,
    if h0 : j = 0 then
      (chalTensor0 h0).symm
        (fun b => u.fieldAt b.val, fun b => u.fieldAt (Fri.tensorNumChallenges W + b.val))
    else if hle : j ≤ P.ldt.rounds then
      (chalTensorField h0 hle).symm u.field
    else
      (chalTensorQuery hle).symm fun t =>
        ⟨pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n), by
          simpa using pointOfIndex_mem_twoAdicDomain P.prim P.n
            (u.bits (t.val + if bits j = 0 then 0 else 1) P.n)⟩)

variable (P : Compiled.Params K) (W M : ℕ) (bits : ℕ → ℕ) (j : ℕ)
  (u : UTensorAns K fslots slots width)

/-- The proof-of-work bits of a round are the first number of the answer. -/
theorem pcsChalTensor_pow : ((pcsChalTensor P W M bits j u).1 : ℕ) = u.bits 0 (bits j) := rfl

/-- In round `0`, the tensor batching schedule reads the first `kCol` field slots
for columns and the next `kOpen` field slots for opening groups. -/
theorem tensor_pcsChalTensor (h0 : j = 0) :
    (pcsChalTensor P W M bits j u).2.tensor =
      (fun b => u.fieldAt b.val, fun b => u.fieldAt (Fri.tensorNumChallenges W + b.val)) := by
  rw [ChalTensor.tensor_of_zero h0]
  simp only [pcsChalTensor, dite_eq_left h0, Equiv.apply_symm_apply]

/-- In a folding round (`0 < j ≤ P.rounds`), the challenge is `u.field`. -/
theorem field_pcsChalTensor (h0 : j ≠ 0) (hle : j ≤ P.rounds) :
    (pcsChalTensor P W M bits j u).2.field = u.field := by
  have hle' : j ≤ P.ldt.rounds := hle
  rw [ChalTensor.field_of_pos_le h0 hle']
  simp only [pcsChalTensor, dite_eq_right h0, dite_eq_left hle', Equiv.apply_symm_apply]

/-- Past the last folding round, the folding field challenge reads zero. -/
theorem field_pcsChalTensor_of_not_le (hle : ¬ j ≤ P.rounds) :
    (pcsChalTensor P W M bits j u).2.field = 0 :=
  ChalTensor.field_of_not_le (S := P.ldt) hle _

/-- In the query round (`j > P.rounds`), query point `t` is the point of the
corresponding bit sample of `u`. -/
theorem points_pcsChalTensor (hle : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    (pcsChalTensor P W M bits j u).2.points t =
      pointOfIndex P.ω P.n P.n (u.bits (t.val + if bits j = 0 then 0 else 1) P.n) := by
  have h0 : j ≠ 0 := by omega
  have hle' : ¬ j ≤ P.ldt.rounds := hle
  rw [ChalTensor.points_of_not_le hle']
  simp only [pcsChalTensor, dite_eq_right h0, dite_eq_right hle', Equiv.apply_symm_apply]

/-- In the query round, the index of query point `t` is the corresponding bit sample of `u`. -/
theorem indexOf_points_pcsChalTensor (hle : ¬ j ≤ P.rounds) (t : Fin P.queries) :
    P.indexOf ((pcsChalTensor P W M bits j u).2.points t) =
      u.bits (t.val + if bits j = 0 then 0 else 1) P.n := by
  rw [points_pcsChalTensor P W M bits j u hle t]
  exact P.indexOf_pointOfIndex (u.bits_lt _ _)

/-- The point of the first domain named by an index below `2 ^ P.n`. -/
private def pointOfT (i : Fin (2 ^ P.n)) : ↥(P.ldt.domain 0) :=
  ⟨pointOfIndex P.ω P.n P.n i, by simpa using pointOfIndex_mem_twoAdicDomain P.prim P.n i⟩

private theorem pointOfT_bijective : Function.Bijective (pointOfT P) := by
  constructor
  · intro a b hab
    exact Fin.ext ((pointOfIndex_inj P.prim le_rfl a.2 b.2).mp (congrArg Subtype.val hab))
  · rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := exists_pointOfIndex_eq P.prim le_rfl (x := x) (by simpa using hx)
    exact ⟨⟨i, hi⟩, rfl⟩

private theorem balanced_pointsT (hn : P.n ≤ width) (q : ℕ) :
    Balanced (fun (v : Fin q → Fin (2 ^ width)) (t : Fin q) =>
      pointOfT P ⟨(v t : ℕ) % 2 ^ P.n, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) :=
  Balanced.postcomp ((Balanced.of_bijective (pointOfT_bijective P)).comp (Balanced.finMod hn))

omit [Field K] [DecidableEq K] in
/-- Reading a 2D tensor challenge `(rCol, rOpen)` from distinct slots of
`Fin fslots → K` is balanced whenever `kCol + kOpen ≤ fslots`. -/
private theorem balanced_tensorSlice [Finite K] {kCol kOpen : ℕ}
    (hfslots : kCol + kOpen ≤ fslots) :
    Balanced (fun (v : Fin fslots → K) =>
      ((fun b : Fin kCol => v ⟨b.val, by omega⟩),
       (fun b : Fin kOpen => v ⟨kCol + b.val, by omega⟩))) := by
  let g : Fin kCol ⊕ Fin kOpen → Fin fslots := fun s =>
    match s with
    | .inl b => ⟨b.val, by omega⟩
    | .inr b => ⟨kCol + b.val, by omega⟩
  have hginj : Function.Injective g := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext (by simpa [g] using congrArg Fin.val hab))
      | inr b =>
        have hv := congrArg Fin.val hab
        dsimp only [g] at hv
        omega
    | inr a =>
      cases b with
      | inl b =>
        have hv := congrArg Fin.val hab
        dsimp only [g] at hv
        omega
      | inr b =>
        have hv := congrArg Fin.val hab
        dsimp only [g] at hv
        exact congrArg Sum.inr (Fin.ext (by omega))
  have h1 : Balanced (fun (v : Fin fslots → K) (s : Fin kCol ⊕ Fin kOpen) => v (g s)) :=
    Balanced.precomp_injective hginj
  have h2 := (Balanced.of_equiv (Equiv.sumArrowEquivProdArrow (Fin kCol) (Fin kOpen) K)).comp h1
  exact h2.congr fun v => rfl

/-- In round `0`, reading `pcsChalTensor` off `UTensorAns` is balanced. -/
private theorem balanced_pcsChalTensor_zero [Finite K]
    (hfslots : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ fslots)
    (hslots : 0 < slots) (hbits : bits j ≤ width) (h0 : j = 0) :
    Balanced (pcsChalTensor P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensor P.ldt W M P.queries) j) := by
  have hb0 : Balanced (fun v : Fin slots → Fin (2 ^ width) => v ⟨0, hslots⟩) := Balanced.eval _
  have hfst := (Balanced.of_equiv (chalTensor0 (S := P.ldt) (W := W) (M := M) (q := P.queries) h0).symm).comp
    (balanced_tensorSlice hfslots)
  have hsnd := (Balanced.finMod hbits).comp hb0
  refine ((Balanced.of_equiv (Equiv.prodComm _ _)).comp (Balanced.prodMap hfst hsnd)).congr fun u => ?_
  refine Prod.ext (Fin.ext ?_) ?_
  · exact (UTensorAns.bits_of_lt u hslots (bits j)).symm
  · simp only [pcsChalTensor, dite_eq_left h0]
    refine congrArg (chalTensor0 h0).symm (Prod.ext ?_ ?_)
    · funext b
      exact (UTensorAns.fieldAt_of_lt u (by omega)).symm
    · funext b
      exact (UTensorAns.fieldAt_of_lt u (by omega)).symm

/-- In a folding round (`0 < j ≤ P.rounds`), reading `pcsChalTensor` off `UTensorAns` is balanced. -/
private theorem balanced_pcsChalTensor_fold [Finite K]
    (hfpos : 0 < fslots) (hslots : 0 < slots) (hbits : bits j ≤ width)
    (h0 : j ≠ 0) (hle : j ≤ P.ldt.rounds) :
    Balanced (pcsChalTensor P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensor P.ldt W M P.queries) j) := by
  have hb0 : Balanced (fun v : Fin slots → Fin (2 ^ width) => v ⟨0, hslots⟩) := Balanced.eval _
  have hf0 : Balanced (fun v : Fin fslots → K => v ⟨0, hfpos⟩) := Balanced.eval _
  have hfst := (Balanced.of_equiv (chalTensorField (S := P.ldt) (W := W) (M := M)
    (q := P.queries) h0 hle).symm).comp hf0
  have hsnd := (Balanced.finMod hbits).comp hb0
  refine ((Balanced.of_equiv (Equiv.prodComm _ _)).comp (Balanced.prodMap hfst hsnd)).congr fun u => ?_
  refine Prod.ext (Fin.ext ?_) ?_
  · exact (UTensorAns.bits_of_lt u hslots (bits j)).symm
  · simp only [pcsChalTensor, dite_eq_right h0, dite_eq_left hle]
    refine congrArg (chalTensorField h0 hle).symm ?_
    exact (UTensorAns.fieldAt_of_lt u hfpos).symm

/-- In the query round (`j > P.rounds`), reading `pcsChalTensor` off `UTensorAns` is balanced. -/
private theorem balanced_pcsChalTensor_query [Finite K]
    (hslots : P.queries + 1 ≤ slots) (hbits : bits j ≤ width) (hn : P.n ≤ width)
    (hle : ¬ j ≤ P.ldt.rounds) :
    Balanced (pcsChalTensor P W M bits j :
      UTensorAns K fslots slots width → GrindChal bits (ChalTensor P.ldt W M P.queries) j) := by
  have h0 : j ≠ 0 := by omega
  have hpts := (Balanced.of_equiv (chalTensorQuery (S := P.ldt) (W := W) (M := M)
    (q := P.queries) hle).symm).comp (balanced_pointsT P (width := width) hn P.queries)
  by_cases hb : bits j = 0
  · have hsub : Subsingleton (Fin (2 ^ bits j)) :=
      Fin.subsingleton_iff_le_one.mpr (by rw [hb, pow_zero])
    have hres : Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin P.queries) =>
        v (Fin.castLE (Nat.le_of_succ_le hslots) t)) :=
      Balanced.precomp_injective (Fin.castLE_injective _)
    have hq := hpts.comp (hres.comp (Balanced.snd (β := Fin fslots → K)))
    refine (hq.prodMk_const ⟨0, Nat.two_pow_pos _⟩).congr fun u => ?_
    refine Prod.ext (Subsingleton.elim _ _) ?_
    simp only [pcsChalTensor, dite_eq_right h0, dite_eq_right hle]
    refine congrArg (chalTensorQuery hle).symm (funext fun t => Subtype.ext ?_)
    change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
    rw [ite_eq_left hb, Nat.add_zero,
      UTensorAns.bits_of_lt u (lt_of_lt_of_le t.2 (Nat.le_of_succ_le hslots))]
    rfl
  · have hres : Balanced (fun (v : Fin slots → Fin (2 ^ width)) (t : Fin (P.queries + 1)) =>
        v (Fin.castLE hslots t)) :=
      Balanced.precomp_injective (Fin.castLE_injective _)
    have hsplit := (Balanced.finConsSplit P.queries).comp
      (hres.comp (Balanced.snd (β := Fin fslots → K)))
    refine ((Balanced.prodMap (Balanced.finMod hbits) hpts).comp hsplit).congr fun u => ?_
    refine Prod.ext (Fin.ext ?_) ?_
    · exact (UTensorAns.bits_of_lt u (by omega) (bits j)).symm
    · simp only [pcsChalTensor, dite_eq_right h0, dite_eq_right hle]
      refine congrArg (chalTensorQuery hle).symm (funext fun t => Subtype.ext ?_)
      change pointOfIndex P.ω P.n P.n _ = pointOfIndex P.ω P.n P.n _
      rw [ite_eq_right hb, UTensorAns.bits_of_lt u (by omega)]
      rfl

/-- **A fraction bound on round `j` of tensor-batched FRI pulls back cleanly to
shape-independent `UTensorAns K fslots slots width`.** -/
theorem fractionLE_pcsChalTensor [Fintype K]
    (hfslots : Fri.tensorNumChallenges W + Fri.tensorNumChallenges M ≤ fslots)
    (hfpos : 0 < fslots) (hslots : P.queries + 1 ≤ slots) (hbits : bits j ≤ width)
    (hn : P.n ≤ width) {p : GrindChal bits (ChalTensor P.ldt W M P.queries) j → Prop} {ε : ℝ}
    (h : FractionLE p ε) :
    FractionLE (fun u : UTensorAns K fslots slots width => p (pcsChalTensor P W M bits j u)) ε := by
  refine FractionLE.comap ?_ h
  by_cases h0 : j = 0
  · exact balanced_pcsChalTensor_zero P W M bits j hfslots (by omega) hbits h0
  · by_cases hle : j ≤ P.ldt.rounds
    · exact balanced_pcsChalTensor_fold P W M bits j hfpos (by omega) hbits h0 hle
    · exact balanced_pcsChalTensor_query P W M bits j hslots hbits hn hle

omit [Field K] [DecidableEq K] in
/-- A fraction bound on `K` pulls back to `u.field` (`u.fieldAt 0`) of `UTensorAns`
whenever `0 < fslots`. -/
theorem fractionLE_tensorField [Zero K] [Fintype K] (hfpos : 0 < fslots) {p : K → Prop} {ε : ℝ}
    (h : FractionLE p ε) :
    FractionLE (fun u : UTensorAns K fslots slots width => p u.field) ε := by
  have hbal : Balanced (fun u : UTensorAns K fslots slots width => u.field) :=
    ((Balanced.eval (⟨0, hfpos⟩ : Fin fslots)).comp Balanced.fst).congr fun u =>
      (UTensorAns.fieldAt_of_lt u hfpos).symm
  exact FractionLE.comap hbal h

end PcsTensor

end CertiFri.Stark
