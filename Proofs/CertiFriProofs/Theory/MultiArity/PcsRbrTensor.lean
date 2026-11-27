import CertiFriProofs.Theory.PcsRbrTensor
import CertiFriProofs.Theory.MultiArity.Ldt

/-!
# Round-by-round soundness of multi-arity tensor-batched FRI

Generalizes `Theory/PcsRbrTensor.lean` from binary folding (`LdtInstance`) to
variable per-round multi-arity folding (`MultiLdtInstance`), composing
`Tensor2DMCA` across all folding round-levels `0 .. S.rounds` with
`StepMCAArity` for each round's `2 ^ (S.logArity i)`-ary fold.

## Main results

* `ClaimsFailMulti`: at some round-level `j ≤ S.rounds`, off-point claims fail.
* `rbrSound_tensorMulti`: full `(S.rounds + 2)`-round round-by-round soundness
  over `ChalTensorMulti S W M q`.
* `rbrSound_grind_tensorMulti`: full `(S.rounds + 2)`-round round-by-round
  soundness with proof-of-work grinding via `PcsRbr.rbrSound_grindDoomed`.
-/

namespace CertiFri.PcsRbr

open Polynomial Oracle

universe u v w w'

/-! ## Multi-arity failing claims and tensor batching round -/

section MultiClaims

variable {F : Type*} [Field F]

/-- Claims fail at some round-level `j ≤ S.rounds` of a multi-arity LDT instance. -/
def ClaimsFailMulti [DecidableEq F] (S : MultiLdtInstance F) (s : F) (θ : ℝ) {m : ℕ → ℕ}
    (claims : ∀ j, Fin (m j) → Claim F) : Prop :=
  ∃ j ≤ S.rounds, ¬ ClaimsHoldOff ((S.domain j).image (s * ·)) (S.degree j) θ (claims j)

/-- Multi-height tensor batching round for a multi-arity LDT instance: if
`ClaimsFailMulti` holds, at most an `ε₀` fraction of `r : TensorChal F W M`
makes every round-level's tensor reduced opening `θ`-close to its code. -/
theorem ClaimsFailMulti.fractionLE_close_tensor [Fintype F] [DecidableEq F]
    {S : MultiLdtInstance F} {s : F} {θ ε₀ : ℝ} {W M : ℕ} {m : ℕ → ℕ}
    {coord : ∀ j, Fin (m j) → Fin M × Fin W}
    {claims : ∀ j, Fin (m j) → Claim F}
    (h : ClaimsFailMulti S s θ claims) (hs : s ≠ 0)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {εα : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀) :
    FractionLE (fun r : TensorChal F W M => ∀ i ≤ S.rounds,
        CloseToCode (S.domain i) (S.degree i) θ (pcsInputTensor s coord claims r i)) ε₀ := by
  obtain ⟨j, hj, hfail⟩ := h
  obtain ⟨bad, hbad, hgood⟩ :=
    claims_of_reducedOpeningTensor_off_points (hmca j hj) (hinj j hj) (claims j)
  refine FractionLE.mono_right ⟨bad, hbad, fun r hr => ?_⟩ (hε j hj)
  by_contra hmem
  exact hfail (hgood r hmem ((closeToCode_image_mul hs _ _ θ _).mpr (hr j hj)))

end MultiClaims

/-! ## Challenges, accessors, and state function -/

section ChalTensorMulti

variable {F : Type u} [Field F]

/-- Round-`i` challenge type for multi-arity tensor-batched FRI:
* round `0`: `TensorChal F W M`;
* rounds `1 .. S.rounds`: folding challenge `F`;
* round `S.rounds + 1` (and beyond): `q` query points in `S.domain 0`. -/
def ChalTensorMulti (S : MultiLdtInstance F) (W M q : ℕ) (i : ℕ) : Type u :=
  if i = 0 then TensorChal F W M
  else if i ≤ S.rounds then F
  else (Fin q → ↥(S.domain 0))

variable {S : MultiLdtInstance F} {W M q i : ℕ}

def chalTensorMulti0 (h : i = 0) : ChalTensorMulti S W M q i ≃ TensorChal F W M :=
  Equiv.cast (ite_eq_left h)

def chalTensorMultiField (h0 : i ≠ 0) (hle : i ≤ S.rounds) : ChalTensorMulti S W M q i ≃ F :=
  Equiv.cast (by simp [ChalTensorMulti, h0, hle])

def chalTensorMultiQuery (h : ¬ i ≤ S.rounds) :
    ChalTensorMulti S W M q i ≃ (Fin q → ↥(S.domain 0)) :=
  Equiv.cast (by
    have h0 : i ≠ 0 := by omega
    simp [ChalTensorMulti, h0, h])

instance [Fintype F] : Fintype (ChalTensorMulti S W M q i) :=
  if h0 : i = 0 then Fintype.ofEquiv _ (chalTensorMulti0 h0).symm
  else if hle : i ≤ S.rounds then Fintype.ofEquiv _ (chalTensorMultiField h0 hle).symm
  else Fintype.ofEquiv _ (chalTensorMultiQuery hle).symm

instance [DecidableEq F] : DecidableEq (ChalTensorMulti S W M q i) :=
  if h0 : i = 0 then (chalTensorMulti0 h0).decidableEq
  else if hle : i ≤ S.rounds then (chalTensorMultiField h0 hle).decidableEq
  else (chalTensorMultiQuery hle).decidableEq

instance [Nonempty ↥(S.domain 0)] : Nonempty (ChalTensorMulti S W M q i) :=
  if h0 : i = 0 then (chalTensorMulti0 h0).nonempty
  else if hle : i ≤ S.rounds then (chalTensorMultiField h0 hle).nonempty
  else (chalTensorMultiQuery hle).nonempty

theorem ChalTensorMulti.nonempty (h : (S.domain 0).Nonempty) (W M q i : ℕ) :
    Nonempty (ChalTensorMulti S W M q i) :=
  haveI := h.to_subtype
  inferInstance

def ChalTensorMulti.tensor (ch : ChalTensorMulti S W M q i) : TensorChal F W M :=
  if h0 : i = 0 then chalTensorMulti0 h0 ch else (fun _ => 0, fun _ => 0)

def ChalTensorMulti.field (ch : ChalTensorMulti S W M q i) : F :=
  if h0 : i = 0 then 0
  else if hle : i ≤ S.rounds then chalTensorMultiField h0 hle ch
  else 0

def ChalTensorMulti.points (ch : ChalTensorMulti S W M q i) (j : Fin q) : F :=
  if hle : i ≤ S.rounds then 0 else (chalTensorMultiQuery hle ch j : F)

theorem ChalTensorMulti.tensor_of_zero (h0 : i = 0) (ch : ChalTensorMulti S W M q i) :
    ch.tensor = chalTensorMulti0 h0 ch :=
  dite_eq_left h0

theorem ChalTensorMulti.field_of_pos_le (h0 : i ≠ 0) (hle : i ≤ S.rounds)
    (ch : ChalTensorMulti S W M q i) : ch.field = chalTensorMultiField h0 hle ch := by
  simp [ChalTensorMulti.field, h0, hle]

theorem ChalTensorMulti.field_of_not_le (hle : ¬ i ≤ S.rounds)
    (ch : ChalTensorMulti S W M q i) : ch.field = 0 := by
  have h0 : i ≠ 0 := by omega
  simp [ChalTensorMulti.field, h0, hle]

theorem ChalTensorMulti.points_of_not_le (hle : ¬ i ≤ S.rounds)
    (ch : ChalTensorMulti S W M q i) (j : Fin q) :
    ch.points j = chalTensorMultiQuery hle ch j :=
  dite_eq_right hle

end ChalTensorMulti

section TensorMultiAccessors

variable {F : Type u} [Field F] {Msg' : Type w} {S : MultiLdtInstance F} {W M q : ℕ}

def tensorOfMulti : {i : ℕ} → Transcript Msg' (ChalTensorMulti S W M q) i → TensorChal F W M
  | _, .nil => (fun _ => 0, fun _ => 0)
  | _, .snoc (i := 0) _ _ ch => ch.tensor
  | _, .snoc (i := _ + 1) t _ _ => tensorOfMulti t

def betasOfTensorMulti : {i : ℕ} → Transcript Msg' (ChalTensorMulti S W M q) i → ℕ → F
  | _, .nil => 0
  | _, .snoc (i := 0) _ _ _ => 0
  | _, .snoc (i := k + 1) t _ ch => Function.update (betasOfTensorMulti t) k ch.field

def queriesOfTensorMulti : {i : ℕ} → Transcript Msg' (ChalTensorMulti S W M q) i → Fin q → F
  | _, .nil => 0
  | _, .snoc _ _ ch => ch.points

@[simp] theorem tensorOfMulti_snoc_zero (t : Transcript Msg' (ChalTensorMulti S W M q) 0)
    (msg : Msg') (ch : ChalTensorMulti S W M q 0) :
    tensorOfMulti (t.snoc msg ch) = ch.tensor := rfl

@[simp] theorem tensorOfMulti_snoc_succ {k : ℕ}
    (t : Transcript Msg' (ChalTensorMulti S W M q) (k + 1)) (msg : Msg')
    (ch : ChalTensorMulti S W M q (k + 1)) :
    tensorOfMulti (t.snoc msg ch) = tensorOfMulti t := rfl

@[simp] theorem betasOfTensorMulti_snoc_succ {k : ℕ}
    (t : Transcript Msg' (ChalTensorMulti S W M q) (k + 1)) (msg : Msg')
    (ch : ChalTensorMulti S W M q (k + 1)) :
    betasOfTensorMulti (t.snoc msg ch) = Function.update (betasOfTensorMulti t) k ch.field := rfl

@[simp] theorem queriesOfTensorMulti_snoc {i : ℕ}
    (t : Transcript Msg' (ChalTensorMulti S W M q) i) (msg : Msg')
    (ch : ChalTensorMulti S W M q i) :
    queriesOfTensorMulti (t.snoc msg ch) = ch.points := rfl

@[simp] theorem tensorOfMulti_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensorMulti S W M q) i),
      tensorOfMulti (t.mapIdx f) = tensorOfMulti t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => tensorOfMulti_mapIdx f t

@[simp] theorem betasOfTensorMulti_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensorMulti S W M q) i),
      betasOfTensorMulti (t.mapIdx f) = betasOfTensorMulti t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => by
    rw [Transcript.mapIdx_snoc, betasOfTensorMulti_snoc_succ, betasOfTensorMulti_snoc_succ,
      betasOfTensorMulti_mapIdx f t]

@[simp] theorem queriesOfTensorMulti_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensorMulti S W M q) i),
      queriesOfTensorMulti (t.mapIdx f) = queriesOfTensorMulti t
  | _, .nil => rfl
  | _, .snoc _ _ _ => rfl

end TensorMultiAccessors

section TensorMultiState

variable {F : Type u} [Field F] [DecidableEq F] {W M : ℕ} {m : ℕ → ℕ}

/-- Oracle-model acceptance for a multi-arity tensor-batched transcript. -/
def AcceptsTensorMulti (S : MultiLdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) {q i : ℕ}
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) i) : Prop :=
  IsCodeword (S.domain S.rounds) (S.degree S.rounds) (wordsOf t S.rounds) ∧
    ∀ j, QueryAcceptsMulti S (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
      (wordsOf t) (betasOfTensorMulti t) (queriesOfTensorMulti t j)

/-- Round-by-round state function for multi-arity tensor-batched FRI. -/
def doomedTensorMulti (S : MultiLdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) (θ : ℝ) (q : ℕ) :
    ∀ i, Transcript (Msg F m) (ChalTensorMulti S W M q) i → Prop
  | 0, _ => True
  | i + 1, t =>
    ClaimsFailMulti S s θ (claimsOf t) →
      if i ≤ S.rounds then
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
          (wordsOf t) (betasOfTensorMulti t) i
      else
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
          (wordsOf t) (betasOfTensorMulti t) S.rounds ∧
          ¬ AcceptsTensorMulti S s coord t

theorem doomedTensorMulti_zero (S : MultiLdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) (θ : ℝ) (q : ℕ)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) 0) :
    doomedTensorMulti S s coord θ q 0 t :=
  trivial

variable {S : MultiLdtInstance F} {s : F} {coord : ∀ j, Fin (m j) → Fin M × Fin W}
  {θ : ℝ} {q : ℕ}

theorem doomedTensorMulti_of_not_claimsFail {i : ℕ}
    {t : Transcript (Msg F m) (ChalTensorMulti S W M q) i}
    (h : ¬ ClaimsFailMulti S s θ (claimsOf t)) :
    doomedTensorMulti S s coord θ q i t := by
  cases i with
  | zero => trivial
  | succ i => exact fun hf => absurd hf h

theorem doomedTensorMulti_succ_iff {k : ℕ} (hk : k ≤ S.rounds)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) (k + 1)) :
    doomedTensorMulti S s coord θ q (k + 1) t ↔
      (ClaimsFailMulti S s θ (claimsOf t) →
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
          (wordsOf t) (betasOfTensorMulti t) k) := by
  simp only [doomedTensorMulti, ite_eq_left hk]

theorem doomedTensorMulti_succ_iff_of_lt {k : ℕ} (hk : S.rounds < k)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) (k + 1)) :
    doomedTensorMulti S s coord θ q (k + 1) t ↔
      (ClaimsFailMulti S s θ (claimsOf t) →
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
          (wordsOf t) (betasOfTensorMulti t) S.rounds ∧
          ¬ AcceptsTensorMulti S s coord t) := by
  simp only [doomedTensorMulti, ite_eq_right (Nat.not_le.mpr hk)]

theorem not_doomedTensorMulti_of_accepts
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) (S.rounds + 2))
    (hfail : ClaimsFailMulti S s θ (claimsOf t)) (hacc : AcceptsTensorMulti S s coord t) :
    ¬ doomedTensorMulti S s coord θ q (S.rounds + 2) t := fun hd =>
  ((doomedTensorMulti_succ_iff_of_lt (Nat.lt_succ_self _) t).mp hd hfail).2 hacc

theorem not_grindDoomedTensorMulti_of_accepts {bits : ℕ → ℕ}
    (t : Transcript (Msg F m) (GrindChal bits (ChalTensorMulti S W M q)) (S.rounds + 2))
    (hpow : PowPasses t) (hfail : ClaimsFailMulti S s θ (claimsOf (ungrind t)))
    (hacc : AcceptsTensorMulti S s coord (ungrind t)) :
    ¬ grindDoomed bits (doomedTensorMulti S s coord θ q) (S.rounds + 2) t :=
  not_grindDoomed hpow (not_doomedTensorMulti_of_accepts (ungrind t) hfail hacc)

theorem grindDoomedTensorMulti_nil (bits : ℕ → ℕ) :
    grindDoomed bits (doomedTensorMulti S s coord θ q) 0 .nil :=
  grindDoomed_nil (doomedTensorMulti_zero S s coord θ q .nil)

end TensorMultiState

/-! ## Round-by-round soundness -/

section TensorMultiRounds

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  {S : MultiLdtInstance F} {s : F} {W M q : ℕ} {m : ℕ → ℕ}
  {coord : ∀ j, Fin (m j) → Fin M × Fin W} {θ : ℝ}

theorem fractionLE_tensorMulti (hs : s ≠ 0)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {εα : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) 0) (msg : Msg F m) :
    FractionLE (fun ch : ChalTensorMulti S W M q 0 =>
      ¬ doomedTensorMulti S s coord θ q 1 (t.snoc msg ch)) ε₀ := by
  have h0 : (0 : ℕ) ≤ S.rounds := Nat.zero_le _
  by_cases hf : ClaimsFailMulti S s θ msg.claims
  · refine fractionLE_of_equiv (chalTensorMulti0 rfl)
      (hf.fractionLE_close_tensor hs hinj hmca hε) fun ch hch i hi => ?_
    by_contra hfar
    refine hch ((doomedTensorMulti_succ_iff h0 _).mpr fun _ =>
      (S.doomed_zero_iff θ _ _ _).mpr ⟨i, hi, ?_⟩)
    rwa [claimsOf_snoc_zero, tensorOfMulti_snoc_zero, ChalTensorMulti.tensor_of_zero rfl]
  · have hnonneg : 0 ≤ ε₀ :=
      (nonneg_of_tensor2DMCA (hmca 0 (Nat.zero_le _))).trans (hε 0 (Nat.zero_le _))
    exact (FractionLE.false.mono_right hnonneg).mono_left fun ch hch =>
      hch (doomedTensorMulti_of_not_claimsFail hf)

theorem fractionLE_fold_tensorMulti {k : ℕ} (hk : k < S.rounds) {ε : ℝ}
    (hstep : StepMCAArity (2 ^ S.logArity k) (S.zeta k) (S.domain k) (S.domain (k + 1))
      (S.degree (k + 1)) θ ε)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) (k + 1)) (msg : Msg F m)
    (hd : doomedTensorMulti S s coord θ q (k + 1) t) :
    FractionLE (fun ch : ChalTensorMulti S W M q (k + 1) =>
      ¬ doomedTensorMulti S s coord θ q (k + 2) (t.snoc msg ch)) ε := by
  classical
  have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hk1 : k + 1 ≤ S.rounds := hk
  by_cases hf : ClaimsFailMulti S s θ (claimsOf t)
  · have hdk := ((doomedTensorMulti_succ_iff hk.le t).mp hd hf).congr
      (c' := Function.update (wordsOf t) k msg.word) (β' := betasOfTensorMulti t)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun _ _ => rfl)
    refine fractionLE_of_equiv (chalTensorMultiField hk0 hk1)
      (fractionLE_iff_card_filter.mpr (hdk.card_escape_le (hstep _))) fun ch hch hgood => hch ?_
    rw [doomedTensorMulti_succ_iff hk1]
    intro _
    rwa [claimsOf_snoc_succ, tensorOfMulti_snoc_succ, wordsOf_snoc_succ,
      betasOfTensorMulti_snoc_succ, ChalTensorMulti.field_of_pos_le hk0 hk1]
  · exact (FractionLE.false.mono_right (nonneg_of_stepMCAArity hstep)).mono_left fun ch hch =>
      hch (doomedTensorMulti_of_not_claimsFail hf)

theorem fractionLE_query_tensorMulti (hθ : 0 ≤ θ)
    (t : Transcript (Msg F m) (ChalTensorMulti S W M q) (S.rounds + 1)) (msg : Msg F m)
    (hd : doomedTensorMulti S s coord θ q (S.rounds + 1) t) :
    FractionLE (fun ch : ChalTensorMulti S W M q (S.rounds + 1) =>
      ¬ doomedTensorMulti S s coord θ q (S.rounds + 2) (t.snoc msg ch)) (θ ^ q) := by
  classical
  have hR : ¬ S.rounds + 1 ≤ S.rounds := Nat.not_succ_le_self _
  have hθq : 0 ≤ θ ^ q := pow_nonneg hθ q
  have hsnoc : ∀ ch : ChalTensorMulti S W M q (S.rounds + 1),
      doomedTensorMulti S s coord θ q (S.rounds + 2) (t.snoc msg ch) ↔
        (ClaimsFailMulti S s θ (claimsOf t) →
          S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
              (Function.update (wordsOf t) S.rounds msg.word)
              (Function.update (betasOfTensorMulti t) S.rounds 0) S.rounds ∧
            ¬ (IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word ∧
              ∀ j, QueryAcceptsMulti S (pcsInputTensor s coord (claimsOf t) (tensorOfMulti t))
                (Function.update (wordsOf t) S.rounds msg.word)
                (Function.update (betasOfTensorMulti t) S.rounds 0)
                (chalTensorMultiQuery hR ch j))) := by
    intro ch
    rw [doomedTensorMulti_succ_iff_of_lt (Nat.lt_succ_self _)]
    simp only [AcceptsTensorMulti, claimsOf_snoc_succ, tensorOfMulti_snoc_succ, wordsOf_snoc_succ,
      betasOfTensorMulti_snoc_succ, queriesOfTensorMulti_snoc,
      ChalTensorMulti.field_of_not_le hR, ChalTensorMulti.points_of_not_le hR,
      Function.update_self]
  by_cases hf : ClaimsFailMulti S s θ (claimsOf t)
  · have hdR := ((doomedTensorMulti_succ_iff le_rfl t).mp hd hf).congr
      (c' := Function.update (wordsOf t) S.rounds msg.word)
      (β' := Function.update (betasOfTensorMulti t) S.rounds 0)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun j hj => Function.update_of_ne hj.ne _ _)
    by_cases hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word
    · have hcount := hdR.card_accepting_queries_le (by rwa [Function.update_self]) q
      refine fractionLE_of_equiv (chalTensorMultiQuery hR) (fractionLE_iff_card_filter.mpr
        (hcount.trans_eq ?_)) fun ch hch => ?_
      · rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, Nat.cast_pow, mul_pow]
      · by_contra hrej
        exact hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hrej hacc.2⟩)
    · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
        hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hfinal hacc.1⟩)
  · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
      hch (doomedTensorMulti_of_not_claimsFail hf)

/-- **Round-by-round soundness of multi-arity tensor-batched FRI.** -/
theorem rbrSound_tensorMulti (S : MultiLdtInstance F) {s : F} (hs : s ≠ 0)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCAArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (εβ i)) :
    RbrSound (S.rounds + 2) (doomedTensorMulti S s coord θ q)
      (roundErrorTensor S.rounds ε₀ εβ θ q) := by
  intro i hi t msg hd
  rcases i with _ | k
  · exact fractionLE_tensorMulti hs hinj hmca hε t msg
  · rcases Nat.lt_or_ge k S.rounds with hk | hk
    · rw [roundErrorTensor_succ_of_lt hk]
      exact fractionLE_fold_tensorMulti hk (hstep k hk) t msg hd
    · obtain rfl : k = S.rounds := by omega
      rw [roundErrorTensor_last]
      exact fractionLE_query_tensorMulti hθ t msg hd

theorem roundErrorTensorMulti_nonneg (S : MultiLdtInstance F) {s : F} {θ : ℝ} (hθ : 0 ≤ θ)
    (q : ℕ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCAArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (εβ i)) (i : ℕ) :
    0 ≤ roundErrorTensor S.rounds ε₀ εβ θ q i := by
  rcases i with _ | k
  · exact (nonneg_of_tensor2DMCA (hmca 0 (Nat.zero_le _))).trans (hε 0 (Nat.zero_le _))
  · by_cases hk : k < S.rounds
    · rw [roundErrorTensor_succ_of_lt hk]
      exact nonneg_of_stepMCAArity (hstep k hk)
    · rw [roundErrorTensor_succ_of_not_lt hk]
      exact pow_nonneg hθ q

/-- **Round-by-round soundness of multi-arity tensor-batched FRI with proof-of-work grinding.** -/
theorem rbrSound_grind_tensorMulti (S : MultiLdtInstance F) {s : F} (hs : s ≠ 0)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ) (bits : ℕ → ℕ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCAArity (2 ^ S.logArity i) (S.zeta i) (S.domain i) (S.domain (i + 1))
        (S.degree (i + 1)) θ (εβ i)) :
    RbrSound (S.rounds + 2) (grindDoomed bits (doomedTensorMulti S s coord θ q))
      (fun i => roundErrorTensor S.rounds ε₀ εβ θ q i / 2 ^ bits i) :=
  rbrSound_grindDoomed (rbrSound_tensorMulti S hs coord hinj hθ q hmca hε hstep)
    (fun i _ => roundErrorTensorMulti_nonneg S hθ q hmca hε hstep i) bits

end TensorMultiRounds

end CertiFri.PcsRbr
