import CertiFriProofs.Theory.PcsRbr.Grinding
import CertiFriProofs.Theory.ProximityGap.TensorMCA

/-!
# Round-by-round soundness of tensor-batched FRI (`FriBatching::Tensor`)

Tensor-batched counterpart of `Theory/PcsRbr.lean`, composing `Tensor2DMCA`
(`Theory/ProximityGap/TensorMCA.lean`) across all folding heights `0 .. S.rounds`
under one shared multilinear tensor challenge schedule
`r = (rCol, rOpen) : TensorChal F W M`.

## Protocol

Fixed: the domains and degree bounds `S : LdtInstance F` (`R = S.rounds`), the coset
shift `s ≠ 0`, global batching bounds `W` (maximum matrix width) and `M` (maximum
opening groups per height), the number `m j` of flat claims at each level `j`, an
injective coordinate map `coord j : Fin (m j) → Fin M × Fin W` assigning each claim
of level `j` its `(openingIdx, colIdx)` slot, the agreement threshold `θ`, and the
query count `q`.

* **Round `0`.** The prover sends the claims of every level (`PcsRbr.Msg.claims`).
  The verifier replies with `r = (rCol, rOpen) : TensorChal F W M`, where
  `kCol = tensorNumChallenges W` and `kOpen = tensorNumChallenges M`. Claim `k` of
  level `j` enters the level-`j` reduced opening with weight
  `tensorWeight rOpen (coord j k).1 * tensorWeight rCol (coord j k).2`.
* **Rounds `1 + i` (`i < R`).** Identical to `Theory/PcsRbr.lean`: prover sends
  word `c i`, verifier replies with `β i : F`.
* **Round `R + 1`.** Identical to `Theory/PcsRbr.lean`: prover sends final word
  `c R`, verifier replies with `q` query points of `S.domain 0`.

## Main results

* `claims_of_reducedOpeningTensor_off_points`: from `Tensor2DMCA D d W M θ ε` and
  injectivity of `coord`, outside an `ε` fraction of `r : TensorChal F W M`,
  `CloseToCode D d θ (reducedOpeningTensor coord r claims)` implies
  `ClaimsHoldOff D d θ claims`.
* `ClaimsFail.fractionLE_close_tensor`: if `ClaimsFail S s θ claims` holds, then
  at most an `ε₀` fraction of `r : TensorChal F W M` makes every level's tensor
  reduced opening `θ`-close to its code, where `ε₀` upper-bounds the single-level
  `Tensor2DMCA` error across `j ≤ S.rounds` (tighter than summing across heights
  because only one failing level is needed).
* `rbrSound_tensor` and `rbrSound_grind_tensor`: full `(S.rounds + 2)`-round
  round-by-round soundness (without and with proof-of-work grinding via
  `PcsRbr.rbrSound_grindDoomed`).
-/

namespace CertiFri.PcsRbr

open Polynomial Oracle

universe u v w w'

section TensorDefs

variable {F : Type u} [Field F]

/-- Round-0 challenge space for 2D tensor batching with maximum width `W` and
maximum opening groups per height `M`: `kCol` column challenges followed by
`kOpen` opening-group challenges. -/
abbrev TensorChal (F : Type u) (W M : ℕ) : Type u :=
  (Fin (Fri.tensorNumChallenges W) → F) × (Fin (Fri.tensorNumChallenges M) → F)

/-- Combined 2D multilinear weight `w_open[o] * w_col[c]` for slot `(o, c)`. -/
def tensorCoordWeight {W M : ℕ} (r : TensorChal F W M) (coord : Fin M × Fin W) : F :=
  tensorWeight r.2 ⟨coord.1.val, lt_two_pow_tensorNumChallenges coord.1.isLt⟩ *
    tensorWeight r.1 ⟨coord.2.val, lt_two_pow_tensorNumChallenges coord.2.isLt⟩

/-- Tensor-batched reduced opening at a single height: claim `k` at coordinate
`(o, c) = coord k` enters with weight `w_open[o] * w_col[c]`. -/
def reducedOpeningTensor {W M m : ℕ} (coord : Fin m → Fin M × Fin W) (r : TensorChal F W M)
    (claims : Fin m → Claim F) (x : F) : F :=
  ∑ k : Fin m,
    tensorCoordWeight r (coord k) * quotientAt (claims k).f (claims k).z (claims k).y x

/-- The level-`j` input function to the low-degree test under tensor batching,
shifted back from the coset `s * D_j` to the subgroup `D_j`. -/
def pcsInputTensor {W M : ℕ} {m : ℕ → ℕ} (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W)
    (claims : ∀ j, Fin (m j) → Claim F) (r : TensorChal F W M) (j : ℕ) (x : F) : F :=
  reducedOpeningTensor (coord j) r (claims j) (s * x)

end TensorDefs

/-! ## Off-point quotient soundness from `Tensor2DMCA` -/

section TensorQuotient

variable {F : Type*} [Field F]

/-- The error parameter of any `Tensor2DMCA` instance is nonnegative. -/
theorem nonneg_of_tensor2DMCA [Fintype F] {D : Finset F} {d W M : ℕ} {θ ε : ℝ}
    (h : Tensor2DMCA D d W M θ ε) : 0 ≤ ε := by
  obtain ⟨bad, hbad, -⟩ := h (fun _ _ _ => 0)
  have hpos : (0 : ℝ) < Fintype.card (TensorChal F W M) := by
    have : Nonempty (TensorChal F W M) := ⟨(fun _ => 0, fun _ => 0)⟩
    exact_mod_cast Fintype.card_pos
  exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg bad.card).trans hbad) hpos

/-- Monotonicity of `Tensor2DMCA` in its error parameter. -/
theorem tensor2DMCA_mono_error [Fintype F] {D : Finset F} {d W M : ℕ} {θ ε ε' : ℝ}
    (h : Tensor2DMCA D d W M θ ε) (hle : ε ≤ ε') : Tensor2DMCA D d W M θ ε' := by
  intro u
  obtain ⟨bad, hbad, hgood⟩ := h u
  exact ⟨bad, hbad.trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _)), hgood⟩

/-- **Single-height off-point quotient soundness from `Tensor2DMCA`.**
For any injective assignment `coord : Fin m → Fin M × Fin W` of claims to 2D
`(openingIdx, colIdx)` slots, outside an `ε` fraction of `r : TensorChal F W M`,
closeness of `reducedOpeningTensor coord r claims` to the code implies
`ClaimsHoldOff D d θ claims`. -/
theorem claims_of_reducedOpeningTensor_off_points [Fintype F] [DecidableEq F]
    {D : Finset F} {d W M m : ℕ} {θ ε : ℝ}
    (hmca : Tensor2DMCA D d W M θ ε)
    {coord : Fin m → Fin M × Fin W} (hinj : Function.Injective coord)
    (claims : Fin m → Claim F) :
    ∃ bad : Finset (TensorChal F W M),
      (bad.card : ℝ) ≤ ε * Fintype.card (TensorChal F W M) ∧
      ∀ r ∉ bad, CloseToCode D d θ (reducedOpeningTensor coord r claims) →
        ClaimsHoldOff D d θ claims := by
  classical
  let u : Fin M → Fin W → F → F := fun o c x =>
    if h : ∃ k : Fin m, coord k = (o, c) then
      quotientAt (claims h.choose).f (claims h.choose).z (claims h.choose).y x
    else 0
  have hu_at : ∀ (k : Fin m) (x : F),
      u (coord k).1 (coord k).2 x =
        quotientAt (claims k).f (claims k).z (claims k).y x := by
    intro k x
    have hex : ∃ k' : Fin m, coord k' = ((coord k).1, (coord k).2) := ⟨k, rfl⟩
    simp only [u, dite_eq_left hex]
    have hk : hex.choose = k := hinj hex.choose_spec
    rw [hk]
  have hsum_eq : ∀ (r : TensorChal F W M) (x : F),
      (∑ o : Fin M,
        tensorWeight r.2 ⟨o.val, lt_two_pow_tensorNumChallenges o.isLt⟩ *
          ∑ c : Fin W,
            tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩ * u o c x) =
      reducedOpeningTensor coord r claims x := by
    intro r x
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    have hsub : (∑ p : Fin M × Fin W,
          tensorWeight r.2 ⟨p.1.val, lt_two_pow_tensorNumChallenges p.1.isLt⟩ *
            (tensorWeight r.1 ⟨p.2.val, lt_two_pow_tensorNumChallenges p.2.isLt⟩ *
              u p.1 p.2 x)) =
        ∑ p ∈ (Finset.univ : Finset (Fin m)).image coord,
          tensorWeight r.2 ⟨p.1.val, lt_two_pow_tensorNumChallenges p.1.isLt⟩ *
            (tensorWeight r.1 ⟨p.2.val, lt_two_pow_tensorNumChallenges p.2.isLt⟩ *
              u p.1 p.2 x) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun p _ hp => ?_).symm
      have hnot : ¬ ∃ k : Fin m, coord k = (p.1, p.2) := by
        rintro ⟨k, hk⟩
        exact hp (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩)
      simp [u, hnot]
    rw [hsub, Finset.sum_image (fun a _ b _ hab => hinj hab)]
    unfold reducedOpeningTensor tensorCoordWeight
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hu_at k x, mul_assoc]
  obtain ⟨bad, hbad, h⟩ := hmca u
  refine ⟨bad, hbad, fun r hr ⟨p, hp, B, hBD, hB, hagree⟩ => ?_⟩
  have hagree' : ∀ x ∈ B,
      (∑ o : Fin M,
        tensorWeight r.2 ⟨o.val, lt_two_pow_tensorNumChallenges o.isLt⟩ *
          ∑ c : Fin W,
            tensorWeight r.1 ⟨c.val, lt_two_pow_tensorNumChallenges c.isLt⟩ * u o c x) =
      p.eval x := by
    intro x hx
    rw [hsum_eq r x]
    exact hagree x hx
  obtain ⟨v, hv, hu⟩ := h r hr p hp B hBD hB hagree'
  refine ⟨B, hBD, hB, fun k => ?_⟩
  obtain ⟨P, hP, hPz, hPB⟩ := exists_poly_of_quotient (B := B.erase (claims k).z)
    (hv (coord k).1 (coord k).2) (Finset.notMem_erase _ _) fun x hx => by
      have hux := hu (coord k).1 (coord k).2 x (Finset.mem_of_mem_erase hx)
      rwa [hu_at k x] at hux
  exact ⟨P, hP, hPz, fun x hx hne => hPB x (Finset.mem_erase.mpr ⟨hne, hx⟩)⟩

/-- **Multi-height tensor batching round.** Assume `Tensor2DMCA` on the coset of
every level `j ≤ S.rounds` with error `εα j ≤ ε₀`. If `ClaimsFail S s θ claims`
holds, at most an `ε₀` fraction of `r : TensorChal F W M` makes every level's
tensor reduced opening `θ`-close to its code. -/
theorem ClaimsFail.fractionLE_close_tensor [Fintype F] [DecidableEq F]
    {S : LdtInstance F} {s : F} {θ ε₀ : ℝ} {W M : ℕ} {m : ℕ → ℕ}
    {coord : ∀ j, Fin (m j) → Fin M × Fin W}
    {claims : ∀ j, Fin (m j) → Claim F}
    (h : ClaimsFail S s θ claims) (hs : s ≠ 0)
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

end TensorQuotient

/-! ## Challenges, accessors, and state function -/

section ChalTensor

variable {F : Type u} [Field F]

/-- The challenge type of round `i` in the tensor-batched protocol:
* round `0`: `TensorChal F W M`;
* rounds `1 .. S.rounds`: a folding challenge `F`;
* round `S.rounds + 1` (and beyond): `q` query points of `S.domain 0`. -/
def ChalTensor (S : LdtInstance F) (W M q : ℕ) (i : ℕ) : Type u :=
  if i = 0 then TensorChal F W M
  else if i ≤ S.rounds then F
  else (Fin q → ↥(S.domain 0))

variable {S : LdtInstance F} {W M q i : ℕ}

/-- Round `0` challenge is a tensor challenge pair `(rCol, rOpen)`. -/
def chalTensor0 (h : i = 0) : ChalTensor S W M q i ≃ TensorChal F W M :=
  Equiv.cast (ite_eq_left h)

/-- Round `i` with `0 < i ≤ S.rounds` has a field-element folding challenge. -/
def chalTensorField (h0 : i ≠ 0) (hle : i ≤ S.rounds) : ChalTensor S W M q i ≃ F :=
  Equiv.cast (by simp [ChalTensor, h0, hle])

/-- Round `i > S.rounds` has a `q`-tuple of query points. -/
def chalTensorQuery (h : ¬ i ≤ S.rounds) : ChalTensor S W M q i ≃ (Fin q → ↥(S.domain 0)) :=
  Equiv.cast (by
    have h0 : i ≠ 0 := by omega
    simp [ChalTensor, h0, h])

/-- The tensor challenge types are finite. -/
instance [Fintype F] : Fintype (ChalTensor S W M q i) :=
  if h0 : i = 0 then Fintype.ofEquiv _ (chalTensor0 h0).symm
  else if hle : i ≤ S.rounds then Fintype.ofEquiv _ (chalTensorField h0 hle).symm
  else Fintype.ofEquiv _ (chalTensorQuery hle).symm

/-- Equality of tensor challenges is decidable. -/
instance [DecidableEq F] : DecidableEq (ChalTensor S W M q i) :=
  if h0 : i = 0 then (chalTensor0 h0).decidableEq
  else if hle : i ≤ S.rounds then (chalTensorField h0 hle).decidableEq
  else (chalTensorQuery hle).decidableEq

/-- The tensor challenge types are nonempty when `S.domain 0` is. -/
instance [Nonempty ↥(S.domain 0)] : Nonempty (ChalTensor S W M q i) :=
  if h0 : i = 0 then (chalTensor0 h0).nonempty
  else if hle : i ≤ S.rounds then (chalTensorField h0 hle).nonempty
  else (chalTensorQuery hle).nonempty

/-- The tensor challenge types are nonempty when `S.domain 0` is. -/
theorem ChalTensor.nonempty (h : (S.domain 0).Nonempty) (W M q i : ℕ) :
    Nonempty (ChalTensor S W M q i) :=
  haveI := h.to_subtype
  inferInstance

/-- The round-`0` tensor challenge; zero tuples in other rounds. -/
def ChalTensor.tensor (ch : ChalTensor S W M q i) : TensorChal F W M :=
  if h0 : i = 0 then chalTensor0 h0 ch else (fun _ => 0, fun _ => 0)

/-- The folding challenge of a round `0 < i ≤ S.rounds`; zero otherwise. -/
def ChalTensor.field (ch : ChalTensor S W M q i) : F :=
  if h0 : i = 0 then 0
  else if hle : i ≤ S.rounds then chalTensorField h0 hle ch
  else 0

/-- The query points of a query round (`i > S.rounds`); zero otherwise. -/
def ChalTensor.points (ch : ChalTensor S W M q i) (j : Fin q) : F :=
  if hle : i ≤ S.rounds then 0 else (chalTensorQuery hle ch j : F)

theorem ChalTensor.tensor_of_zero (h0 : i = 0) (ch : ChalTensor S W M q i) :
    ch.tensor = chalTensor0 h0 ch :=
  dite_eq_left h0

theorem ChalTensor.field_of_pos_le (h0 : i ≠ 0) (hle : i ≤ S.rounds)
    (ch : ChalTensor S W M q i) : ch.field = chalTensorField h0 hle ch := by
  simp [ChalTensor.field, h0, hle]

theorem ChalTensor.field_of_not_le (hle : ¬ i ≤ S.rounds) (ch : ChalTensor S W M q i) :
    ch.field = 0 := by
  have h0 : i ≠ 0 := by omega
  simp [ChalTensor.field, h0, hle]

theorem ChalTensor.points_of_not_le (hle : ¬ i ≤ S.rounds) (ch : ChalTensor S W M q i)
    (j : Fin q) : ch.points j = chalTensorQuery hle ch j :=
  dite_eq_right hle

end ChalTensor

section TensorAccessors

variable {F : Type u} [Field F] {Msg' : Type w} {S : LdtInstance F} {W M q : ℕ}

/-- The tensor batching challenge `(rCol, rOpen)` of a transcript: the challenge of round `0`. -/
def tensorOf : {i : ℕ} → Transcript Msg' (ChalTensor S W M q) i → TensorChal F W M
  | _, .nil => (fun _ => 0, fun _ => 0)
  | _, .snoc (i := 0) _ _ ch => ch.tensor
  | _, .snoc (i := _ + 1) t _ _ => tensorOf t

/-- The folding challenges of a tensor-batched transcript: `betasOfTensor t k` is the
challenge of round `1 + k`, and zero if no such round exists or it is a query round. -/
def betasOfTensor : {i : ℕ} → Transcript Msg' (ChalTensor S W M q) i → ℕ → F
  | _, .nil => 0
  | _, .snoc (i := 0) _ _ _ => 0
  | _, .snoc (i := k + 1) t _ ch => Function.update (betasOfTensor t) k ch.field

/-- The query points of a tensor-batched transcript: those of its last challenge. -/
def queriesOfTensor : {i : ℕ} → Transcript Msg' (ChalTensor S W M q) i → Fin q → F
  | _, .nil => 0
  | _, .snoc _ _ ch => ch.points

@[simp] theorem tensorOf_snoc_zero (t : Transcript Msg' (ChalTensor S W M q) 0)
    (msg : Msg') (ch : ChalTensor S W M q 0) :
    tensorOf (t.snoc msg ch) = ch.tensor := rfl

@[simp] theorem tensorOf_snoc_succ {k : ℕ} (t : Transcript Msg' (ChalTensor S W M q) (k + 1))
    (msg : Msg') (ch : ChalTensor S W M q (k + 1)) :
    tensorOf (t.snoc msg ch) = tensorOf t := rfl

@[simp] theorem betasOfTensor_snoc_succ {k : ℕ}
    (t : Transcript Msg' (ChalTensor S W M q) (k + 1)) (msg : Msg')
    (ch : ChalTensor S W M q (k + 1)) :
    betasOfTensor (t.snoc msg ch) = Function.update (betasOfTensor t) k ch.field := rfl

@[simp] theorem queriesOfTensor_snoc {i : ℕ} (t : Transcript Msg' (ChalTensor S W M q) i)
    (msg : Msg') (ch : ChalTensor S W M q i) :
    queriesOfTensor (t.snoc msg ch) = ch.points := rfl

@[simp] theorem tensorOf_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensor S W M q) i), tensorOf (t.mapIdx f) = tensorOf t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => tensorOf_mapIdx f t

@[simp] theorem betasOfTensor_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensor S W M q) i),
      betasOfTensor (t.mapIdx f) = betasOfTensor t
  | _, .nil => rfl
  | _, .snoc (i := 0) _ _ _ => rfl
  | _, .snoc (i := _ + 1) t _ _ => by
    rw [Transcript.mapIdx_snoc, betasOfTensor_snoc_succ, betasOfTensor_snoc_succ,
      betasOfTensor_mapIdx f t]

@[simp] theorem queriesOfTensor_mapIdx {Msg'' : Type w'} (f : ℕ → Msg' → Msg'') :
    ∀ {i : ℕ} (t : Transcript Msg' (ChalTensor S W M q) i),
      queriesOfTensor (t.mapIdx f) = queriesOfTensor t
  | _, .nil => rfl
  | _, .snoc _ _ _ => rfl

end TensorAccessors

/-! ## State function and round-by-round soundness -/

section TensorState

variable {F : Type u} [Field F] [DecidableEq F] {W M : ℕ} {m : ℕ → ℕ}

/-- Oracle-model acceptance for a tensor-batched transcript: the final word is a
codeword of the last level, and every query accepts the fold chain starting from
`pcsInputTensor`. -/
def AcceptsTensor (S : LdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) {q i : ℕ}
    (t : Transcript (Msg F m) (ChalTensor S W M q) i) : Prop :=
  IsCodeword (S.domain S.rounds) (S.degree S.rounds) (wordsOf t S.rounds) ∧
    ∀ j, QueryAccepts S.rounds (pcsInputTensor s coord (claimsOf t) (tensorOf t))
      (wordsOf t) (betasOfTensor t) (queriesOfTensor t j)

/-- Round-by-round state function for tensor-batched FRI. -/
def doomedTensor (S : LdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) (θ : ℝ) (q : ℕ) :
    ∀ i, Transcript (Msg F m) (ChalTensor S W M q) i → Prop
  | 0, _ => True
  | i + 1, t =>
    ClaimsFail S s θ (claimsOf t) →
      if i ≤ S.rounds then
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOf t))
          (wordsOf t) (betasOfTensor t) i
      else
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOf t))
          (wordsOf t) (betasOfTensor t) S.rounds ∧
          ¬ AcceptsTensor S s coord t

/-- The empty tensor-batched transcript is doomed. -/
theorem doomedTensor_zero (S : LdtInstance F) (s : F)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W) (θ : ℝ) (q : ℕ)
    (t : Transcript (Msg F m) (ChalTensor S W M q) 0) :
    doomedTensor S s coord θ q 0 t :=
  trivial

variable {S : LdtInstance F} {s : F} {coord : ∀ j, Fin (m j) → Fin M × Fin W}
  {θ : ℝ} {q : ℕ}

theorem doomedTensor_of_not_claimsFail {i : ℕ}
    {t : Transcript (Msg F m) (ChalTensor S W M q) i}
    (h : ¬ ClaimsFail S s θ (claimsOf t)) : doomedTensor S s coord θ q i t := by
  cases i with
  | zero => trivial
  | succ i => exact fun hf => absurd hf h

theorem doomedTensor_succ_iff {k : ℕ} (hk : k ≤ S.rounds)
    (t : Transcript (Msg F m) (ChalTensor S W M q) (k + 1)) :
    doomedTensor S s coord θ q (k + 1) t ↔
      (ClaimsFail S s θ (claimsOf t) →
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOf t))
          (wordsOf t) (betasOfTensor t) k) := by
  simp only [doomedTensor, ite_eq_left hk]

theorem doomedTensor_succ_iff_of_lt {k : ℕ} (hk : S.rounds < k)
    (t : Transcript (Msg F m) (ChalTensor S W M q) (k + 1)) :
    doomedTensor S s coord θ q (k + 1) t ↔
      (ClaimsFail S s θ (claimsOf t) →
        S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOf t))
          (wordsOf t) (betasOfTensor t) S.rounds ∧
          ¬ AcceptsTensor S s coord t) := by
  simp only [doomedTensor, ite_eq_right (Nat.not_le.mpr hk)]

/-- A full tensor-batched transcript whose claims fail and on which the verifier
accepts is not doomed. -/
theorem not_doomedTensor_of_accepts
    (t : Transcript (Msg F m) (ChalTensor S W M q) (S.rounds + 2))
    (hfail : ClaimsFail S s θ (claimsOf t)) (hacc : AcceptsTensor S s coord t) :
    ¬ doomedTensor S s coord θ q (S.rounds + 2) t := fun hd =>
  ((doomedTensor_succ_iff_of_lt (Nat.lt_succ_self _) t).mp hd hfail).2 hacc

/-- With proof of work: a full transcript whose PoW checks pass, whose claims
fail, and on which the verifier accepts is not doomed. -/
theorem not_grindDoomedTensor_of_accepts {bits : ℕ → ℕ}
    (t : Transcript (Msg F m) (GrindChal bits (ChalTensor S W M q)) (S.rounds + 2))
    (hpow : PowPasses t) (hfail : ClaimsFail S s θ (claimsOf (ungrind t)))
    (hacc : AcceptsTensor S s coord (ungrind t)) :
    ¬ grindDoomed bits (doomedTensor S s coord θ q) (S.rounds + 2) t :=
  not_grindDoomed hpow (not_doomedTensor_of_accepts (ungrind t) hfail hacc)

/-- The empty transcript is doomed with proof of work. -/
theorem grindDoomedTensor_nil (bits : ℕ → ℕ) :
    grindDoomed bits (doomedTensor S s coord θ q) 0 .nil :=
  grindDoomed_nil (doomedTensor_zero S s coord θ q .nil)

end TensorState

/-! ## Round-by-round error bounds -/

/-- The error of each round of the tensor-batched protocol: `ε₀` for round `0`,
`εβ i` for folding round `1 + i` (`i < R`), and `θ ^ q` for query round `R + 1`. -/
def roundErrorTensor (R : ℕ) (ε₀ : ℝ) (εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) : ℕ → ℝ
  | 0 => ε₀
  | i + 1 => if i < R then εβ i else θ ^ q

@[simp] theorem roundErrorTensor_zero (R : ℕ) (ε₀ : ℝ) (εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundErrorTensor R ε₀ εβ θ q 0 = ε₀ := rfl

theorem roundErrorTensor_succ_of_lt {R i : ℕ} (h : i < R) (ε₀ : ℝ) (εβ : ℕ → ℝ) (θ : ℝ)
    (q : ℕ) : roundErrorTensor R ε₀ εβ θ q (i + 1) = εβ i :=
  ite_eq_left h

theorem roundErrorTensor_succ_of_not_lt {R i : ℕ} (h : ¬ i < R) (ε₀ : ℝ) (εβ : ℕ → ℝ) (θ : ℝ)
    (q : ℕ) : roundErrorTensor R ε₀ εβ θ q (i + 1) = θ ^ q :=
  ite_eq_right h

@[simp] theorem roundErrorTensor_last (R : ℕ) (ε₀ : ℝ) (εβ : ℕ → ℝ) (θ : ℝ) (q : ℕ) :
    roundErrorTensor R ε₀ εβ θ q (R + 1) = θ ^ q :=
  roundErrorTensor_succ_of_not_lt (Nat.lt_irrefl R) ε₀ εβ θ q

section TensorRounds

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
  {S : LdtInstance F} {s : F} {W M q : ℕ} {m : ℕ → ℕ}
  {coord : ∀ j, Fin (m j) → Fin M × Fin W} {θ : ℝ}

/-- Round `0` (tensor batching): at most an `ε₀` fraction of tensor schedules
escape the doomed state. -/
theorem fractionLE_tensor (hs : s ≠ 0)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {εα : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (t : Transcript (Msg F m) (ChalTensor S W M q) 0) (msg : Msg F m) :
    FractionLE (fun ch : ChalTensor S W M q 0 => ¬ doomedTensor S s coord θ q 1 (t.snoc msg ch))
      ε₀ := by
  have h0 : (0 : ℕ) ≤ S.rounds := Nat.zero_le _
  by_cases hf : ClaimsFail S s θ msg.claims
  · refine fractionLE_of_equiv (chalTensor0 rfl)
      (hf.fractionLE_close_tensor hs hinj hmca hε) fun ch hch i hi => ?_
    by_contra hfar
    refine hch ((doomedTensor_succ_iff h0 _).mpr fun _ =>
      (S.doomed_zero_iff θ _ _ _).mpr ⟨i, hi, ?_⟩)
    rwa [claimsOf_snoc_zero, tensorOf_snoc_zero, ChalTensor.tensor_of_zero rfl]
  · have hnonneg : 0 ≤ ε₀ :=
      (nonneg_of_tensor2DMCA (hmca 0 (Nat.zero_le _))).trans (hε 0 (Nat.zero_le _))
    exact (FractionLE.false.mono_right hnonneg).mono_left fun ch hch =>
      hch (doomedTensor_of_not_claimsFail hf)

/-- Folding round `k < S.rounds` of the tensor-batched protocol. -/
theorem fractionLE_fold_tensor {k : ℕ} (hk : k < S.rounds) {ε : ℝ}
    (hstep : StepMCA (S.domain k) (S.domain (k + 1)) (S.degree (k + 1)) θ ε)
    (t : Transcript (Msg F m) (ChalTensor S W M q) (k + 1)) (msg : Msg F m)
    (hd : doomedTensor S s coord θ q (k + 1) t) :
    FractionLE (fun ch : ChalTensor S W M q (k + 1) =>
      ¬ doomedTensor S s coord θ q (k + 2) (t.snoc msg ch)) ε := by
  classical
  have hk0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
  have hk1 : k + 1 ≤ S.rounds := hk
  by_cases hf : ClaimsFail S s θ (claimsOf t)
  · have hdk := ((doomedTensor_succ_iff hk.le t).mp hd hf).congr
      (c' := Function.update (wordsOf t) k msg.word) (β' := betasOfTensor t)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun _ _ => rfl)
    refine fractionLE_of_equiv (chalTensorField hk0 hk1)
      (fractionLE_iff_card_filter.mpr (hdk.card_escape_le (hstep _))) fun ch hch hgood => hch ?_
    rw [doomedTensor_succ_iff hk1]
    intro _
    rwa [claimsOf_snoc_succ, tensorOf_snoc_succ, wordsOf_snoc_succ, betasOfTensor_snoc_succ,
      ChalTensor.field_of_pos_le hk0 hk1]
  · exact (FractionLE.false.mono_right (Compose.nonneg_of_stepMCA hstep)).mono_left fun ch hch =>
      hch (doomedTensor_of_not_claimsFail hf)

/-- Query round `S.rounds + 1` of the tensor-batched protocol. -/
theorem fractionLE_query_tensor (hθ : 0 ≤ θ)
    (t : Transcript (Msg F m) (ChalTensor S W M q) (S.rounds + 1)) (msg : Msg F m)
    (hd : doomedTensor S s coord θ q (S.rounds + 1) t) :
    FractionLE (fun ch : ChalTensor S W M q (S.rounds + 1) =>
      ¬ doomedTensor S s coord θ q (S.rounds + 2) (t.snoc msg ch)) (θ ^ q) := by
  classical
  have hR : ¬ S.rounds + 1 ≤ S.rounds := Nat.not_succ_le_self _
  have hθq : 0 ≤ θ ^ q := pow_nonneg hθ q
  have hsnoc : ∀ ch : ChalTensor S W M q (S.rounds + 1),
      doomedTensor S s coord θ q (S.rounds + 2) (t.snoc msg ch) ↔
        (ClaimsFail S s θ (claimsOf t) →
          S.Doomed θ (pcsInputTensor s coord (claimsOf t) (tensorOf t))
              (Function.update (wordsOf t) S.rounds msg.word)
              (Function.update (betasOfTensor t) S.rounds 0) S.rounds ∧
            ¬ (IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word ∧
              ∀ j, QueryAccepts S.rounds (pcsInputTensor s coord (claimsOf t) (tensorOf t))
                (Function.update (wordsOf t) S.rounds msg.word)
                (Function.update (betasOfTensor t) S.rounds 0) (chalTensorQuery hR ch j))) := by
    intro ch
    rw [doomedTensor_succ_iff_of_lt (Nat.lt_succ_self _)]
    simp only [AcceptsTensor, claimsOf_snoc_succ, tensorOf_snoc_succ, wordsOf_snoc_succ,
      betasOfTensor_snoc_succ, queriesOfTensor_snoc, ChalTensor.field_of_not_le hR,
      ChalTensor.points_of_not_le hR, Function.update_self]
  by_cases hf : ClaimsFail S s θ (claimsOf t)
  · have hdR := ((doomedTensor_succ_iff le_rfl t).mp hd hf).congr
      (c' := Function.update (wordsOf t) S.rounds msg.word)
      (β' := Function.update (betasOfTensor t) S.rounds 0)
      (fun j hj => Function.update_of_ne hj.ne _ _) (fun j hj => Function.update_of_ne hj.ne _ _)
    by_cases hfinal : IsCodeword (S.domain S.rounds) (S.degree S.rounds) msg.word
    · have hcount := hdR.card_accepting_queries_le (by rwa [Function.update_self]) q
      refine fractionLE_of_equiv (chalTensorQuery hR) (fractionLE_iff_card_filter.mpr
        (hcount.trans_eq ?_)) fun ch hch => ?_
      · rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, Nat.cast_pow, mul_pow]
      · by_contra hrej
        exact hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hrej hacc.2⟩)
    · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
        hch ((hsnoc ch).mpr fun _ => ⟨hdR, fun hacc => hfinal hacc.1⟩)
  · exact (FractionLE.false.mono_right hθq).mono_left fun ch hch =>
      hch (doomedTensor_of_not_claimsFail hf)

/-- **Round-by-round soundness of tensor-batched FRI.** -/
theorem rbrSound_tensor (S : LdtInstance F) {s : F} (hs : s ≠ 0)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i)) :
    RbrSound (S.rounds + 2) (doomedTensor S s coord θ q)
      (roundErrorTensor S.rounds ε₀ εβ θ q) := by
  intro i hi t msg hd
  rcases i with _ | k
  · exact fractionLE_tensor hs hinj hmca hε t msg
  · rcases Nat.lt_or_ge k S.rounds with hk | hk
    · rw [roundErrorTensor_succ_of_lt hk]
      exact fractionLE_fold_tensor hk (hstep k hk) t msg hd
    · obtain rfl : k = S.rounds := by omega
      rw [roundErrorTensor_last]
      exact fractionLE_query_tensor hθ t msg hd

/-- Under the hypotheses of `rbrSound_tensor`, every round error is nonnegative. -/
theorem roundErrorTensor_nonneg (S : LdtInstance F) {s : F} {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ)
    {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i)) (i : ℕ) :
    0 ≤ roundErrorTensor S.rounds ε₀ εβ θ q i := by
  rcases i with _ | k
  · exact (nonneg_of_tensor2DMCA (hmca 0 (Nat.zero_le _))).trans (hε 0 (Nat.zero_le _))
  · by_cases hk : k < S.rounds
    · rw [roundErrorTensor_succ_of_lt hk]
      exact Compose.nonneg_of_stepMCA (hstep k hk)
    · rw [roundErrorTensor_succ_of_not_lt hk]
      exact pow_nonneg hθ q

/-- **Round-by-round soundness of tensor-batched FRI with proof-of-work grinding.** -/
theorem rbrSound_grind_tensor (S : LdtInstance F) {s : F} (hs : s ≠ 0)
    (coord : ∀ j, Fin (m j) → Fin M × Fin W)
    (hinj : ∀ j ≤ S.rounds, Function.Injective (coord j))
    {θ : ℝ} (hθ : 0 ≤ θ) (q : ℕ) (bits : ℕ → ℕ) {εα εβ : ℕ → ℝ} {ε₀ : ℝ}
    (hmca : ∀ j ≤ S.rounds, Tensor2DMCA ((S.domain j).image (s * ·)) (S.degree j) W M θ (εα j))
    (hε : ∀ j ≤ S.rounds, εα j ≤ ε₀)
    (hstep : ∀ i < S.rounds,
      StepMCA (S.domain i) (S.domain (i + 1)) (S.degree (i + 1)) θ (εβ i)) :
    RbrSound (S.rounds + 2) (grindDoomed bits (doomedTensor S s coord θ q))
      (fun i => roundErrorTensor S.rounds ε₀ εβ θ q i / 2 ^ bits i) :=
  rbrSound_grindDoomed (rbrSound_tensor S hs coord hinj hθ q hmca hε hstep)
    (fun i _ => roundErrorTensor_nonneg S hθ q hmca hε hstep i) bits

end TensorRounds

end CertiFri.PcsRbr
