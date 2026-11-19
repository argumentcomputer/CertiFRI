import CertiFriProofs.Theory.Pcs
import CertiFriProofs.Theory.Oracle.BadEvent

/-!
# Claims whose opening points may lie in the coset

`Theory/Pcs.lean` proves the `α` round for fixed claims, under the hypothesis
that no opening point lies in the coset of its level. In the round-by-round
protocol of `Theory/PcsRbr.lean` the claims are a message of the prover. This
file proves the `α` round with no hypothesis on the opening points, for a
weaker notion of what it means for the claims to hold.

## Why there is no hypothesis on the opening points

The verifier does not check that the opening points avoid the cosets.
Plonky3's `open_inputs` rejects a proof only when a *query* point equals an
opening point (`OpeningPointMatchesQueryPoint`). A state function that treats
claims with an opening point in a coset like claims that hold gives a true
theorem, but that theorem says nothing about a proof with such claims, and the
verifier accepts such a proof unless a query hits the point.

Without the hypothesis, the quotient argument still gives everything except
the value of a claimed function at the opening point of its claim
(`claims_of_reducedOpening_off_points`). The verifier cannot know more: it
never reads the function there without rejecting. The condition on the claims
is weakened to match.

* `ClaimsHoldOff D d θ claims` is `ClaimsHold D d θ claims` with the agreement
  between a claimed function and its polynomial asked at the points of the
  dense set other than the opening point of the claim. The polynomial still
  takes the claimed value at the claimed point.
* `ClaimsFail S s θ claims`: at some level the claims do not hold in this
  sense. It is the condition under which the state function of
  `Theory/PcsRbr.lean` tracks the low-degree test.

When no opening point lies in the coset of its level, nothing changes:
`ClaimsHoldOff` is `ClaimsHold` (`claimsHoldOff_iff_claimsHold`) and
`ClaimsFail` is `PcsDoomed` (`claimsFail_iff_pcsDoomed`). In general
`ClaimsFail` implies `PcsDoomed` (`ClaimsFail.pcsDoomed`). A wrong value
claimed for a function that is a polynomial of degree at most `d` on the whole
coset makes the claims fail wherever the opening point is, as soon as
`d + 1 < θ * |D|` (`not_claimsHoldOff_of_eval_ne`).

## The `α` round

`ClaimsFail.fractionLE_close`: if the claims fail, at most a
`∑ j ∈ range (rounds + 1), εα j` fraction of the values of `α` make every
reduced opening `θ`-close to its code. The proof uses the error of one failing
level only; the sum is an upper bound for it.

## Assumptions and scope

`CurveMCA` on the coset of each level is a hypothesis, as in `Theory/Pcs.lean`.

In the model the quotient at an opening point is zero (division by zero), where
Plonky3 rejects the query. So on the queries Plonky3 does not reject, the model
reads the same reduced openings as Plonky3.

The degree slack of `ClaimsHold` remains: the polynomials have degree at most
`S.degree j`, one more than an honest polynomial has.
-/

namespace CertiFri.PcsRbr

open Polynomial Oracle

variable {F : Type*} [Field F]

/-! ## Holding away from the opening points -/

/-- The claims hold away from their opening points. There is a set holding a
fraction `θ` of `D` on which every claimed function agrees, except possibly at
the opening point of the claim, with a polynomial of degree at most `d` that
takes the claimed value at the claimed point. The set is common to all the
claims. -/
def ClaimsHoldOff (D : Finset F) (d : ℕ) (θ : ℝ) {m : ℕ} (claims : Fin m → Claim F) : Prop :=
  ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ k, ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
    P.eval (claims k).z = (claims k).y ∧ ∀ x ∈ B, x ≠ (claims k).z → (claims k).f x = P.eval x

/-- Claims that hold also hold away from their opening points. -/
theorem claimsHoldOff_of_claimsHold {D : Finset F} {d : ℕ} {θ : ℝ} {m : ℕ}
    {claims : Fin m → Claim F} (h : ClaimsHold D d θ claims) : ClaimsHoldOff D d θ claims := by
  obtain ⟨B, hBD, hB, hk⟩ := h
  refine ⟨B, hBD, hB, fun k => ?_⟩
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  exact ⟨P, hP, hPz, fun x hx _ => hPB x hx⟩

/-- When no opening point lies in `D`, holding away from the opening points is
holding. -/
theorem claimsHoldOff_iff_claimsHold {D : Finset F} {d : ℕ} {θ : ℝ} {m : ℕ}
    {claims : Fin m → Claim F} (hz : ∀ k, (claims k).z ∉ D) :
    ClaimsHoldOff D d θ claims ↔ ClaimsHold D d θ claims := by
  refine ⟨fun ⟨B, hBD, hB, hk⟩ => ⟨B, hBD, hB, fun k => ?_⟩, claimsHoldOff_of_claimsHold⟩
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  exact ⟨P, hP, hPz, fun x hx => hPB x hx fun e => hz k (e ▸ hBD hx)⟩

/-- A wrong value makes the claims fail, wherever the opening point is. Let the
function of claim `k` be, on all of `D`, a polynomial `P` of degree at most `d`
whose value at the claimed point is not the claimed value. If a set of density
`θ` has more than `d + 1` points, the claims do not hold away from their
opening points. -/
theorem not_claimsHoldOff_of_eval_ne {D : Finset F} {d : ℕ} {θ : ℝ} {m : ℕ}
    {claims : Fin m → Claim F} {k : Fin m} {P : F[X]} (hP : P.degree < (d + 1 : ℕ))
    (hf : ∀ x ∈ D, (claims k).f x = P.eval x) (hy : P.eval (claims k).z ≠ (claims k).y)
    (hθ : (d : ℝ) + 1 < θ * D.card) : ¬ ClaimsHoldOff D d θ claims := by
  classical
  rintro ⟨B, hBD, hB, h⟩
  obtain ⟨Q, hQ, hQz, hQB⟩ := h k
  have hcard : d + 1 ≤ (B.erase (claims k).z).card := by
    have h1 : d + 1 < B.card := by exact_mod_cast hθ.trans_le hB
    have h2 := Finset.pred_card_le_card_erase (s := B) (a := (claims k).z)
    omega
  have hPQ : P = Q := eq_of_degrees_lt_of_eval_finset_eq (B.erase (claims k).z)
    (hP.trans_le (by exact_mod_cast hcard)) (hQ.trans_le (by exact_mod_cast hcard))
    fun x hx => by
      rw [← hf x (hBD (Finset.mem_of_mem_erase hx)),
        hQB x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)]
  exact hy (hPQ ▸ hQz)

/-- The error of a level that satisfies `CurveMCA` is nonnegative. -/
theorem nonneg_of_curveMCA [Fintype F] {D : Finset F} {d n : ℕ} {θ ε : ℝ}
    (h : CurveMCA D d n θ ε) : 0 ≤ ε := by
  obtain ⟨bad, hbad, -⟩ := h fun _ _ => 0
  have hF : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  exact nonneg_of_mul_nonneg_left ((Nat.cast_nonneg bad.card).trans hbad) hF

/-! ## Claims that fail -/

/-- The claims fail: at some level they do not hold away from their opening
points. -/
def ClaimsFail [DecidableEq F] (S : LdtInstance F) (s : F) (θ : ℝ) {m : ℕ → ℕ}
    (claims : ∀ j, Fin (m j) → Claim F) : Prop :=
  ∃ j ≤ S.rounds, ¬ ClaimsHoldOff ((S.domain j).image (s * ·)) (S.degree j) θ (claims j)

variable [DecidableEq F] {S : LdtInstance F} {s : F} {θ : ℝ} {m : ℕ → ℕ}
  {claims : ∀ j, Fin (m j) → Claim F}

/-- Claims that fail are doomed in the sense of `Theory/Pcs.lean`: at some
level they do not hold. -/
theorem ClaimsFail.pcsDoomed (h : ClaimsFail S s θ claims) : PcsDoomed S s θ claims := by
  obtain ⟨j, hj, hfail⟩ := h
  exact ⟨j, hj, fun hhold => hfail (claimsHoldOff_of_claimsHold hhold)⟩

/-- When no opening point lies in the coset of its level, the claims fail
exactly when they are doomed in the sense of `Theory/Pcs.lean`. -/
theorem claimsFail_iff_pcsDoomed
    (hz : ∀ j ≤ S.rounds, ∀ k, (claims j k).z ∉ (S.domain j).image (s * ·)) :
    ClaimsFail S s θ claims ↔ PcsDoomed S s θ claims :=
  exists_congr fun j => and_congr_right fun hj =>
    not_congr (claimsHoldOff_iff_claimsHold (hz j hj))

/-- If the claims fail, `θ` is positive. -/
theorem ClaimsFail.pos (h : ClaimsFail S s θ claims) : 0 < θ :=
  h.pcsDoomed.pos

/-- The `α` round. Assume `CurveMCA` on the coset of every level, with error
`εα j` at level `j`. If the claims fail, at most a
`∑ j ∈ range (rounds + 1), εα j` fraction of the values of `α` make every input
of the low-degree test `θ`-close to its code. There is no hypothesis on the
opening points. -/
theorem ClaimsFail.fractionLE_close [Fintype F] (h : ClaimsFail S s θ claims) (hs : s ≠ 0)
    {εα : ℕ → ℝ}
    (hmca : ∀ j ≤ S.rounds, CurveMCA ((S.domain j).image (s * ·)) (S.degree j) (m j) θ (εα j)) :
    FractionLE (fun α : F => ∀ i ≤ S.rounds,
        CloseToCode (S.domain i) (S.degree i) θ (pcsInput s claims α i))
      (∑ j ∈ Finset.range (S.rounds + 1), εα j) := by
  obtain ⟨j, hj, hfail⟩ := h
  obtain ⟨bad, hbad, hgood⟩ := claims_of_reducedOpening_off_points (hmca j hj) (claims j)
  have hle : εα j ≤ ∑ j ∈ Finset.range (S.rounds + 1), εα j :=
    Finset.single_le_sum
      (fun i hi => nonneg_of_curveMCA (hmca i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  refine FractionLE.mono_right ⟨bad, hbad, fun α hα => ?_⟩ hle
  by_contra hmem
  exact hfail (hgood α hmem ((closeToCode_image_mul hs _ _ θ _).mpr (hα j hj)))

end CertiFri.PcsRbr
