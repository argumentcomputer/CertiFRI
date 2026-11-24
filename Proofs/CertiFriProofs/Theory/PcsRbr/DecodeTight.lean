import CertiFriProofs.Theory.ProximityGap
import CertiFriProofs.Theory.PcsRbr.Claims

/-!
# Decoding a word with no slack, for opening points outside the coset

`Theory/PcsRbr/Decode.lean` decodes a word to the polynomial that agrees with
it on all but one point of a fraction `θ` of `D`. The point left out is the
opening point of a claim, where `ClaimsHoldOff` (`Theory/PcsRbr/Claims.lean`)
says nothing about the claimed function, and it costs a margin of
`D.card + d + 3 ≤ 2 * θ * D.card`, which fails on small sets `D` whatever the
rate. This file decodes with no point left out. The margin is then a condition
on the rate alone, and the price is a hypothesis: the opening point of the
claim is not in `D`.

* `decodeT D d θ f`: a polynomial of degree at most `d` that agrees with `f` on
  a subset of `D` holding a fraction `θ` of `D`, if there is one, and zero
  otherwise. It is a choice, not an algorithm.
* `StrictMargin D d θ`: the condition `D.card + d < 2 * θ * D.card`, under
  which there is at most one such polynomial (`decodeT_eq`).
* `eval_decodeT_of_claimsHoldOff`: under the margin, if the claims hold away
  from their opening points and the opening point of a claim is not in `D`, the
  claimed value is the value of the decoded polynomial of its function at the
  opening point.

## The margin

Two subsets of `D` that each hold a fraction `θ` of `D` share at least
`2 * θ * D.card - D.card` points. Under `StrictMargin` that is more than `d`,
and two polynomials of degree at most `d` that agree at `d + 1` points are
equal. For `θ = 1 - δ` and the rate `ρ = d / D.card` the margin reads
`2 * δ + ρ < 1`: the unique-decoding radius `δ < (1 - ρ) / 2`, for a set `D` of
any size.

## Assumptions and scope

Nothing is assumed beyond the margin and, in `eval_decodeT_of_claimsHoldOff`,
that the opening point is not in `D`. Both are hypotheses of the theorems that
need them. There is no protocol and no probability here: a caller whose opening
points are random pays for the second hypothesis with the probability that a
point lands in `D`.

The degree bound of the decoded polynomial is that of `ClaimsHoldOff`: degree
at most `d`, one more than an honest polynomial has when `d` is the number of
its coefficients.

Not covered: claims whose opening point is in `D` (`decode` of
`Theory/PcsRbr/Decode.lean` covers them, under its larger margin), decoding
beyond the unique-decoding radius, and any algorithm that computes `decodeT`.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Decoding -/

/-- The strict margin for unique decoding: two sets that each hold a fraction
`θ` of `D` share more than `d` points. -/
def StrictMargin (D : Finset F) (d : ℕ) (θ : ℝ) : Prop :=
  (D.card : ℝ) + d < 2 * θ * D.card

open Classical in
/-- The polynomial a word decodes to, with no point left out: a polynomial of
degree at most `d` that agrees with `f` on a subset `B` of `D` with
`θ * D.card ≤ B.card`, if there is one, and zero otherwise. -/
noncomputable def decodeT (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) : F[X] :=
  if h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x
  then Classical.choose h else 0

variable {D : Finset F} {d : ℕ} {θ : ℝ}

/-- The decoded polynomial has degree at most `d`. -/
theorem degree_decodeT_lt (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) :
    (decodeT D d θ f).degree < (d + 1 : ℕ) := by
  unfold decodeT
  split
  · next h => exact (Classical.choose_spec h).1
  · rw [degree_zero]
    exact WithBot.bot_lt_coe _

/-- Under the strict margin, the decoded polynomial is any polynomial that
qualifies: two subsets of `D` that each hold a fraction `θ` of `D` share more
than `d` points. -/
theorem decodeT_eq (hm : StrictMargin D d θ) {f : F → F} {P : F[X]} (hP : P.degree < (d + 1 : ℕ))
    {B : Finset F} (hB : B ⊆ D) (hcard : θ * D.card ≤ B.card) (hf : ∀ x ∈ B, f x = P.eval x) :
    decodeT D d θ f = P := by
  have h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x := ⟨P, hP, B, hB, hcard, hf⟩
  obtain ⟨hQ, B', hB', hcard', hf'⟩ := Classical.choose_spec h
  rw [decodeT, dite_eq_left h]
  refine eq_of_agree_of_card hQ hP hB' hB ?_ hf' hf
  have hlt : ((D.card + d : ℕ) : ℝ) < ((B'.card + B.card : ℕ) : ℝ) := by
    unfold StrictMargin at hm
    push_cast
    linarith
  have := Nat.cast_lt.mp hlt
  omega

open Classical in
/-- The decoded polynomial depends on the word only through its values on `D`. -/
theorem decodeT_congr {f g : F → F} (D : Finset F) (d : ℕ) (θ : ℝ) (h : ∀ x ∈ D, f x = g x) :
    decodeT D d θ f = decodeT D d θ g := by
  have hpred : (fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = P.eval x) =
      fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, g x = P.eval x := by
    funext P
    refine propext (and_congr_right fun _ => exists_congr fun B => and_congr_right fun hB =>
      and_congr_right fun _ => forall₂_congr fun x hx => ?_)
    rw [h x (hB hx)]
  have key : ∀ p q : F[X] → Prop, p = q →
      (if h : ∃ P, p P then Classical.choose h else (0 : F[X])) =
        if h : ∃ P, q P then Classical.choose h else 0 := by
    rintro p q rfl
    rfl
  exact key _ _ hpred

/-! ## Claims that hold -/

/-- Claims that hold are evaluations of the decoded polynomials, at the opening
points outside `D`. Under the strict margin, if the claims hold away from their
opening points and the opening point of claim `k` is not in `D`, the value of
claim `k` is the value at its opening point of the polynomial its function
decodes to. -/
theorem eval_decodeT_of_claimsHoldOff (hm : StrictMargin D d θ) {m : ℕ} {claims : Fin m → Claim F}
    (h : PcsRbr.ClaimsHoldOff D d θ claims) (k : Fin m) (hz : (claims k).z ∉ D) :
    (decodeT D d θ (claims k).f).eval (claims k).z = (claims k).y := by
  obtain ⟨B, hBD, hB, hk⟩ := h
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  rw [decodeT_eq hm hP hBD hB fun x hx => hPB x hx fun e => hz (e ▸ hBD hx)]
  exact hPz

end CertiFri
