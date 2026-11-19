import CertiFriProofs.Theory.ProximityGap
import CertiFriProofs.Theory.PcsRbr.Claims

/-!
# Decoding a word, and what claims that hold say about the decoded polynomial

`ClaimsHoldOff D d θ claims` (`Theory/PcsRbr/Claims.lean`) gives, for every
claim, some polynomial of degree at most `d` that takes the claimed value at
the opening point and agrees with the claimed function on a large subset of
`D`, away from the opening point. The polynomial may depend on the claim. This
file shows that, inside the unique-decoding radius, it depends on the claimed
function alone: it is the polynomial the function decodes to.

* `decode D d θ f`: a polynomial of degree at most `d` that agrees with `f` on
  a subset of `D` holding all but one point of a fraction `θ` of `D`, if there
  is one, and zero otherwise. It is a choice, not an algorithm.
* `DecodeMargin D d θ`: the condition `D.card + d + 3 ≤ 2 * θ * D.card`, under
  which there is at most one such polynomial (`decode_eq`).
* `eval_decode_of_claimsHoldOff`: under the margin, if the claims hold away
  from their opening points, every claimed value is the value of the decoded
  polynomial of its function at the opening point.
* `Extracts`, `claimsFail_of_not_extracts`: the same for the levels of a
  low-degree test, in the contrapositive: if some claim of some level is not an
  evaluation of the decoded polynomial of its function, the claims fail
  (`PcsRbr.ClaimsFail`).

## The margin

Two subsets of `D` that each hold all but one point of a fraction `θ` of `D`
share at least `2 * θ * D.card - 2 - D.card` points. Under `DecodeMargin` that
is at least `d + 1`, and two polynomials of degree at most `d` that agree at
`d + 1` points are equal. The "all but one point" is the opening point of a
claim, where `ClaimsHoldOff` says nothing about the function. For `θ = 1 - δ`
and the rate `ρ = d / D.card` the margin reads `2 * δ + ρ + 3 / D.card ≤ 1`:
the unique-decoding radius `δ ≤ (1 - ρ) / 2`, less `3 / (2 * D.card)`.

## Assumptions and scope

Nothing is assumed beyond the margin, which is a hypothesis of every theorem
that needs it. There is no protocol and no probability here.

The degree bound of the decoded polynomial is that of `ClaimsHoldOff`: degree
at most `d`, one more than an honest polynomial has when `d` is the number of
its coefficients.

Not covered: decoding beyond the unique-decoding radius, where a word may be
close to several polynomials, and any algorithm that computes `decode`.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Decoding -/

/-- The margin for unique decoding: two sets that each hold all but one point of
a fraction `θ` of `D` share more than `d` points. -/
def DecodeMargin (D : Finset F) (d : ℕ) (θ : ℝ) : Prop :=
  (D.card : ℝ) + d + 3 ≤ 2 * θ * D.card

open Classical in
/-- The polynomial a word decodes to: a polynomial of degree at most `d` that
agrees with `f` on a subset `B` of `D` with `θ * D.card ≤ B.card + 1`, if there
is one, and zero otherwise. -/
noncomputable def decode (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) : F[X] :=
  if h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card + 1 ∧ ∀ x ∈ B, f x = P.eval x
  then Classical.choose h else 0

variable {D : Finset F} {d : ℕ} {θ : ℝ}

/-- The decoded polynomial has degree at most `d`. -/
theorem degree_decode_lt (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) :
    (decode D d θ f).degree < (d + 1 : ℕ) := by
  unfold decode
  split
  · next h => exact (Classical.choose_spec h).1
  · rw [degree_zero]
    exact WithBot.bot_lt_coe _

/-- Under the margin, the decoded polynomial is any polynomial that qualifies. -/
theorem decode_eq (hm : DecodeMargin D d θ) {f : F → F} {P : F[X]} (hP : P.degree < (d + 1 : ℕ))
    {B : Finset F} (hB : B ⊆ D) (hcard : θ * D.card ≤ B.card + 1) (hf : ∀ x ∈ B, f x = P.eval x) :
    decode D d θ f = P := by
  have h : ∃ P : F[X], P.degree < (d + 1 : ℕ) ∧
      ∃ B ⊆ D, θ * D.card ≤ B.card + 1 ∧ ∀ x ∈ B, f x = P.eval x := ⟨P, hP, B, hB, hcard, hf⟩
  obtain ⟨hQ, B', hB', hcard', hf'⟩ := Classical.choose_spec h
  rw [decode, dite_eq_left h]
  refine eq_of_agree_of_card hQ hP hB' hB ?_ hf' hf
  have hle : ((D.card + (d + 1) : ℕ) : ℝ) ≤ ((B'.card + B.card : ℕ) : ℝ) := by
    unfold DecodeMargin at hm
    push_cast
    linarith
  exact Nat.cast_le.mp hle

open Classical in
/-- The decoded polynomial depends on the word only through its values on `D`. -/
theorem decode_congr {f g : F → F} (D : Finset F) (d : ℕ) (θ : ℝ) (h : ∀ x ∈ D, f x = g x) :
    decode D d θ f = decode D d θ g := by
  have hpred : (fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card + 1 ∧ ∀ x ∈ B, f x = P.eval x) =
      fun P : F[X] => P.degree < (d + 1 : ℕ) ∧
        ∃ B ⊆ D, θ * D.card ≤ B.card + 1 ∧ ∀ x ∈ B, g x = P.eval x := by
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

/-- Claims that hold are evaluations of the decoded polynomials. Under the
margin, if the claims hold away from their opening points, the value of every
claim is the value at its opening point of the polynomial its function decodes
to, and that polynomial has degree at most `d`. -/
theorem eval_decode_of_claimsHoldOff (hm : DecodeMargin D d θ) {m : ℕ} {claims : Fin m → Claim F}
    (h : PcsRbr.ClaimsHoldOff D d θ claims) (k : Fin m) :
    (decode D d θ (claims k).f).eval (claims k).z = (claims k).y ∧
      (decode D d θ (claims k).f).degree < (d + 1 : ℕ) := by
  classical
  refine ⟨?_, degree_decode_lt D d θ _⟩
  obtain ⟨B, hBD, hB, hk⟩ := h
  obtain ⟨P, hP, hPz, hPB⟩ := hk k
  have hcard : θ * D.card ≤ (B.erase (claims k).z).card + 1 := by
    have h1 : (B.card : ℝ) ≤ ((B.erase (claims k).z).card + 1 : ℕ) := by
      have := Finset.pred_card_le_card_erase (s := B) (a := (claims k).z)
      exact_mod_cast (by omega : B.card ≤ (B.erase (claims k).z).card + 1)
    push_cast at h1
    exact hB.trans h1
  rw [decode_eq hm hP ((Finset.erase_subset _ _).trans hBD) hcard fun x hx =>
    hPB x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)]
  exact hPz

/-! ## The levels of a low-degree test -/

variable [DecidableEq F] {S : LdtInstance F} {s : F} {m : ℕ → ℕ}
  {claims : ∀ j, Fin (m j) → Claim F}

/-- Every claim of every level up to the last round is an evaluation of the
polynomial its function decodes to, on the coset of its level. -/
def Extracts (S : LdtInstance F) (s : F) (θ : ℝ) {m : ℕ → ℕ}
    (claims : ∀ j, Fin (m j) → Claim F) : Prop :=
  ∀ j ≤ S.rounds, ∀ k : Fin (m j),
    (decode ((S.domain j).image (s * ·)) (S.degree j) θ (claims j k).f).eval (claims j k).z =
      (claims j k).y

/-- If some claim is not an evaluation of its decoded polynomial, the claims
fail. The margin is asked at the levels that have a claim. -/
theorem claimsFail_of_not_extracts
    (hm : ∀ j ≤ S.rounds, m j ≠ 0 → DecodeMargin ((S.domain j).image (s * ·)) (S.degree j) θ)
    (h : ¬ Extracts S s θ claims) : PcsRbr.ClaimsFail S s θ claims := by
  by_contra hfail
  refine h fun j hj k => ?_
  have hmj : m j ≠ 0 := fun h0 => (h0 ▸ k).elim0
  have hhold : PcsRbr.ClaimsHoldOff ((S.domain j).image (s * ·)) (S.degree j) θ (claims j) :=
    not_not.mp fun hn => hfail ⟨j, hj, hn⟩
  exact (eval_decode_of_claimsHoldOff (hm j hj hmj) hhold k).1

/-- Claims that do not fail are evaluations of the decoded polynomials. -/
theorem extracts_of_not_claimsFail
    (hm : ∀ j ≤ S.rounds, m j ≠ 0 → DecodeMargin ((S.domain j).image (s * ·)) (S.degree j) θ)
    (h : ¬ PcsRbr.ClaimsFail S s θ claims) : Extracts S s θ claims :=
  not_not.mp fun hne => h (claimsFail_of_not_extracts hm hne)

end CertiFri
