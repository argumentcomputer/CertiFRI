import CertiFriProofs.Theory.Fold

/-!
# From mutual correlated agreement for curves to the folding step

`CurveMCA` is a statement about several functions on one domain: for most
challenges `β`, a set on which the curve `∑ k, β ^ k * u k` agrees with a
codeword is a set on which every `u k` agrees with a codeword. `StepMCA` is the
shape one folding round consumes: one committed function on `D`, one input on
the squares `D'`, and the conclusion that the committed function agrees with a
codeword above the set.

This file proves that the first gives the second, with the same agreement
threshold and the same error: `StepMCA.of_curveMCA` for three-term curves
(even part, odd part, input), and `StepMCAFor.zero_of_curveMCA` for two-term
curves when no input joins the round.

The only assumption besides `CurveMCA` is the `SquareStep` between the two
domains. Whether `CurveMCA` holds for given parameters is a question about
Reed–Solomon codes that this file does not address.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

namespace Fold

/-- Squaring from `D` onto `D'` has a section: a function choosing a square
root in `D` for every point of `D'`. -/
theorem exists_sqrt {D D' : Finset F} (hstep : SquareStep D D') :
    ∃ s : F → F, ∀ y ∈ D', s y ∈ D ∧ s y ^ 2 = y := by
  choose! s hs using hstep.exists_sq
  exact ⟨s, hs⟩

/-- Let `s` choose square roots. If the even and odd parts of `c`, read at the
chosen roots, agree with `v₀` and `v₁` on `B`, then `c` agrees with
`unfoldPoly v₀ v₁` at every point of `D` whose square is in `B`, whichever of
the two roots that point is. -/
theorem eq_eval_unfoldPoly_of_sqrt {D D' : Finset F} (hstep : SquareStep D D') {c s : F → F}
    (hs : ∀ y ∈ D', s y ∈ D ∧ s y ^ 2 = y) {B : Finset F} (hB : B ⊆ D') {v₀ v₁ : F[X]}
    (he : ∀ y ∈ B, evenAt c (s y) = v₀.eval y) (ho : ∀ y ∈ B, oddAt c (s y) = v₁.eval y)
    {x : F} (hx : x ∈ D) (hxB : x ^ 2 ∈ B) : c x = (unfoldPoly v₀ v₁).eval x := by
  have hparts : evenAt c x = evenAt c (s (x ^ 2)) ∧ oddAt c x = oddAt c (s (x ^ 2)) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hs _ (hB hxB)).2 with h | h
    · rw [h]
      exact ⟨rfl, rfl⟩
    · rw [h]
      exact ⟨(evenAt_neg c x).symm, (oddAt_neg c x).symm⟩
  exact eq_eval_unfoldPoly hstep.two_ne_zero (hstep.ne_zero x hx)
    (hparts.1.trans (he _ hxB)) (hparts.2.trans (ho _ hxB))

/-- The reduction behind both theorems of this file, for one challenge. Let `s`
choose square roots. Suppose that whenever `e + β * o + β ^ 2 * ro` agrees with
a codeword on a large set `B`, where `e` and `o` are the even and odd parts of
`c` read at the chosen roots, each of `e`, `o` and `ro` agrees with a codeword
on `B`. Then `β` is a good challenge for `c` and `ro`. -/
theorem goodChallenge_of_sqrt {D D' : Finset F} (hstep : SquareStep D D') {d' : ℕ} {θ : ℝ}
    {ro c s : F → F} {β : F} (hs : ∀ y ∈ D', s y ∈ D ∧ s y ^ 2 = y)
    (h : ∀ p : F[X], p.degree < d' → ∀ B ⊆ D', θ * D'.card ≤ B.card →
      (∀ y ∈ B, evenAt c (s y) + β * oddAt c (s y) + β ^ 2 * ro y = p.eval y) →
      ∃ v₀ v₁ v₂ : F[X], v₀.degree < d' ∧ v₁.degree < d' ∧ v₂.degree < d' ∧
        (∀ y ∈ B, evenAt c (s y) = v₀.eval y) ∧ (∀ y ∈ B, oddAt c (s y) = v₁.eval y) ∧
        ∀ y ∈ B, ro y = v₂.eval y) :
    GoodChallenge D D' d' θ ro c β := by
  intro p hp B hB hcard hfold
  obtain ⟨v₀, v₁, v₂, h₀, h₁, h₂, he, ho, hro⟩ := h p hp B hB hcard fun y hy => by
    obtain ⟨hsD, hsq⟩ := hs y (hB hy)
    have := hfold (s y) hsD (by rwa [hsq])
    rwa [hsq] at this
  exact ⟨⟨unfoldPoly v₀ v₁, degree_unfoldPoly_lt h₀ h₁, fun x hx hxB =>
    eq_eval_unfoldPoly_of_sqrt hstep hs hB he ho hx hxB⟩, v₂, h₂, hro⟩

end Fold

/-- Mutual correlated agreement for three-term curves on `D'` gives mutual
correlated agreement for the folding round from `D` to `D'`, with the same
threshold and error, whatever input joins. The three terms are the even part of
the committed function, its odd part, and the input. -/
theorem StepMCA.of_curveMCA [Fintype F] {D D' : Finset F} (hstep : SquareStep D D') {d' : ℕ}
    {θ ε : ℝ} (h : CurveMCA D' d' 3 θ ε) : StepMCA D D' d' θ ε := by
  intro ro c
  obtain ⟨s, hs⟩ := Fold.exists_sqrt hstep
  obtain ⟨bad, hbad, hgood⟩ := h ![fun y => evenAt c (s y), fun y => oddAt c (s y), ro]
  refine ⟨bad, hbad, fun β hβ => Fold.goodChallenge_of_sqrt hstep hs fun p hp B hB hcard hp' => ?_⟩
  obtain ⟨v, hv, huv⟩ := hgood β hβ p hp B hB hcard fun y hy => by
    simpa [Fin.sum_univ_three, add_assoc] using hp' y hy
  exact ⟨v 0, v 1, v 2, hv 0, hv 1, hv 2, huv 0, huv 1, huv 2⟩

/-- A round in which no input joins needs only two-term curves. -/
theorem StepMCAFor.zero_of_curveMCA [Fintype F] {D D' : Finset F} (hstep : SquareStep D D')
    {d' : ℕ} {θ ε : ℝ} (h : CurveMCA D' d' 2 θ ε) : StepMCAFor D D' d' θ ε (fun _ => 0) := by
  intro c
  obtain ⟨s, hs⟩ := Fold.exists_sqrt hstep
  obtain ⟨bad, hbad, hgood⟩ := h ![fun y => evenAt c (s y), fun y => oddAt c (s y)]
  refine ⟨bad, hbad, fun β hβ => Fold.goodChallenge_of_sqrt hstep hs fun p hp B hB hcard hp' => ?_⟩
  obtain ⟨v, hv, huv⟩ := hgood β hβ p hp B hB hcard fun y hy => by
    simpa [Fin.sum_univ_two] using hp' y hy
  refine ⟨v 0, v 1, 0, hv 0, hv 1, ?_, huv 0, huv 1, fun _ _ => (eval_zero).symm⟩
  rw [degree_zero]
  exact WithBot.bot_lt_coe d'

end CertiFri
