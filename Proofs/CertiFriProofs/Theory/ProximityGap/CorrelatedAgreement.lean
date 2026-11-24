import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# Correlated agreement in the unique-decoding regime: the statement

The Reed–Solomon code of the polynomials of degree below `d` on a domain `D`
corrects `e` errors uniquely when `2 * e + d ≤ D.card`. `CurveCA F T` is
correlated agreement for curves in that regime, with threshold `T`: if the
combination `∑ k, β ^ k * u k` is within `e` errors of the code for more than
`T D.card e m` values of `β`, then the `u k` agree with codewords outside one
common set of at most `e` points.

This file only states the property and fixes the threshold `udThreshold`. It
is proved in `ProximityGap/UniqueDecoding.lean`, and used, as a hypothesis, in
`ProximityGap/UniqueDecodingMCA.lean`.
-/

namespace CertiFri

open Polynomial

/-- **Correlated agreement for curves over Reed–Solomon codes, in the
unique-decoding regime**, with threshold `T`.

For every domain `D`, degree bound `d`, number of errors `e` with
`2 * e + d ≤ D.card`, and words `u 0, …, u (m - 1)`: if for more than
`T D.card e m` values of `β` the word `∑ k, β ^ k * u k` differs from some
polynomial of degree below `d` at no more than `e` points of `D`, then there
are polynomials `v k` of degree below `d` such that the points of `D` where
some `u k` differs from `v k` number at most `e`. -/
def CurveCA (F : Type*) [Field F] [DecidableEq F] (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (D : Finset F) (d e m : ℕ), 2 * e + d ≤ D.card → ∀ (u : Fin m → F → F) (G : Finset F),
    T D.card e m < G.card →
    (∀ β ∈ G, ∃ p : F[X], p.degree < d ∧
      (D.filter fun x => ∑ k : Fin m, β ^ (k : ℕ) * u k x ≠ p.eval x).card ≤ e) →
    ∃ v : Fin m → F[X], (∀ k, (v k).degree < d) ∧
      (D.filter fun x => ∃ k, u k x ≠ (v k).eval x).card ≤ e

/-- The threshold of the unique-decoding proximity gap proved here: for a
domain of `n` points, `e` errors and a curve of `m` terms,
`(m - 1) * (n + e)` exceptional parameters (linear in `n`, matching BCIKS). -/
def udThreshold (n e m : ℕ) : ℕ := (m - 1) * (n + e)

end CertiFri
