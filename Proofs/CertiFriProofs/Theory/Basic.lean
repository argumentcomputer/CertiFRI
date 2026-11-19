import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The low-degree test: shared definitions

The definitions every part of the theory is stated in: Reed–Solomon codewords,
the folding step, the proximity hypotheses, and what one query of the verifier
checks. The theorems are in the sibling modules.

A function on an evaluation domain is a total function `F → F` of which only
the values on the domain matter. This keeps subtypes out of the statements.

The model is the binary-folding low-degree test of Plonky3's `verify_fri`
(`fri/src/verifier.rs`), in which inputs of smaller heights join the fold at the
round whose height matches theirs. It is an oracle model: the committed
codewords are functions, with no Merkle trees and no Fiat–Shamir.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Reed–Solomon codewords -/

/-- `f` agrees on `D` with a polynomial of degree below `d`: a codeword of the
Reed–Solomon code of dimension `d` on the evaluation domain `D`. -/
def IsCodeword (D : Finset F) (d : ℕ) (f : F → F) : Prop :=
  ∃ p : F[X], p.degree < d ∧ ∀ x ∈ D, f x = p.eval x

/-- `f` agrees with a codeword on at least a fraction `θ` of `D`. With
`θ = 1 - δ`, this says `f` is within relative distance `δ` of the code. -/
def CloseToCode (D : Finset F) (d : ℕ) (θ : ℝ) (f : F → F) : Prop :=
  ∃ p : F[X], p.degree < d ∧ ∃ B ⊆ D, θ * D.card ≤ B.card ∧ ∀ x ∈ B, f x = p.eval x

theorem IsCodeword.closeToCode {D : Finset F} {d : ℕ} {f : F → F} (h : IsCodeword D d f)
    {θ : ℝ} (hθ : θ ≤ 1) : CloseToCode D d θ f := by
  obtain ⟨p, hp, hf⟩ := h
  refine ⟨p, hp, D, Finset.Subset.refl D, ?_, hf⟩
  have : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
  nlinarith

/-! ## Folding

One round halves the domain by squaring. A function `f` on `D` splits as
`f x = e (x ^ 2) + x * o (x ^ 2)`, and its fold with challenge `β` is
`e + β * o` on the squares. The functions below take a point `x` of `D` and
return the value at `x ^ 2`, so no square root is ever chosen. -/

/-- The even part of `f` at `x ^ 2`. -/
def evenAt (f : F → F) (x : F) : F := (f x + f (-x)) / 2

/-- The odd part of `f` at `x ^ 2`. -/
def oddAt (f : F → F) (x : F) : F := (f x - f (-x)) / (2 * x)

/-- The fold of `f` with challenge `β`, at `x ^ 2`. This is the value Plonky3's
`fold_row` computes for arity two (`foldAt_eq_interpolate`). -/
def foldAt (f : F → F) (β x : F) : F := evenAt f x + β * oddAt f x

theorem evenAt_neg (f : F → F) (x : F) : evenAt f (-x) = evenAt f x := by
  simp only [evenAt, neg_neg, add_comm]

theorem oddAt_neg (f : F → F) (x : F) : oddAt f (-x) = oddAt f x := by
  simp only [oddAt, neg_neg, mul_neg, div_neg, ← neg_div, neg_sub]

/-- The fold depends on `x` only through `x ^ 2`. -/
theorem foldAt_neg (f : F → F) (β x : F) : foldAt f β (-x) = foldAt f β x := by
  simp only [foldAt, evenAt_neg, oddAt_neg]

/-- A function is its even part plus `x` times its odd part. -/
theorem evenAt_add_mul_oddAt (h2 : (2 : F) ≠ 0) (f : F → F) {x : F} (hx : x ≠ 0) :
    evenAt f x + x * oddAt f x = f x := by
  simp only [evenAt, oddAt]
  field_simp
  ring

/-- The fold is the value at `β` of the line through `(x, f x)` and
`(-x, f (-x))`, which is how Plonky3's `fold_row` computes it. -/
theorem foldAt_eq_interpolate (h2 : (2 : F) ≠ 0) (f : F → F) (β : F) {x : F} (hx : x ≠ 0) :
    foldAt f β x = f x + (β - x) * (f (-x) - f x) / (-x - x) := by
  have hxx : -x - x = -(2 * x) := by ring
  simp only [foldAt, evenAt, oddAt, hxx, div_neg]
  field_simp
  ring

/-- `D'` is the set of squares of `D`, and `D` is closed under negation, so
squaring is two-to-one from `D` onto `D'`. -/
structure SquareStep (D D' : Finset F) : Prop where
  two_ne_zero : (2 : F) ≠ 0
  ne_zero : ∀ x ∈ D, x ≠ 0
  neg_mem : ∀ x ∈ D, -x ∈ D
  sq_mem : ∀ x ∈ D, x ^ 2 ∈ D'
  exists_sq : ∀ y ∈ D', ∃ x ∈ D, x ^ 2 = y

/-! ## Proximity hypotheses

The soundness theorems take these as hypotheses. Each is a statement about
Reed–Solomon codes alone, with no protocol in it. -/

/-- Mutual correlated agreement for curves with `m` terms.

For all but an `ε` fraction of `β`: whenever `∑ k, β ^ k * u k` agrees with a
codeword on a set `B` holding at least a fraction `θ` of `D`, every `u k`
agrees with a codeword on that same `B`. -/
def CurveMCA [Fintype F] (D : Finset F) (d m : ℕ) (θ ε : ℝ) : Prop :=
  ∀ u : Fin m → F → F, ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
    ∀ β ∉ bad, ∀ p : F[X], p.degree < d → ∀ B ⊆ D, θ * D.card ≤ B.card →
      (∀ x ∈ B, ∑ k : Fin m, β ^ (k : ℕ) * u k x = p.eval x) →
      ∃ v : Fin m → F[X], (∀ k, (v k).degree < d) ∧ ∀ k, ∀ x ∈ B, u k x = (v k).eval x

/-- The challenge `β` is good for the committed function `c` on `D` and the
input `ro` on `D'`: whenever the fold of `c`, plus `β ^ 2` times `ro`, agrees
with a codeword on a set `B` holding at least a fraction `θ` of `D'`, then `c`
agrees with a codeword above `B` and `ro` agrees with a codeword on `B`.

`d'` is the degree bound on `D'`; the bound on `D` is twice that. -/
def GoodChallenge (D D' : Finset F) (d' : ℕ) (θ : ℝ) (ro c : F → F) (β : F) : Prop :=
  ∀ p : F[X], p.degree < d' → ∀ B ⊆ D', θ * D'.card ≤ B.card →
    (∀ x ∈ D, x ^ 2 ∈ B → foldAt c β x + β ^ 2 * ro (x ^ 2) = p.eval (x ^ 2)) →
    (∃ p₀ : F[X], p₀.degree < (2 * d' : ℕ) ∧ ∀ x ∈ D, x ^ 2 ∈ B → c x = p₀.eval x) ∧
    (∃ p₁ : F[X], p₁.degree < d' ∧ ∀ y ∈ B, ro y = p₁.eval y)

/-- Mutual correlated agreement for one folding round with the input `ro`
joining: whatever `c` the prover committed to, all but an `ε` fraction of the
challenges are good. -/
def StepMCAFor [Fintype F] (D D' : Finset F) (d' : ℕ) (θ ε : ℝ) (ro : F → F) : Prop :=
  ∀ c : F → F, ∃ bad : Finset F, (bad.card : ℝ) ≤ ε * Fintype.card F ∧
    ∀ β ∉ bad, GoodChallenge D D' d' θ ro c β

/-- `StepMCAFor` for every input. -/
def StepMCA [Fintype F] (D D' : Finset F) (d' : ℕ) (θ ε : ℝ) : Prop :=
  ∀ ro : F → F, StepMCAFor D D' d' θ ε ro

/-! ## The verifier's query

Level `i` is the domain after `i` folds. `ro i` is the input of that height
(the zero function when there is none), `c i` is the codeword the prover
committed to at level `i`, and `β i` is the challenge that folds level `i`
into level `i + 1`. After the last round the prover sends a polynomial in the
clear instead of a commitment; `c rounds` is its evaluation. -/

/-- The domains and degree bounds of one run. -/
structure LdtInstance (F : Type*) [Field F] where
  /-- Number of folding rounds. -/
  rounds : ℕ
  /-- The evaluation domain at each level. -/
  domain : ℕ → Finset F
  /-- The degree bound at each level. -/
  degree : ℕ → ℕ
  step : ∀ i < rounds, SquareStep (domain i) (domain (i + 1))
  degree_step : ∀ i < rounds, degree i = 2 * degree (i + 1)

/-- What the verifier checks on the query at `x`, a point of the first domain.

The first committed codeword carries the tallest input. At each round, the next
codeword (the final polynomial, after the last round) is the fold of the
current one plus `β ^ 2` times the input of the new height. This is the chain
of Plonky3's `fold_query` with every arity two, including the comparison with
the final polynomial. -/
def QueryAccepts (r : ℕ) (ro c : ℕ → F → F) (β : ℕ → F) (x : F) : Prop :=
  c 0 x = ro 0 x ∧
    ∀ i < r, c (i + 1) (x ^ 2 ^ (i + 1)) =
      foldAt (c i) (β i) (x ^ 2 ^ i) + β i ^ 2 * ro (i + 1) (x ^ 2 ^ (i + 1))

end CertiFri
