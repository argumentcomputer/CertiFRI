import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Inductions
import CertiFriProofs.Theory.Basic

/-!
# The algebra of folding

Every polynomial `p` splits as `e(X²) + X · o(X²)`. This file defines the two
parts, the fold `e + β · o` of a polynomial, and the inverse operation that
builds a polynomial from its two parts, with the degree bounds of each. It then
connects them to the pointwise operations `evenAt`, `oddAt` and `foldAt` of
`Basic.lean`: where a function agrees with `p` at `x` and at `-x`, its fold at
`x` is the value of the fold of `p` at `x ^ 2`.

The consequence for codes is `IsCodeword.fold`: folding a codeword of degree
bound `2 * d'` on `D` gives a codeword of degree bound `d'` on the squares of
`D`.

The pointwise statements assume `(2 : F) ≠ 0`, and `x ≠ 0` where the odd part
is involved. Nothing here is about distance from the code: the file covers
exact agreement only.
-/

namespace CertiFri

open Polynomial

variable {F : Type*} [Field F]

/-! ## Even and odd parts of a polynomial -/

/-- The even part of `p`: the polynomial `e` in `p = e(X²) + X · o(X²)`. Its
coefficients are the coefficients of `p` of even index. -/
noncomputable def evenPart (p : F[X]) : F[X] := contract 2 p

/-- The odd part of `p`: the polynomial `o` in `p = e(X²) + X · o(X²)`. Its
coefficients are the coefficients of `p` of odd index. -/
noncomputable def oddPart (p : F[X]) : F[X] := contract 2 (divX p)

/-- The coefficient of `X ^ n` in the even part is the coefficient of
`X ^ (2 * n)` in the polynomial. -/
theorem coeff_evenPart (p : F[X]) (n : ℕ) : (evenPart p).coeff n = p.coeff (2 * n) := by
  rw [evenPart, coeff_contract two_ne_zero, mul_comm]

/-- The coefficient of `X ^ n` in the odd part is the coefficient of
`X ^ (2 * n + 1)` in the polynomial. -/
theorem coeff_oddPart (p : F[X]) (n : ℕ) : (oddPart p).coeff n = p.coeff (2 * n + 1) := by
  rw [oddPart, coeff_contract two_ne_zero, coeff_divX, mul_comm]

/-- A polynomial is its even part at `X²` plus `X` times its odd part at `X²`. -/
theorem evenPart_comp_add_X_mul_oddPart_comp (p : F[X]) :
    (evenPart p).comp (X ^ 2) + X * (oddPart p).comp (X ^ 2) = p := by
  ext n
  rw [← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow, coeff_add]
  cases n with
  | zero =>
    rw [coeff_X_mul_zero, add_zero, coeff_expand two_pos, ite_eq_left (dvd_zero 2),
      coeff_evenPart, Nat.zero_div, mul_zero]
  | succ m =>
    rw [coeff_X_mul, coeff_expand two_pos, coeff_expand two_pos, coeff_evenPart, coeff_oddPart]
    by_cases h : 2 ∣ m
    · have h' : ¬ 2 ∣ m + 1 := by omega
      have hm : 2 * (m / 2) = m := by omega
      simp [h, h', hm]
    · have h' : 2 ∣ m + 1 := by omega
      have hm : 2 * ((m + 1) / 2) = m + 1 := by omega
      simp [h, h', hm]

/-- The even part of a polynomial of degree below `2 * d` has degree below `d`. -/
theorem degree_evenPart_lt {p : F[X]} {d : ℕ} (h : p.degree < (2 * d : ℕ)) :
    (evenPart p).degree < d := by
  rw [degree_lt_iff_coeff_zero] at h ⊢
  intro m hm
  rw [coeff_evenPart]
  exact h _ (by omega)

/-- The odd part of a polynomial of degree below `2 * d` has degree below `d`. -/
theorem degree_oddPart_lt {p : F[X]} {d : ℕ} (h : p.degree < (2 * d : ℕ)) :
    (oddPart p).degree < d := by
  rw [degree_lt_iff_coeff_zero] at h ⊢
  intro m hm
  rw [coeff_oddPart]
  exact h _ (by omega)

/-- Multiplying by a constant keeps a degree bound. -/
theorem Fold.degree_C_mul_lt (a : F) {p : F[X]} {d : ℕ} (h : p.degree < d) :
    (C a * p).degree < d := by
  rw [C_mul']
  exact (degree_smul_le a p).trans_lt h

/-- The fold of a polynomial: `e + β · o`. -/
noncomputable def foldPoly (β : F) (p : F[X]) : F[X] := evenPart p + C β * oddPart p

/-- The fold of a polynomial of degree below `2 * d` has degree below `d`. -/
theorem degree_foldPoly_lt {p : F[X]} {d : ℕ} (β : F) (h : p.degree < (2 * d : ℕ)) :
    (foldPoly β p).degree < d :=
  (degree_add_le _ _).trans_lt
    (max_lt (degree_evenPart_lt h) (Fold.degree_C_mul_lt β (degree_oddPart_lt h)))

/-- The polynomial with even part `v₀` and odd part `v₁`. -/
noncomputable def unfoldPoly (v₀ v₁ : F[X]) : F[X] := v₀.comp (X ^ 2) + X * v₁.comp (X ^ 2)

/-- A polynomial is the unfolding of its even and odd parts. -/
theorem unfoldPoly_evenPart_oddPart (p : F[X]) : unfoldPoly (evenPart p) (oddPart p) = p :=
  evenPart_comp_add_X_mul_oddPart_comp p

/-- The polynomial built from two parts of degree below `d` has degree below
`2 * d`. -/
theorem degree_unfoldPoly_lt {v₀ v₁ : F[X]} {d : ℕ} (h₀ : v₀.degree < d) (h₁ : v₁.degree < d) :
    (unfoldPoly v₀ v₁).degree < (2 * d : ℕ) := by
  rw [degree_lt_iff_coeff_zero] at h₀ h₁ ⊢
  intro m hm
  rw [unfoldPoly, ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow, coeff_add,
    coeff_expand two_pos]
  have h0 : (if 2 ∣ m then v₀.coeff (m / 2) else 0) = 0 := by
    split_ifs
    · exact h₀ _ (by omega)
    · rfl
  rw [h0, zero_add]
  cases m with
  | zero => exact coeff_X_mul_zero _
  | succ k =>
    rw [coeff_X_mul, coeff_expand two_pos]
    split_ifs
    · exact h₁ _ (by omega)
    · rfl

/-- The value of `unfoldPoly v₀ v₁` at `x` is `v₀ (x²) + x · v₁ (x²)`. -/
theorem eval_unfoldPoly (v₀ v₁ : F[X]) (x : F) :
    (unfoldPoly v₀ v₁).eval x = v₀.eval (x ^ 2) + x * v₁.eval (x ^ 2) := by
  simp [unfoldPoly, eval_comp]

/-- The value of a polynomial at `x` is its even part at `x²` plus `x` times its
odd part at `x²`. -/
theorem eval_eq_evenPart_add_mul_oddPart (p : F[X]) (x : F) :
    p.eval x = (evenPart p).eval (x ^ 2) + x * (oddPart p).eval (x ^ 2) := by
  rw [← eval_unfoldPoly, unfoldPoly_evenPart_oddPart]

/-! ## Pointwise folding -/

/-- Where `f` agrees with `p` at `x` and at `-x`, the even part of `f` at `x`
is the value of the even part of `p` at `x ^ 2`. -/
theorem evenAt_eq_eval_evenPart (h2 : (2 : F) ≠ 0) {f : F → F} {p : F[X]} {x : F}
    (h : f x = p.eval x) (h' : f (-x) = p.eval (-x)) :
    evenAt f x = (evenPart p).eval (x ^ 2) := by
  rw [evenAt, h, h', eval_eq_evenPart_add_mul_oddPart p x,
    eval_eq_evenPart_add_mul_oddPart p (-x), neg_sq]
  field_simp
  ring

/-- Where `f` agrees with `p` at `x ≠ 0` and at `-x`, the odd part of `f` at
`x` is the value of the odd part of `p` at `x ^ 2`. -/
theorem oddAt_eq_eval_oddPart (h2 : (2 : F) ≠ 0) {f : F → F} {p : F[X]} {x : F} (hx : x ≠ 0)
    (h : f x = p.eval x) (h' : f (-x) = p.eval (-x)) :
    oddAt f x = (oddPart p).eval (x ^ 2) := by
  rw [oddAt, h, h', eval_eq_evenPart_add_mul_oddPart p x,
    eval_eq_evenPart_add_mul_oddPart p (-x), neg_sq]
  field_simp
  ring

/-- Where `f` agrees with `p` at `x ≠ 0` and at `-x`, the fold of `f` at `x` is
the value of the fold of `p` at `x ^ 2`. -/
theorem foldAt_eq_eval_foldPoly (h2 : (2 : F) ≠ 0) {f : F → F} {p : F[X]} (β : F) {x : F}
    (hx : x ≠ 0) (h : f x = p.eval x) (h' : f (-x) = p.eval (-x)) :
    foldAt f β x = (foldPoly β p).eval (x ^ 2) := by
  rw [foldAt, evenAt_eq_eval_evenPart h2 h h', oddAt_eq_eval_oddPart h2 hx h h', foldPoly,
    eval_add, eval_mul, eval_C]

/-- A function whose even and odd parts at `x` are the values of `v₀` and `v₁`
takes the value of `unfoldPoly v₀ v₁` at `x`. -/
theorem eq_eval_unfoldPoly (h2 : (2 : F) ≠ 0) {f : F → F} {v₀ v₁ : F[X]} {x : F} (hx : x ≠ 0)
    (he : evenAt f x = v₀.eval (x ^ 2)) (ho : oddAt f x = v₁.eval (x ^ 2)) :
    f x = (unfoldPoly v₀ v₁).eval x := by
  rw [eval_unfoldPoly, ← he, ← ho, evenAt_add_mul_oddAt h2 f hx]

/-- Folding a codeword gives a codeword: if `f` is a codeword of degree bound
`2 * d'` on `D`, then any function whose value at each `x ^ 2` is the fold of
`f` at `x` is a codeword of degree bound `d'` on the squares of `D`. -/
theorem IsCodeword.fold {D D' : Finset F} (hstep : SquareStep D D') {d' : ℕ} {f : F → F}
    (hf : IsCodeword D (2 * d') f) (β : F) {g : F → F}
    (hg : ∀ x ∈ D, g (x ^ 2) = foldAt f β x) : IsCodeword D' d' g := by
  obtain ⟨p, hp, hfp⟩ := hf
  refine ⟨foldPoly β p, degree_foldPoly_lt β hp, fun y hy => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hstep.exists_sq y hy
  rw [hg x hx]
  exact foldAt_eq_eval_foldPoly hstep.two_ne_zero β (hstep.ne_zero x hx) (hfp x hx)
    (hfp (-x) (hstep.neg_mem x hx))

end CertiFri
