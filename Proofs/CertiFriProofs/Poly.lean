import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import CertiFri.Poly
import CertiFriProofs.Refines

/-!
# The final polynomial

The executable verifier evaluates the final polynomial by Horner's rule on the
coefficient array the proof carries. In the model that array is a polynomial of
degree below its length, and the executable evaluation is its evaluation
(`Refines.horner_eq_eval`).
-/

namespace CertiFri

open Polynomial

variable {F K : Type} [FieldOps F] [Field K]

/-- The polynomial with the given coefficients, lowest degree first. -/
noncomputable def polyOfCoeffs : List K → K[X]
  | [] => 0
  | c :: cs => C c + X * polyOfCoeffs cs

theorem coeff_polyOfCoeffs : ∀ (cs : List K) (i : ℕ), (polyOfCoeffs cs).coeff i = cs.getD i 0
  | [], i => by simp [polyOfCoeffs]
  | c :: cs, 0 => by simp [polyOfCoeffs]
  | c :: cs, i + 1 => by simp [polyOfCoeffs, coeff_polyOfCoeffs cs i]

/-- A coefficient list of length `n` is a polynomial of degree below `n`. -/
theorem degree_polyOfCoeffs_lt (cs : List K) : (polyOfCoeffs cs).degree < cs.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyOfCoeffs]
  simp [hm]

theorem eval_polyOfCoeffs (x : K) :
    ∀ cs : List K, (polyOfCoeffs cs).eval x = cs.foldr (fun c acc => acc * x + c) 0
  | [] => by simp [polyOfCoeffs]
  | c :: cs => by
    simp only [polyOfCoeffs, eval_add, eval_C, eval_mul, eval_X, List.foldr_cons,
      eval_polyOfCoeffs x cs]
    ring

/-- Horner's rule commutes with the abstraction map. -/
theorem Refines.map_foldr_horner (r : Refines F K) (x : F) :
    ∀ cs : List F,
      r.toModel (cs.foldr (fun c acc => acc * x + c) 0)
        = (cs.map r.toModel).foldr (fun c acc => acc * r.toModel x + c) 0
  | [] => r.map_zero
  | c :: cs => by
    simp only [List.foldr_cons, List.map_cons, r.map_add, r.map_mul, r.map_foldr_horner x cs]

/-- The executable evaluation of a coefficient array is the evaluation of the
polynomial it stands for. -/
theorem Refines.horner_eq_eval (r : Refines F K) (coeffs : Array F) (x : F) :
    r.toModel (horner coeffs x)
      = (polyOfCoeffs (coeffs.toList.map r.toModel)).eval (r.toModel x) := by
  rw [eval_polyOfCoeffs, ← r.map_foldr_horner, horner, Array.foldr_toList]

end CertiFri
