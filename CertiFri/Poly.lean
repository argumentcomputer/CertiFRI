import CertiFri.Field

/-!
# Polynomial evaluation

The last check of every query compares the folded value with the final
polynomial the prover sent in the clear, evaluated at the query's point.
-/

namespace CertiFri

/-- Evaluate at `x` the polynomial with coefficients `coeffs`, lowest degree
first, by Horner's rule (port of `HornerIter::horner`). -/
def horner {F : Type} [FieldOps F] (coeffs : Array F) (x : F) : F :=
  coeffs.foldr (fun coeff acc => acc * x + coeff) 0

end CertiFri
