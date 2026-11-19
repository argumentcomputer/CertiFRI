/-!
# FRI parameters

Port of `FriParameters` from Plonky3 (`fri/src/config.rs`), without the
commitment-scheme handle: here the commitment scheme is an argument of the
verifier, not a field of the parameters.
-/

namespace CertiFri

/-- The numbers that define one instance of the FRI protocol. -/
structure FriParams where
  /-- Log of the blowup factor: the committed codewords have rate `2 ^ (-logBlowup)`. -/
  logBlowup : Nat
  /-- Log of the coefficient count of the final polynomial. -/
  logFinalPolyLen : Nat
  /-- Largest log-arity a single folding round may use; `1` is binary folding.
  The verifier accepts only proofs whose rounds all fold by two, whatever this
  cap is. -/
  maxLogArity : Nat
  /-- Number of query indices drawn in the query phase. -/
  numQueries : Nat
  /-- Grinding bits before each folding challenge. -/
  commitPowBits : Nat
  /-- Grinding bits before the query indices. -/
  queryPowBits : Nat
  deriving Repr, DecidableEq, Inhabited

namespace FriParams

/-- Coefficient count of the final polynomial. -/
def finalPolyLen (p : FriParams) : Nat := 2 ^ p.logFinalPolyLen

/-- Log-height of the evaluation domain at which folding stops. -/
def logFinalHeight (p : FriParams) : Nat := p.logBlowup + p.logFinalPolyLen

/-- Query-phase bits under the ethSTARK conjecture (Plonky3's
`conjectured_soundness_bits`). This is a figure for comparison, not something
the proofs in this repository establish. -/
def conjecturedSoundnessBits (p : FriParams) : Nat :=
  p.logBlowup * p.numQueries + p.queryPowBits

end FriParams

end CertiFri
