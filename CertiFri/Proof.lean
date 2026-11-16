import CertiFri.Mmcs

/-!
# Opening proofs

Proof structures for input openings, folding commitments and the final polynomial.
These structures do not define a wire encoding.

No length in a proof should be trusted. The planned verifier must compare each
proof-supplied length against the parameters and claims before indexing it.
These structures do not enforce those checks.
-/

namespace CertiFri

/-- The openings of one input commitment at every query index, with one shared proof. -/
structure BatchOpening {F : Type} (inputMmcs : Mmcs F) where
  /-- `openedValues[q][m]` is the row of matrix `m` at the index of query `q`. -/
  openedValues : Array (Array (Array F))
  /-- The proof authenticating every opened row. -/
  openingProof : inputMmcs.MultiProof

/-- The openings of one commit-phase codeword at every query, with one shared proof. -/
structure CommitPhaseStep {EF : Type} (friMmcs : Mmcs EF) where
  /-- For each query, the values of the folded group other than the one the
  verifier already holds: one fewer than the arity of the round. -/
  siblingValues : Array (Array EF)
  /-- The proof authenticating every query's group. -/
  openingProof : friMmcs.MultiProof

/-- An opening proof: the low-degree test of the batched quotient, together
with the openings of the input commitments it is checked against. -/
structure FriProof {F EF : Type} (inputMmcs : Mmcs F) (friMmcs : Mmcs EF) where
  /-- Grinding witness before the challenge that batches the claimed openings. -/
  batchPowWitness : F
  /-- One commitment per folding round. -/
  commitPhaseCommits : Array friMmcs.Commitment
  /-- One grinding witness per folding round. -/
  commitPowWitnesses : Array F
  /-- One multi-opening per input commitment. -/
  inputOpenings : Array (BatchOpening inputMmcs)
  /-- One multi-opening per folding round. -/
  commitPhaseOpenings : Array (CommitPhaseStep friMmcs)
  /-- Coefficients of the final polynomial, lowest degree first. -/
  finalPoly : Array EF
  /-- Grinding witness before the query indices. -/
  queryPowWitness : F

end CertiFri
