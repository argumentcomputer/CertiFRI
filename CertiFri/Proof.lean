import CertiFri.Mmcs

/-!
# Opening proofs

Port of `FriProof`, `CommitPhaseMultiStep` and `BatchMultiOpening` from Plonky3
(`fri/src/proof.rs`).

No length in a proof is trusted. Every length is fixed by the parameters and
the claims, and the verifier compares the proof against it before reading.
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
