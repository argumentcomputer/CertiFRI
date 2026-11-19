/-!
# Opening proofs

Port of `FriProof`, `CommitPhaseMultiStep` and `BatchMultiOpening` from Plonky3
(`fri/src/proof.rs`). The two proof types are those of the commitment schemes
(`Mmcs.MultiProof`).

No length in a proof is trusted. Every length is fixed by the parameters and
the shape of the claims, and the verifier compares the proof against it.
-/

namespace CertiFri

/-- The openings of one input commitment at every query index, with one shared proof. -/
structure BatchOpening (F InputProof : Type) where
  /-- `openedValues[q][m]` is the row of matrix `m` at the index of query `q`. -/
  openedValues : Array (Array (Array F))
  /-- The proof authenticating every opened row. -/
  openingProof : InputProof

/-- The openings of one commit-phase codeword at every query, with one shared proof. -/
structure CommitPhaseStep (EF CommitProof : Type) where
  /-- Log of the arity of the round, as the proof states it. The verifier
  requires `1`. -/
  logArity : Nat
  /-- For each query, the values of the folded group other than the one the
  verifier already holds: one fewer than the arity of the round. -/
  siblingValues : Array (Array EF)
  /-- The proof authenticating every query's group. -/
  openingProof : CommitProof

/-- An opening proof: the low-degree test of the batched quotient, together
with the openings of the input commitments it is checked against. `D` is the
type of digests. -/
structure FriProof (F EF D InputProof CommitProof : Type) where
  /-- One commitment per folding round. -/
  commitPhaseCommits : Array D
  /-- One grinding witness per folding round. -/
  commitPowWitnesses : Array F
  /-- One multi-opening per input commitment. -/
  inputOpenings : Array (BatchOpening F InputProof)
  /-- One multi-opening per folding round. -/
  commitPhaseOpenings : Array (CommitPhaseStep EF CommitProof)
  /-- Coefficients of the final polynomial, lowest degree first. -/
  finalPoly : Array EF
  /-- Grinding witness before the query indices. -/
  queryPowWitness : F

end CertiFri
