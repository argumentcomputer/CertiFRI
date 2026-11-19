/-!
# Commitment scheme interface

The verifying side of a mixed-matrix commitment scheme: one commitment to
several matrices of different heights, opened at many row indices with one
shared proof. Port of the part of Plonky3's `Mmcs` trait the FRI verifier uses
(`commit/src/mmcs.rs`).

The scheme is a value, not a type class, because the verifier holds two of
them: one over the base field for the input commitments, and one over the
extension field for the commit-phase codewords. Both commit to digests of the
same type `D`, which is what the transcript absorbs.
-/

namespace CertiFri

/-- The dimensions of one committed matrix.

Plonky3 records the number of rows. Every matrix this verifier commits to has a
power-of-two number of rows, so the log is recorded instead. -/
structure Dimensions where
  /-- Number of columns. -/
  width : Nat
  /-- Log of the number of rows. -/
  logHeight : Nat
  deriving Repr, DecidableEq

/-- The verifying side of a commitment scheme over rows of `T`, whose
commitments are digests in `D`. -/
structure Mmcs (T D : Type) where
  /-- One proof authenticating the rows opened at several indices. -/
  MultiProof : Type
  /-- Check that, for each query `q`, `openedValues[q][m]` is the row of matrix
  `m` at index `indices[q]`, against a commitment to matrices of the given
  `dimensions`. An index addresses the tallest matrix; a shorter matrix is
  opened at the index shifted right by the difference in log-heights.
  Port of `Mmcs::verify_multi_batch`. -/
  verifyMultiBatch : D → (dimensions : Array Dimensions) → (indices : Array Nat) →
    (openedValues : Array (Array (Array T))) → MultiProof → Bool

end CertiFri
