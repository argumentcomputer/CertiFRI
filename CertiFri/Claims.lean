/-!
# Opening claims

What the verifier is asked to check: for each commitment, for each matrix
under it, the claimed evaluations of every column at each opening point.

Port of `CommitmentOpening`, `MatrixOpening` and `PointOpening` from Plonky3
(`commit/src/pcs/univariate.rs`). Plonky3 records the domain of a matrix as a
coset, but its verifier reads only the size, so here a matrix carries the log
of its size.
-/

namespace CertiFri

/-- Claimed evaluations of every column of one matrix at one point, in column order. -/
structure PointOpening (EF : Type) where
  /-- The opening point. -/
  point : EF
  /-- The claimed evaluation of each column at `point`. -/
  values : Array EF
  deriving Repr

/-- The claims about one committed matrix. -/
structure MatrixOpening (EF : Type) where
  /-- Log of the number of rows before the blowup. Each column is claimed to be
  a polynomial of degree below `2 ^ logDegree`. -/
  logDegree : Nat
  /-- The points the matrix is opened at, with the claimed evaluations. -/
  points : Array (PointOpening EF)
  deriving Repr

/-- One commitment and the claims about each matrix under it, in commitment order. -/
structure CommitmentOpening (EF Commitment : Type) where
  /-- The commitment whose matrices are opened. -/
  commitment : Commitment
  /-- The claims about each matrix, in the order the matrices were committed. -/
  matrices : Array (MatrixOpening EF)
  deriving Repr

end CertiFri
