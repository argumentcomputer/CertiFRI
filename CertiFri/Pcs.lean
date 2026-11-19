import CertiFri.Claims
import CertiFri.Verifier

/-!
# The verifier on Plonky3-shaped claims

`Fri.verify` takes the claims as a public shape and two flat arrays. Plonky3's
`pcs.verify` takes them nested: for each commitment, for each matrix under it,
the opening points with the claimed evaluations of every column
(`commitments_with_opening_points`, here `CommitmentOpening`).

`verifyClaims` is `Fri.verify` on the shape and the flat arrays of nested
claims. The flattening keeps Plonky3's order: batch, matrix, point, column.
`verifyClaimsFrom` is the same for `Fri.verifyFrom`.

Nested claims can give different numbers of values at two points of one matrix,
which a shape cannot express. Plonky3 rejects such claims (the count of values
at every point must be the width of the opened row), and so does
`verifyClaims`.

Nothing is proved here. The security theorems are about `Fri.verify`; this
file only rearranges its input.
-/

namespace CertiFri.Fri

variable {EF D : Type}

/-- The width a matrix is claimed to have: the number of values at its first
opening point, or zero if it has none. -/
def claimedWidth (m : MatrixOpening EF) : Nat :=
  match m.points[0]? with
  | some p => p.values.size
  | none => 0

/-- The shape of nested claims. -/
def claimShape (claims : Array (CommitmentOpening EF D)) : ClaimShape :=
  claims.toList.map fun c => c.matrices.toList.map fun m =>
    ⟨m.logDegree, claimedWidth m, m.points.size⟩

/-- The opening points of nested claims, in the order batch, matrix, point. -/
def claimPoints (claims : Array (CommitmentOpening EF D)) : Array EF :=
  (claims.toList.flatMap fun c => c.matrices.toList.flatMap fun m =>
    m.points.toList.map (·.point)).toArray

/-- The claimed values of nested claims, in the order batch, matrix, point, column. -/
def claimValues (claims : Array (CommitmentOpening EF D)) : Array EF :=
  (claims.toList.flatMap fun c => c.matrices.toList.flatMap fun m =>
    m.points.toList.flatMap (·.values.toList)).toArray

/-- Every opening point of a matrix comes with as many values as the first. -/
def widthsUniform (claims : Array (CommitmentOpening EF D)) : Bool :=
  claims.all fun c => c.matrices.all fun m => m.points.all fun p =>
    p.values.size == claimedWidth m

/-- The verifier on nested claims: `Fri.verify` on their shape, their opening
points and their claimed values. -/
def verifyClaims {σ F : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
    [Inhabited D] (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D)
    (init : σ) (params : FriParams) (claims : Array (CommitmentOpening EF D))
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  widthsUniform claims
    && verify inputMmcs friMmcs chal init params (claimShape claims)
      (claims.map (·.commitment)) (claimPoints claims) (claimValues claims) proof

/-- The verifier on nested claims, inside a larger protocol: `Fri.verifyFrom`
on their shape, their opening points and their claimed values, from the
challenger state `s` the caller reached. This has the contract of Plonky3's
`pcs.verify`. -/
def verifyClaimsFrom {σ F : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
    [Inhabited D] (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D)
    (s : σ) (params : FriParams) (claims : Array (CommitmentOpening EF D))
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  widthsUniform claims
    && verifyFrom inputMmcs friMmcs chal s params (claimShape claims)
      (claims.map (·.commitment)) (claimPoints claims) (claimValues claims) proof

end CertiFri.Fri
