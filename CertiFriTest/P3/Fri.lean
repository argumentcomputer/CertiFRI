import CertiFriTest.P3.Vector

/-!
# The verifier on proofs made by Plonky3

The vectors of `CertiFriTest/vectors/fri` are statements and opening proofs
produced by Plonky3's `TwoAdicFriPcs` at revision `3152b14a`, over Goldilocks
and its quadratic extension, with BLAKE3 Merkle trees and the BLAKE3-based
challenger. Plonky3's own verifier accepts each of them.

The tests run `Fri.verifyClaims` with the primitives of `CertiFriP3` on each
vector, in both forms of the commitment proofs: one full Merkle path per query
(the form the soundness theorem is about), and Plonky3's pruned proofs. They
also compare the challenges the verifier derives with those Plonky3 derived,
and check that tampered statements and proofs are rejected.

The challenger starts from the empty state and absorbs the commitments and the
opening points before the claimed values, as the generator does on Plonky3's
side.
-/

namespace CertiFriTest.P3

open CertiFri CertiFri.Fri CertiFri.P3

/-- The challenger state the vectors start from. -/
def initial : ChallengerState := ChallengerState.new ByteArray.empty

/-- The verifier on a vector, with one full Merkle path per query. -/
def acceptsPaths (v : Vector) : Bool :=
  verifyClaims (merkleMmcs baseHasher) (merkleMmcs extHasher) challenger initial v.params
    v.claims v.paths

/-- The verifier on a vector, with Plonky3's pruned Merkle proofs. -/
def acceptsPruned (v : Vector) : Bool :=
  verifyClaims (prunedMmcs baseHasher) (prunedMmcs extHasher) challenger initial v.params
    v.claims v.pruned

/-- The challenges the verifier derives for a vector. -/
def challenges (v : Vector) : Challenges GoldilocksExt :=
  transcript challenger initial v.params (claimShape v.claims) (v.claims.map (·.commitment))
    (claimPoints v.claims) (claimValues v.claims) v.paths

/-- The derived challenges are those Plonky3 derived. -/
def challengesMatch (v : Vector) : Bool :=
  let ch := challenges v
  ch.alpha == v.alpha && ch.betas == v.betas && ch.indices == v.indices && ch.powOk

/-- Run a check on a vector file; a file that does not parse fails the check. -/
def check (text : String) (f : Vector → Bool) : Bool :=
  match parseVector text with
  | .ok v => f v
  | .error _ => false

def small : String := include_str "../vectors/fri/small.json"
def mixed : String := include_str "../vectors/fri/mixed.json"
def const : String := include_str "../vectors/fri/const.json"
def wide : String := include_str "../vectors/fri/wide.json"

/-! ## Plonky3's proofs are accepted -/

-- The transcript: the same challenges as Plonky3.
#guard check small challengesMatch
#guard check mixed challengesMatch
#guard check const challengesMatch
#guard check wide challengesMatch

-- One full Merkle path per query.
#guard check small acceptsPaths
#guard check mixed acceptsPaths
#guard check const acceptsPaths
#guard check wide acceptsPaths

-- Plonky3's pruned Merkle proofs.
#guard check small acceptsPruned
#guard check mixed acceptsPruned
#guard check const acceptsPruned
#guard check wide acceptsPruned

-- The vectors have the intended sizes: `mixed` folds four times, and its
-- proof-of-work checks are on.
#guard check mixed fun v =>
  numRounds v.params (claimShape v.claims) == 4 && v.params.commitPowBits == 3
    && v.params.queryPowBits == 5 && v.claims.size == 2

/-! ## Tampered inputs are rejected -/

/-- Add one to a field element's first coordinate. -/
def bump (x : GoldilocksExt) : GoldilocksExt := x + 1

/-- Change the first claimed value of the first point of matrix `m` of batch `b`. -/
def bumpValue (v : Vector) (b m : Nat) : Vector :=
  { v with claims := v.claims.modify b (fun c =>
      { c with matrices := c.matrices.modify m (fun mat =>
          { mat with points := mat.points.modify 0 (fun p =>
              { p with values := p.values.modify 0 bump }) }) }) }

/-- Change the first opening point of matrix `m` of batch `b`. -/
def bumpPoint (v : Vector) (b m : Nat) : Vector :=
  { v with claims := v.claims.modify b (fun c =>
      { c with matrices := c.matrices.modify m (fun mat =>
          { mat with points := mat.points.modify 0 (fun p => { p with point := bump p.point }) }) }) }

/-- Change the first coefficient of the final polynomial, in both forms of the proof. -/
def bumpFinal (v : Vector) : Vector :=
  { v with
    paths := { v.paths with finalPoly := v.paths.finalPoly.modify 0 bump }
    pruned := { v.pruned with finalPoly := v.pruned.finalPoly.modify 0 bump } }

/-- Change the sibling value of the first query in round `i`, in both forms. -/
def bumpSibling (v : Vector) (i : Nat) : Vector :=
  { v with
    paths := { v.paths with commitPhaseOpenings := v.paths.commitPhaseOpenings.modify i (fun o =>
      { o with siblingValues := o.siblingValues.modify 0 (fun s => s.modify 0 bump) }) }
    pruned := { v.pruned with commitPhaseOpenings := v.pruned.commitPhaseOpenings.modify i (fun o =>
      { o with siblingValues := o.siblingValues.modify 0 (fun s => s.modify 0 bump) }) } }

/-- Change the first opened entry of the first query of input batch `b`, in both forms. -/
def bumpOpened (v : Vector) (b : Nat) : Vector :=
  { v with
    paths := { v.paths with inputOpenings := v.paths.inputOpenings.modify b (fun o =>
      { o with openedValues := o.openedValues.modify 0 (fun rows =>
          rows.modify 0 (fun row => row.modify 0 (· + 1))) }) }
    pruned := { v.pruned with inputOpenings := v.pruned.inputOpenings.modify b (fun o =>
      { o with openedValues := o.openedValues.modify 0 (fun rows =>
          rows.modify 0 (fun row => row.modify 0 (· + 1))) }) } }

/-- Change the proof-of-work witness before the queries, in both forms. -/
def bumpQueryWitness (v : Vector) : Vector :=
  { v with
    paths := { v.paths with queryPowWitness := v.paths.queryPowWitness + 1 }
    pruned := { v.pruned with queryPowWitness := v.pruned.queryPowWitness + 1 } }

/-- Rejected in both forms of the commitment proofs. -/
def rejects (v : Vector) : Bool := !acceptsPaths v && !acceptsPruned v

-- A changed claimed value, in every matrix.
#guard check mixed fun v => rejects (bumpValue v 0 0) && rejects (bumpValue v 0 1)
  && rejects (bumpValue v 0 2) && rejects (bumpValue v 1 0) && rejects (bumpValue v 1 1)
#guard check small fun v => rejects (bumpValue v 0 0) && rejects (bumpValue v 0 1)
#guard check const fun v => rejects (bumpValue v 0 0) && rejects (bumpValue v 0 1)
  && rejects (bumpValue v 1 0)

-- A changed opening point.
#guard check mixed fun v => rejects (bumpPoint v 0 0) && rejects (bumpPoint v 1 1)

-- A changed final polynomial.
#guard check mixed fun v => rejects (bumpFinal v)
#guard check small fun v => rejects (bumpFinal v)

-- A changed sibling value, in every round.
#guard check mixed fun v => (List.range 4).all fun i => rejects (bumpSibling v i)

-- A changed opened entry of an input matrix.
#guard check mixed fun v => rejects (bumpOpened v 0) && rejects (bumpOpened v 1)

-- A changed proof-of-work witness: `wide` asks for eight zero bits.
#guard check wide fun v => rejects (bumpQueryWitness v)

-- Other parameters than the proof was made for.
#guard check mixed fun v => rejects { v with params := { v.params with numQueries := 6 } }
#guard check mixed fun v => rejects { v with params := { v.params with logBlowup := 1 } }
#guard check mixed fun v => rejects { v with params := { v.params with queryPowBits := 20 } }

end CertiFriTest.P3
