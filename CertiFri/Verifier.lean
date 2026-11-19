import CertiFri.Params
import CertiFri.Bits
import CertiFri.Field
import CertiFri.Poly
import CertiFri.Challenger
import CertiFri.Merkle
import CertiFri.Proof

/-!
# The FRI verifier

The verifier of the polynomial commitment scheme: given commitments to batches
of matrices, opening points and claimed evaluations, and an opening proof, it
decides whether to accept the claims.

It follows `TwoAdicFriPcs::verify` and `verify_fri` of Plonky3 at revision
`3152b14a` (`fri/src/two_adic_pcs.rs`, `fri/src/verifier.rs`), restricted to
folding by two: a proof with a round of another arity is rejected. It is
generic over the two fields, the two commitment schemes and the challenger.

## The statement

The claims are given by their *shape* and two flat arrays.

* `ClaimShape`: for each batch, for each matrix of the batch, the log of its
  row count before the blowup, its width, and the number of points it is opened
  at. The shape is public: it is fixed before any proof is made.
* `points`: the opening points, in the order batch, matrix, point.
* `values`: the claimed evaluations, in the order batch, matrix, point, column.

`pointRefs` and `claimRefs` enumerate the opening points and the claimed
evaluations of a shape in these orders, with the position of each in the flat
arrays. Claim `c` says: column `c.col` of matrix `c.matrix` of batch `c.batch`,
whose codeword has `2 ^ c.logHeight` entries, is the evaluation of a polynomial
of degree below `2 ^ (c.logHeight - logBlowup)` that takes the value
`values[c.valueIdx]` at `points[c.pointIdx]`.

## The run

1. `shapeOk`: every length in the statement and in the proof is the one the
   parameters and the shape fix.
2. `transcript`: the challenges, from the challenger. The verifier absorbs the
   commitments, the opening points and the claimed values, and squeezes the
   batching challenge. For each round it absorbs the round's commitment, checks
   the proof-of-work witness and squeezes the folding challenge. It absorbs the
   final polynomial and the arity of every round, checks the last witness, and
   squeezes the query indices.
3. `verifyWith`: the checks, given the challenges. The opened rows of every
   input batch are checked against its commitment. For each query, the opened
   values are combined into one reduced opening per height
   (`reducedOpening`), the fold chain is walked (`foldChain`), and its end is
   compared with the final polynomial. The rows the fold chain reconstructs are
   checked against the commitment of each round.

## Differences from Plonky3

* Plonky3's `pcs.verify` starts from a challenger that the caller has already
  fed the commitments and the opening points. Here `verify` absorbs them itself
  (`firstMessage`), commitments first, then points, then the claimed values;
  the last part is what `pcs.verify` absorbs. A caller reproduces this in
  Plonky3 by observing the commitments and the points before `pcs.open`.
* Only folding by two. Plonky3 reads the arity of each round from the proof and
  allows any up to `max_log_arity`.
* The checks are evaluated in another order, and a failed check gives `false`,
  not an error value. The set of accepted inputs is meant to be the same; this
  is tested, not proved (`CertiFriTest`).
* The fold of a row is computed by the formula for the line through two points
  (`foldRow`), where Plonky3 calls a general Lagrange interpolation. In a field
  the two agree.

## What is proved

Nothing in this file. The proofs package relates `verify` to the model verifier
of the security theory, and derives soundness (`Proofs/CertiFriProofs/Exec/`).
-/

namespace CertiFri.Fri

/-! ## The shape of the claims -/

/-- What is public about one committed matrix. -/
structure MatrixShape where
  /-- Log of the number of rows before the blowup: each column is claimed to be
  a polynomial of degree below `2 ^ logDegree`. -/
  logDegree : Nat
  /-- Number of columns. -/
  width : Nat
  /-- Number of points the matrix is opened at. -/
  numPoints : Nat
  deriving Repr, DecidableEq

/-- The shape of the claims: for each batch, the matrices committed under it,
in commitment order. -/
abbrev ClaimShape := List (List MatrixShape)

/-- One opening point of one matrix. -/
structure PointRef where
  /-- The batch of the matrix. -/
  batch : Nat
  /-- The position of the matrix in its batch. -/
  matrix : Nat
  /-- Log of the number of entries of a committed column: `logDegree + logBlowup`. -/
  logHeight : Nat
  /-- Number of columns of the matrix. -/
  width : Nat
  deriving Repr, DecidableEq

/-- One claimed evaluation: a column of a matrix at one of its opening points. -/
structure ClaimRef where
  /-- The batch of the matrix. -/
  batch : Nat
  /-- The position of the matrix in its batch. -/
  matrix : Nat
  /-- The column. -/
  col : Nat
  /-- Log of the number of entries of the committed column. -/
  logHeight : Nat
  /-- The position of the opening point in `points`. -/
  pointIdx : Nat
  /-- The position of the claimed value in `values`. -/
  valueIdx : Nat
  deriving Repr, DecidableEq

/-- The opening points of a shape, in the order batch, matrix, point. The
position of an entry in this list is the position of its point in `points`. -/
def pointRefs (logBlowup : Nat) (shape : ClaimShape) : List PointRef :=
  shape.zipIdx.flatMap fun (mats, batch) =>
    mats.zipIdx.flatMap fun (m, matrix) =>
      List.replicate m.numPoints ⟨batch, matrix, m.logDegree + logBlowup, m.width⟩

/-- The claimed evaluations of a shape, in the order batch, matrix, point,
column. This is the order in which Plonky3's `open_inputs` visits them, and the
order of `values`. -/
def claimRefs (logBlowup : Nat) (shape : ClaimShape) : List ClaimRef :=
  ((pointRefs logBlowup shape).zipIdx.flatMap fun (p, pointIdx) =>
      (List.range p.width).map fun col => (p, pointIdx, col)).zipIdx.map
    fun ((p, pointIdx, col), valueIdx) => ⟨p.batch, p.matrix, col, p.logHeight, pointIdx, valueIdx⟩

/-- Log of the size of the first domain: the largest log-height of a committed
column, or zero when nothing is committed (`log_global_max_height`). -/
def logMaxHeight (logBlowup : Nat) (shape : ClaimShape) : Nat :=
  (shape.flatten.map fun m => m.logDegree + logBlowup).foldr max 0

/-- The number of folding rounds: from the first domain down to the final height. -/
def numRounds (params : FriParams) (shape : ClaimShape) : Nat :=
  logMaxHeight params.logBlowup shape - params.logFinalHeight

/-- The dimensions of the matrices of one batch, as committed. -/
def batchDims (logBlowup : Nat) (mats : List MatrixShape) : Array Dimensions :=
  (mats.map fun m => ⟨m.width, m.logDegree + logBlowup⟩).toArray

/-- The claims of level `j`: those about columns with `2 ^ (n - j)` entries,
where `n` is the log of the size of the first domain. They keep the order of
`claimRefs`. -/
def levelClaims (logBlowup : Nat) (shape : ClaimShape) (n j : Nat) : List ClaimRef :=
  (claimRefs logBlowup shape).filter fun c => c.logHeight + j == n

/-! ## The challenges -/

/-- The challenges of one run. -/
structure Challenges (EF : Type) where
  /-- The challenge that batches the claims of one height. -/
  alpha : EF
  /-- The folding challenge of each round. -/
  betas : Array EF
  /-- Whether every proof-of-work check passed. -/
  powOk : Bool
  /-- The query indices. -/
  indices : Array Nat

section Transcript

variable {σ F EF D : Type} [FieldOps F]

/-- What the verifier absorbs before the batching challenge: the commitments,
the opening points, the claimed values. -/
def firstMessage (commitments : Array D) (points values : Array EF) :
    List (Observation F EF D) :=
  commitments.toList.map .digest ++ points.toList.map .ext ++ values.toList.map .ext

/-- What the verifier absorbs after the last folding challenge: the
coefficients of the final polynomial, and the log-arity of every round, which
is one (`Val::from_usize(log_arity)` in Plonky3). -/
def finalMessage (rounds : Nat) (finalPoly : Array EF) : List (Observation F EF D) :=
  finalPoly.toList.map .ext ++ List.replicate rounds (.base 1)

/-- The commit phase of the transcript, for the first `rounds` rounds: absorb
the commitment of the round, check its proof-of-work witness, squeeze the
folding challenge. Returns the folding challenges, whether every check passed,
and the state of the challenger. -/
def commitPhase [Inhabited D] (chal : Challenger σ F EF D) (commitPowBits : Nat)
    (commits : Array D) (witnesses : Array F) : (rounds : Nat) → σ → Array EF × Bool × σ
  | 0, s => (#[], true, s)
  | i + 1, s =>
    let prev := commitPhase chal commitPowBits commits witnesses i s
    let s := chal.observe prev.2.2 (.digest (commits.getD i default))
    let pow := chal.checkWitness s commitPowBits (witnesses.getD i 0)
    let beta := chal.sampleExt pow.2
    (prev.1.push beta.1, prev.2.1 && pow.1, beta.2)

/-- The challenges of a run, derived from the challenger in state `init`. The
order of the operations is that of Plonky3's `pcs.verify` and `verify_fri`,
after the commitments and the opening points are absorbed. -/
def transcript [Inhabited D] (chal : Challenger σ F EF D) (init : σ) (params : FriParams)
    (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    {InputProof CommitProof : Type} (proof : FriProof F EF D InputProof CommitProof) :
    Challenges EF :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := numRounds params shape
  let s := chal.observeAll init (firstMessage commitments points values)
  let alpha := chal.sampleExt s
  let commit := commitPhase chal params.commitPowBits proof.commitPhaseCommits
    proof.commitPowWitnesses rounds alpha.2
  let s := chal.observeAll commit.2.2 (finalMessage rounds proof.finalPoly)
  let pow := chal.checkWitness s params.queryPowBits proof.queryPowWitness
  { alpha := alpha.1
    betas := commit.1
    powOk := commit.2.1 && pow.1
    indices := (chal.sampleIndices n params.numQueries pow.2).toArray }

end Transcript

/-! ## The arithmetic of one query -/

section Arithmetic

variable {F EF : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]

/-- The point of `index` in the domain of level `j`, the subgroup of order
`2 ^ (n - j)`: the generator of that subgroup to the bit reversal of the
index. The generator is the `2 ^ j`-th power of the generator of order `2 ^ n`. -/
def domainPoint (n j index : Nat) : F :=
  fieldPow (fieldPow (TwoAdicOps.twoAdicGenerator n) (2 ^ j)) (reverseBitsLen index (n - j))

/-- The point of `index` in the coset of level `j`, on which the columns with
`2 ^ (n - j)` entries are committed, as an element of the extension field. -/
def cosetPoint (n j index : Nat) : EF :=
  ExtensionOps.embed (TwoAdicOps.cosetShift * domainPoint (F := F) n j index)

/-- The opened value of a claim's column, from the opened rows of one query:
`rows[batch][matrix][col]`, and zero if there is no such entry. -/
def openedEntry (rows : Array (Array (Array F))) (c : ClaimRef) : F :=
  ((rows.getD c.batch #[]).getD c.matrix #[]).getD c.col 0

/-- The reduced opening of the claims `claims` at the query point `x`: claim
number `k` enters with `alpha ^ k`, as the quotient
`(value - opened) / (point - x)`. In Plonky3's `open_inputs` this is the entry
of `reduced_openings` for one height. -/
def reducedOpening (alpha x : EF) (points values : Array EF) (rows : Array (Array (Array F)))
    (claims : List ClaimRef) : EF :=
  (claims.foldl (fun (acc : EF × EF) c =>
      (acc.1 + acc.2 * ((values.getD c.valueIdx 0 - ExtensionOps.embed (openedEntry rows c)) *
          (points.getD c.pointIdx 0 - x)⁻¹),
        acc.2 * alpha)) (0, 1)).1

/-- Plonky3's `fold_row` for arity two: the value at `beta` of the line through
`(x, e0)` and `(-x, e1)`. -/
def foldRow (beta : EF) (x : F) (e0 e1 : EF) : EF :=
  e0 + (beta - ExtensionOps.embed x) * (e1 - e0) * (ExtensionOps.embed (-x - x))⁻¹

/-- The row of a folding round: the value folded so far and the sibling value
from the proof, placed by the low bit of the index. -/
def placeRow (folded sibling : EF) (index : Nat) : EF × EF :=
  if index % 2 = 0 then (folded, sibling) else (sibling, folded)

/-- The fold chain of one query (`fold_query`): the value after `i` rounds, and
the rows of the rounds walked, first round first.

It starts with the reduced opening of level `0`. In round `i` the row holds the
value so far and the sibling value `sib i`, placed by the low bit of
`index >>> i`. The row is folded with the challenge of the round at the point
of its first entry, and the square of the challenge times the reduced opening
of level `i + 1` is added. -/
def foldChain (n : Nat) (ros : Array EF) (sib : Nat → EF) (betas : Array EF) (index : Nat) :
    Nat → EF × List (EF × EF)
  | 0 => (ros.getD 0 0, [])
  | i + 1 =>
    let prev := foldChain n ros sib betas index i
    let row := placeRow prev.1 (sib i) (index >>> i)
    let beta := betas.getD i 0
    (foldRow beta (domainPoint (F := F) n i (2 * (index >>> (i + 1)))) row.1 row.2 +
        beta * beta * ros.getD (i + 1) 0,
      prev.2 ++ [row])

end Arithmetic

/-! ## The checks -/

section Checks

variable {F EF D : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  {InputProof CommitProof : Type}

/-- The opened rows of one query: for each input batch, the rows of its
matrices at the query's index. -/
def queryRows (proof : FriProof F EF D InputProof CommitProof) (t : Nat) :
    Array (Array (Array F)) :=
  proof.inputOpenings.map fun o => o.openedValues.getD t #[]

/-- The sibling value of query `t` in round `i`; zero if the proof has none. -/
def sibling (proof : FriProof F EF D InputProof CommitProof) (i t : Nat) : EF :=
  match proof.commitPhaseOpenings[i]? with
  | some o => (o.siblingValues.getD t #[]).getD 0 0
  | none => 0

/-- The reduced openings of one query, one per level `j ≤ rounds`: the claims
of the level combined at the point of `index >>> j` in the coset of the level. -/
def reducedOpenings (n rounds : Nat) (levels : Nat → List ClaimRef) (alpha : EF)
    (points values : Array EF) (rows : Array (Array (Array F))) (index : Nat) : Array EF :=
  Array.ofFn (n := rounds + 1) fun j =>
    reducedOpening alpha (cosetPoint (F := F) n j.val (index >>> j.val)) points values rows
      (levels j.val)

/-- What the verifier computes for one query. -/
structure QueryResult (EF : Type) where
  /-- Whether the query's own checks pass. -/
  ok : Bool
  /-- The rows of the folding rounds, as reconstructed by the fold chain. -/
  rows : List (EF × EF)

/-- The checks of query `t` at index `index`, apart from the commitment checks.

* No opening point is the query point of its matrix: Plonky3 rejects such a
  query (`OpeningPointMatchesQueryPoint`), since the quotient is undefined.
* When the final polynomial is a constant, the reduced opening of the last
  level is zero. Plonky3 checks this for the height `log_blowup`, where a
  committed column is the codeword of a constant.
* The end of the fold chain is the value of the final polynomial at the point
  the query has reached. -/
def checkQuery (params : FriParams) (shape : ClaimShape) (levels : Nat → List ClaimRef)
    (points values : Array EF) (proof : FriProof F EF D InputProof CommitProof)
    (ch : Challenges EF) (t index : Nat) : QueryResult EF :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := numRounds params shape
  let ros := reducedOpenings (F := F) n rounds levels ch.alpha points values (queryRows proof t) index
  let chain := foldChain (F := F) n ros (fun i => sibling proof i t) ch.betas index rounds
  let distinct := (pointRefs params.logBlowup shape).zipIdx.all fun (p, pointIdx) =>
    !(points.getD pointIdx 0 -
      cosetPoint (F := F) n (n - p.logHeight) (index >>> (n - p.logHeight)) == 0)
  let constOk := params.logFinalPolyLen != 0 || ros.getD rounds 0 == 0
  let finalOk := chain.1 ==
    horner proof.finalPoly (ExtensionOps.embed (domainPoint (F := F) n rounds (index >>> rounds)))
  { ok := distinct && constOk && finalOk, rows := chain.2 }

/-- The commitment checks of the input batches: the opened rows of all queries
against the commitment of each batch. The index of a query is shifted to the
tallest matrix of the batch (`reduced_indices` in `open_inputs`). -/
def inputChecks (inputMmcs : Mmcs F D) (params : FriParams) (shape : ClaimShape)
    (commitments : Array D) (inputOpenings : Array (BatchOpening F inputMmcs.MultiProof))
    (indices : Array Nat) : Bool :=
  let n := logMaxHeight params.logBlowup shape
  (List.range shape.length).all fun b =>
    match commitments[b]?, inputOpenings[b]? with
    | some root, some opening =>
      let dims := batchDims params.logBlowup (shape.getD b [])
      inputMmcs.verifyMultiBatch root dims
        (Array.ofFn (n := params.numQueries) fun t =>
          indices.getD t.val 0 >>> (n - Merkle.maxLogHeight dims.toList))
        opening.openedValues opening.openingProof
    | _, _ => false

/-- The commitment checks of the folding rounds: for each round, the rows of
all queries, as reconstructed by the fold chains, against the commitment of the
round. The codeword of round `i` is committed as a matrix of width two; the row
of a query is at its index shifted by `i + 1`. -/
def commitChecks (friMmcs : Mmcs EF D) (numQueries n rounds : Nat) (commits : Array D)
    (openings : Array (CommitPhaseStep EF friMmcs.MultiProof)) (indices : Array Nat)
    (rows : Array (List (EF × EF))) : Bool :=
  (List.range rounds).all fun i =>
    match commits[i]?, openings[i]? with
    | some root, some opening =>
      friMmcs.verifyMultiBatch root #[⟨2, n - i - 1⟩]
        (Array.ofFn (n := numQueries) fun t => indices.getD t.val 0 >>> (i + 1))
        (Array.ofFn (n := numQueries) fun t =>
          #[#[((rows.getD t.val []).getD i (0, 0)).1, ((rows.getD t.val []).getD i (0, 0)).2]])
        opening.openingProof
    | _, _ => false

/-- Every length in the statement and in the proof is the one the parameters
and the shape fix, and the parameters and the shape are ones the verifier
handles.

* There is a query, and folding by two is allowed.
* Something is committed, every matrix is opened at a point, and no committed
  column is shorter than the final height. Plonky3 rejects each of these
  (`MissingInitialReducedOpening`, `MatrixWithoutOpeningPoints`,
  `UnconsumedReducedOpenings`).
* The first domain exists in the field.
* One commitment per batch, one point per opening point, one value per claim.
* One commitment, one witness and one opening per folding round; every round
  folds by two and has one sibling value per query.
* The final polynomial has the configured length.
* One opening per input batch, with rows for every query and every matrix. -/
def shapeOk (params : FriParams) (shape : ClaimShape) (commitments : Array D)
    (points values : Array EF) (proof : FriProof F EF D InputProof CommitProof) : Bool :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := numRounds params shape
  params.numQueries != 0 && params.maxLogArity != 0
    && !shape.flatten.isEmpty
    && shape.flatten.all (fun m =>
      m.numPoints != 0 && decide (params.logFinalHeight ≤ m.logDegree + params.logBlowup))
    && decide (n ≤ TwoAdicOps.twoAdicity (F := F))
    && commitments.size == shape.length
    && points.size == (pointRefs params.logBlowup shape).length
    && values.size == (claimRefs params.logBlowup shape).length
    && proof.commitPhaseCommits.size == rounds
    && proof.commitPowWitnesses.size == rounds
    && proof.commitPhaseOpenings.size == rounds
    && proof.commitPhaseOpenings.all (fun o =>
      o.logArity == 1 && o.siblingValues.size == params.numQueries
        && o.siblingValues.all (·.size == 1))
    && proof.finalPoly.size == params.finalPolyLen
    && proof.inputOpenings.size == shape.length
    && (List.range shape.length).all (fun b =>
      match proof.inputOpenings[b]? with
      | some o => o.openedValues.size == params.numQueries
          && o.openedValues.all (·.size == (shape.getD b []).length)
      | none => false)

/-- **The checks of the verifier, given the challenges.**

Every proof-of-work check passed, there is one query index per query and each
is an index of the first domain, the opened rows of the input batches are
committed, every query passes its own checks, and the rows of the fold chains
are committed. -/
def verifyWith (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (params : FriParams)
    (shape : ClaimShape) (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) (ch : Challenges EF) :
    Bool :=
  let n := logMaxHeight params.logBlowup shape
  let rounds := numRounds params shape
  let levelArr := Array.ofFn (n := rounds + 1) fun j => levelClaims params.logBlowup shape n j.val
  let results := Array.ofFn (n := params.numQueries) fun t =>
    checkQuery (F := F) params shape (fun j => levelArr.getD j []) points values proof ch t.val
      (ch.indices.getD t.val 0)
  ch.powOk && ch.indices.size == params.numQueries
    && (List.range params.numQueries).all (fun t => decide (ch.indices.getD t 0 < 2 ^ n))
    && inputChecks inputMmcs params shape commitments proof.inputOpenings ch.indices
    && results.all (·.ok)
    && commitChecks friMmcs params.numQueries n rounds proof.commitPhaseCommits
        proof.commitPhaseOpenings ch.indices (results.map (·.rows))

/-- **The FRI verifier.** Accept the claims of shape `shape`, with opening
points `points` and claimed values `values` about the matrices committed under
`commitments`, on the proof `proof`.

`inputMmcs` and `friMmcs` are the commitment schemes of the input matrices and
of the codewords of the folding rounds. `chal` is the challenger and `init` its
state before anything of this run is absorbed. -/
def verify {σ : Type} [Inhabited D] (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (chal : Challenger σ F EF D) (init : σ) (params : FriParams) (shape : ClaimShape)
    (commitments : Array D) (points values : Array EF)
    (proof : FriProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  shapeOk (F := F) params shape commitments points values proof
    && verifyWith inputMmcs friMmcs params shape commitments points values proof
      (transcript chal init params shape commitments points values proof)

end Checks

end CertiFri.Fri
