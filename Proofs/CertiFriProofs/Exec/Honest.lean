import CertiFriProofs.Exec.Arith
import CertiFriProofs.Theory.Completeness

/-!
# Completeness: what an honest statement and an honest proof are

Completeness says that the verifier accepts every proof that follows the
protocol. This file states what following the protocol means. The theorems are
in the sibling modules.

Nothing here is a program. The honest prover appears only through the
properties of what it produces.

* `Committed`: what stands behind the commitments. For every column a
  polynomial, and for every matrix its rows.
* `HonestStatement`: the committed rows are the evaluations of the polynomials
  on the coset of the matrix, the polynomials respect the degree bound, every
  claimed value is the value of the column's polynomial at the opening point,
  and no opening point lies on the coset its matrix is committed on.
* `inputPoly`: the polynomial that the claims of one level reduce to. Claim
  number `k` of the level enters with `α ^ k`, as the quotient
  `(P - y) / (X - z)`, read on the unshifted domain.
* `honestWord`: the polynomial the prover commits to in each folding round
  (`honestPoly` of `Theory/Completeness.lean` on the `inputPoly`s), and after
  the last round the final polynomial.
* `HonestProof`: with the challenges the verifier itself derives from the
  proof, the proof-of-work checks pass, the opened rows of the inputs are the
  committed rows and their Merkle openings verify, the codeword of every round
  is `honestWord`, its Merkle openings verify, the sibling values are its
  values, and the final polynomial is `honestWord` after the last round.

## Remarks

* The challenges in `HonestProof` are those of `Fri.transcript` on the proof
  itself. A prover that commits to each round after deriving the challenges of
  the rounds before it produces such a proof; that construction is not in this
  file.
* That the proof-of-work checks pass is part of honesty. A witness is found by
  search and need not exist.
* `HonestProof` asks that the Merkle openings verify. That the openings of a
  correctly built tree do is `Merkle` completeness, proved separately.
* The codeword of a round is committed as elements of the executable extension
  field. `rep` picks, for a value in `K`, an element that represents it.
-/

namespace CertiFri.Exec

open Fri Polynomial

variable {σ F EF D K : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Field K] [DecidableEq K] [DecidableEq D] [Inhabited D]
  (m : FieldModel F EF K) (params : FriParams) (shape : ClaimShape)
  (wf : WellFormed m params shape)

/-- What stands behind the commitments: the polynomial of every column and the
rows of every matrix. `poly batch matrix col` and `row batch matrix index`. -/
structure Committed (F K : Type) [Field K] where
  /-- The polynomial of a column. -/
  poly : ℕ → ℕ → ℕ → K[X]
  /-- A row of a committed matrix. -/
  row : ℕ → ℕ → ℕ → Array F

/-- An element of the executable extension field that represents `x`. -/
noncomputable def rep (x : K) : EF := Function.surjInv m.surj x

omit [TwoAdicOps F] [DecidableEq K] [DecidableEq D] [Inhabited D] in
/-- `rep x` represents `x`. -/
theorem toModel_rep (x : K) : m.ext.toModel (rep m x) = x :=
  Function.surjInv_eq m.surj x

/-- **The statement is honest**: behind the commitments are polynomials of the
allowed degree, the committed rows are their evaluations on the coset of each
matrix, the claimed values are their values at the opening points, and no
opening point lies on the coset of its matrix. -/
structure HonestStatement (w : Committed F K) (points values : Array EF) : Prop where
  /-- Every column is a polynomial of degree below `2 ^ logDegree`. -/
  degree : ∀ c ∈ claimRefs params.logBlowup shape,
    (w.poly c.batch c.matrix c.col).degree < (2 ^ (c.logHeight - params.logBlowup) : ℕ)
  /-- The committed rows hold the evaluations of the columns on the coset. -/
  row_eval : ∀ c ∈ claimRefs params.logBlowup shape, ∀ i < 2 ^ c.logHeight,
    m.base.toModel ((w.row c.batch c.matrix i).getD c.col 0) =
      (w.poly c.batch c.matrix c.col).eval
        ((modelParams m params shape wf).shift *
          pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            c.logHeight i)
  /-- Every claimed value is the value of the column at the opening point. -/
  value : ∀ c ∈ claimRefs params.logBlowup shape,
    m.ext.toModel (values.getD c.valueIdx 0) =
      (w.poly c.batch c.matrix c.col).eval (m.ext.toModel (points.getD c.pointIdx 0))
  /-- No opening point lies on the coset its matrix is committed on. -/
  off_domain : ∀ (p : PointRef) (pointIdx : ℕ),
    (pointRefs params.logBlowup shape)[pointIdx]? = some p → ∀ i,
      m.ext.toModel (points.getD pointIdx 0) ≠
        (modelParams m params shape wf).shift *
          pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
            p.logHeight i

/-- The quotient of a claim, as a polynomial: `(P - y) / (X - z)` for the
column `P`, the claimed value `y` and the opening point `z`. Its value at a
point `x ≠ z` is `(y - P x) / (z - x)`, the quotient the verifier forms. -/
noncomputable def quotientPoly (w : Committed F K) (points values : Array EF) (c : ClaimRef) :
    K[X] :=
  (w.poly c.batch c.matrix c.col - C (m.ext.toModel (values.getD c.valueIdx 0))) /ₘ
    (X - C (m.ext.toModel (points.getD c.pointIdx 0)))

/-- The polynomial the claims of level `j` reduce to, as a polynomial in the
point of the unshifted domain of the level: claim number `k` of the level
enters with `α ^ k`, as its quotient at `shift * X`. -/
noncomputable def inputPoly (w : Committed F K) (points values : Array EF) (α : K) (j : ℕ) :
    K[X] :=
  ((levelClaims params.logBlowup shape (logMaxHeight params.logBlowup shape) j).zipIdx.map
    fun ck => C (α ^ ck.2) *
      (quotientPoly m w points values ck.1).comp
        (C (modelParams m params shape wf).shift * X)).sum

/-- The polynomial the honest prover commits to at level `i`: the reduced
claims of level `0`, folded `i` times, with the reduced claims of each level
added as the fold reaches it. At level `numRounds` it is the final polynomial. -/
noncomputable def honestWord (w : Committed F K) (points values : Array EF) (α : K)
    (β : ℕ → K) (i : ℕ) : K[X] :=
  honestPoly (inputPoly m params shape wf w points values α) β i

/-- **The proof is honest** for the committed data `w`, with the hash
functions `hIn` and `hFri` and the challenger `chal` started at `init`.

Write `ch` for the challenges the verifier derives from the proof
(`Fri.transcript`), `idx t` for the index of query `t`, and `G i` for
`honestWord` at level `i` with the challenges of `ch` read in `K`. -/
structure HonestProof (hIn : MerkleHasher F D) (hFri : MerkleHasher EF D)
    (chal : Challenger σ F EF D) (init : σ) (w : Committed F K) (commitments : Array D)
    (points values : Array EF) (proof : FriProof F EF D (Array (List D)) (Array (List D))) :
    Prop where
  /-- Every length is the one the parameters and the shape fix. -/
  shape_ok : shapeOk (F := F) params shape commitments points values proof = true
  /-- Every proof-of-work check passes. -/
  pow : (transcript chal init params shape commitments points values proof).powOk = true
  /-- The challenger returns indices of the first domain. -/
  index_lt : ∀ t < params.numQueries,
    (transcript chal init params shape commitments points values proof).indices.getD t 0 <
      2 ^ logMaxHeight params.logBlowup shape
  /-- The openings of every input batch verify against its commitment. -/
  input_open : ∀ b < shape.length, ∃ root opening,
    commitments[b]? = some root ∧ proof.inputOpenings[b]? = some opening ∧
      Merkle.verifyOpenings hIn root (batchDims params.logBlowup (shape.getD b []))
        (Array.ofFn (n := params.numQueries) fun t =>
          (transcript chal init params shape commitments points values proof).indices.getD t.val 0
            >>> (logMaxHeight params.logBlowup shape -
              Merkle.maxLogHeight (batchDims params.logBlowup (shape.getD b [])).toList))
        opening.openedValues opening.openingProof = true
  /-- The opened entries are the committed ones. -/
  input_rows : ∀ c ∈ claimRefs params.logBlowup shape, ∀ t < params.numQueries,
    openedEntry (queryRows proof t) c =
      (w.row c.batch c.matrix
        ((transcript chal init params shape commitments points values proof).indices.getD t 0
          >>> (logMaxHeight params.logBlowup shape - c.logHeight))).getD c.col 0
  /-- The rows of `G i` at the queried positions verify against the commitment
  of round `i`. Row `p` holds the values at the points of the indices `2 * p`
  and `2 * p + 1` of level `i`. -/
  round_open : ∀ i < numRounds params shape, ∃ root opening,
    proof.commitPhaseCommits[i]? = some root ∧ proof.commitPhaseOpenings[i]? = some opening ∧
      Merkle.verifyOpenings hFri root #[⟨2, logMaxHeight params.logBlowup shape - i - 1⟩]
        (Array.ofFn (n := params.numQueries) fun t =>
          (transcript chal init params shape commitments points values proof).indices.getD t.val 0
            >>> (i + 1))
        (Array.ofFn (n := params.numQueries) fun t =>
          #[#[rep m ((honestWord m params shape wf w points values
                (m.ext.toModel
                  (transcript chal init params shape commitments points values proof).alpha)
                (fun r => m.ext.toModel
                  ((transcript chal init params shape commitments points values
                    proof).betas.getD r 0)) i).eval
              (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
                (logMaxHeight params.logBlowup shape - i)
                (2 * ((transcript chal init params shape commitments points values
                  proof).indices.getD t.val 0 >>> (i + 1))))),
            rep m ((honestWord m params shape wf w points values
                (m.ext.toModel
                  (transcript chal init params shape commitments points values proof).alpha)
                (fun r => m.ext.toModel
                  ((transcript chal init params shape commitments points values
                    proof).betas.getD r 0)) i).eval
              (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
                (logMaxHeight params.logBlowup shape - i)
                (2 * ((transcript chal init params shape commitments points values
                  proof).indices.getD t.val 0 >>> (i + 1)) + 1)))]])
        opening.openingProof = true
  /-- The sibling value of a query in round `i` is the value of `G i` at the
  other point of the query's pair. -/
  sibling_eval : ∀ i < numRounds params shape, ∀ t < params.numQueries,
    m.ext.toModel (sibling proof i t) =
      (honestWord m params shape wf w points values
          (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
          (fun r => m.ext.toModel
            ((transcript chal init params shape commitments points values proof).betas.getD r 0))
          i).eval
        (pointOfIndex (modelParams m params shape wf).ω (modelParams m params shape wf).n
          (logMaxHeight params.logBlowup shape - i)
          (((transcript chal init params shape commitments points values proof).indices.getD t 0
            >>> i) ^^^ 1))
  /-- The final polynomial is `G numRounds`. -/
  final : polyOfCoeffs (proof.finalPoly.toList.map m.ext.toModel) =
    honestWord m params shape wf w points values
      (m.ext.toModel (transcript chal init params shape commitments points values proof).alpha)
      (fun r => m.ext.toModel
        ((transcript chal init params shape commitments points values proof).betas.getD r 0))
      (numRounds params shape)

end CertiFri.Exec
