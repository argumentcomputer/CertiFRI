import CertiFri.Pcs
import CertiFri.Stark.Logup
import CertiFri.Stark.System

/-!
# The multi-stark verifier

The verifier of multi-stark, a STARK for systems of several circuits that are
connected by lookups, built on Plonky3's FRI commitment scheme. Port of
`System::verify_multiple_claims` and `verify_after_challenges`
(`src/verifier.rs`) and of `System::verify_batch` (`src/batch.rs`) of
multi-stark at revision `3515632`. It is generic over the two fields, the two
commitment schemes and the challenger, and it calls the FRI verifier of this
repository (`Fri.verifyFrom`) for the openings.

## The statement

A system (`System`) fixes the circuits. A proof (`Proof`) says which circuits
are active and how tall the trace of each is. The claim checked is: for each
active circuit there is a main trace of that height, over the base field, such
that every constraint of the circuit holds on every row, and such that the
lookup messages of all rows of all active circuits, together with the public
claims, cancel: every message is sent with total multiplicity zero.

## The run

`verify` checks one proof against public claims:

1. `shapeOk`: every length in the proof is the one the system fixes.
2. The lookup sum leaving the last circuit is zero.
3. `firstMessage`, `lookupChallenges`: the verifier absorbs the shape of the
   system, the activation bitmap, the commitment to the fixed traces, the
   commitment to the main traces, the log trace heights and the claims, and
   squeezes the two lookup challenges `β` and `γ`.
4. `claimsAccumulator`: the lookup sum of the claims, which enters the first
   circuit. A claim whose message is zero is rejected.
5. `checkAfterChallenges`, the part shared with the batch protocol:
   * `mainChallenges`: absorb the commitment to the lookup traces and the
     lookup sum leaving each circuit, squeeze the constraint challenge `α`,
     absorb the commitment to the quotients, squeeze the out-of-domain point
     `ζ`. Reject `ζ = 0` and `ζ` in a trace domain.
   * `openingClaims`, `Fri.verifyClaimsFrom`: the values opened at `ζ`, and at
     its successor `ζ * g` for the traces, are those of the committed
     columns.
   * `circuitOk`, for each active circuit: evaluate the constraints of the
     graph and the lookup constraints on the opened values, fold them with
     `α`, and compare with the quotient, reassembled from its chunks, times
     the vanishing polynomial of the trace domain at `ζ`.

`verifyBatch` checks a batch: several proofs of one system that share `β` and
`γ`, so that a message sent in one proof can be received in another. The
challenges are squeezed after the headers of all shards and the messages of the
batch are absorbed (`batchFirstMessage`). Each shard then runs step 5 from the
shared state, after absorbing its own position. The sum leaving the last
circuit of a shard is its residual; the residuals and the lookup sum of the
batch's messages must add up to zero.

## Differences from multi-stark

* multi-stark's configuration can omit some openings
  (`omit_unused_next_row_openings`, `omit_inactive_preprocessed_openings`).
  The FRI configuration leaves both off, and so does this port: the main and
  fixed traces of an active circuit are always opened at two points, the fixed
  trace of an inactive circuit at one.
* multi-stark also rejects a log trace height of 64 or more, the width of a
  machine word. Here the bound is `maxLogDegree` alone, which is below 64 in
  every configuration of the FRI backend.
* The checks are evaluated in another order, and a failed check gives `false`,
  not an error value. A read outside an array gives zero where multi-stark
  panics; the shape check excludes such reads for a well-formed system.
* Only folding by two in the opening proof, as in `Fri.verify`.

## What is and is not checked here

As in multi-stark, the verifier attaches no meaning to the claims or to the
messages of a batch: which are admissible is the application's policy. The
system is an input: the constraint graphs are not absorbed into the transcript,
only their sizes (`shapeMessage`), so the guarantee is for a system fixed
before the proof is made.

## What is proved

Nothing in this file. The acceptance of proofs made by multi-stark is tested
(`CertiFriTest/Stark`).
-/

namespace CertiFri.Stark

open CertiFri.Fri

/-- The circuits a proof covers: the positions set in the activation bitmap,
in increasing order. -/
def activeIndices (active : Array Bool) : List Nat :=
  (List.range active.size).filter fun i => active.getD i false

/-! ## The shape of a proof -/

section Shape

variable {F EF D InputProof CommitProof : Type}

/-- `rows` holds `count` rows of `width` values each. -/
def rowsOk (rows : Array (Array EF)) (count width : Nat) : Bool :=
  rows.size == count && rows.all (·.size == width)

/-- The fixed trace of circuit `ci`, among the opened values of a proof; no
rows if the circuit has no fixed trace. -/
def preprocessedRows (sys : System F D) (proof : Proof F EF D InputProof CommitProof)
    (ci : Nat) : Array (Array EF) :=
  match sys.preprocessedIndices.getD ci none with
  | some slot => proof.preprocessedOpened.getD slot #[]
  | none => #[]

/-- **The proof has the shape the system fixes** (`verify_shape`):

* the system has a circuit, the bitmap has one bit per circuit and one is set;
* there is one log trace height, one outgoing lookup sum and one group of
  opened values of each kind per active circuit, and one group of opened values
  per fixed trace;
* the system has a commitment to fixed traces exactly when a circuit has one;
* a trace is opened at two points, the fixed trace of an inactive circuit and
  a quotient at one, and each opened row has the width of its matrix;
* the trace of a circuit with a fixed trace has the height of the fixed trace;
* the trace and the quotient domain of each circuit are within the supported
  size. -/
def shapeOk [FieldOps F] [FieldOps EF] [ExtensionOps F EF] (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) : Bool :=
  let d := ExtensionOps.degree (F := F) (EF := EF)
  let act := activeIndices proof.active
  let numPreprocessed := (sys.preprocessedIndices.toList.filter Option.isSome).length
  sys.circuits.size != 0
    && proof.active.size == sys.circuits.size
    && !act.isEmpty
    && proof.logDegrees.size == act.length
    && sys.preprocessedCommit.isNone == (numPreprocessed == 0)
    && proof.preprocessedOpened.size == numPreprocessed
    && proof.stage1Opened.size == act.length
    && proof.stage2Opened.size == act.length
    && proof.quotientOpened.size == act.length
    && proof.intermediateAccumulators.size == act.length
    && (List.range sys.circuits.size).all (fun ci =>
      proof.active.getD ci false || (sys.preprocessedIndices.getD ci none).isNone
        || rowsOk (preprocessedRows sys proof ci) 1 (sys.circuits.getD ci default).preprocessedWidth)
    && act.zipIdx.all (fun (ci, pos) =>
      let c := sys.circuits.getD ci default
      let k := proof.logDegrees.getD pos 0
      decide (k ≤ sys.maxLogDegree)
        && decide (k + Nat.log2 c.quotientDegree ≤ sys.maxLogDegree)
        && (c.preprocessedHeight == 0 || 2 ^ k == c.preprocessedHeight)
        && rowsOk (proof.stage1Opened.getD pos #[]) 2 c.mainWidth
        && rowsOk (proof.stage2Opened.getD pos #[]) 2 c.stage2Width
        && ((sys.preprocessedIndices.getD ci none).isNone
          || rowsOk (preprocessedRows sys proof ci) 2 c.preprocessedWidth)
        && rowsOk (proof.quotientOpened.getD pos #[]) 1 (c.quotientDegree * d))

end Shape

/-! ## The transcript -/

section Transcript

variable {σ F EF D InputProof CommitProof : Type} [FieldOps F]

/-- A size, absorbed as a base-field element (`from_usize`). -/
def observeNat (n : Nat) : Observation F EF D :=
  .base (fieldOfNat n)

/-- The sizes of a system (`observe_shape`): the number of circuits, and for
each circuit its number of constraint values, its largest constraint degree,
the height and the width of its fixed trace, the widths of its main and lookup
traces, and its lookup group size. -/
def shapeMessage (sys : System F D) : List (Observation F EF D) :=
  observeNat sys.circuits.size :: sys.circuits.toList.flatMap fun c =>
    [observeNat c.constraintCount, observeNat c.maxConstraintDegree,
      observeNat c.preprocessedHeight, observeNat c.preprocessedWidth, observeNat c.mainWidth,
      observeNat c.stage2Width, observeNat c.lookupGroupSize]

/-- An activation bitmap, one field element per bit. -/
def activeMessage (active : Array Bool) : List (Observation F EF D) :=
  active.toList.map fun a => .base (if a then 1 else 0)

/-- The commitment to the fixed traces, if the system has one. -/
def fixedMessage (sys : System F D) : List (Observation F EF D) :=
  match sys.preprocessedCommit with
  | some c => [.digest c]
  | none => []

/-- The public claims with their lengths (`observe_claims`): the number of
claims, then each claim's length and elements. -/
def claimsMessage (claims : Array (Array F)) : List (Observation F EF D) :=
  observeNat claims.size :: claims.toList.flatMap fun claim =>
    observeNat claim.size :: claim.toList.map .base

/-- What the verifier of one proof absorbs before the lookup challenges. -/
def firstMessage (sys : System F D) (proof : Proof F EF D InputProof CommitProof)
    (claims : Array (Array F)) : List (Observation F EF D) :=
  shapeMessage sys ++ activeMessage proof.active ++ fixedMessage sys
    ++ [.digest proof.stage1Commit] ++ proof.logDegrees.toList.map observeNat
    ++ claimsMessage claims

/-- What the verifier of a batch absorbs before the lookup challenges
(`batch_challenger`): the sizes of the system, the commitment to the fixed
traces, the header of every shard and the messages of the batch, each list
with its length. -/
def batchFirstMessage (sys : System F D) (preamble : BatchPreamble F D) :
    List (Observation F EF D) :=
  shapeMessage sys ++ fixedMessage sys
    ++ observeNat preamble.headers.size :: preamble.headers.toList.flatMap (fun h =>
      activeMessage h.active ++ [.digest h.stage1Commit]
        ++ observeNat h.logDegrees.size :: h.logDegrees.toList.map observeNat
        ++ claimsMessage h.claims)
    ++ observeNat preamble.messages.size :: preamble.messages.toList.flatMap (fun m =>
      observeNat m.args.size :: m.args.toList.map .base ++ [.base m.multiplicity])

/-- The two lookup challenges `β` and `γ`, and the state after them
(`sample_lookup_challenges`): each is absorbed back after it is squeezed. -/
def lookupChallenges (chal : Challenger σ F EF D) (s : σ) : EF × EF × σ :=
  let beta := chal.sampleExt s
  let s := chal.observe beta.2 (.ext beta.1)
  let gamma := chal.sampleExt s
  (beta.1, gamma.1, chal.observe gamma.2 (.ext gamma.1))

/-- The challenges of the part of a run that follows the lookup challenges. -/
structure Challenges (σ EF : Type) where
  /-- The challenge that folds the constraints of a circuit. -/
  alpha : EF
  /-- The out-of-domain point. -/
  zeta : EF
  /-- The state of the challenger after `zeta`: where the opening proof
  starts. -/
  state : σ

/-- What the verifier absorbs between the lookup challenges and the constraint
challenge: the commitment to the lookup traces and the lookup sum leaving each
active circuit. -/
def secondMessage (proof : Proof F EF D InputProof CommitProof) : List (Observation F EF D) :=
  .digest proof.stage2Commit :: proof.intermediateAccumulators.toList.map .ext

/-- The constraint challenge and the out-of-domain point, derived from the
challenger in state `s`: absorb `secondMessage`, squeeze `α`, absorb the
commitment to the quotients, squeeze `ζ`. -/
def mainChallenges (chal : Challenger σ F EF D) (s : σ)
    (proof : Proof F EF D InputProof CommitProof) : Challenges σ EF :=
  let alpha := chal.sampleExt (chal.observeAll s (secondMessage proof))
  let zeta := chal.sampleExt (chal.observe alpha.2 (.digest proof.quotientCommit))
  { alpha := alpha.1, zeta := zeta.1, state := zeta.2 }

end Transcript

/-! ## The lookup sum of public messages -/

section Accumulator

variable {F EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]

/-- The fingerprint of a message: `∑_i γ^i * args[i]`. -/
def fingerprint (gamma : EF) (args : Array F) : EF :=
  args.foldr (fun a acc => acc * gamma + ExtensionOps.embed a) 0

/-- The lookup sum of messages given with their multiplicities:
`∑ multiplicity / (β + fingerprint)`, and whether every denominator is nonzero
(`try_messages_accumulator`). -/
def messagesAccumulator (beta gamma : EF) (messages : List (Array F × F)) : Bool × EF :=
  messages.foldl
    (fun acc m =>
      let denominator := beta + fingerprint gamma m.1
      (acc.1 && !(denominator == 0), acc.2 + denominator⁻¹ * ExtensionOps.embed m.2))
    (true, 0)

/-- The lookup sum of public claims, each with multiplicity one
(`try_claims_accumulator`). -/
def claimsAccumulator (beta gamma : EF) (claims : Array (Array F)) : Bool × EF :=
  messagesAccumulator beta gamma (claims.toList.map fun claim => (claim, 1))

end Accumulator

/-! ## The opening claims -/

section Openings

variable {F EF D InputProof CommitProof : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F]
  [ExtensionOps F EF]

/-- The successor of a point for a trace of `2 ^ k` rows: the point times the
generator of the trace domain. A column at the successor of `x` is its next
row at `x`. -/
def nextPoint (k : Nat) (zeta : EF) : EF :=
  zeta * ExtensionOps.embed (TwoAdicOps.twoAdicGenerator (F := F) k)

/-- The claims about one matrix of `2 ^ k` rows: row `i` of `rows` holds its
columns at `points[i]`. -/
def matrixOpening (k : Nat) (points : List EF) (rows : Array (Array EF)) : MatrixOpening EF :=
  { logDegree := k
    points := ((points.zip rows.toList).map fun pr => { point := pr.1, values := pr.2 }).toArray }

/-- **The claims the opening proof is checked against**, in the order the
prover opened them: the main traces, the lookup traces and the quotients of
the active circuits, then the fixed traces of all circuits that have one.

A trace of an active circuit is opened at `ζ` and at its successor; a quotient
at `ζ`; the fixed trace of an inactive circuit at `ζ`, on its own domain. -/
def openingClaims (sys : System F D) (proof : Proof F EF D InputProof CommitProof) (zeta : EF) :
    Array (CommitmentOpening EF D) :=
  let act := activeIndices proof.active
  let twoPoints (k : Nat) : List EF := [zeta, nextPoint (F := F) k zeta]
  let traces (opened : Array (Array (Array EF))) (points : Nat → List EF) :
      Array (MatrixOpening EF) :=
    (act.zipIdx.map fun (_, pos) =>
      let k := proof.logDegrees.getD pos 0
      matrixOpening k (points k) (opened.getD pos #[])).toArray
  let fixed : Array (MatrixOpening EF) :=
    ((List.range sys.circuits.size).filterMap fun ci =>
      if (sys.preprocessedIndices.getD ci none).isNone then none
      else
        let rows := preprocessedRows sys proof ci
        match act.idxOf? ci with
        | some pos =>
          let k := proof.logDegrees.getD pos 0
          some (matrixOpening k (twoPoints k) rows)
        | none =>
          some (matrixOpening (Nat.log2 (sys.circuits.getD ci default).preprocessedHeight)
            [zeta] rows)).toArray
  #[{ commitment := proof.stage1Commit, matrices := traces proof.stage1Opened twoPoints },
    { commitment := proof.stage2Commit, matrices := traces proof.stage2Opened twoPoints },
    { commitment := proof.quotientCommit, matrices := traces proof.quotientOpened fun _ => [zeta] }]
    ++ match sys.preprocessedCommit with
      | some c => #[{ commitment := c, matrices := fixed }]
      | none => #[]

end Openings

/-! ## The constraints of one circuit -/

section Constraints

variable {F EF : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]

/-- The row selectors of a trace domain at a point outside it, and the inverse
of its vanishing polynomial there. -/
structure Selectors (EF : Type) where
  /-- A multiple of the Lagrange polynomial of the first row. -/
  isFirstRow : EF
  /-- A multiple of the Lagrange polynomial of the last row. -/
  isLastRow : EF
  /-- The polynomial that vanishes on the last row only. -/
  isTransition : EF
  /-- The inverse of the vanishing polynomial of the domain. -/
  invVanishing : EF

/-- The selectors of the trace domain of `2 ^ k` rows at `zeta` (Plonky3's
`selectors_at_point` for a subgroup): with `Z = zeta ^ (2 ^ k) - 1` and `g` the
generator, `Z / (zeta - 1)`, `Z / (zeta - g⁻¹)`, `zeta - g⁻¹` and `1 / Z`. The
selectors are not normalised: on its own row the first is `2 ^ k` and the
second `2 ^ k * g`. -/
def selectorsAt (k : Nat) (zeta : EF) : Selectors EF :=
  let vanishing := fieldPowTwo zeta k - 1
  let last : EF := ExtensionOps.embed (TwoAdicOps.twoAdicGenerator (F := F) k)⁻¹
  { isFirstRow := vanishing * (zeta - 1)⁻¹
    isLastRow := vanishing * (zeta - last)⁻¹
    isTransition := zeta - last
    invVanishing := vanishing⁻¹ }

/-- The public values of a circuit: the coordinates of `β`, of `γ`, of the
lookup sum entering the circuit and of the one leaving it, each coordinate
embedded in the extension. -/
def lookupPublics (beta gamma acc nextAcc : EF) : Array EF :=
  ([beta, gamma, acc, nextAcc].flatMap fun e =>
    (ExtensionOps.toBasis (F := F) e).toList.map ExtensionOps.embed).toArray

/-- The quotient at `ζ`, reassembled from its opened chunks:
`∑_i (ζ ^ n) ^ i * chunk_i`, where chunk `i` is given by the coordinates at
positions `i * d` to `i * d + d - 1` of the opened row. -/
def quotientValue (chunks : Nat) (zetaPowN : EF) (row : Array EF) : EF :=
  let d := ExtensionOps.degree (F := F) (EF := EF)
  ((List.range chunks).foldl
    (fun (acc : EF × EF) i =>
      (acc.1 + acc.2 * fromExtBasis F (row.extract (i * d) ((i + 1) * d)), acc.2 * zetaPowN))
    (0, 1)).1

/-- **The constraint check of one circuit** with a trace of `2 ^ k` rows.

`preprocessed`, `main` and `stage2` hold the rows opened at `ζ` and at its
successor, `quotientRow` the chunks of the quotient at `ζ`; `acc` and `nextAcc`
are the lookup sums entering and leaving the circuit.

The values of the zeros of the graph, followed by the lookup constraints, are
folded with `α`, first value at the highest power. The result times the inverse
of the vanishing polynomial at `ζ` must be the quotient at `ζ`. -/
def circuitOk (c : Circuit F) (k : Nat) (beta gamma acc nextAcc alpha zeta : EF)
    (preprocessed main stage2 : Array (Array EF)) (quotientRow : Array EF) : Bool :=
  let d := ExtensionOps.degree (F := F) (EF := EF)
  let sels := selectorsAt (F := F) k zeta
  let publics := lookupPublics (F := F) beta gamma acc nextAcc
  let view : RowValues EF :=
    { preprocessed := preprocessed.getD 0 #[]
      preprocessedNext := preprocessed.getD 1 #[]
      main := main.getD 0 #[]
      mainNext := main.getD 1 #[]
      stage2 := stage2.getD 0 #[]
      stage2Next := stage2.getD 1 #[]
      publics := publics
      isFirstRow := sels.isFirstRow
      isLastRow := sels.isLastRow
      isTransition := sels.isTransition }
  let buf := c.graph.sweep view
  let lastRowValue : F := fieldOfNat (2 ^ k) * TwoAdicOps.twoAdicGenerator (F := F) k
  let deltaScaled : Array EF := Array.ofFn (n := d) fun j =>
    (publics.getD (3 * d + j.val) 0 - publics.getD (2 * d + j.val) 0)
      * ExtensionOps.embed lastRowValue⁻¹
  let values := c.graph.constraintValues buf
    ++ logupConstraintValues F c.graph.lookups buf view.stage2 view.stage2Next publics deltaScaled
      sels.isLastRow c.lookupGroupSize
  let composition := values.foldl (fun folded v => folded * alpha + v) 0
  composition * sels.invVanishing
    == quotientValue (F := F) c.quotientDegree (fieldPowTwo zeta k) quotientRow

end Constraints

/-! ## The verifier -/

section Verify

variable {σ F EF D : Type} [FieldOps F] [FieldOps EF] [TwoAdicOps F] [ExtensionOps F EF]
  [Inhabited D]

/-- The out-of-domain point is usable: it is not zero, and it is outside the
trace domain of every active circuit. -/
def zetaOk {InputProof CommitProof : Type} (proof : Proof F EF D InputProof CommitProof)
    (zeta : EF) : Bool :=
  !(zeta == 0)
    && (List.range (activeIndices proof.active).length).all fun pos =>
      !(fieldPowTwo zeta (proof.logDegrees.getD pos 0) == 1)

/-- The constraint checks of all active circuits, the lookup sum `acc` entering
the first one. Each circuit hands its outgoing sum to the next. -/
def constraintsOk {InputProof CommitProof : Type} (sys : System F D)
    (proof : Proof F EF D InputProof CommitProof) (beta gamma acc alpha zeta : EF) : Bool :=
  (activeIndices proof.active).zipIdx.all fun (ci, pos) =>
    circuitOk (sys.circuits.getD ci default) (proof.logDegrees.getD pos 0) beta gamma
      (if pos = 0 then acc else proof.intermediateAccumulators.getD (pos - 1) 0)
      (proof.intermediateAccumulators.getD pos 0) alpha zeta
      (preprocessedRows sys proof ci) (proof.stage1Opened.getD pos #[])
      (proof.stage2Opened.getD pos #[]) ((proof.quotientOpened.getD pos #[]).getD 0 #[])

/-- **The checks that follow the lookup challenges** (`verify_after_challenges`),
from the challenger in state `s`, with the lookup challenges `beta` and `gamma`
and the lookup sum `acc` entering the first circuit: the out-of-domain point is
usable, the opened values are those of the committed columns, and every active
circuit passes its constraint check. -/
def checkAfterChallenges (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (chal : Challenger σ F EF D) (sys : System F D)
    (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof) (s : σ)
    (beta gamma acc : EF) : Bool :=
  let ch := mainChallenges chal s proof
  zetaOk proof ch.zeta
    && verifyClaimsFrom inputMmcs friMmcs chal ch.state sys.fri
      (openingClaims sys proof ch.zeta) proof.openingProof
    && constraintsOk sys proof beta gamma acc ch.alpha ch.zeta

/-- The lookup sum leaving the last active circuit of a proof; zero if the
proof has none. -/
def residual {InputProof CommitProof : Type} (proof : Proof F EF D InputProof CommitProof) :
    EF :=
  proof.intermediateAccumulators.back?.getD 0

/-- **The multi-stark verifier, for one proof.** Accept `proof` as a proof for
the system `sys` with the public claims `claims`.

`inputMmcs` and `friMmcs` are the commitment schemes of the committed matrices
and of the codewords of the opening proof. `chal` is the challenger and `init`
its state before anything of this run is absorbed; in multi-stark that state
already binds the parameters of the opening proof
(`initialise_challenger`). -/
def verify (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D)
    (init : σ) (sys : System F D) (claims : Array (Array F))
    (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  shapeOk sys proof
    && residual proof == 0
    &&
      let lc := lookupChallenges chal (chal.observeAll init (firstMessage sys proof claims))
      let acc := claimsAccumulator lc.1 lc.2.1 claims
      acc.1 && checkAfterChallenges inputMmcs friMmcs chal sys proof lc.2.2 lc.1 lc.2.1 acc.2

/-- The check of shard `shard` of a batch (`verify_batch_shard_from`), from the
shared state `s` and the shared lookup challenges: the proof has the shape the
system fixes and is the one its header describes, and it passes the checks that
follow the lookup challenges, after the position of the shard is absorbed. The
lookup sum entering its first circuit is that of the header's claims. -/
def shardOk [BEq D] (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D) (chal : Challenger σ F EF D)
    (sys : System F D) (s : σ) (beta gamma : EF) (shard : Nat) (header : ShardHeader F D)
    (proof : Proof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  shapeOk sys proof
    && header.active == proof.active
    && header.stage1Commit == proof.stage1Commit
    && header.logDegrees == proof.logDegrees
    &&
      let acc := claimsAccumulator beta gamma header.claims
      acc.1 && checkAfterChallenges inputMmcs friMmcs chal sys proof
        (chal.observe s (observeNat shard)) beta gamma acc.2

/-- **The multi-stark verifier, for a batch.** Accept `batch` as a batch proof
for the system `sys`: there is a shard, one proof per header, no message of the
batch is zero, every shard passes its check under the shared challenges, and
the residuals of the shards and the lookup sum of the batch's messages add up
to zero. -/
def verifyBatch [BEq D] (inputMmcs : Mmcs F D) (friMmcs : Mmcs EF D)
    (chal : Challenger σ F EF D) (init : σ) (sys : System F D)
    (batch : BatchProof F EF D inputMmcs.MultiProof friMmcs.MultiProof) : Bool :=
  let headers := batch.preamble.headers
  headers.size != 0
    && headers.size == batch.proofs.size
    &&
      let lc := lookupChallenges chal
        (chal.observeAll init (batchFirstMessage sys batch.preamble))
      let messages := messagesAccumulator lc.1 lc.2.1
        (batch.preamble.messages.toList.map fun m => (m.args, m.multiplicity))
      messages.1
        && (headers.toList.zip batch.proofs.toList).zipIdx.all (fun (hp, shard) =>
          shardOk inputMmcs friMmcs chal sys lc.2.2 lc.1 lc.2.1 shard hp.1 hp.2)
        && batch.proofs.foldl (fun total proof => total + residual proof) messages.2 == 0

end Verify

end CertiFri.Stark
