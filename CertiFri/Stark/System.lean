import CertiFri.Params
import CertiFri.Proof
import CertiFri.Stark.Graph

/-!
# Systems and proofs of multi-stark

The data the multi-stark verifier works on, as Lean structures: a system of
circuits (the verifying key), a proof, and the preamble and proofs of a batch.
Ports of `Circuit` and `System` (`src/system.rs`), `Proof` (`src/prover.rs`),
`ShardHeader`, `BatchMessage`, `BatchPreamble` and `BatchProof`
(`src/batch.rs`) of multi-stark at revision `3515632`.

Only what the verifier reads is kept. A system here has no fixed trace (only
its commitment), no prover key and no backend hooks; a circuit has no count of
lookups or of public values, which the verifier takes from the graph and from
the degree of the extension.

## Differences from multi-stark

* The values opened on the fixed traces are an array, empty when the system
  has no fixed trace. multi-stark has an optional array there and treats a
  missing one as empty.
* Sizes and logarithms are natural numbers. multi-stark stores the log of a
  trace height in a byte.

Decoding a proof or a key from bytes is not part of this port.
-/

namespace CertiFri.Stark

/-- One circuit of a system, as the verifier reads it. -/
structure Circuit (F : Type) where
  /-- The constraints and the lookups. -/
  graph : Graph F
  /-- Number of columns of the main trace. -/
  mainWidth : Nat
  /-- Number of columns of the fixed trace; zero if the circuit has none. -/
  preprocessedWidth : Nat
  /-- Number of rows of the fixed trace; zero if the circuit has none. A
  circuit with a fixed trace is proved at exactly this height. -/
  preprocessedHeight : Nat
  /-- Number of columns of the lookup trace: the degree of the extension for
  each group of lookups. -/
  stage2Width : Nat
  /-- Number of lookups whose messages share one accumulator step. -/
  lookupGroupSize : Nat
  /-- Number of constraint values folded with the constraint challenge: the
  zeros of the graph and the lookup constraints. The verifier only absorbs
  it. -/
  constraintCount : Nat
  /-- The largest degree of a constraint, as a multiple of the trace degree.
  It fixes the number of chunks of the quotient. -/
  maxConstraintDegree : Nat
  deriving Inhabited

/-- The number of chunks the quotient of a circuit is committed in
(`Circuit::quotient_degree`): the least power of two that is at least
`max(maxConstraintDegree, 2) - 1`. -/
def Circuit.quotientDegree {F : Type} (c : Circuit F) : Nat :=
  (max c.maxConstraintDegree 2 - 1).nextPowerOfTwo

/-- A system of circuits with the parameters its proofs are checked under:
the verifying key. -/
structure System (F D : Type) where
  /-- The circuits. -/
  circuits : Array (Circuit F)
  /-- The commitment to the fixed traces of all circuits, if any has one. -/
  preprocessedCommit : Option D
  /-- For each circuit, the position of its fixed trace under
  `preprocessedCommit`, if it has one. Positions increase with the circuit. -/
  preprocessedIndices : Array (Option Nat)
  /-- The parameters of the opening proof. -/
  fri : FriParams
  /-- The largest log of a trace height the commitment scheme supports
  (`max_log_degree`), which also bounds the log of the quotient domain. -/
  maxLogDegree : Nat

/-- A proof for a system. `F` and `EF` are the base field and the extension,
`D` the digests, `InputProof` and `CommitProof` the opening proofs of the two
commitment schemes of the opening argument.

Apart from `active`, every array with one entry per circuit has one entry per
*active* circuit, in the order of the circuits. Opened values are indexed by
matrix, then opening point, then column. -/
structure Proof (F EF D InputProof CommitProof : Type) where
  /-- Which circuits the proof covers. An inactive circuit has an empty
  trace: it is not committed, not opened and not checked. -/
  active : Array Bool
  /-- The commitment to the main traces. -/
  stage1Commit : D
  /-- The commitment to the lookup traces. -/
  stage2Commit : D
  /-- The commitment to the chunks of the quotients. -/
  quotientCommit : D
  /-- The lookup sum leaving each active circuit. -/
  intermediateAccumulators : Array EF
  /-- The log of the trace height of each active circuit. -/
  logDegrees : Array Nat
  /-- The opened chunks of the quotient of each active circuit, at the
  out-of-domain point. -/
  quotientOpened : Array (Array (Array EF))
  /-- The opened rows of each fixed trace, by position under the commitment:
  at the out-of-domain point and its successor for an active circuit, at the
  point alone for an inactive one. -/
  preprocessedOpened : Array (Array (Array EF))
  /-- The opened rows of the main trace of each active circuit, at the
  out-of-domain point and its successor. -/
  stage1Opened : Array (Array (Array EF))
  /-- The opened rows of the lookup trace of each active circuit, at the
  out-of-domain point and its successor. -/
  stage2Opened : Array (Array (Array EF))
  /-- The opening proof for all the opened values. -/
  openingProof : FriProof F EF D InputProof CommitProof

/-- What one shard of a batch publishes before the lookup challenges are
drawn. -/
structure ShardHeader (F D : Type) where
  /-- The activation bitmap of the shard's proof. -/
  active : Array Bool
  /-- The commitment to the shard's main traces. -/
  stage1Commit : D
  /-- The log trace heights of the shard's proof. -/
  logDegrees : Array Nat
  /-- The public claims of the shard. -/
  claims : Array (Array F)

/-- A lookup message of the batch that no shard carries: a claim, or a pull
the verifier performs. -/
structure BatchMessage (F : Type) where
  /-- The arguments of the message. -/
  args : Array F
  /-- Its multiplicity. -/
  multiplicity : F

/-- Everything the shared lookup challenges of a batch depend on. -/
structure BatchPreamble (F D : Type) where
  /-- One header per shard. -/
  headers : Array (ShardHeader F D)
  /-- The messages of the batch. -/
  messages : Array (BatchMessage F)

/-- A batch proof: the preamble and one proof per shard. -/
structure BatchProof (F EF D InputProof CommitProof : Type) where
  /-- The preamble. -/
  preamble : BatchPreamble F D
  /-- The proofs of the shards, in the order of the headers. -/
  proofs : Array (Proof F EF D InputProof CommitProof)

end CertiFri.Stark
