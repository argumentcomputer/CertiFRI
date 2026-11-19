import CertiFriTest.Stark.Vector

/-!
# The verifier on proofs made by multi-stark

The vectors of `CertiFriTest/vectors/stark` are systems with proofs produced by
multi-stark at revision `3515632` in its production configuration: Goldilocks,
its quadratic extension, BLAKE3 Merkle trees, the BLAKE3-based challenger
seeded with the protocol tag and the parameters, and Plonky3's FRI at revision
`3152b14a`. multi-stark's own verifier accepts each of them.

The tests run `Stark.verify` and `Stark.verifyBatch` with the primitives of
`CertiFriP3` on each vector, compare the challenges they derive with those
multi-stark derived, and check that changed statements, proofs and systems are
rejected.

This is a test on a handful of proofs. Nothing is proved about the port.
-/

namespace CertiFriTest.Stark

open CertiFri CertiFri.Stark CertiFri.P3 CertiFriTest.P3

/-! ## Running the verifier -/

/-- The state multi-stark's challenger starts from (`initialise_challenger`). -/
def initial (v : Vector) : ChallengerState := ChallengerState.new v.seed

/-- The single-proof verifier, on a system, claims and a proof. -/
def verifySingle (seed : ByteArray) (sys : System Goldilocks Digest)
    (claims : Array (Array Goldilocks)) (proof : VProof) : Bool :=
  Stark.verify (prunedMmcs baseHasher) (prunedMmcs extHasher) challenger
    (ChallengerState.new seed) sys claims proof

/-- The batch verifier, on a system and a batch proof. -/
def verifyBatched (seed : ByteArray) (sys : System Goldilocks Digest)
    (batch : BatchProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest)) :
    Bool :=
  Stark.verifyBatch (prunedMmcs baseHasher) (prunedMmcs extHasher) challenger
    (ChallengerState.new seed) sys batch

/-- A check on the single proof of a vector; a vector without one fails. -/
def onSingle (v : Vector) (f : Single → Bool) : Bool :=
  match v.single with
  | some s => f s
  | none => false

/-- A check on the batch proof of a vector; a vector without one fails. -/
def onBatch (v : Vector) (f : Batch → Bool) : Bool :=
  match v.batch with
  | some b => f b
  | none => false

/-- Run a check on a vector file; a file that does not parse fails the check. -/
def check (text : String) (f : Vector → Bool) : Bool :=
  match parseVector text with
  | .ok v => f v
  | .error _ => false

/-- The single proof of a vector is accepted. -/
def acceptsSingle (v : Vector) : Bool :=
  onSingle v fun s => verifySingle v.seed v.system s.claims s.proof

/-- The batch proof of a vector is accepted. -/
def acceptsBatch (v : Vector) : Bool :=
  onBatch v fun b => verifyBatched v.seed v.system b.proof

/-! ## The derived challenges -/

/-- The challenges derived for one proof from the state `s` after the lookup
challenges are those multi-stark derived. -/
def challengesMatch (sys : System Goldilocks Digest) (proof : VProof) (s : ChallengerState)
    (debug : Debug) : Bool :=
  let ch := mainChallenges challenger s proof
  let claims := openingClaims sys proof ch.zeta
  let fri := Fri.transcriptFrom challenger ch.state sys.fri (Fri.claimShape claims)
    (Fri.claimValues claims) proof.openingProof
  ch.alpha == debug.alpha && ch.zeta == debug.zeta && fri.alpha == debug.friAlpha && fri.powOk

/-- The challenges of the single proof of a vector are those multi-stark derived. -/
def singleChallengesMatch (v : Vector) : Bool :=
  onSingle v fun s =>
    let lc := lookupChallenges challenger
      (challenger.observeAll (initial v) (firstMessage v.system s.proof s.claims))
    lc.1 == s.beta && lc.2.1 == s.gamma && challengesMatch v.system s.proof lc.2.2 s.debug

/-- The challenges of the batch proof of a vector are those multi-stark derived. -/
def batchChallengesMatch (v : Vector) : Bool :=
  onBatch v fun b =>
    let lc := lookupChallenges challenger
      (challenger.observeAll (initial v) (batchFirstMessage v.system b.proof.preamble))
    lc.1 == b.beta && lc.2.1 == b.gamma && b.shards.size == b.proof.proofs.size
      && (b.proof.proofs.toList.zip b.shards.toList).zipIdx.all fun (pd, shard) =>
        challengesMatch v.system pd.1 (challenger.observe lc.2.2 (observeNat shard)) pd.2

/-- The number of quotient chunks of every circuit is the one multi-stark computes. -/
def quotientDegreesMatch (v : Vector) : Bool :=
  v.system.circuits.map (·.quotientDegree) == v.quotientDegrees
    && v.extensionDegree == ExtensionOps.degree (F := Goldilocks) (EF := GoldilocksExt)

/-! ## Changes that must be rejected -/

/-- Another extension element. -/
def bump (e : GoldilocksExt) : GoldilocksExt := e + 1

/-- Opened values with one entry changed. -/
def bumpOpened (opened : Array (Array (Array GoldilocksExt))) (matrix point column : Nat) :
    Array (Array (Array GoldilocksExt)) :=
  opened.modify matrix (·.modify point (·.modify column bump))

/-- Claims with the first element of the first claim changed. -/
def bumpClaims (claims : Array (Array Goldilocks)) : Array (Array Goldilocks) :=
  claims.modify 0 (·.modify 0 (· + 1))

/-- A system with the constraint graph of circuit `ci` changed by `f`. -/
def mapGraph (sys : System Goldilocks Digest) (ci : Nat)
    (f : Graph Goldilocks → Graph Goldilocks) : System Goldilocks Digest :=
  { sys with circuits := sys.circuits.modify ci fun c => { c with graph := f c.graph } }

/-- A graph with one more node, a constant one, that must vanish. -/
def addFalseZero (g : Graph Goldilocks) : Graph Goldilocks :=
  { g with nodes := g.nodes.push (.const 1), zeros := g.zeros.push g.nodes.size }

/-- A graph whose first lookup has its multiplicity negated. -/
def negateFirstLookup (g : Graph Goldilocks) : Graph Goldilocks :=
  match g.lookups[0]? with
  | some l =>
    { g with
      nodes := g.nodes.push (.neg l.multiplicity)
      lookups := g.lookups.modify 0 fun l => { l with multiplicity := g.nodes.size } }
  | none => g

/-- The changes to a proof that every vector must reject, each with a name. -/
def proofChanges : List (String × (VProof → VProof)) := [
  ("stage-1 opened value", fun p => { p with stage1Opened := bumpOpened p.stage1Opened 0 0 0 }),
  ("stage-1 next-row value", fun p => { p with stage1Opened := bumpOpened p.stage1Opened 0 1 0 }),
  ("stage-2 opened value", fun p => { p with stage2Opened := bumpOpened p.stage2Opened 0 0 0 }),
  ("stage-2 next-row value", fun p => { p with stage2Opened := bumpOpened p.stage2Opened 0 1 0 }),
  ("quotient opened value", fun p => { p with quotientOpened := bumpOpened p.quotientOpened 0 0 0 }),
  ("accumulator", fun p =>
    { p with intermediateAccumulators := p.intermediateAccumulators.modify 0 bump }),
  ("log degree", fun p => { p with logDegrees := p.logDegrees.modify 0 (· + 1) }),
  ("commitments exchanged", fun p =>
    { p with stage1Commit := p.stage2Commit, stage2Commit := p.stage1Commit }),
  ("quotient commitment", fun p => { p with quotientCommit := p.stage1Commit }),
  ("activation bit", fun p => { p with active := p.active.modify 0 (!·) }),
  ("one opened row too few", fun p => { p with stage1Opened := p.stage1Opened.modify 0 (·.pop) }),
  ("final polynomial", fun p =>
    { p with openingProof.finalPoly := p.openingProof.finalPoly.modify 0 bump }),
  ("query witness", fun p =>
    { p with openingProof.queryPowWitness := p.openingProof.queryPowWitness + 1 }),
  ("input opening", fun p =>
    { p with openingProof.inputOpenings := p.openingProof.inputOpenings.modify 0 fun o =>
      { o with openedValues := o.openedValues.modify 0 (·.modify 0 (·.modify 0 (· + 1))) } })]

/-- The changes to a system that every vector must reject, each with a name. -/
def systemChanges : List (String × (System Goldilocks Digest → System Goldilocks Digest)) := [
  ("false constraint", fun sys => mapGraph sys 0 addFalseZero),
  ("group size", fun sys =>
    { sys with circuits := sys.circuits.modify 0 fun c =>
      { c with lookupGroupSize := c.lookupGroupSize + 1 } }),
  ("constraint count", fun sys =>
    { sys with circuits := sys.circuits.modify 0 fun c =>
      { c with constraintCount := c.constraintCount + 1 } }),
  ("query count", fun sys => { sys with fri.numQueries := sys.fri.numQueries + 1 }),
  ("blowup", fun sys => { sys with fri.logBlowup := sys.fri.logBlowup + 1 })]

/-- The names of the changes to the single proof of a vector that are wrongly
accepted. -/
def acceptedSingleChanges (v : Vector) : List String :=
  match v.single with
  | none => ["no single proof"]
  | some s =>
    (proofChanges.filterMap fun (name, f) =>
      if verifySingle v.seed v.system s.claims (f s.proof) then some name else none)
    ++ (systemChanges.filterMap fun (name, f) =>
      if verifySingle v.seed (f v.system) s.claims s.proof then some name else none)
    ++ (if verifySingle (v.seed.push 0) v.system s.claims s.proof then ["seed"] else [])

/-- The names of the changes to shard `shard` of the batch proof of a vector
that are wrongly accepted. -/
def acceptedBatchChanges (v : Vector) (shard : Nat) : List String :=
  match v.batch with
  | none => ["no batch proof"]
  | some b =>
    (proofChanges.filterMap fun (name, f) =>
      if verifyBatched v.seed v.system { b.proof with proofs := b.proof.proofs.modify shard f }
      then some name else none)
    ++ (systemChanges.filterMap fun (name, f) =>
      if verifyBatched v.seed (f v.system) b.proof then some name else none)
    ++ (if verifyBatched (v.seed.push 0) v.system b.proof then ["seed"] else [])

/-! ## The vectors -/

def lookup : String := include_str "../vectors/stark/lookup.json"
def fixed : String := include_str "../vectors/stark/fixed.json"
def batch : String := include_str "../vectors/stark/batch.json"
def sparse : String := include_str "../vectors/stark/sparse.json"

/-- The circuits a single proof covers and the log trace height of each. -/
def activity (v : Vector) : Option (List Nat × Array Nat) :=
  v.single.map fun s => (activeIndices s.proof.active, s.proof.logDegrees)

-- The vectors have the intended features. `lookup`: two circuits of
-- different heights, no fixed trace, no grinding.
#guard check lookup fun v =>
  activity v == some ([0, 1], #[3, 2]) && v.system.preprocessedCommit.isNone
    && v.system.fri.queryPowBits == 0

-- `fixed`: an inactive circuit, two fixed traces, lookups grouped by two with
-- a last group of one, quotients of one, two and four chunks, grinding.
#guard check fixed fun v =>
  activity v == some ([0, 1, 3], #[2, 3, 2])
    && v.system.preprocessedIndices == #[none, some 0, none, some 1]
    && v.system.circuits.map (fun c => (c.graph.lookups.size, c.lookupGroupSize))
      == #[(3, 2), (1, 1), (1, 1), (0, 1)]
    && v.quotientDegrees == #[2, 1, 1, 4]
    && v.system.fri.commitPowBits == 2 && v.system.fri.queryPowBits == 4

-- `sparse`: the same system, with a circuit that has a fixed trace left
-- inactive, and a final polynomial of two coefficients.
#guard check sparse fun v =>
  activity v == some ([0, 1], #[2, 3]) && v.system.fri.logFinalPolyLen == 1

-- `batch`: two shards, the second with one active circuit, and two messages.
#guard check batch fun v => onBatch v fun b =>
  b.proof.proofs.map (fun p => activeIndices p.active) == #[[0, 1], [1]]
    && b.proof.preamble.messages.size == 2

/-! ## multi-stark's proofs are accepted -/

-- The number of quotient chunks of every circuit.
#guard check lookup quotientDegreesMatch
#guard check fixed quotientDegreesMatch
#guard check batch quotientDegreesMatch
#guard check sparse quotientDegreesMatch

-- The transcript: the same challenges as multi-stark.
#guard check lookup singleChallengesMatch
#guard check fixed singleChallengesMatch
#guard check sparse singleChallengesMatch
#guard check batch batchChallengesMatch

-- The single-proof verifier.
#guard check lookup acceptsSingle
#guard check fixed acceptsSingle
#guard check sparse acceptsSingle

-- The batch verifier.
#guard check batch acceptsBatch

/-! ## Changed proofs, systems and parameters are rejected -/

-- With grinding before the queries, every change is rejected.
#guard check fixed fun v => acceptedSingleChanges v == []
#guard check sparse fun v => acceptedSingleChanges v == []

-- Without it the witness is neither absorbed nor checked, as in Plonky3, so a
-- changed witness is accepted. Every other change is rejected.
#guard check lookup fun v => acceptedSingleChanges v == ["query witness"]
#guard check batch fun v => acceptedBatchChanges v 0 == ["query witness"]
#guard check batch fun v => acceptedBatchChanges v 1 == ["query witness"]

-- The claims are part of the statement.
#guard check lookup fun v => onSingle v fun s =>
  !verifySingle v.seed v.system (bumpClaims s.claims) s.proof
#guard check fixed fun v => onSingle v fun s =>
  !verifySingle v.seed v.system (s.claims.push #[1, 1]) s.proof
    && !verifySingle v.seed v.system s.claims.pop s.proof

-- A lookup sent with the opposite multiplicity: the sizes of the system, and
-- so the transcript, are unchanged, and the lookup constraints fail.
#guard check lookup fun v => onSingle v fun s =>
  !verifySingle v.seed (mapGraph v.system 0 negateFirstLookup) s.claims s.proof
#guard check fixed fun v => onSingle v fun s =>
  !verifySingle v.seed (mapGraph v.system 0 negateFirstLookup) s.claims s.proof

-- A false constraint on any circuit that is active.
#guard check fixed fun v => onSingle v fun s =>
  [0, 1, 3].all fun ci => !verifySingle v.seed (mapGraph v.system ci addFalseZero) s.claims s.proof

-- A change to an inactive circuit's constraints is not noticed: an inactive
-- circuit is not checked.
#guard check fixed fun v => onSingle v fun s =>
  verifySingle v.seed (mapGraph v.system 2 addFalseZero) s.claims s.proof

-- A value opened on a fixed trace, of an active circuit and of an inactive one.
#guard check sparse fun v => onSingle v fun s =>
  [0, 1].all fun slot => !verifySingle v.seed v.system s.claims
    { s.proof with preprocessedOpened := bumpOpened s.proof.preprocessedOpened slot 0 0 }

-- The commitment to the fixed traces.
#guard check fixed fun v => onSingle v fun s =>
  !verifySingle v.seed { v.system with preprocessedCommit := some s.proof.stage1Commit }
    s.claims s.proof

/-- A single proof with its claims, presented as a batch of one shard without
messages. -/
def asBatch (s : Single) :
    BatchProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest) :=
  let header : ShardHeader Goldilocks Digest :=
    { active := s.proof.active
      stage1Commit := s.proof.stage1Commit
      logDegrees := s.proof.logDegrees
      claims := s.claims }
  { preamble := { headers := #[header], messages := #[] }, proofs := #[s.proof] }

-- A single proof is not a batch of one, and a shard is not a single proof.
#guard check lookup fun v => onSingle v fun s => !verifyBatched v.seed v.system (asBatch s)
#guard check batch fun v => onBatch v fun b =>
  (b.proof.preamble.headers.toList.zip b.proof.proofs.toList).all fun (h, p) =>
    !verifySingle v.seed v.system h.claims p

/-! ## Changed batches are rejected -/

/-- The batch proof of a vector, changed by `f`, is rejected. -/
def rejectsBatch (v : Vector)
    (f : BatchProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest) →
      BatchProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest)) :
    Bool :=
  onBatch v fun b => !verifyBatched v.seed v.system (f b.proof)

-- The shards exchanged, proofs alone and proofs with headers.
#guard check batch fun v => rejectsBatch v fun b => { b with proofs := b.proofs.reverse }
#guard check batch fun v => rejectsBatch v fun b =>
  { preamble := { b.preamble with headers := b.preamble.headers.reverse }
    proofs := b.proofs.reverse }

-- A shard dropped, with its header.
#guard check batch fun v => rejectsBatch v fun b =>
  { preamble := { b.preamble with headers := b.preamble.headers.pop }, proofs := b.proofs.pop }

-- No shard at all.
#guard check batch fun v => rejectsBatch v fun b =>
  { preamble := { b.preamble with headers := #[] }, proofs := #[] }

-- The messages of the batch: one changed, one dropped, all dropped.
#guard check batch fun v => rejectsBatch v fun b =>
  { b with preamble.messages := b.preamble.messages.modify 0 fun m =>
    { m with multiplicity := m.multiplicity + 1 } }
#guard check batch fun v => rejectsBatch v fun b =>
  { b with preamble.messages := b.preamble.messages.modify 0 fun m =>
    { m with args := m.args.modify 0 (· + 1) } }
#guard check batch fun v => rejectsBatch v fun b =>
  { b with preamble.messages := b.preamble.messages.pop }
#guard check batch fun v => rejectsBatch v fun b => { b with preamble.messages := #[] }

-- A claim of a header.
#guard check batch fun v => rejectsBatch v fun b =>
  { b with preamble.headers := b.preamble.headers.modify 0 fun h =>
    { h with claims := bumpClaims h.claims } }

-- A header that does not describe its proof.
#guard check batch fun v => rejectsBatch v fun b =>
  { b with preamble.headers := b.preamble.headers.modify 1 fun h =>
    { h with logDegrees := h.logDegrees.modify 0 (· + 1) } }

end CertiFriTest.Stark
