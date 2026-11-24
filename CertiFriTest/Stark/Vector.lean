import CertiFriTest.P3.Vector
import CertiFri.Stark.Verifier

/-!
# Reading the multi-stark test vectors

A decoder for the JSON files that `CertiFriTest/vectors/stark` writes: a
system, and proofs for it made by multi-stark at revision `3515632`, with the
challenges multi-stark's verifier derives on the way. The schema is documented
in `CertiFriTest/vectors/stark/README.md`. Field elements, digests and the
opening proof are encoded as in the FRI vectors (`CertiFriTest/P3/Vector.lean`).

This is test code. The JSON format is this repository's own; multi-stark
serialises proofs with bincode, which is not decoded here.
-/

namespace CertiFriTest.Stark

open Lean (Json)
open CertiFri CertiFri.Stark CertiFri.P3 CertiFriTest.P3

/-- The proofs of the vectors: over Goldilocks and its quadratic extension,
with BLAKE3 digests and Plonky3's pruned Merkle proofs. -/
abbrev VProof := Proof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest)

def parseBool (j : Json) : Parse Bool := j.getBool?

def parseString (j : Json) : Parse String := j.getStr?

/-- A value that may be `null`. -/
def parseOption {α : Type} (f : Json → Parse α) (j : Json) : Parse (Option α) :=
  if j.isNull then pure none else some <$> f j

/-- A key that may be absent or `null`. -/
def parseOptKey {α : Type} (j : Json) (key : String) (f : Json → Parse α) : Parse (Option α) :=
  match j.getObjVal? key with
  | .ok v => parseOption f v
  | .error _ => pure none

def parseSource (j : Json) : Parse Source := do
  match ← parseString j with
  | "preprocessed" => pure .preprocessed
  | "main" => pure .main
  | "stage2" => pure .stage2
  | other => throw s!"unknown source {other}"

def parseNode (j : Json) : Parse (Node Goldilocks) := do
  match ← parseKey j "op" parseString with
  | "const" => pure (.const (← parseKey j "value" parseField))
  | "var" =>
    pure (.var {
      source := ← parseKey j "source" parseSource
      next := ← parseKey j "next" parseBool
      index := ← parseKey j "index" parseNat })
  | "public" => pure (.pub (← parseKey j "index" parseNat))
  | "is_first_row" => pure .isFirstRow
  | "is_last_row" => pure .isLastRow
  | "is_transition" => pure .isTransition
  | "add" => pure (.add (← parseKey j "a" parseNat) (← parseKey j "b" parseNat))
  | "sub" => pure (.sub (← parseKey j "a" parseNat) (← parseKey j "b" parseNat))
  | "mul" => pure (.mul (← parseKey j "a" parseNat) (← parseKey j "b" parseNat))
  | "neg" => pure (.neg (← parseKey j "a" parseNat))
  | other => throw s!"unknown node {other}"

def parseGraph (j : Json) : Parse (Graph Goldilocks) := do
  pure {
    nodes := ← parseKey j "nodes" (parseArray parseNode)
    zeros := ← parseKey j "zeros" (parseArray parseNat)
    lookups := ← parseKey j "lookups" (parseArray fun l => do
      pure {
        multiplicity := ← parseKey l "multiplicity" parseNat
        args := ← parseKey l "args" (parseArray parseNat) }) }

/-- A circuit, with the number of quotient chunks multi-stark computes for it. -/
def parseCircuit (j : Json) : Parse (Circuit Goldilocks × Nat) := do
  let circuit : Circuit Goldilocks := {
    graph := ← parseKey j "graph" parseGraph
    mainWidth := ← parseKey j "main_width" parseNat
    preprocessedWidth := ← parseKey j "preprocessed_width" parseNat
    preprocessedHeight := ← parseKey j "preprocessed_height" parseNat
    stage2Width := ← parseKey j "stage_2_width" parseNat
    lookupGroupSize := ← parseKey j "lookup_group_size" parseNat
    constraintCount := ← parseKey j "constraint_count" parseNat
    maxConstraintDegree := ← parseKey j "max_constraint_degree" parseNat }
  pure (circuit, ← parseKey j "quotient_degree" parseNat)

/-- Opened values: `[matrix][point][column]`. -/
def parseOpened (j : Json) : Parse (Array (Array (Array GoldilocksExt))) :=
  parseArray (parseArray (parseArray parseExt)) j

def parseStarkProof (j : Json) : Parse VProof := do
  let commitments ← j.getObjVal? "commitments"
  pure {
    active := ← parseKey j "active" (parseArray parseBool)
    stage1Commit := ← parseKey commitments "stage_1_trace" parseDigest
    stage2Commit := ← parseKey commitments "stage_2_trace" parseDigest
    quotientCommit := ← parseKey commitments "quotient_chunks" parseDigest
    intermediateAccumulators := ← parseKey j "intermediate_accumulators" (parseArray parseExt)
    logDegrees := ← parseKey j "log_degrees" (parseArray parseNat)
    quotientOpened := ← parseKey j "quotient_opened_values" parseOpened
    preprocessedOpened := (← parseOptKey j "preprocessed_opened_values" parseOpened).getD #[]
    stage1Opened := ← parseKey j "stage_1_opened_values" parseOpened
    stage2Opened := ← parseKey j "stage_2_opened_values" parseOpened
    openingProof := ← parseKey j "opening_proof" (parseProof parsePruned) }

/-- The challenges multi-stark derives while it checks one proof. -/
structure Debug where
  /-- The constraint challenge. -/
  alpha : GoldilocksExt
  /-- The out-of-domain point. -/
  zeta : GoldilocksExt
  /-- The batching challenge of the opening proof. -/
  friAlpha : GoldilocksExt

def parseDebug (j : Json) : Parse Debug := do
  pure {
    alpha := ← parseKey j "constraint_challenge" parseExt
    zeta := ← parseKey j "zeta" parseExt
    friAlpha := ← parseKey j "fri_alpha" parseExt }

/-- One proof with public claims, and what multi-stark derived. -/
structure Single where
  claims : Array (Array Goldilocks)
  proof : VProof
  /-- The lookup challenge `β`. -/
  beta : GoldilocksExt
  /-- The fingerprint challenge `γ`. -/
  gamma : GoldilocksExt
  debug : Debug

/-- A batch proof, and what multi-stark derived. -/
structure Batch where
  proof : BatchProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest)
  /-- The shared lookup challenge `β`. -/
  beta : GoldilocksExt
  /-- The shared fingerprint challenge `γ`. -/
  gamma : GoldilocksExt
  /-- One entry per shard. -/
  shards : Array Debug

def parseClaimList (j : Json) : Parse (Array (Array Goldilocks)) :=
  parseArray (parseArray parseField) j

def parseSingle (j : Json) : Parse Single := do
  let debug ← j.getObjVal? "debug"
  pure {
    claims := ← parseKey j "claims" parseClaimList
    proof := ← parseKey j "proof" parseStarkProof
    beta := ← parseKey debug "lookup_challenge" parseExt
    gamma := ← parseKey debug "fingerprint_challenge" parseExt
    debug := ← parseDebug debug }

def parseBatch (j : Json) : Parse Batch := do
  let preamble ← j.getObjVal? "preamble"
  let debug ← j.getObjVal? "debug"
  pure {
    proof := {
      preamble := {
        headers := ← parseKey preamble "headers" (parseArray fun h => do
          pure {
            active := ← parseKey h "active" (parseArray parseBool)
            stage1Commit := ← parseKey h "stage_1_trace" parseDigest
            logDegrees := ← parseKey h "log_degrees" (parseArray parseNat)
            claims := ← parseKey h "claims" parseClaimList })
        messages := ← parseKey preamble "messages" (parseArray fun m => do
          pure {
            args := ← parseKey m "args" (parseArray parseField)
            multiplicity := ← parseKey m "multiplicity" parseField }) }
      proofs := ← parseKey j "proofs" (parseArray parseStarkProof) }
    beta := ← parseKey debug "lookup_challenge" parseExt
    gamma := ← parseKey debug "fingerprint_challenge" parseExt
    shards := ← parseKey debug "shards" (parseArray parseDebug) }

/-- A test vector: a system, the initial state of the challenger, and a proof
or a batch proof (or both). -/
structure Vector where
  /-- The bytes the challenger starts from: multi-stark's protocol tag and the
  parameters of the opening proof. -/
  seed : ByteArray
  system : System Goldilocks Digest
  /-- For each circuit, the number of quotient chunks multi-stark computes. -/
  quotientDegrees : Array Nat
  /-- The degree of the extension, as the file states it. -/
  extensionDegree : Nat
  single : Option Single
  batch : Option Batch

def parseVector (text : String) : Parse Vector := do
  let j ← Json.parse text
  let system ← j.getObjVal? "system"
  let circuits ← parseKey system "circuits" (parseArray parseCircuit)
  let seed ← parseKey j "seed" (parseArray fun b => do
    let n ← b.getNat?
    if n < 256 then pure n.toUInt8 else throw s!"{n} is not a byte")
  pure {
    seed := ByteArray.mk seed
    system := {
      circuits := circuits.map (·.1)
      preprocessedCommit := ← parseOptKey system "preprocessed_commit" parseDigest
      preprocessedIndices := ← parseKey system "preprocessed_indices"
        (parseArray (parseOption parseNat))
      fri := ← parseKey j "params" parseParams
      maxLogDegree := ← parseKey j "max_log_degree" parseNat }
    quotientDegrees := circuits.map (·.2)
    extensionDegree := ← parseKey j "extension_degree" parseNat
    single := ← parseOptKey j "single" parseSingle
    batch := ← parseOptKey j "batch" parseBatch }

end CertiFriTest.Stark
