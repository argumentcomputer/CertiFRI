import CertiFriTest.P3.Vector

/-!
# Benchmark of the verifier

`lake exe certifri-bench <vector.json> [runs]` reads a test vector written by
`CertiFriTest/vectors/fri` (a statement and an opening proof made by Plonky3),
runs the verifier on it `runs` times as compiled code, and prints the time per
run. It times the verifier in both forms of the commitment proofs: one full
Merkle path per query, and Plonky3's pruned proofs.

Reading and decoding the file is not timed. The verifier is `Fri.verifyClaims`
with the primitives of `CertiFriP3`, started from the empty challenger state.
It then times the parts of a run separately: the transcript, the arithmetic of
the queries, and the Merkle checks.

The vector generator prints the time of Plonky3's own verifier on the same
proof (`cargo run --release -- --bench <dir> <runs>`).
-/

open CertiFri CertiFri.Fri CertiFri.P3 CertiFriTest.P3

/-- The challenger state the vectors start from. -/
def benchInitial : ChallengerState := ChallengerState.new ByteArray.empty

/-- The verifier with one full Merkle path per query. -/
@[noinline] def benchPaths (v : Vector) : Bool :=
  verifyClaims (merkleMmcs baseHasher) (merkleMmcs extHasher) challenger benchInitial v.params
    v.claims v.paths

/-- The verifier with Plonky3's pruned Merkle proofs. -/
@[noinline] def benchPruned (v : Vector) : Bool :=
  verifyClaims (prunedMmcs baseHasher) (prunedMmcs extHasher) challenger benchInitial v.params
    v.claims v.pruned

/-- Run `f` on the vector `runs` times; print whether every run accepted and
the mean time of a run. -/
def timeRuns (name : String) (runs : Nat) (ref : IO.Ref Vector) (f : Vector → Bool) : IO Unit := do
  let start ← IO.monoNanosNow
  let mut accepted := true
  for _ in [0:runs] do
    let v ← ref.get
    accepted := accepted && f v
  let stop ← IO.monoNanosNow
  let micros := (stop - start) / (1000 * runs)
  IO.println s!"{name}: accepted={accepted}, {micros / 1000}.{(micros % 1000) / 100}{(micros % 100) / 10}{micros % 10} ms per run over {runs} runs"

/-- The challenges of a vector. -/
@[noinline] def benchChallenges (v : Vector) : Challenges GoldilocksExt :=
  transcript challenger benchInitial v.params (claimShape v.claims) (v.claims.map (·.commitment))
    (claimPoints v.claims) (claimValues v.claims) v.paths

/-- What the verifier computes for every query, given the challenges. -/
@[noinline] def benchQueries (v : Vector) (ch : Challenges GoldilocksExt) :
    Array (QueryResult GoldilocksExt) :=
  let shape := claimShape v.claims
  let n := logMaxHeight v.params.logBlowup shape
  let levelArr := Array.ofFn (n := numRounds v.params shape + 1) fun j =>
    levelClaims v.params.logBlowup shape n j.val
  Array.ofFn (n := v.params.numQueries) fun t =>
    checkQuery (F := Goldilocks) v.params shape (fun j => levelArr.getD j [])
      (claimPoints v.claims) (claimValues v.claims) v.paths ch t.val (ch.indices.getD t.val 0)

/-- The Merkle checks of the input batches, with one path per query. -/
@[noinline] def benchInputChecks (v : Vector) (ch : Challenges GoldilocksExt) : Bool :=
  inputChecks (merkleMmcs baseHasher) v.params (claimShape v.claims)
    (v.claims.map (·.commitment)) v.paths.inputOpenings ch.indices

/-- The Merkle checks of the folding rounds, with one path per query. -/
@[noinline] def benchCommitChecks (v : Vector) (ch : Challenges GoldilocksExt)
    (results : Array (QueryResult GoldilocksExt)) : Bool :=
  let shape := claimShape v.claims
  commitChecks (merkleMmcs extHasher) v.params.numQueries (logMaxHeight v.params.logBlowup shape)
    (numRounds v.params shape) v.paths.commitPhaseCommits v.paths.commitPhaseOpenings ch.indices
    (results.map (·.rows))

/-- Run `f` on the vector `runs` times; return the mean time of a run in
microseconds. The results are added up so that no run is dropped. -/
def meanMicros (runs : Nat) (ref : IO.Ref Vector) (f : Vector → Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  let mut total := 0
  for _ in [0:runs] do
    let v ← ref.get
    total := total + f v
  let stop ← IO.monoNanosNow
  if total == 0 then IO.eprintln "a part of the run failed"
  return (stop - start) / (1000 * runs)

def showMillis (micros : Nat) : String :=
  s!"{micros / 1000}.{(micros % 1000) / 100}{(micros % 100) / 10}{micros % 10} ms"

/-- Time the parts of a run with one path per query: the transcript, the
arithmetic of the queries, and the two groups of Merkle checks. Each later
part is timed together with the parts it needs, and the difference is shown. -/
def breakdown (runs : Nat) (ref : IO.Ref Vector) : IO Unit := do
  let transcriptTime ← meanMicros runs ref fun v => (benchChallenges v).indices.size
  let withQueries ← meanMicros runs ref fun v =>
    ((benchQueries v (benchChallenges v)).filter (·.ok)).size
  let withInputs ← meanMicros runs ref fun v =>
    (benchInputChecks v (benchChallenges v)).toNat
  let withRounds ← meanMicros runs ref fun v =>
    let ch := benchChallenges v
    (benchCommitChecks v ch (benchQueries v ch)).toNat
  IO.println "parts of a run with one path per query:"
  IO.println s!"  transcript: {showMillis transcriptTime}"
  IO.println s!"  query arithmetic: {showMillis (withQueries - transcriptTime)}"
  IO.println s!"  Merkle checks of the inputs: {showMillis (withInputs - transcriptTime)}"
  IO.println s!"  Merkle checks of the rounds: {showMillis (withRounds - withQueries)}"

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: rest =>
    let runs := (rest.head?.bind String.toNat?).getD 10
    let text ← IO.FS.readFile path
    match parseVector text with
    | .error e =>
      IO.eprintln s!"{path}: {e}"
      return 1
    | .ok v =>
      let shape := claimShape v.claims
      IO.println s!"{path}: {v.params.numQueries} queries, {numRounds v.params shape} rounds, first domain 2^{logMaxHeight v.params.logBlowup shape}, {(claimValues v.claims).size} claimed values"
      let ref ← IO.mkRef v
      timeRuns "one path per query" runs ref benchPaths
      timeRuns "pruned proofs" runs ref benchPruned
      breakdown runs ref
      return 0
  | [] =>
    IO.eprintln "usage: certifri-bench <vector.json> [runs]"
    return 1
