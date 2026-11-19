import Lean.Data.Json
import CertiFri.Pcs
import CertiFriP3.Hashers
import CertiFriP3.Challenger
import CertiFriP3.Pruned

/-!
# Reading the Plonky3 test vectors

A decoder for the JSON files that `CertiFriTest/vectors/fri` writes: a
statement and an opening proof made by Plonky3's `TwoAdicFriPcs`, with the
values Plonky3's verifier derives on the way. The schema is documented in
`CertiFriTest/vectors/fri/README.md`.

A file gives every commitment proof in two forms, and so the decoder returns
two proofs: one with a full Merkle path per query, one with Plonky3's pruned
proof.

This is test code. The JSON format is this repository's own; it is not a
format Plonky3 reads or writes.
-/

namespace CertiFriTest.P3

open Lean (Json)
open CertiFri CertiFri.Fri CertiFri.P3

/-- A parser result: a value, or a message saying what was wrong. -/
abbrev Parse := Except String

/-- A field element: a number below the order. -/
def parseField (j : Json) : Parse Goldilocks := do
  let n ← j.getNat?
  if n < Goldilocks.order then pure (Goldilocks.ofNat n)
  else throw s!"field element {n} is not canonical"

/-- An array, with each entry parsed by `f`. -/
def parseArray {α : Type} (f : Json → Parse α) (j : Json) : Parse (Array α) := do
  (← j.getArr?).mapM f

/-- An extension element: `[c0, c1]`. -/
def parseExt (j : Json) : Parse GoldilocksExt := do
  let coords ← parseArray parseField j
  match coords with
  | #[c0, c1] => pure ⟨c0, c1⟩
  | _ => throw "an extension element has two coordinates"

/-- A digest: 32 bytes. -/
def parseDigest (j : Json) : Parse Digest := do
  let bytes ← parseArray (fun b => do
    let n ← b.getNat?
    if n < 256 then pure n.toUInt8 else throw s!"{n} is not a byte") j
  match Digest.ofBytes? (ByteArray.mk bytes) with
  | some d => pure d
  | none => throw "a digest has 32 bytes"

/-- The field `key` of an object, parsed by `f`. -/
def parseKey {α : Type} (j : Json) (key : String) (f : Json → Parse α) : Parse α := do
  f (← j.getObjVal? key)

def parseNat (j : Json) : Parse Nat := j.getNat?

def parseParams (j : Json) : Parse FriParams := do
  pure {
    logBlowup := ← parseKey j "log_blowup" parseNat
    logFinalPolyLen := ← parseKey j "log_final_poly_len" parseNat
    maxLogArity := ← parseKey j "max_log_arity" parseNat
    numQueries := ← parseKey j "num_queries" parseNat
    commitPowBits := ← parseKey j "commit_proof_of_work_bits" parseNat
    queryPowBits := ← parseKey j "query_proof_of_work_bits" parseNat }

def parseClaims (j : Json) : Parse (Array (CommitmentOpening GoldilocksExt Digest)) :=
  parseArray (fun batch => do
    pure {
      commitment := ← parseKey batch "commitment" parseDigest
      matrices := ← parseKey batch "matrices" (parseArray fun matrix => do
        pure {
          logDegree := ← parseKey matrix "log_degree" parseNat
          points := ← parseKey matrix "points" (parseArray fun point => do
            pure {
              point := ← parseKey point "point" parseExt
              values := ← parseKey point "values" (parseArray parseExt) }) }) }) j

/-- One full path per query, from the `paths` form of an opening proof. -/
def parsePaths (j : Json) : Parse (Array (List Digest)) :=
  parseKey j "paths" (parseArray fun path => do pure (← parseArray parseDigest path).toList)

/-- Plonky3's pruned proof, from the `pruned` form of an opening proof. -/
def parsePruned (j : Json) : Parse (PrunedPaths Digest) := do
  let pruned ← j.getObjVal? "pruned"
  pure ⟨← parseKey pruned "sibling_hashes" (parseArray parseDigest)⟩

/-- A proof, with its commitment proofs parsed by `opening`. -/
def parseProof {α : Type} (opening : Json → Parse α) (j : Json) :
    Parse (FriProof Goldilocks GoldilocksExt Digest α α) := do
  pure {
    commitPhaseCommits := ← parseKey j "commit_phase_commits" (parseArray parseDigest)
    commitPowWitnesses := ← parseKey j "commit_pow_witnesses" (parseArray parseField)
    inputOpenings := ← parseKey j "input_openings" (parseArray fun o => do
      pure {
        openedValues := ← parseKey o "opened_values"
          (parseArray (parseArray (parseArray parseField)))
        openingProof := ← parseKey o "opening_proof" opening })
    commitPhaseOpenings := ← parseKey j "commit_phase_openings" (parseArray fun o => do
      pure {
        logArity := ← parseKey o "log_arity" parseNat
        siblingValues := ← parseKey o "sibling_values" (parseArray (parseArray parseExt))
        openingProof := ← parseKey o "opening_proof" opening })
    finalPoly := ← parseKey j "final_poly" (parseArray parseExt)
    queryPowWitness := ← parseKey j "query_pow_witness" parseField }

/-- A test vector: a statement, the proof in its two forms, and the challenges
Plonky3's verifier derived. -/
structure Vector where
  params : FriParams
  claims : Array (CommitmentOpening GoldilocksExt Digest)
  /-- The proof with one full Merkle path per query. -/
  paths : FriProof Goldilocks GoldilocksExt Digest (Array (List Digest)) (Array (List Digest))
  /-- The proof with Plonky3's pruned Merkle proofs. -/
  pruned : FriProof Goldilocks GoldilocksExt Digest (PrunedPaths Digest) (PrunedPaths Digest)
  /-- The batching challenge Plonky3 derived. -/
  alpha : GoldilocksExt
  /-- The folding challenges Plonky3 derived. -/
  betas : Array GoldilocksExt
  /-- The query indices Plonky3 derived. -/
  indices : Array Nat

def parseVector (text : String) : Parse Vector := do
  let j ← Json.parse text
  let proof ← j.getObjVal? "proof"
  let debug ← j.getObjVal? "debug"
  pure {
    params := ← parseKey j "params" parseParams
    claims := ← parseKey j "claims" parseClaims
    paths := ← parseProof parsePaths proof
    pruned := ← parseProof parsePruned proof
    alpha := ← parseKey debug "alpha" parseExt
    betas := ← parseKey debug "betas" (parseArray parseExt)
    indices := ← parseKey debug "indices" (parseArray parseNat) }

end CertiFriTest.P3
