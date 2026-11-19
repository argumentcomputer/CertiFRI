/-!
# Fiat–Shamir challenger interface

The verifier derives its challenges from a challenger: a state machine that
absorbs what the prover sent and squeezes challenges out. This file is the
interface the verifier is written against. It follows the traits Plonky3's FRI
verifier uses (`CanObserve`, `FieldChallenger`, `CanSampleBits`,
`GrindingChallenger`), with one difference: an extension-field element is
absorbed as one value here, where Plonky3 absorbs its base-field coordinates
one at a time. An instance that reproduces Plonky3's transcript absorbs the
coordinates in its `observe`.

Which values are absorbed, and in which order, is the verifier's business
(`CertiFri/Verifier.lean`), not the challenger's.
-/

namespace CertiFri

/-- One value absorbed into the transcript: a base-field element, an
extension-field element, or a digest. -/
inductive Observation (F EF D : Type) where
  /-- A base-field element. -/
  | base (a : F)
  /-- An extension-field element. -/
  | ext (e : EF)
  /-- A digest, such as a Merkle root. -/
  | digest (d : D)
  deriving Repr, DecidableEq

/-- A challenger with states `σ`, over base field `F`, extension field `EF` and
digests `D`. -/
structure Challenger (σ F EF D : Type) where
  /-- Absorb one value. -/
  observe : σ → Observation F EF D → σ
  /-- Squeeze one extension-field element. -/
  sampleExt : σ → EF × σ
  /-- Squeeze an integer below `2 ^ bits`. -/
  sampleBits : σ → (bits : Nat) → Nat × σ

namespace Challenger

variable {σ F EF D : Type}

/-- Absorb a list of values, first to last. -/
def observeAll (chal : Challenger σ F EF D) (s : σ) (obs : List (Observation F EF D)) : σ :=
  obs.foldl chal.observe s

/-- Check a grinding witness: absorb it, then require the next `bits` sampled
bits to be zero. Port of `GrindingChallenger::check_witness`.

At zero difficulty nothing is absorbed and every witness passes. -/
def checkWitness (chal : Challenger σ F EF D) (s : σ) (bits : Nat) (witness : F) : Bool × σ :=
  if bits = 0 then (true, s)
  else
    let s := chal.observe s (.base witness)
    let sampled := chal.sampleBits s bits
    (sampled.1 == 0, sampled.2)

/-- Squeeze `count` integers below `2 ^ bits`, one after the other. -/
def sampleIndices (chal : Challenger σ F EF D) (bits : Nat) : (count : Nat) → σ → List Nat
  | 0, _ => []
  | count + 1, s =>
    let sampled := chal.sampleBits s bits
    sampled.1 :: sampleIndices chal bits count sampled.2

end Challenger

end CertiFri
