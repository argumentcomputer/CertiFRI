/-!
# Fiat–Shamir challenger interface

The operations of the sponge the verifier derives its challenges from, as a
state machine over a state type `C`. Port of the `CanObserve`, `CanSample`,
`CanSampleBits` and `GrindingChallenger` traits Plonky3's FRI verifier uses.

This is the sponge only. What is absorbed, in which order and under which
domain separation, is the transcript layer, which is not written yet.
-/

namespace CertiFri

/-- A challenger over the base field `F`. -/
class ChallengerOps (C : Type) (F : outParam Type) where
  /-- Absorb one field element. -/
  observe : C → F → C
  /-- Squeeze one field element. -/
  sample : C → F × C
  /-- Squeeze an integer below `2 ^ bits`. -/
  sampleBits : C → (bits : Nat) → Nat × C

/-- Check a grinding witness: absorb it, then require the next `bits` sampled
bits to be zero. Port of `GrindingChallenger::check_witness`.

At zero difficulty nothing is absorbed and every witness passes, so a verifier
must separately pin the witness to its canonical value there. -/
def checkWitness {C F : Type} [ChallengerOps C F] (challenger : C) (bits : Nat) (witness : F) :
    Bool × C :=
  if bits = 0 then (true, challenger)
  else
    let challenger := ChallengerOps.observe challenger witness
    let (sampled, challenger) := ChallengerOps.sampleBits challenger bits
    (sampled == 0, challenger)

end CertiFri
