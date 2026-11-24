import Mathlib
import CertiFriP3.Bn254
import CertiFriProofs.P3.Primes
import CertiFriProofs.P3.FpLaws
import CertiFriProofs.P3.Model

/-!
# The scalar field of BN254 is a field

The code of `CertiFriP3/Bn254.lean` implements the integers modulo the order
`r` of the BN254 curve, and its generators of the two-adic subgroups are
primitive roots.

## Contents

* `Bn254.primeRep`, `Bn254.refines`: the code refines `ZMod r`.
* `Bn254.twoAdicRep`: the table of generators is compatible. The 28 squarings
  are checked by evaluating the code.
* `Bn254.isPrimitiveRoot_twoAdicGenerator`: the generator of order `2 ^ k` is
  a primitive root of that order for `k ≤ 28`.

## Assumptions

None: the order is prime (`P3/Primes.lean`).

## Not covered

A `StarkModel`: no extension of this field is implemented, and no verifier of
this repository runs over it.
-/

namespace CertiFri.P3.Bn254

/-- The scalar field of BN254 implements the integers modulo its order. -/
def primeRep : PrimeRep Bn254 order :=
  Fp.primeRep order_prime

/-- The code refines the field `ZMod r`. -/
def refines : Refines Bn254 (ZMod order) :=
  primeRep.refines

/-- The order is more than two. -/
theorem two_lt_order : 2 < order := by
  decide

/-- The generators of the two-adic subgroups are compatible, and the coset
shift is not zero. -/
theorem twoAdicRep : TwoAdicRep primeRep where
  gen_zero := by decide +kernel
  gen_one := by decide +kernel
  gen_sq := by decide +kernel
  shift := by decide +kernel

/-- The generator of order `2 ^ k` is a primitive root of that order. -/
theorem isPrimitiveRoot_twoAdicGenerator (k : ℕ) (hk : k ≤ 28) :
    IsPrimitiveRoot (refines.toModel (twoAdicGenerator k)) (2 ^ k) :=
  twoAdicRep.isPrimitiveRoot two_lt_order k hk

end CertiFri.P3.Bn254
