import Mathlib
import CertiFriP3.BabyBear
import CertiFriProofs.P3.Primes
import CertiFriProofs.P3.FpLaws
import CertiFriProofs.P3.QuarticLaws

/-!
# BabyBear and its quartic extension are a model of the verifier's fields

The code of `CertiFriP3/BabyBear.lean` implements the field
`BabyBear.K = (ZMod p)[X] / (X^4 - 11)` of `p ^ 4` elements, with
`p = 2^31 - 2^27 + 1`, as the theorems about the verifiers require
(`StarkModel`, and through it `FieldModel` and `WellFormed`).

## Contents

* `BabyBear.primeRep`: the base field implements the integers modulo `p`.
* `BabyBear.twoAdicRep`: Plonky3's table of generators is compatible, so the
  generator of order `2 ^ k` is a primitive root of that order for `k ≤ 27`.
  The 27 squarings are checked by evaluating the code.
* `BabyBear.K`, with `BabyBear.card_K`.
* `BabyBear.starkModel`: the model of the two fields.
* `BabyBear.natCast_inj`: natural numbers below `p` are different in
  `BabyBear.K`.
* `BabyBear.toZMod_nonResidue`: the constant `W` of the code is `11`.

## Assumptions

None: the order is prime and `X^4 - 11` is irreducible (`P3/Primes.lean`,
`P3/Binomial.lean`).
-/

open Polynomial

namespace CertiFri.P3

open CertiFri.Exec.Stark

namespace BabyBear

/-- The BabyBear field implements the integers modulo its order. -/
def primeRep : PrimeRep BabyBear order :=
  Fp.primeRep order_prime

/-- The order is more than two. -/
theorem two_lt_order : 2 < order := by
  decide

/-- Plonky3's generators of the two-adic subgroups are compatible, and the
coset shift is not zero. -/
theorem twoAdicRep : TwoAdicRep primeRep where
  gen_zero := by decide +kernel
  gen_one := by decide +kernel
  gen_sq := by decide +kernel
  shift := by decide +kernel

/-- `X^4 - 11` is irreducible over the BabyBear field: neither `11` nor `-11` is a
square. -/
instance irreducible_fact : Fact (Irreducible (X ^ 4 - C 11 : (ZMod order)[X])) :=
  ⟨Binomial.irreducible_four eleven_not_isSquare neg_eleven_not_isSquare⟩

/-- The field of `p ^ 4` elements that models the extension of BabyBear:
`(ZMod p)[X] / (X^4 - 11)`. -/
abbrev K : Type := Binomial (ZMod order) 4 11

/-- The model field has `p ^ 4` elements. -/
theorem card_K : Fintype.card K = order ^ 4 := by
  rw [Binomial.card, ZMod.card]

/-- Natural numbers below the order are different in the model field. -/
theorem natCast_inj {a b : ℕ} (ha : a < order) (hb : b < order) (h : (a : K) = b) : a = b := by
  exact Binomial.natCast_injOn order ha hb h

/-- The value of the constant `W` of the code is `11`. -/
theorem toZMod_nonResidue : primeRep.toZMod (QuarticParams.nonResidue : BabyBear) = 11 := by
  have h : primeRep.toNat (QuarticParams.nonResidue : BabyBear) = 11 := by decide +kernel
  rw [PrimeRep.toZMod, h, Nat.cast_ofNat]

/-- **The model of BabyBear and its quartic extension.** -/
noncomputable def starkModel : StarkModel BabyBear BabyBearExt K :=
  P3.starkModel twoAdicRep two_lt_order (Quartic.binomialRep primeRep 11 toZMod_nonResidue)

end BabyBear

end CertiFri.P3
