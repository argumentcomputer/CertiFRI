import CertiFriP3.PrimeField
import CertiFriP3.Quartic

/-!
# The BabyBear field and its quartic extension

The prime field of order `p = 2^31 - 2^27 + 1`, as Plonky3's `BabyBear`
(`baby-bear/src/baby_bear.rs`), and its extension
`BabyBear[X] / (X^4 - 11)`, Plonky3's `BinomialExtensionField<BabyBear, 4>`,
with the instances the verifier is written against: `FieldOps`, `TwoAdicOps`
and `ExtensionOps BabyBear BabyBearExt`.

The base field is the field `Fp p` of `PrimeField.lean`: an element is its
representative below `p`. Plonky3 keeps a word in Montgomery form; the values
are the same. The extension is the quartic extension of `Quartic.lean` with
the constant `W = 11`.

Nothing is proved in this package. That `p` is prime, that the operations are
those of the two fields and that the generators are primitive roots is proved
in the proofs package (`Proofs/CertiFriProofs/P3/BabyBearModel.lean`).

Not covered: the extensions of degree five and eight that Plonky3 defines,
encodings of an element as bytes, and Plonky3's Poseidon2 over this field. A
verifier over BabyBear also needs a hasher and a challenger, which this
package has for Goldilocks only.
-/

namespace CertiFri.P3

/-- The order `p = 2^31 - 2^27 + 1` of the BabyBear field. -/
def BabyBear.order : Nat := 0x78000001

/-- The order is not zero. -/
instance BabyBear.order_neZero : NeZero BabyBear.order := ⟨by decide⟩

/-- The BabyBear field. -/
abbrev BabyBear : Type := Fp BabyBear.order

namespace BabyBear

/-- Plonky3's `BabyBear::TWO_ADIC_GENERATORS`: entry `k` is a generator of the
subgroup of order `2^k`, and each entry is the square of the next. -/
def twoAdicGenerators : Array Nat := #[
  0x00000001, 0x78000000, 0x67055c21, 0x5ee99486, 0x0bb4c4e4, 0x2d4cc4da, 0x669d6090,
  0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226, 0x4c734715, 0x11c33e2a,
  0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6, 0x5cf5713f, 0x3e9430e8, 0x0ba067a3,
  0x18adc27d, 0x21fd55bc, 0x4b859b3d, 0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41]

/-- Plonky3's `BabyBear::two_adic_generator(bits)` for `bits ≤ 27`. Plonky3
panics above 27; this function returns zero there. -/
def twoAdicGenerator (bits : Nat) : BabyBear :=
  match twoAdicGenerators[bits]? with
  | some n => Fp.ofNat n
  | none => 0

/-- Plonky3's `BabyBear::GENERATOR`: the generator `31` of the multiplicative
group. -/
def generator : BabyBear := Fp.ofNat 31

instance : TwoAdicOps BabyBear where
  twoAdicity := 27
  twoAdicGenerator := twoAdicGenerator
  cosetShift := generator

/-- Plonky3's `BinomiallyExtendable<4>::W` for BabyBear: the constant `11`. -/
instance : QuarticParams BabyBear := ⟨Fp.ofNat 11⟩

end BabyBear

/-- The quartic extension `BabyBear[X] / (X^4 - 11)`. -/
abbrev BabyBearExt : Type := Quartic BabyBear

end CertiFri.P3
