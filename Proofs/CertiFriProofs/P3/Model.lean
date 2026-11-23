import Mathlib
import CertiFriProofs.P3.PrimeRep
import CertiFriProofs.P3.Binomial
import CertiFriProofs.Exec.Stark.Model

/-!
# From implementations of the fields to the model of the verifier

The theorems about the verifiers assume a `FieldModel` (the opening proof) or a
`StarkModel` (the STARK verifier): the executable fields `F` and `EF`
implement a field `K`, with the extension structure and the two-adic structure
the verifier uses. This file builds a `StarkModel` from three facts about
concrete code: `F` implements a prime field (`PrimeRep`), its generators are
compatible (`TwoAdicRep`), and `EF` implements a binomial extension of it in
coordinates (`BinomialRep`). The field `K` is `Binomial (ZMod p) d w`.

## Contents

* `TwoAdicRep`: the generator of order one is one, the generator of order two
  is minus one, each generator is the square of the next, and the coset shift
  is not zero. `TwoAdicRep.isPrimitiveRoot`: the generator of order `2 ^ k` is
  then a primitive root of that order.
* `BinomialRep`: the executable extension has coordinates in the base field,
  its abstraction map is the combination of the powers of `X` with them, every
  tuple of coordinates is an element, and `embed`, `toBasis` and `ofBasis`
  are what they should be in coordinates.
* `starkModel`: the model, with `starkModel_base`, `starkModel_ext` and
  `starkModel_extData` describing its components.

## Assumptions

None beyond the three structures, an odd prime `p`, and the irreducibility of
`X^d - w`.
-/

open Polynomial

namespace CertiFri.P3

open CertiFri.Exec.Stark

variable {F EF : Type} [FieldOps F] [FieldOps EF] {p : ℕ}

/-- The two-adic structure of an implementation of a prime field: what has to
be checked of the table of generators and of the coset shift. -/
structure TwoAdicRep [TwoAdicOps F] (R : PrimeRep F p) : Prop where
  /-- The generator of order one is one. -/
  gen_zero : R.toNat (TwoAdicOps.twoAdicGenerator 0) = 1
  /-- The generator of order two is minus one. -/
  gen_one : R.toNat (TwoAdicOps.twoAdicGenerator 1) = p - 1
  /-- Each generator is the square of the next. -/
  gen_sq : ∀ k < TwoAdicOps.twoAdicity (F := F),
    (TwoAdicOps.twoAdicGenerator (k + 1) * TwoAdicOps.twoAdicGenerator (k + 1) : F) =
      TwoAdicOps.twoAdicGenerator k
  /-- The coset shift is not zero. -/
  shift : R.toNat TwoAdicOps.cosetShift ≠ 0

/-- The generator of order `2 ^ k` is a primitive root of that order, in
`ZMod p` for an odd prime `p`. -/
theorem TwoAdicRep.isPrimitiveRoot [TwoAdicOps F] [Fact p.Prime] {R : PrimeRep F p}
    (T : TwoAdicRep R) (hp : 2 < p) :
    ∀ k ≤ TwoAdicOps.twoAdicity (F := F),
      IsPrimitiveRoot (R.toZMod (TwoAdicOps.twoAdicGenerator k)) (2 ^ k) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).mp h')
    omega
  refine isPrimitiveRoot_two_pow_of_chain h2
    (fun k => R.toZMod (TwoAdicOps.twoAdicGenerator k)) _ ?_ ?_ ?_
  · rw [PrimeRep.toZMod, T.gen_zero, Nat.cast_one]
  · rw [PrimeRep.toZMod, T.gen_one, Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub,
      Nat.cast_one]
  · intro k hk
    rw [← T.gen_sq k hk, sq]
    exact (R.refines.map_mul _ _).symm

/-- The executable field `EF` implements the binomial extension
`(ZMod p)[X] / (X^d - w)` of the prime field that `F` implements, in
coordinates. -/
structure BinomialRep (F EF : Type) [FieldOps F] [FieldOps EF] [ExtensionOps F EF] {p : ℕ}
    [Fact p.Prime] (R : PrimeRep F p) (d : ℕ) (w : ZMod p)
    [Fact (Irreducible (X ^ d - C w : (ZMod p)[X]))] where
  /-- The coordinates of an element. -/
  coord : EF → ℕ → F
  /-- The extension refines the binomial field. -/
  ext : Refines EF (Binomial (ZMod p) d w)
  /-- The abstraction map is the combination of the powers of `X` with the
  coordinates. -/
  toModel_eq : ∀ x, ext.toModel x = Binomial.ofCoords fun i => R.toZMod (coord x i)
  /-- Every tuple of coordinates is an element. -/
  surj : ∀ c : ℕ → F, ∃ x, ∀ i < d, coord x i = c i
  /-- The degree is the executable one. -/
  degree_eq : ExtensionOps.degree (F := F) (EF := EF) = d
  /-- The embedding of the base field, in coordinates. -/
  embed : ∀ (a : F) (i : ℕ), i < d → coord (ExtensionOps.embed a) i = if i = 0 then a else 0
  /-- `toBasis` returns one coordinate per basis element. -/
  toBasis_size : ∀ x : EF, (ExtensionOps.toBasis (F := F) x).size = d
  /-- `toBasis` returns the coordinates. -/
  toBasis : ∀ (x : EF) (i : ℕ), i < d → (ExtensionOps.toBasis x).getD i 0 = coord x i
  /-- `ofBasis` returns the element with the given coordinates. -/
  ofBasis : ∀ a : Array F, a.size = d →
    ∀ i < d, coord (ExtensionOps.ofBasis a) i = a.getD i 0

variable [TwoAdicOps F] [ExtensionOps F EF] [Fact p.Prime] {R : PrimeRep F p} {d : ℕ}
  {w : ZMod p} [Fact (Irreducible (X ^ d - C w : (ZMod p)[X]))]

/-- **The model of the fields of the STARK verifier**, from an implementation
of a prime field with compatible generators and an implementation of a
binomial extension of it. -/
noncomputable def starkModel (T : TwoAdicRep R) (hp : 2 < p) (E : BinomialRep F EF R d w) :
    StarkModel F EF (Binomial (ZMod p) d w) where
  base := R.refines.map Binomial.of
  ext := E.ext
  embed := fun a => by
    rw [E.toModel_eq, Refines.map_toModel, PrimeRep.refines_toModel, Binomial.of_eq_ofCoords,
      Binomial.ofCoords_eq_iff]
    intro i hi
    rw [E.embed a i hi]
    split
    · rfl
    · exact R.refines.map_zero
  surj := fun y => by
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨c, hc⟩ := Binomial.exists_ofCoords y
    choose c' hc' using fun i => R.toZMod_surjective (c i)
    obtain ⟨x, hx⟩ := E.surj c'
    refine ⟨x, ?_⟩
    rw [E.toModel_eq, ← hc, Binomial.ofCoords_eq_iff]
    intro i hi
    rw [hx i hi, hc' i]
  extData := Binomial.extData
  degree_eq := E.degree_eq.symm
  toBasis_size := E.toBasis_size
  toBasis := fun x k hk => by
    rw [E.toBasis x k hk, E.toModel_eq]
    exact congrArg Binomial.of
      (Binomial.coords_ofCoords (d := d) (fun i => R.toZMod (E.coord x i)) k hk).symm
  ofBasis := fun a ha => by
    rw [E.toModel_eq]
    refine Finset.sum_congr rfl fun i hi => ?_
    change Binomial.of (R.toZMod (E.coord (ExtensionOps.ofBasis a) i)) * Binomial.root ^ i = _
    rw [E.ofBasis a ha i (Finset.mem_range.mp hi)]
    rfl
  generator := fun k hk =>
    (T.isPrimitiveRoot hp k hk).map_of_injective
      (f := (Binomial.of : ZMod p →+* Binomial (ZMod p) d w)) (RingHom.injective _)
  generator_sq := fun k hk => by
    rw [← T.gen_sq k hk, Refines.map_mul, sq]
  shift_ne := fun h => by
    have h' : R.toZMod TwoAdicOps.cosetShift = 0 :=
      Binomial.of.injective (h.trans (map_zero _).symm)
    exact T.shift (by rw [← R.val_toZMod, h', ZMod.val_zero])

/-- The base field of the model: the value in `ZMod p`, embedded. -/
@[simp] theorem starkModel_base (T : TwoAdicRep R) (hp : 2 < p) (E : BinomialRep F EF R d w)
    (a : F) : (starkModel T hp E).base.toModel a = Binomial.of (R.toZMod a) :=
  rfl

/-- The extension field of the model. -/
@[simp] theorem starkModel_ext (T : TwoAdicRep R) (hp : 2 < p) (E : BinomialRep F EF R d w) :
    (starkModel T hp E).ext = E.ext :=
  rfl

/-- The extension structure of the model. -/
@[simp] theorem starkModel_extData (T : TwoAdicRep R) (hp : 2 < p)
    (E : BinomialRep F EF R d w) : (starkModel T hp E).extData = Binomial.extData :=
  rfl

end CertiFri.P3
