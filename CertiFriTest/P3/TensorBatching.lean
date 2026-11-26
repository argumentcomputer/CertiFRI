import CertiFri.TensorBatching
import CertiFriP3.GoldilocksExt3

/-!
# Tensor FRI Batching Tests

Cross-checks `CertiFri.Fri.tensorNumChallenges`, `tensorWeights`, and
`tensorWeightExplicit` against the exact Rust test vectors from
`multi-stark` `v6` (`src/p3_adapter/fri_batching.rs`,
`tensor_weights_match_explicit_multilinear_monomials` and
`packed_ext_weights_dot_product_matches_scalar_for_cubic_extension`).
-/

namespace CertiFriTest.P3.TensorBatching

open CertiFri CertiFri.Fri CertiFri.P3

private def ext3 (a b c : UInt64) : GoldilocksExt3 :=
  ⟨Goldilocks.ofUInt64 a, Goldilocks.ofUInt64 b, Goldilocks.ofUInt64 c⟩

-- Challenge counts match `count.next_power_of_two().trailing_zeros()`.
#guard tensorNumChallenges 0 == 0
#guard tensorNumChallenges 1 == 0
#guard tensorNumChallenges 2 == 1
#guard tensorNumChallenges 3 == 2
#guard tensorNumChallenges 4 == 2
#guard tensorNumChallenges 5 == 3
#guard tensorNumChallenges 7 == 3
#guard tensorNumChallenges 8 == 3
#guard tensorNumChallenges 9 == 4
#guard tensorNumChallenges 16 == 4
#guard tensorNumChallenges 17 == 5
#guard tensorNumChallenges 25 == 5
#guard tensorNumChallenges 256 == 8

-- Wire tags match `FriBatching::as_u8`.
#guard FriBatching.horner.wireTag == 0
#guard FriBatching.tensor.wireTag == 1

-- Rust vector from `tensor_weights_match_explicit_multilinear_monomials`.
private def rustChallenges : Array GoldilocksExt3 :=
  #[ext3 3 5 7, ext3 11 13 17, ext3 19 23 29]

#guard (tensorWeights (#[] : Array GoldilocksExt3) 0).isEmpty
#guard tensorWeights (#[] : Array GoldilocksExt3) 1 == #[GoldilocksExt3.one]

private def checkLen (len : Nat) : Bool :=
  let k := tensorNumChallenges len
  let chals := (rustChallenges.toList.take k)
  let got := tensorWeights chals.toArray len
  got.size == len &&
    (List.range len).all fun j =>
      got.getD j GoldilocksExt3.zero == tensorWeightExplicit chals j

#guard (List.range 8).all fun i => checkLen (i + 1)

-- 5-challenge (len = 25) check matching `packed_ext_weights_dot_product_matches_scalar_for_cubic_extension`.
private def rustChallenges5 : Array GoldilocksExt3 :=
  Array.ofFn (n := 5) fun i =>
    let v : UInt64 := i.val.toUInt64
    ext3 (3 * v + 2) (5 * v + 7) (11 * v + 13)

#guard
  let got := tensorWeights rustChallenges5 25
  got.size == 25 &&
    (List.range 25).all fun j =>
      got.getD j GoldilocksExt3.zero == tensorWeightExplicit rustChallenges5.toList j

-- 2D tensor factorisation check: `w_open[o] * w_col[c] = w_{col ++ open}[c + 2^kCol * o]`.
#guard
  let colChals := #[ext3 3 5 7, ext3 11 13 17]
  let openChals := #[ext3 19 23 29]
  let wCol := tensorWeights colChals 3
  let wOpen := tensorWeights openChals 2
  let wJoint := tensorWeights (colChals ++ openChals) 8
  (List.range 2).all fun o =>
    (List.range 3).all fun c =>
      wOpen.getD o 0 * wCol.getD c 0 == wJoint.getD (c + 4 * o) 0

-- Pinned Rust-computed weight vectors, produced by
-- `multi_stark::p3_adapter::fri_batching::tensor_weights` over
-- `CubicTrinomialExtensionField<Goldilocks>` (`X^3 - X - 1`).

private def rustExpectedR3 : Array GoldilocksExt3 := #[
  ext3 1 0 0,
  ext3 3 5 7,
  ext3 11 13 17,
  ext3 209 389 312,
  ext3 19 23 29,
  ext3 363 673 538,
  ext3 977 1761 1434,
  ext3 22428 39703 29984
]

#guard tensorWeights rustChallenges 8 == rustExpectedR3

private def rustExpectedR5 : Array GoldilocksExt3 := #[
  ext3 1 0 0,
  ext3 2 7 13,
  ext3 5 12 24,
  ext3 334 695 509,
  ext3 8 17 35,
  ext3 482 1011 748,
  ext3 868 1849 1411,
  ext3 35650 62031 45392,
  ext3 11 22 46,
  ext3 630 1327 987,
  ext3 1135 2426 1862,
  ext3 46842 81575 59667,
  ext3 1640 3525 2737,
  ext3 68264 119095 87050,
  ext3 125644 220437 161033,
  ext3 4244200 7406723 5591926,
  ext3 14 27 57,
  ext3 778 1643 1226,
  ext3 1402 3003 2313,
  ext3 58034 101119 73942,
  ext3 2026 4363 3400,
  ext3 84571 147627 107879,
  ext3 155642 273239 199580,
  ext3 5260451 9179679 6929719,
  ext3 2650 5723 4487
]

#guard tensorWeights rustChallenges5 25 == rustExpectedR5

-- High-bit Goldilocks inputs near `p = 2^64 - 2^32 + 1 = 18446744069414584321`,
-- pinning both Goldilocks modular reduction and cubic trinomial `X^3 = X + 1`
-- reduction against Rust `multi-stark`.
private def rustChallengesBig : Array GoldilocksExt3 := #[
  ext3 18446744069414584320 18446744069414584319 18446744069414584318,
  ext3 1311768467463790320 18364758544493064720 18446744069414584304,
  ext3 16045690984503098046 9223372036854775808 4294967301
]

private def rustExpectedBig : Array GoldilocksExt3 := #[
  ext3 1 0 0,
  ext3 18446744069414584320 18446744069414584319 18446744069414584318,
  ext3 1311768467463790320 18364758544493064720 18446744069414584304,
  ext3 17380932176715352838 16151149234173082170 14675409716866252631,
  ext3 16045690984503098046 9223372036854775808 4294967301,
  ext3 11624425104586392891 4802106139758201455 7203159233259622326,
  ext3 14272807465657587220 13530733850594897633 8761560380233819903,
  ext3 1398846499748417359 2650856251038225760 5754332797389669388
]

#guard tensorWeights rustChallengesBig 8 == rustExpectedBig

end CertiFriTest.P3.TensorBatching
