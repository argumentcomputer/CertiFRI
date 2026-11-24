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

end CertiFriTest.P3.TensorBatching
