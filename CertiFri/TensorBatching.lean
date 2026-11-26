import CertiFri.Field
import CertiFri.Challenger

/-!
# Tensor FRI Batching (`FriBatching::Tensor`, `multi-stark` `v6`)

Executable specification of `multi-stark` `v6`'s `FriBatching::Tensor`
(`src/p3_adapter/fri_batching.rs`), matching its challenge sampling order,
multilinear weight expansion, and reduced-opening accumulation byte-for-byte.

Given `maxWidth` columns and `maxOpenings` opening groups:
* `tensorNumChallenges count` returns `0` for `count ≤ 1`, and `⌈log₂ count⌉`
  otherwise (`count.next_power_of_two().trailing_zeros()` in Rust).
* `tensorWeights challenges len` expands `r₀, …, r_{k-1}` into the length-`len`
  multilinear basis `w[j] = ∏_{b : (j >>> b) &&& 1 = 1} r_b` by iterative doubling.
* `TensorSchedule.sample` draws `k_col = tensorNumChallenges maxWidth` column
  challenges first, then `k_open = tensorNumChallenges maxOpenings` opening
  challenges, matching `FriBatchingSchedule::sample`.
* `tensorOpeningTerm` and `reducedOpeningTensor` accumulate
  `w_open[o] * (∑_c w_col[c] * (p_at_z[c] - embed p_at_x[c])) * (z - x)⁻¹`,
  matching `open_inputs_with_schedule`.

The unconditional unique-decoding soundness reduction (`TensorMCA`, error linear
in `k_col + k_open` instead of `W * M`) and the Johnson-regime reduction are
proved in `Proofs/CertiFriProofs/Theory/ProximityGap/TensorMCA.lean` and
`Proofs/CertiFriProofs/Exec/SoundnessTensor.lean`.
-/

namespace CertiFri.Fri

/-- FRI batching mode matching `multi-stark`'s `FriBatching`. -/
inductive FriBatching where
  | horner : FriBatching
  | tensor : FriBatching
  deriving DecidableEq, Repr, Inhabited

/-- Wire tag matching `FriBatching::as_u8` (`Horner = 0`, `Tensor = 1`). -/
def FriBatching.wireTag : FriBatching → UInt8
  | .horner => 0
  | .tensor => 1

/-- Number of independent extension-field challenges needed to form a tensor
weight table of length `count`: `0` if `count ≤ 1`, else `⌈log₂ count⌉`. -/
def tensorNumChallenges (count : Nat) : Nat :=
  if count ≤ 1 then 0 else Nat.log2 (count - 1) + 1

/-- One doubling step of tensor weight expansion: appends `r * w` for each
existing weight `w`, stopping once `len` weights have been produced. -/
def tensorStep {EF : Type} [FieldOps EF] (len : Nat) (acc : List EF) (r : EF) : List EF :=
  (acc ++ acc.map (fun w => r * w)).take len

/-- Multilinear tensor weight table of length `len` from `challenges`, built by
iterative doubling starting from `[1]` (empty for `len = 0`). Matches
`multi-stark`'s `tensor_weights` element-for-element. -/
def tensorWeightsList {EF : Type} [FieldOps EF] (challenges : List EF) (len : Nat) : List EF :=
  if len = 0 then []
  else challenges.foldl (tensorStep len) [1]

/-- Array form of `tensorWeightsList`. -/
def tensorWeights {EF : Type} [FieldOps EF] (challenges : Array EF) (len : Nat) : Array EF :=
  (tensorWeightsList challenges.toList len).toArray

/-- Explicit multilinear monomial weight `∏_{b : (j >>> b) &&& 1 = 1} r[b]`
for index `j`, matching the reference formula in `multi-stark` tests. -/
def tensorWeightExplicit {EF : Type} [FieldOps EF] (challenges : List EF) (j : Nat) : EF :=
  go challenges j 1
where
  go : List EF → Nat → EF → EF
    | [], _, acc => acc
    | r :: rs, idx, acc =>
      let acc' := if idx % 2 = 1 then acc * r else acc
      go rs (idx / 2) acc'

/-- Sample `count` independent extension-field challenges from `chal`. -/
def sampleExtMany {σ F EF D : Type} (chal : Challenger σ F EF D) :
    Nat → σ → List EF × σ
  | 0, s => ([], s)
  | n + 1, s =>
    let (r, s') := chal.sampleExt s
    let (rs, s'') := sampleExtMany chal n s'
    (r :: rs, s'')

/-- Sampled tensor batching schedule (`col_challenges` first, then `open_challenges`),
matching `multi-stark`'s `FriBatchingSchedule::sample`. -/
structure TensorSchedule (EF : Type) where
  colChallenges : Array EF
  openChallenges : Array EF
  colWeights : Array EF
  openWeights : Array EF
  deriving Repr

/-- Sample a `TensorSchedule` from `chal` for at most `maxWidth` columns and
`maxOpenings` opening groups, drawing `colChallenges` first and `openChallenges`
second (matching `FriBatchingSchedule::sample`). -/
def TensorSchedule.sample {σ F EF D : Type} [FieldOps EF] (chal : Challenger σ F EF D)
    (s : σ) (maxWidth maxOpenings : Nat) : TensorSchedule EF × σ :=
  let kCol := tensorNumChallenges maxWidth
  let kOpen := tensorNumChallenges maxOpenings
  let (colChals, s1) := sampleExtMany chal kCol s
  let (openChals, s2) := sampleExtMany chal kOpen s1
  let colArr := colChals.toArray
  let openArr := openChals.toArray
  ({ colChallenges := colArr
     openChallenges := openArr
     colWeights := tensorWeights colArr maxWidth
     openWeights := tensorWeights openArr maxOpenings }, s2)

/-- Column-batched linear combination `∑_c colWeights[c] * (claimed[c] - embed opened[c])`
for one matrix opening at a point `z`, matching `open_inputs_with_schedule`. -/
def tensorColAcc {F EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    (colWeights : Array EF) (claimed : Array EF) (opened : Array F) : EF :=
  let n := min claimed.size opened.size
  (List.range n).foldl (fun acc c =>
    acc + colWeights.getD c 0 * (claimed.getD c 0 - ExtensionOps.embed (opened.getD c 0))) 0

/-- Single opening group's contribution to the reduced opening at query point `x`:
`openWeight * tensorColAcc colWeights claimed opened * (z - x)⁻¹`. -/
def tensorOpeningTerm {F EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    (colWeights : Array EF) (openWeight z x : EF) (claimed : Array EF) (opened : Array F) : EF :=
  openWeight * tensorColAcc colWeights claimed opened * (z - x)⁻¹

/-- Reduced opening for a height level under `FriBatching::Tensor`: sums
`tensorOpeningTerm` over all `(openingIdx, z, claimed, opened)` tuples at that height. -/
def reducedOpeningTensor {F EF : Type} [FieldOps F] [FieldOps EF] [ExtensionOps F EF]
    (sched : TensorSchedule EF) (x : EF)
    (openings : List (Nat × EF × Array EF × Array F)) : EF :=
  openings.foldl (fun acc (oIdx, z, claimed, opened) =>
    acc + tensorOpeningTerm sched.colWeights (sched.openWeights.getD oIdx 0) z x claimed opened) 0

end CertiFri.Fri
