# certifri

A FRI polynomial commitment verifier in Lean 4, with a proof of soundness.
Only the verifier is certified. The prover is an ordinary Rust program.

The protocol is Plonky3's `TwoAdicFriPcs` at revision `3152b14a`, the revision
the Rust prover pins, with folding by two. Only the commitment scheme is in
scope, not the STARK built on it. The protocol is not zero-knowledge.

## Status

- **The verifier** is `Fri.verify` in `CertiFri/Verifier.lean`: executable,
  generic over the two fields, the two commitment schemes and the challenger,
  with no dependency beyond the Lean toolchain.
- **It is proved sound** in the random-oracle model, up to the unique-decoding
  radius, with no hypothesis about Reed–Solomon codes
  (`Exec.soundness_uniqueDecoding` in
  `Proofs/CertiFriProofs/Exec/SoundnessUnconditional.lean`), on `propext`,
  `Classical.choice` and `Quot.sound`, with no `sorry`. The theorem is about
  the verifier with ideal primitives; see
  [What the theorems assume](#what-the-theorems-assume).
- **It accepts proofs made by Plonky3**: with the Goldilocks, BLAKE3 and
  challenger code of `CertiFriP3`, it accepts the opening proofs that Plonky3
  produces and derives the same challenges, and it rejects tampered ones
  (`CertiFriTest/P3/Fri.lean`). This is a test on a handful of proofs, not a
  theorem. The primitives of `CertiFriP3` are tested against Plonky3, not
  proved.

## The verifier

```lean
Fri.verify inputMmcs friMmcs chal init params shape commitments points values proof : Bool
```

The claims are given by a public shape and two flat arrays. The shape lists,
for each commitment, the matrices under it: the log of the row count, the
width, and the number of opening points. `points` holds the opening points in
the order batch, matrix, point, and `values` the claimed evaluations in the
order batch, matrix, point, column. `Fri.verifyClaims` (`CertiFri/Pcs.lean`)
takes the claims nested the way Plonky3's `pcs.verify` does.

The verifier absorbs the commitments, the opening points and the claimed values
into the challenger, and then follows Plonky3's `verify_fri`. Plonky3 leaves the
first two to the caller; a Plonky3 prover matches by observing the commitments
and the points before `pcs.open`.

It rejects a proof with a folding round of arity other than two.

## What is proved

`Proofs/CertiFriProofs/Exec/` relates the executable verifier to a model
verifier, and `Proofs/CertiFriProofs/Theory/` proves the model sound.

**Refinement** (`Exec.run_model_of_accepts`). If `Fri.verify` accepts, the model
verifier accepts the corresponding transcript. It has three parts: the
arithmetic of one query (`Exec/Arith.lean`), the commitment checks and the
verdict (`Exec/Checks.lean`), and the transcript (`Exec/Transcript.lean`).

**Soundness** (`Exec.soundness`). Fix the parameters and the shape of the
claims. An adversary making at most `Q` oracle queries gets the executable
verifier to accept claims that fail with probability at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)

where `N` is `Q` plus the verifier's own queries, `εmax` bounds the error of
every round (divided by `2 ^ bits` where the round has a proof-of-work check),
and `D` is the digest type. "The claims fail" is about the functions that the
adversary's hash queries commit to under the commitments: at some height they
do not agree, on a `θ` fraction of the domain, with polynomials of the degree
bound that take the claimed values.

`Exec.soundness` takes two proximity hypotheses about Reed–Solomon codes, at
any agreement `θ`. `Exec.soundness_uniqueDecoding` proves both, for agreement
`θ = 1 - δ` with `2 * δ + ρ ≤ 1`, where `ρ = 2 ^ (-logBlowup)` is the rate:
every distance up to the unique-decoding radius. Its round errors are, with `n`
the log of the size of the first domain and `c = 2 ^ n * (δ * 2 ^ n + 1) + 1`,

- batching: `(number of claimed values) * c / |K|`,
- each folding round: `2 * c / |K| / 2 ^ commitPowBits`,
- queries: `(1 - δ) ^ numQueries / 2 ^ queryPowBits`,

for an extension field `K`, and `εmax` is their maximum.

For example, with blowup 4 the radius is `δ = 3/8`, so each query contributes
`log₂ (8/5) ≈ 0.68` bits: 100 queries give a query error of about `2 ^ -68`,
or `2 ^ -88` with 20 bits of proof of work. Over the quadratic extension of
Goldilocks (`|K| ≈ 2 ^ 128`), a trace of `2 ^ 20` rows (`n = 22`) with a
thousand claimed values has a batching error of about `2 ^ -75`, which is then
the largest of the three. These figures are arithmetic on the bound above, not
separate theorems.

The theory behind it:

| Module | Contents |
| --- | --- |
| `Theory/Basic` | Shared definitions: codewords, the fold, the proximity hypotheses, the query check. |
| `Theory/Domain` | Two-adic evaluation domains; query indices and domain points; cosets. |
| `Theory/Fold`, `Completeness` | Even and odd parts of a polynomial; honest codewords pass every query. |
| `Theory/Soundness`, `SoundnessCount` | Oracle-model soundness of the low-degree test, relative to the folding hypothesis. |
| `Theory/ProximityGap`, `StepMCA`, `Unconditional` | The proximity hypotheses proved by an elementary argument for `δ ≤ (1 - ρ) / (m + 1)` with `m` terms, and the low-degree test with no hypothesis under `4 * δ + ρ ≤ 1`. |
| `Theory/ProximityGap/UniqueDecoding`, `UniqueDecodingMCA` | The proximity hypotheses proved up to the unique-decoding radius `δ ≤ (1 - ρ) / 2`, for any number of terms: correlated agreement by the Berlekamp–Welch decoder with the challenge as an indeterminate, then the mutual form. |
| `Theory/Quotient`, `Pcs` | From the low-degree test to the evaluation claims. |
| `Theory/PcsRbr` | The whole check as one round-by-round sound protocol, with grinding. |
| `Theory/Oracle` | The random-oracle model: bad-event and collision bounds, Fiat–Shamir, Merkle binding and frozen trees against the query log. |
| `Theory/Compiled` | The model of the non-interactive protocol and its soundness. |
| `Exec` | The executable verifier refines the model; soundness of the executable verifier, with the proximity hypotheses and with them proved. |

Also proved, about executable code: the Merkle opening check is binding up to a
hash collision (`CertiFri/Merkle.lean`), and Horner's rule computes the
evaluation of the final polynomial (`Proofs/CertiFriProofs/Poly.lean`).

### What the theorems assume

- **Ideal primitives.** The leaf hash, the compression function and the
  challenger are one random oracle. A row is hashed as the oracle's answer to
  the row of field elements it holds, and each challenge is the oracle's answer
  to everything the verifier has absorbed so far, in rounds
  (`Exec.freeChallenger`). The oracle answers the three kinds of query
  independently. Plonky3's BLAKE3 instantiation does not separate them: a leaf
  hash, a compression and a transcript hash are the same function on bytes.
- **Proximity gaps, beyond the unique-decoding radius only.** The theorems
  need two facts about Reed–Solomon codes, `CurveMCA` (batching the claims) and
  `StepMCA` (folding). Up to the unique-decoding radius, `2 * δ + ρ ≤ 1`, both
  are proved here and `Exec.soundness_uniqueDecoding` assumes nothing about
  the code. For a larger radius (towards the Johnson bound or capacity) they
  are hypotheses of `Exec.soundness`: arguments of the theorem, not axioms.
  The proved error is quadratic in the size of the domain.
- **The fields.** The two executable fields implement one mathematical field,
  every element of which is represented (`Exec.FieldModel`), the generator of
  the first domain is a primitive root of unity, and the coset shift is not
  zero (`Exec.WellFormed`).
- **Merkle commitments with one path per query** (`merkleMmcs`).
- **A fixed shape.** The parameters and the shape of the claims are fixed
  before the adversary runs. The shape is not absorbed into the transcript.

### What they do not establish

- Anything about the code in `CertiFriP3`: that its Goldilocks arithmetic is a
  `FieldModel`, that BLAKE3 or the challenger are implemented correctly, or
  that they behave like a random oracle.
- Soundness with Plonky3's pruned Merkle proofs as such. A pruned proof is
  unpacked and then checked by the certified Merkle check
  (`P3.prunedMmcs_accepts`), but the soundness theorem is stated for one path
  per query.
- Completeness. That honest proofs are accepted is tested, not proved.
- Zero knowledge. The protocol is not zero-knowledge.
- That the verifier accepts exactly what Plonky3's accepts. The tests compare
  the two on a few proofs.
- The honest degree bound: an accepted claim is about a polynomial of degree at
  most the bound, one more than an honest polynomial has, and agreement is not
  asked at the claim's own opening point. The committed functions take values
  in the extension field.

## Tests

They run as part of the build: a failing `#guard` fails the build.

- `CertiFriTest/Fri.lean`: an honest prover over the field with 97 elements,
  written as test code, with a toy hasher and a toy challenger. The verifier
  accepts its proofs and rejects tampered ones.
- `CertiFriTest/P3/Fri.lean`: the verifier on four opening proofs made by
  Plonky3 (`CertiFriTest/vectors/fri`, a Rust program that also checks each
  proof with Plonky3's verifier). Each is accepted with one Merkle path per
  query and with Plonky3's pruned proofs, the derived challenges equal
  Plonky3's, and tampered values, points, final polynomials, sibling values,
  opened entries, witnesses and parameters are rejected.
- `CertiFriTest/P3/`: Goldilocks, its quadratic extension, BLAKE3, the Merkle
  hashers, the challenger and the pruned Merkle proofs against values computed
  by Plonky3.
- `CertiFriTest/Merkle.lean`: the Merkle tree layout against openings produced
  by Plonky3.

The JSON format of the vectors is this repository's own. Decoding the bytes a
Plonky3 prover serializes is not written.

## Benchmark

```sh
(cd CertiFriTest/vectors/fri && cargo run --release -- --bench /tmp/bench 200)  # Plonky3's verifier
lake exe certifri-bench /tmp/bench/bench-16.json 50                             # this verifier, compiled
```

Both verify the same proofs (blowup 4, 100 queries, 16 bits of grinding), on
one thread, without the time to decode the proof. On the machine these were
last run on (AMD Ryzen 7 8845HS), per verification:

| First domain | Plonky3 | This verifier, one path per query | This verifier, pruned proofs |
| --- | --- | --- | --- |
| `2^12` | 1.3 ms | 3.9 ms | 4.9 ms |
| `2^16` | 2.2 ms | 5.8 ms | 8.0 ms |
| `2^20` | 3.2 ms | 7.4 ms | 10.3 ms |

Plonky3 verifies pruned proofs, so the last column is the like-for-like one.
More than half of this verifier's time with one path per query is the
arithmetic of the queries, which inverts one extension-field element per
claimed value; Plonky3 inverts one per opening point, in a batch.

## Layout

| Path | Contents |
| --- | --- |
| `CertiFri/` | The certified verifier. No dependency beyond the Lean toolchain. Proofs that need only core Lean sit next to the code. |
| `CertiFriP3/` | The Plonky3 instantiation: Goldilocks, BLAKE3, the challenger, pruned Merkle proofs. Tested, not proved. |
| `CertiFriTest/` | Executable checks against reference code and against Plonky3, and the generators of their vectors. |
| `Proofs/` | A separate Lake package that depends on Mathlib and on `CertiFri`: the security theory, and the refinement of the executable verifier to it. |
| `plonky3/` | Submodule: a Plonky3 checkout for reference. Nothing builds from it. |

Mathlib is confined to `Proofs/` so that a project can depend on the verifier
without inheriting it.

`CertiFri/Schedule.lean` and `CertiFri/Shape.lean` derive a folding schedule
from the claims, as later Plonky3 revisions do, and prove two properties of it.
The verifier does not use them: at revision `3152b14a` the arities are read
from the proof, and the verifier requires each to be two. The `plonky3/`
submodule points at that later revision (`0d803737`), not at `3152b14a`.

## Build

```sh
lake build --wfail                 # the verifier, the Plonky3 instantiation, the tests
(cd Proofs && lake build --wfail)  # the proofs; fetches Mathlib on first use
```

`--wfail` turns warnings into errors, so a `sorry` fails the build.
The two `lean-toolchain` files must name the same toolchain.
