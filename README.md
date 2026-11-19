# certifri

A FRI polynomial commitment verifier in Lean 4, written to be proved correct.
Only the verifier is certified. The prover will be an ordinary Rust program.

The protocol follows Plonky3's `TwoAdicFriPcs`. The revision it is read against
is pinned as the `plonky3/` submodule. Only the commitment scheme is in scope,
not the STARK built on it.

## Status

There is no executable FRI verifier yet. The security theory is proved for a
mathematical model of the verifier (see [Theory](#theory)); the executable
verifier and its refinement to that model are not written.

Everything below is proved on `propext`, `Quot.sound` and (in `Proofs/` only)
`Classical.choice`, with no `sorry`.

Executable code and its lemmas:

- The folding schedule and the shape of a run, derived from the parameters and
  the claims (`CertiFri/Schedule.lean`, `CertiFri/Shape.lean`). The derived
  schedule folds from the tallest claimed height exactly to the final height,
  and every round folds by between one bit and the configured cap. Plonky3
  checks these two properties by exhaustive test below height `2 ^ 10`.
- Evaluation of the final polynomial by Horner's rule, and a proof that it
  computes the evaluation of a polynomial of degree below the coefficient
  count (`Proofs/CertiFriProofs/Poly.lean`).
- Merkle commitments to a batch of matrices of different heights
  (`CertiFri/Merkle.lean`): the check of an opening, and binding. Two accepted
  openings under one root that address the same row of a matrix open the same
  row, or one of the two hash functions has a collision. The hash functions
  are parameters; no concrete hash is implemented. The tree layout is checked
  against openings produced by Plonky3 (`CertiFriTest/Merkle.lean`).

The parameters, claims, proof, field and challenger modules are interface
definitions with no theorems yet.

## Theory

`Proofs/CertiFriProofs/Theory/` holds the security theory of the protocol with
binary folding. The main result is `Compiled.Params.soundness`
(`Theory/Compiled/Soundness.lean`): for the non-interactive protocol with
Merkle commitments and Fiat–Shamir challenges, an adversary making at most `Q`
oracle queries gets the model verifier to accept claims that fail with
probability at most

    N * εmax + ((batches + 1) * (rounds + 2) + 3) * N * (N - 1) / (2 * |D|)

where `N` is `Q` plus the verifier's own queries, `εmax` bounds the error of
every round, and `D` is the digest type. "The claims fail" is about the
functions that the adversary's hash queries commit to under the input roots:
at some height they do not agree, on a `θ` fraction of the domain, with
polynomials of the degree bound that take the claimed values. The doc comment
of the theorem states every assumption.

| Module | Contents |
| --- | --- |
| `Basic` | Shared definitions: codewords, the fold, the proximity hypotheses, the query check. |
| `Domain` | Two-adic evaluation domains; query indices and domain points; cosets. |
| `Fold`, `Completeness` | Even and odd parts of a polynomial; honest codewords pass every query. |
| `Soundness`, `SoundnessCount` | Oracle-model soundness of the low-degree test, relative to the folding hypothesis. |
| `ProximityGap`, `StepMCA`, `Unconditional` | The proximity hypotheses proved by an elementary argument for `δ ≤ (1 - ρ) / (m + 1)` with `m` terms, and the low-degree test with no hypothesis under `4 * δ + ρ ≤ 1`. |
| `Quotient`, `Pcs` | From the low-degree test to the evaluation claims. |
| `PcsRbr` | The whole check as one round-by-round sound protocol, with grinding. |
| `Oracle` | The random-oracle model: bad-event and collision bounds, Fiat–Shamir, Merkle binding and frozen trees against the query log. |
| `Compiled` | The model of the non-interactive protocol and its soundness. |

What the theorems assume:

- The leaf hash, the compression function and the challenger are one random
  oracle, and each challenge depends on the whole transcript before it.
- Two proximity hypotheses about Reed–Solomon codes, `CurveMCA` (batching the
  claims) and `StepMCA` (folding). They are arguments of the theorems, not
  axioms. The folding hypothesis is proved here for `4 * δ + ρ ≤ 1`
  (`Compiled.Params.soundness_of_relDist`). The batching hypothesis is proved
  only in a regime that shrinks with the number of claims, so in practice it
  stays a hypothesis.

What they do not establish:

- Anything about the executable verifier: the theorems are about a model
  verifier, and no refinement connects the two yet.
- Zero knowledge. The protocol is not zero-knowledge.
- Completeness of the non-interactive protocol. Only the query check on honest
  codewords is proved.
- Security of a concrete hash function or sponge.
- The honest degree bound: an accepted claim is about a polynomial of degree at
  most the bound, one more than an honest polynomial has, and agreement is not
  asked at the claim's own opening point.

## Layout

| Path | Contents |
| --- | --- |
| `CertiFri/` | The executable verifier. No dependency beyond the Lean toolchain. Proofs that need only core Lean sit next to the code. |
| `CertiFriTest/` | Executable checks of the verifier against reference code. They run as part of the build. |
| `Proofs/` | A separate Lake package that depends on Mathlib and on `CertiFri`: the mathematical model, the refinement theorems relating the executable code to it, and the security theorems. |
| `plonky3/` | Submodule: the Plonky3 revision this port is read against. Reference only; nothing builds from it yet. |

Mathlib is confined to `Proofs/` so that a project can depend on the verifier
without inheriting it.

## Build

```sh
lake build --wfail                 # the verifier and its tests
(cd Proofs && lake build --wfail)  # the proofs; fetches Mathlib on first use
```

`--wfail` turns warnings into errors, so a `sorry` fails the build.
The two `lean-toolchain` files must name the same toolchain.
