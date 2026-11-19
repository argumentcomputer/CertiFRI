# certifri

A FRI polynomial commitment verifier in Lean 4, written to be proved correct.
Only the verifier is certified. The prover will be an ordinary Rust program.

The protocol follows Plonky3's `TwoAdicFriPcs`. The revision it is read against
is pinned as the `plonky3/` submodule. Only the commitment scheme is in scope,
not the STARK built on it.

## Status

This is a scaffold. There is no FRI verifier yet.

What exists, and is proved on `propext`, `Quot.sound` and (in `Proofs/` only)
`Classical.choice`, with no `sorry`:

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
