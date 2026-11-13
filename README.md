# certifri

A FRI polynomial commitment verifier in Lean 4, written to be proved correct.
Only the verifier is certified. The prover will be an ordinary Rust program.

The protocol follows Plonky3's `TwoAdicFriPcs`. The revision it is read against
is pinned as the `plonky3/` submodule. Only the commitment scheme is in scope,
not the STARK built on it.

## Status

This is a scaffold. There is no verifier yet.

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

The parameters, claims, proof, field, challenger and commitment-scheme modules
are interface definitions with no theorems yet.

## Layout

| Path | Contents |
| --- | --- |
| `CertiFri/` | The executable verifier. No dependency beyond the Lean toolchain. Proofs that need only core Lean sit next to the code. |
| `Proofs/` | A separate Lake package that depends on Mathlib and on `CertiFri`: the mathematical model, the refinement theorems relating the executable code to it, and the security theorems. |
| `plonky3/` | Submodule: the Plonky3 revision this port is read against. Reference only; nothing builds from it yet. |

Mathlib is confined to `Proofs/` so that a project can depend on the verifier
without inheriting it.

## Build

```sh
lake build --wfail                 # the verifier
(cd Proofs && lake build --wfail)  # the proofs; fetches Mathlib on first use
```

`--wfail` turns warnings into errors, so a `sorry` fails the build.
The two `lean-toolchain` files must name the same toolchain.
