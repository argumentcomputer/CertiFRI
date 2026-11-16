# CertiFRI

CertiFRI owns the Rust proving pipeline used by Ix and is developing a formally
verified FRI polynomial commitment verifier in Lean 4.

The native Rust crate is `certifri`. It supplies circuit construction, lookups,
sharded STARK proving, polynomial commitments, proof serialization, reference
verification, and optional CUDA acceleration. Execution and witness generation
remain native Rust callers. The crate has no Lean runtime or Lean FFI dependency.

## Rust API

The implementation lives in `prover/`; there is no `multi-stark` package or
runtime dependency. Ix imports `certifri` directly. The core entry points are:

- `system::{CircuitInputs, System, SystemWitness, ProverKey}` for setup and proofs.
- `batch` for sharded proofs with shared lookup challenges.
- `plonkish` for circuit construction and witness generation.
- `traits` and `config::ProofConfig` for alternate fields, transcripts and PCSs.
- `types::GoldilocksBlake3Config` for the CPU/CUDA FRI configuration.
- `prover::Proof` and `batch::BatchProof` for serialization and transport.

See the [Rust API guide](prover/README.md),
[Plonkish guide](prover/docs/plonkish.md), and
[backend interfaces](prover/docs/pcs-abstraction.md).

For adjacent checkouts, Ix's workspace dependency is:

```toml
certifri = { path = "../CertiFRI/prover" }
```

Its member crates use `certifri = { workspace = true }` and forward the
`parallel` and `cuda` features. A Git dependency can instead name this repository
and an exact commit. Cargo finds the `certifri` package under `prover/` automatically.

Plonky3 is a pinned Cargo git dependency in `prover/Cargo.toml`, and
`Cargo.lock` pins transitive dependencies.
The legacy `multi-stark/v0` transcript label is intentionally retained for
compatibility with existing proofs and Ix's verifier; it is not a dependency.
The reference FRI configuration is non-hiding.

The CUDA library, exported symbols, build metadata and tuning variables use
`certifri` / `CERTIFRI_*` names. See the [CUDA guide](prover/cuda/README.md).
CPU builds need no CUDA toolkit. Consumers choose their own CPU target flags.

## Lean certification

The Lean verifier is still a scaffold. Its certification scope is the FRI
polynomial commitment scheme; the Rust prover, STARK pipeline and witness
generation are not formally verified. There is no completed Rust-to-Lean proof
encoding or end-to-end Lean verifier yet.

Connecting the Lean verifier to Rust proofs requires a shared proof encoding
and transcript contract. The mathematical results established here are:

- The folding schedule and run shape are derived from parameters and claims.
  With a positive arity cap, the schedule covers the required height reduction,
  and each round folds between one bit and that cap (`Schedule.lean`,
  `Shape.lean`). Inputs already at or below the final height require no rounds.
- Horner evaluation refines mathematical polynomial evaluation, with degree
  below the coefficient count (`Proofs/CertiFriProofs/Poly.lean`).

There are no `sorry`s. The parameter, claims, proof, field, challenger and
commitment-scheme modules currently define interfaces. Mathlib is confined to
`Proofs/`, so consumers of the executable Lean package do not inherit it.

## Layout

| Path | Contents |
| --- | --- |
| `prover/` | The `certifri` Rust crate, including CPU/CUDA backends, examples and tests. |
| `CertiFri/` | Executable Lean definitions and proofs requiring only core Lean. |
| `Proofs/` | Mathematical models and refinement proofs using Mathlib. |

## Build

Rust uses `rust-toolchain.toml` and builds independently of Lean:

```sh
cargo build --workspace --locked
cargo test --workspace --locked --features parallel
cargo clippy --workspace --all-targets --features parallel --locked -- -D warnings
cargo run -p certifri --locked --release --example simple_proof
cargo run -p certifri --locked --release --example pcs_example
```

For native CPU tuning, set `RUSTFLAGS="-Ctarget-cpu=native"`.
For larger tests, `--profile dev-ci` enables optimizations and debug information.
CUDA validation is available via `prover/cuda/smoke.sh`, run from `prover/`.

The Lean packages build independently:

```sh
lake build --wfail
(cd Proofs && lake build --wfail)
```

`--wfail` turns warnings into errors, so a `sorry` fails the build. The two
`lean-toolchain` files must name the same toolchain.

## Source provenance

The Rust implementation derives from `argumentcomputer/multi-stark`.
CertiFRI owns the source and API;
this is not a wrapper or a dependency on that repository. The original
[MIT](prover/LICENSE-MIT) and [Apache-2.0](prover/LICENSE-APACHE) licenses are
retained with the source.
