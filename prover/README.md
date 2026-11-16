# CertiFRI Rust API

The `certifri` crate owns the native proving pipeline consumed by Ix.
It provides circuit construction, lookups, sharded STARK proving, polynomial
commitments, serialization and optional CUDA acceleration. Its source derives
from `argumentcomputer/multi-stark`. The original MIT and Apache-2.0 licenses
are retained beside this file.

Commands below can be run from this directory. From the repository root,
select this crate with `-p certifri`. For the dependency setup and the
separate Lean certification scope, see the [repository README](../README.md).
Native CPU tuning is opt-in here via `RUSTFLAGS="-Ctarget-cpu=native"`;
downstream projects such as Ix control their own build flags.

A multi-circuit STARK proving system built on [Plonky3](https://github.com/Plonky3/Plonky3).

Prove and verify multiple AIR circuits in a single proof, with cross-circuit
lookup arguments for shared state.

## Features

- **Multi-circuit proofs** — bundle multiple AIR circuits into one proof with
  independent trace heights
- **Lookup arguments** — push/pull interactions of arbitrary length between
  circuits, enforced via accumulator-based multiset checks
- **Preprocessed tables** — commit to fixed tables once, reuse across proofs
- **Plonkish builder** — describe a fixed computation with native-field values,
  enforced copies, public bindings, witness hints, and fixed-table lookups
- **Generic over field, hash, and PCS** — the protocol is parameterized by a
  `ProofConfig` (base field via the PCS, challenge field, challenger);
  a batteries-included Goldilocks/Blake3 instantiation is provided
- **Serialization** — `Proof::to_bytes` / `Proof::from_bytes` via bincode
- **Parallel proving** — opt-in via the `parallel` feature flag
- **CUDA transforms** — opt-in sppark Goldilocks DFT/LDE backend via the
  `cuda` feature; normal builds remain independent of CUDA

## Reference configuration

The protocol (`system`, `prover`, `verifier` modules) is generic over
[`ProofConfig`](src/config.rs) (`StarkGenericConfig` is a compatibility alias).
The reference configuration is `GoldilocksBlake3Config` in [`types`](src/types.rs):

| Component | Choice                                        |
|-----------|-----------------------------------------------|
| Field     | Goldilocks (p = 2^64 - 2^32 + 1)              |
| Extension | Degree-2 binomial extension (~2^128 elements) |
| Hash      | Blake3                                        |
| PCS       | FRI over Merkle trees                         |

A second instantiation (BabyBear field, degree-4 extension, Poseidon2
hashing) lives in the test suite to keep the protocol honest about its
genericity. When writing your own configuration, pick a challenge field
large enough for the target security level — the Schwartz-Zippel terms of
the soundness error scale with 1/|challenge field|.

`CommitmentParameters` sets the blowup and Merkle cap; `FriParameters` sets
folding, queries and grinding. At `log_blowup = 1` and `num_queries = 100`,
the conjectural query-phase estimate `ρ^num_queries` is 2^(-100). This is not
a complete security bound for the PCS or STARK. See the
[verifier module docs](src/verifier.rs) for assumptions and limits; the Rust
protocol is not formally verified.

> :warning: **Not zero-knowledge.** The reference configuration commits traces
> without blinding — FRI query responses reveal witness data.
> Do not use this when the witness must remain hidden
> from the verifier.

## Examples

**Minimal prove-and-verify** (no lookups):
```sh
cargo run --example simple_proof --release
```

**Preprocessed trace with lookups** (byte range-check table):
```sh
cargo run --example preprocessed_proof --release
```

**Multi-circuit with lookup arguments**:
```sh
cargo run --example lookup_proof --release
```

See the [Plonkish builder guide](docs/plonkish.md) and
[backend interfaces](docs/pcs-abstraction.md) for APIs and examples.

## Benchmarks

```sh
cargo bench --bench certifri --features parallel
```

Benchmarks cover `prove` and `verify` at 2^12, 2^13, and 2^14 trace rows
using a U32 addition circuit with lookups and a preprocessed byte table.
Use `--features parallel` for representative numbers and
`RUSTFLAGS="-Ctarget-cpu=native"` to enable native SIMD instructions.

## CUDA acceleration

The optional `cuda` feature routes the production Goldilocks configuration's
PCS and quotient transforms through sppark. For the same inputs and configuration,
CPU and CUDA backends must produce byte-identical proofs accepted by the same
CPU verifier; the smoke harness checks this contract.
The default build does not invoke `nvcc` or link the CUDA runtime. Enable the
backend explicitly:

```sh
cargo test --release --features parallel,cuda
./cuda/smoke.sh
cargo run --release --locked --features parallel,cuda --example cuda_dft_bench
```

Building with CUDA requires the toolkit; running the backend requires an
NVIDIA GPU. The backend can keep trace LDEs, mixed-height BLAKE3 Merkle
commitments, lookup construction, quotient evaluation, batched openings and
FRI folding resident on the device, with host paths for small or spilled work.

See [cuda/README.md](cuda/README.md) for architecture, build settings, the NVIDIA
correctness harness, platform limitations, and benchmark commands.

### sppark transforms

Every CUDA build uses [sppark](https://github.com/argumentcomputer/sppark)'s
Goldilocks NTT. Cargo pins the dependency. Its borrowed streams keep
panel allocation, transforms and freeing on the caller's stream. Tiny generic
host matrices retain the CPU DFT. CPU builds do not depend on sppark or CUDA.

An immutable per-device plan fixes each transform's panel size, launch groups
and coset powers. Admission and execution share the plan. Dimensions must fit
the compiled domain (currently 2^28 rows), checked byte arithmetic and at least
one column within the panel budget; invalid shapes fail before allocation.

`CERTIFRI_SPPARK_PANEL_BYTES` caps the transform scratch, 4 GiB by default;
a budget smaller than one column is a configuration error. Columns are
transformed in launch groups sized to the device's L2 cache. Both are captured
when the device DFT is constructed. Staging copies reuse sppark's per-device
CPU workers. `CERTIFRI_CUDA_AUX_DEVICES` names further CUDA ordinals,
comma separated, that take the coset LDEs the primary device leaves to the
host. The C adapter catches native exceptions, synchronizes outstanding
device work on failure, and returns CUDA error codes to Rust.

`build.rs` builds `libcertifri_cuda.so` with a C ABI and private, statically
linked CUDA and GNU C++ runtimes. This boundary also lets downstream Lean
applications load the backend without mixing C++ runtimes. CertiFRI itself
has no Lean runtime dependency. Installed applications must package the shared
library and configure its runtime search path; see the CUDA guide.

```sh
cargo test --release --features parallel,cuda --lib cuda::sppark::tests::
CERTIFRI_CUDA_BENCH_SHAPES="20,533,2" cargo run --release --features parallel,cuda --example cuda_resident_lde_bench
```

## License

MIT or Apache-2.0
