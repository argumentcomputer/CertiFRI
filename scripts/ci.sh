#!/usr/bin/env bash
# The checks CI runs (.github/workflows/ci.yml), one step per argument, from any directory:
#
#   scripts/ci.sh lean-build    the verifier, the Plonky3 instantiation, the tests, then the
#                               proofs, with warnings as errors (a `sorry` fails the build)
#   scripts/ci.sh leanchecker   replay every module of CertiFri, CertiFriP3 and CertiFriProofs
#                               in the kernel (needs lean-build)
#   scripts/ci.sh axioms        every constant of those libraries depends only on propext,
#                               Classical.choice and Quot.sound (needs lean-build)
#   scripts/ci.sh multi-stark   multi-stark's tests and doc tests
#
# Lean comes from `lean-toolchain` (through elan, or a toolchain already on PATH); Rust from
# `multi-stark/rust-toolchain.toml`.
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)

step() {
  case "$1" in
    lean-build)
      cd "$root"
      # The proofs must be built with the verifier's toolchain.
      cmp lean-toolchain Proofs/lean-toolchain
      lake build --wfail
      cd "$root/Proofs"
      lake exe cache get
      lake build --wfail
      ;;
    leanchecker)
      # `leanchecker M` replays, in the kernel, every module whose name has `M` as a prefix,
      # against the environment of that module's imports. Mathlib is not replayed. Modules are
      # replayed in parallel, each with its own copy of its imports (Mathlib included): one
      # thread peaked at 7 GB, four at 30 GB. Hence one thread unless LEANCHECKER_THREADS is set.
      cd "$root/Proofs"
      LEAN_NUM_THREADS="${LEANCHECKER_THREADS:-1}" lake env leanchecker --verbose \
        CertiFri CertiFriP3 CertiFriProofs
      ;;
    axioms)
      cd "$root/Proofs"
      lake env lean ../scripts/CheckAxioms.lean
      ;;
    multi-stark)
      cd "$root/multi-stark"
      cargo test --locked --profile dev-ci --features parallel
      ;;
    *)
      echo "unknown step: $1" >&2
      return 2
      ;;
  esac
}

[ $# -gt 0 ] || { echo "usage: scripts/ci.sh lean-build|leanchecker|axioms|multi-stark ..." >&2; exit 2; }
for s in "$@"; do
  echo "== scripts/ci.sh $s"
  (step "$s")
done
