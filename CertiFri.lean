import CertiFri.Params
import CertiFri.Bits
import CertiFri.Field
import CertiFri.Poly
import CertiFri.Challenger
import CertiFri.Mmcs
import CertiFri.Claims
import CertiFri.Proof
import CertiFri.Schedule
import CertiFri.Shape

/-!
# CertiFri

Definitions and supporting proofs for a planned FRI polynomial commitment
verifier. Transcript replay, opening checks and the complete verifier are not
implemented yet.

This package is the executable side. It depends on nothing beyond the Lean
toolchain. The mathematical model and the theorems that need Mathlib are in the
`Proofs/` package.
-/
