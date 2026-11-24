import CertiFri.Params
import CertiFri.Bits
import CertiFri.Field
import CertiFri.Poly
import CertiFri.Challenger
import CertiFri.Mmcs
import CertiFri.Merkle
import CertiFri.Claims
import CertiFri.Proof
import CertiFri.Schedule
import CertiFri.Shape
import CertiFri.Verifier
import CertiFri.Pcs
import CertiFri.TensorBatching
import CertiFri.Stark.Graph
import CertiFri.Stark.Logup
import CertiFri.Stark.System
import CertiFri.Stark.Verifier

/-!
# CertiFri

A FRI polynomial commitment verifier, written to be proved correct, and a
port of the multi-stark verifier that is built on it (`CertiFri/Stark/`).

This package is the executable side. It depends on nothing beyond the Lean
toolchain. The mathematical model and the theorems that need Mathlib are in the
`Proofs/` package.
-/
