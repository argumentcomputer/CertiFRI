import CertiFriP3.Hashers
import CertiFriP3.Challenger
import CertiFriP3.DomainSep
import CertiFriP3.Pruned

/-!
# The Plonky3 instantiation

The primitives that make the generic verifier of `CertiFri` check proofs
produced by Plonky3: the Goldilocks field and its quadratic extension, BLAKE3,
the Merkle hashers, the challenger, Plonky3's pruned Merkle proofs, and the
decoding of proofs.

This library is tested against values computed by Plonky3 (`CertiFriTest`), not
proved. The one theorem in it, `P3.prunedMmcs_accepts`, says that a pruned
Merkle proof is accepted only through the certified Merkle check.
-/
