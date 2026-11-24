import CertiFriP3.GoldilocksExt3
import CertiFriP3.Blake2b
import CertiFriP3.Hashers
import CertiFriP3.Challenger
import CertiFriP3.DomainSep
import CertiFriP3.Pruned
import CertiFriP3.PrimeField
import CertiFriP3.Quartic
import CertiFriP3.BabyBear
import CertiFriP3.Bn254

/-!
# The Plonky3 instantiation

The primitives that make the generic verifier of `CertiFri` check proofs
produced by Plonky3: the Goldilocks field and its quadratic extension, BLAKE3,
the Merkle hashers, the challenger, Plonky3's pruned Merkle proofs, and the
decoding of proofs.

Two more of Plonky3's fields are here, with the instances the verifier is
written against: the BabyBear field with its quartic extension
(`BabyBear.lean`) and the scalar field of BN254 (`Bn254.lean`). They are built
from the prime field on natural numbers below the order (`PrimeField.lean`) and
from the quartic binomial extension of a field (`Quartic.lean`). These fields
have no hasher and no challenger here: the hashers and the challenger of this
library are those of Goldilocks.

This library is tested against values computed by Plonky3 (`CertiFriTest`). The
one theorem in it, `P3.prunedMmcs_accepts`, says that a pruned Merkle proof is
accepted only through the certified Merkle check. The laws of the fields are
proved in the proofs package, under `Proofs/CertiFriProofs/P3/`; nothing is
proved about BLAKE3, the hashers or the challenger.
-/
