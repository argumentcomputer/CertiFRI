import CertiFriTest.Merkle
import CertiFriTest.Fri
import CertiFriTest.P3.Goldilocks
import CertiFriTest.P3.GoldilocksExt
import CertiFriTest.P3.BabyBear
import CertiFriTest.P3.Bn254
import CertiFriTest.P3.GoldilocksExt3
import CertiFriTest.P3.Blake3
import CertiFriTest.P3.Hashers
import CertiFriTest.P3.Challenger
import CertiFriTest.P3.DomainSep
import CertiFriTest.P3.TensorBatching
import CertiFriTest.P3.Pruned
import CertiFriTest.P3.Fri
import CertiFriTest.Stark.Arith
import CertiFriTest.Stark.MultiStark

/-!
# Tests

Executable checks of the verifier against reference code. They run when the
package is built: a failing `#guard` fails the build.
-/
