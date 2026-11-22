import CertiFri.Verifier
import CertiFriP3.DomainSep

/-!
# Tests of the Goldilocks cubic trinomial extension `GoldilocksExt3`

Checks of `CertiFriP3/GoldilocksExt3.lean`, `ext3Hasher`, `challenger3`,
`ext3HasherSep`, and `challenger3Sep`:

* The modulus relation `X^3 = X + 1`, `X^4 = X^2 + X`, and `X^p ≠ X`.
* Karatsuba multiplication vs naive schoolbook multiplication modulo
  `X^3 - X - 1`.
* Exact adjugate/norm inverse: `inv? 0 = none`, `inv 0 = 0`, `a * a⁻¹ = 1`,
  and Frobenius `a ^ (p^3 - 1) = 1` for nonzero elements.
* Canonical serialization (`pushBytes`, `ofCanonical?`, `ofBytesAt?`) failing
  closed on `≥ p` or truncated buffers.
* `ext3Hasher` block streaming vs `Blake3.hash ∘ ext3RowBytes`.
* End-to-end `Fri.verify` over `Goldilocks` / `GoldilocksExt3` with both stock
  and domain-separated BLAKE3 hashers and challengers (honest acceptance and
  tamper rejection).
-/

namespace CertiFriTest.P3.GoldilocksExt3

open CertiFri CertiFri.P3 CertiFri.Fri

abbrev E3 := UInt64 × UInt64 × UInt64

def g (w : UInt64) : Goldilocks := Goldilocks.ofUInt64 w
def e3 (c : E3) : GoldilocksExt3 := ⟨g c.1, g c.2.1, g c.2.2⟩
def coords (a : GoldilocksExt3) : E3 := (a.c0.val, a.c1.val, a.c2.val)

def X : GoldilocksExt3 := e3 (0, 1, 0)
def X2 : GoldilocksExt3 := e3 (0, 0, 1)

/-- Reference schoolbook multiplication modulo `X^3 - X - 1`. -/
def schoolbookMul (a b : GoldilocksExt3) : GoldilocksExt3 :=
  let t0 := a.c0 * b.c0
  let t1 := a.c0 * b.c1 + a.c1 * b.c0
  let t2 := a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0
  let t3 := a.c1 * b.c2 + a.c2 * b.c1
  let t4 := a.c2 * b.c2
  ⟨t0 + t3, t1 + t3 + t4, t2 + t4⟩

/-! ## Modulus, embedding, and basis -/

#guard ExtensionOps.degree Goldilocks GoldilocksExt3 = 3
#guard coords (0 : GoldilocksExt3) = (0, 0, 0)
#guard coords (1 : GoldilocksExt3) = (1, 0, 0)
#guard coords (ExtensionOps.embed (g 5)) = (5, 0, 0)
#guard X * X == X2
#guard X * X * X == X + 1
#guard X2 * X2 == X2 + X
#guard fieldPow X Goldilocks.order != X
#guard ExtensionOps.toBasis (F := Goldilocks) (e3 (10, 20, 30)) == #[g 10, g 20, g 30]
#guard ExtensionOps.ofBasis (EF := GoldilocksExt3) #[g 10, g 20, g 30] == e3 (10, 20, 30)
#guard ExtensionOps.ofBasis (EF := GoldilocksExt3) #[g 10] == e3 (10, 0, 0)
#guard ExtensionOps.ofBasis (EF := GoldilocksExt3) #[g 10, g 20, g 30, g 40] == e3 (10, 20, 30)
#guard GoldilocksExt3.inv? 0 == none
#guard (0 : GoldilocksExt3)⁻¹ == 0

/-! ## Field laws, Karatsuba equivalence, and Frobenius -/

def samples : Array GoldilocksExt3 := #[
  0, 1, X, X2, e3 (1, 1, 1),
  e3 (0xFFFFFFFF00000000, 0xFFFFFFFF00000000, 0xFFFFFFFF00000000),
  e3 (0x100000000, 0xFFFFFFFF, 7),
  e3 (0x0123456789ABCDEF, 0xFEDCBA9876543210, 0x13579BDF2468ACE0),
  e3 (0x8000000000000000, 0x7FFFFFFFFFFFFFFF, 0xDEADBEEFCAFEBABE)]

#guard samples.all fun a => samples.all fun b =>
  a * b == schoolbookMul a b && a + b == b + a && a * b == b * a &&
    a - b == a + -b && a - b + b == a

#guard samples.all fun a => samples.all fun b => samples.all fun c =>
  a * (b + c) == a * b + a * c && a * (b * c) == a * b * c

#guard samples.all fun a =>
  if a == 0 then
    GoldilocksExt3.inv? a == none && a⁻¹ == 0
  else
    match GoldilocksExt3.inv? a with
    | some invA => invA == a⁻¹ && a * invA == 1 && invA⁻¹ == a
    | none => false

-- Norm is multiplicative: N(a * b) = N(a) * N(b).
#guard samples.all fun a => samples.all fun b =>
  GoldilocksExt3.norm (a * b) == GoldilocksExt3.norm a * GoldilocksExt3.norm b

-- Multiplicative group has order `p^3 - 1`, and `a^(p^3) = a`.
#guard samples.all fun a =>
  a == 0 || fieldPow a (Goldilocks.order ^ 3 - 1) == 1

/-! ## Canonical serialization -/

#guard samples.all fun a =>
  let bs := a.pushBytes ByteArray.empty
  bs.size == 24 && GoldilocksExt3.ofBytesAt? bs 0 == some a

#guard GoldilocksExt3.ofCanonical? 0xFFFFFFFF00000001 0 0 == none
#guard GoldilocksExt3.ofCanonical? 0 0xFFFFFFFF00000001 0 == none
#guard GoldilocksExt3.ofCanonical? 0 0 0xFFFFFFFF00000001 == none
#guard GoldilocksExt3.ofBytesAt? (ByteArray.mk (Array.replicate 23 0)) 0 == none

/-! ## Hasher block streaming vs byte serialization -/

def ext3Row (seed : UInt64) (n : Nat) : Array GoldilocksExt3 :=
  Array.ofFn (n := n) fun i =>
    let k := i.val.toUInt64
    e3 ((seed + 3 * k + 1) * 0x9E3779B97F4A7C15,
        (seed + 3 * k + 2) * 0x9E3779B97F4A7C15,
        (seed + 3 * k + 3) * 0x9E3779B97F4A7C15)

#guard (List.range 20 ++ [42, 43, 85, 86, 128, 129]).all fun n =>
  let row := ext3Row 17 n
  ext3Hasher.hashRows row == Blake3.hash (Hashers.ext3RowBytes row)

-- Domain-separated `ext3HasherSep` differs from plain `ext3Hasher`.
#guard ext3HasherSep.hashRows (ext3Row 17 3) != ext3Hasher.hashRows (ext3Row 17 3)

/-! ## End-to-end `Fri.verify` over `Goldilocks` / `GoldilocksExt3` -/

private structure Tree3 (T : Type) where
  logHeight : Nat
  rows : Array (Array T)

private def buildLevels {T : Type} (H : MerkleHasher T Digest) (t : Tree3 T) :
    Array (Array Digest) := Id.run do
  let mut cur : Array Digest := t.rows.map H.hashRows
  let mut levels : Array (Array Digest) := #[cur]
  for _ in List.range t.logHeight do
    let next := Array.ofFn (n := cur.size / 2) fun i =>
      H.compress (cur.getD (2 * i.val) default) (cur.getD (2 * i.val + 1) default)
    levels := levels.push next
    cur := next
  return levels

private def treeRoot (levels : Array (Array Digest)) : Digest :=
  (levels.getD (levels.size - 1) #[]).getD 0 default

private def treePath (levels : Array (Array Digest)) (logHeight index : Nat) : List Digest :=
  (List.range logHeight).map fun lvl =>
    (levels.getD lvl #[]).getD ((index >>> lvl) ^^^ 1) default

private abbrev Poly3 := Array GoldilocksExt3

private def polyAdd (a b : Poly3) : Poly3 :=
  Array.ofFn (n := max a.size b.size) fun i => a.getD i.val 0 + b.getD i.val 0

private def polyScale (c : GoldilocksExt3) (a : Poly3) : Poly3 :=
  a.map (c * ·)

private def polyQuotient (p : Poly3) (z : GoldilocksExt3) : Poly3 :=
  ((p.toList.drop 1).foldr (fun c (acc : List GoldilocksExt3) =>
    (c + z * acc.headD 0) :: acc) []).toArray

private def polySubstScale (p : Poly3) (s : GoldilocksExt3) : Poly3 :=
  Array.ofFn (n := p.size) fun i => p.getD i.val 0 * fieldPow s i.val

private def polyFold (p : Poly3) (beta : GoldilocksExt3) : Poly3 :=
  Array.ofFn (n := (p.size + 1) / 2) fun i =>
    p.getD (2 * i.val) 0 + beta * p.getD (2 * i.val + 1) 0

private structure FriInst3 where
  params : FriParams
  shape : ClaimShape
  commitments : Array Digest
  points : Array GoldilocksExt3
  values : Array GoldilocksExt3
  proof : FriProof Goldilocks GoldilocksExt3 Digest (Array (List Digest)) (Array (List Digest))

private def proveSingleBatch3
    (baseH : MerkleHasher Goldilocks Digest)
    (extH : MerkleHasher GoldilocksExt3 Digest)
    (chal : Challenger ChallengerState Goldilocks GoldilocksExt3 Digest)
    (params : FriParams) (logDeg : Nat) (cols : Array (Array Goldilocks))
    (pts : Array GoldilocksExt3) : FriInst3 := Id.run do
  let lb := params.logBlowup
  let shape : ClaimShape := [[⟨logDeg, cols.size, pts.size⟩]]
  let n := logMaxHeight lb shape
  let rounds := numRounds params shape
  let shiftB : Goldilocks := TwoAdicOps.cosetShift
  let shiftE : GoldilocksExt3 := ExtensionOps.embed shiftB
  let h := logDeg + lb
  let inputTree : Tree3 Goldilocks := {
    logHeight := h
    rows := Array.ofFn (n := 2 ^ h) fun i =>
      cols.map fun f => horner f (shiftB * domainPoint n (n - h) i.val) }
  let inputLevels := buildLevels baseH inputTree
  let commitments := #[treeRoot inputLevels]
  let extCols : Array Poly3 := cols.map (·.map ExtensionOps.embed)
  let values : Array GoldilocksExt3 :=
    pts.flatMap fun z => extCols.map fun f => horner f z
  let mut s := chal.observeAll (ChallengerState.new ByteArray.empty)
    (firstMessage commitments pts values)
  let (alpha, s') := chal.sampleExt s
  s := s'
  let reduced0 : Poly3 :=
    let sum := (levelClaims lb shape n 0).foldl (fun (acc : Poly3 × GoldilocksExt3) c =>
      let f := extCols.getD c.col #[]
      let z := pts.getD c.pointIdx 0
      (polyAdd acc.1 (polyScale acc.2 (polyQuotient f z)), acc.2 * alpha)) (#[], 1)
    polySubstScale sum.1 shiftE
  let mut cur := reduced0
  let mut commits : Array Digest := #[]
  let mut witnesses : Array Goldilocks := #[]
  let mut codewords : Array Poly3 := #[]
  let mut roundLevels : Array (Array (Array Digest)) := #[]
  for i in List.range rounds do
    let tree : Tree3 GoldilocksExt3 := {
      logHeight := n - i - 1
      rows := Array.ofFn (n := 2 ^ (n - i - 1)) fun p =>
        #[horner cur (ExtensionOps.embed (domainPoint (F := Goldilocks) n i (2 * p.val))),
          horner cur (ExtensionOps.embed (domainPoint (F := Goldilocks) n i (2 * p.val + 1)))] }
    let lvls := buildLevels extH tree
    let commit := treeRoot lvls
    s := chal.observe s (.digest commit)
    let (_, s') := chal.checkWitness s params.commitPowBits 0
    let (beta, s'') := chal.sampleExt s'
    s := s''
    commits := commits.push commit
    witnesses := witnesses.push 0
    codewords := codewords.push cur
    roundLevels := roundLevels.push lvls
    cur := polyFold cur beta
  let finalPoly : Poly3 := Array.ofFn (n := params.finalPolyLen) fun i => cur.getD i.val 0
  s := chal.observeAll s (finalMessage rounds finalPoly)
  let (_, s') := chal.checkWitness s params.queryPowBits 0
  s := s'
  let indices := (chal.sampleIndices n params.numQueries s).toArray
  let inputOpenings : Array (BatchOpening Goldilocks (Array (List Digest))) := #[{
    openedValues := indices.map fun idx => #[inputTree.rows.getD idx #[]]
    openingProof := indices.map fun idx => treePath inputLevels h idx }]
  let commitPhaseOpenings := (Array.range rounds).map fun i =>
    let cw := codewords.getD i #[]
    let lvls := roundLevels.getD i #[]
    { logArity := 1
      siblingValues := indices.map fun idx =>
        #[horner cw (ExtensionOps.embed (domainPoint (F := Goldilocks) n i ((idx >>> i) ^^^ 1)))]
      openingProof := indices.map fun idx => treePath lvls (n - i - 1) (idx >>> (i + 1))
      : CommitPhaseStep GoldilocksExt3 (Array (List Digest)) }
  return {
    params, shape, commitments, points := pts, values
    proof := {
      commitPhaseCommits := commits
      commitPowWitnesses := witnesses
      inputOpenings
      commitPhaseOpenings
      finalPoly
      queryPowWitness := 0 } }

private def verifyInst3
    (baseH : MerkleHasher Goldilocks Digest)
    (extH : MerkleHasher GoldilocksExt3 Digest)
    (chal : Challenger ChallengerState Goldilocks GoldilocksExt3 Digest)
    (inst : FriInst3) : Bool :=
  verify (merkleMmcs baseH) (merkleMmcs extH) chal (ChallengerState.new ByteArray.empty)
    inst.params inst.shape inst.commitments inst.points inst.values inst.proof

def testParams3 : FriParams :=
  { logBlowup := 2, logFinalPolyLen := 1, maxLogArity := 1, numQueries := 4,
    commitPowBits := 0, queryPowBits := 0 }

def testCols3 : Array (Array Goldilocks) :=
  #[#[g 3, g 11, g 29, g 47, g 5, g 13, g 31, g 53],
    #[g 7, g 19, g 37, g 61, g 2, g 17, g 41, g 71]]

def testPts3 : Array GoldilocksExt3 :=
  #[e3 (12345, 67890, 54321), e3 (999999, 111111, 222222)]

def instPlain3 : FriInst3 :=
  proveSingleBatch3 baseHasher ext3Hasher challenger3 testParams3 3 testCols3 testPts3

def instSep3 : FriInst3 :=
  proveSingleBatch3 baseHasherSep ext3HasherSep challenger3Sep testParams3 3 testCols3 testPts3

-- Honest `GoldilocksExt3` FRI proofs pass verification (both plain and domain-separated).
#guard verifyInst3 baseHasher ext3Hasher challenger3 instPlain3
#guard verifyInst3 baseHasherSep ext3HasherSep challenger3Sep instSep3

-- Cross-domain verification rejects (plain proof under domain-separated verifier and vice versa).
#guard !verifyInst3 baseHasherSep ext3HasherSep challenger3Sep instPlain3
#guard !verifyInst3 baseHasher ext3Hasher challenger3 instSep3

-- Tampering with a claimed value or final polynomial is rejected.
#guard !verifyInst3 baseHasherSep ext3HasherSep challenger3Sep
  { instSep3 with values := instSep3.values.set! 0 (instSep3.values.getD 0 0 + 1) }
#guard !verifyInst3 baseHasherSep ext3HasherSep challenger3Sep
  { instSep3 with proof := { instSep3.proof with
      finalPoly := instSep3.proof.finalPoly.set! 0 (instSep3.proof.finalPoly.getD 0 0 + 1) } }

end CertiFriTest.P3.GoldilocksExt3
