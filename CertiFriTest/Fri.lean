import CertiFri.Verifier
import CertiFriTest.Merkle

/-!
# Tests of the FRI verifier on a toy instance

An honest prover, written here as test code, produces opening proofs over the
field with 97 elements, with the toy hasher of `CertiFriTest/Merkle.lean` and a
toy challenger. The tests check that the verifier accepts these proofs and
rejects tampered ones.

The instance is small enough to see through, and independent of the Plonky3
instantiation: the extension field is the base field, a digest is a number, and
the challenger is an arithmetic mixing function. Nothing here is secure, and
nothing is proved about the prover.

The prover works with polynomials in coefficient form. For each level it forms
the reduced opening polynomial of the claims of that level, folds as the
verifier expects (even part plus the challenge times the odd part, plus the
square of the challenge times the next reduced opening), commits to the
codeword of every round with a reference Merkle tree, and sends the last
polynomial in the clear.
-/

namespace CertiFriTest.Fri

open CertiFri CertiFri.Fri CertiFriTest.Merkle

/-! ## The field with 97 elements -/

/-- The modulus. `97 - 1 = 2 ^ 5 * 3`, so the field has a subgroup of order `2 ^ 5`. -/
def modulus : Nat := 97

/-- An element of the field, as its representative below the modulus. -/
structure Fp where
  val : Nat
  deriving DecidableEq, Repr, Inhabited

def Fp.of (n : Nat) : Fp := ⟨n % modulus⟩

def Fp.npow (a : Fp) : Nat → Fp
  | 0 => ⟨1⟩
  | k + 1 => Fp.of (a.val * (Fp.npow a k).val)

instance : FieldOps Fp where
  zero := ⟨0⟩
  one := ⟨1⟩
  add a b := Fp.of (a.val + b.val)
  sub a b := Fp.of (a.val + modulus - b.val)
  mul a b := Fp.of (a.val * b.val)
  neg a := Fp.of (modulus - a.val)
  inv a := Fp.npow a (modulus - 2)
  beq a b := a.val == b.val

/-- `5` generates the multiplicative group, so `5 ^ 3 = 28` has order `2 ^ 5`. -/
instance : TwoAdicOps Fp where
  twoAdicity := 5
  twoAdicGenerator bits := Fp.npow ⟨28⟩ (2 ^ (5 - bits))
  cosetShift := ⟨5⟩

/-- The extension is the field itself. -/
instance : ExtensionOps Fp Fp where
  degree := 1
  embed a := a
  toBasis a := #[a]
  ofBasis coords := coords.getD 0 0

/-! ## Toy primitives -/

/-- The toy hasher on field elements. -/
def hasher : MerkleHasher Fp Nat where
  hashRows xs := toy.hashRows (xs.map (·.val))
  compress := toy.compress

def mix (s x : Nat) : Nat := (s * 1000003 + x + 12345) % 4294967291

/-- A toy challenger: the state is a number, mixed with every absorbed value
and stepped at every squeeze. -/
def chal : Challenger Nat Fp Fp Nat where
  observe s o :=
    match o with
    | .base a => mix s (a.val + 1)
    | .ext e => mix s (e.val + 1000)
    | .digest d => mix s (d + 5000)
  sampleExt s := (Fp.of (mix s 77 / 7), mix s 77)
  sampleBits s bits := (mix s 99 / 11 % 2 ^ bits, mix s 99)

/-! ## Polynomials -/

/-- Coefficients, lowest degree first. -/
abbrev Poly := Array Fp

def Poly.eval (p : Poly) (x : Fp) : Fp := horner p x

def Poly.add (a b : Poly) : Poly :=
  Array.ofFn (n := max a.size b.size) fun i => a.getD i.val 0 + b.getD i.val 0

def Poly.scale (c : Fp) (a : Poly) : Poly := a.map (c * ·)

/-- `(p(X) - p(z)) / (X - z)`, by synthetic division. -/
def Poly.quotient (p : Poly) (z : Fp) : Poly :=
  (p.toList.drop 1).foldr (fun c (acc : List Fp) => (c + z * acc.headD 0) :: acc) [] |>.toArray

/-- `p(s * X)`. -/
def Poly.substScale (p : Poly) (s : Fp) : Poly :=
  Array.ofFn (n := p.size) fun i => p.getD i.val 0 * Fp.npow s i.val

/-- The even part plus `beta` times the odd part. -/
def Poly.fold (p : Poly) (beta : Fp) : Poly :=
  Array.ofFn (n := (p.size + 1) / 2) fun i => p.getD (2 * i.val) 0 + beta * p.getD (2 * i.val + 1) 0

-- (X^2 + 2X + 3 - 11) / (X - 2) = X + 4, since 2^2 + 2*2 + 3 = 11.
#guard (Poly.quotient #[⟨3⟩, ⟨2⟩, ⟨1⟩] ⟨2⟩) == #[⟨4⟩, ⟨1⟩]

/-! ## The prover -/

/-- A matrix to commit to: its columns as polynomials of degree below
`2 ^ logDegree`, and the points to open it at. -/
structure MatrixIn where
  logDegree : Nat
  cols : Array Poly
  points : Array Fp

/-- A statement and a proof for it. -/
structure Instance where
  params : FriParams
  shape : ClaimShape
  commitments : Array Nat
  points : Array Fp
  values : Array Fp
  proof : FriProof Fp Fp Nat (Array (List Nat)) (Array (List Nat))

/-- The first witness that passes the proof-of-work check, or zero. -/
def grind (s : Nat) (bits : Nat) : Fp :=
  ((List.range modulus).find? fun w => (chal.checkWitness s bits ⟨w⟩).1).map Fp.mk |>.getD 0

/-- The honest prover. -/
def prove (params : FriParams) (batches : Array (Array MatrixIn)) : Instance := Id.run do
  let lb := params.logBlowup
  let shape : ClaimShape := batches.toList.map fun b => b.toList.map fun m =>
    ⟨m.logDegree, m.cols.size, m.points.size⟩
  let n := logMaxHeight lb shape
  let rounds := numRounds params shape
  let shift : Fp := TwoAdicOps.cosetShift
  -- The committed codewords of the inputs, on the coset of their level.
  let trees : Array (Array Matrix) := batches.map fun b => b.map fun m =>
    let h := m.logDegree + lb
    { logHeight := h
      rows := Array.ofFn (n := 2 ^ h) fun i =>
        m.cols.map fun f => (f.eval (shift * domainPoint n (n - h) i.val)).val }
  let commitments := trees.map rootOf
  let points : Array Fp := batches.flatMap fun b => b.flatMap fun m => m.points
  let values : Array Fp := batches.flatMap fun b => b.flatMap fun m =>
    m.points.flatMap fun z => m.cols.map fun f => f.eval z
  -- The batching challenge.
  let mut s := chal.observeAll 0 (firstMessage commitments points values)
  let (alpha, s') := chal.sampleExt s
  s := s'
  -- The reduced opening polynomial of each level, as a polynomial in the
  -- point of the unshifted domain.
  let colOf (c : ClaimRef) : Poly :=
    ((batches.getD c.batch #[]).getD c.matrix ⟨0, #[], #[]⟩).cols.getD c.col #[]
  let reduced (j : Nat) : Poly :=
    let sum := (levelClaims lb shape n j).foldl (fun (acc : Poly × Fp) c =>
      (acc.1.add (Poly.scale acc.2 ((colOf c).quotient (points.getD c.pointIdx 0))), acc.2 * alpha))
      (#[], 1)
    sum.1.substScale shift
  -- The commit phase.
  let mut cur := reduced 0
  let mut commits : Array Nat := #[]
  let mut witnesses : Array Fp := #[]
  let mut codewords : Array Poly := #[]
  let mut roundTrees : Array (Array Matrix) := #[]
  for i in List.range rounds do
    let tree : Array Matrix := #[{
      logHeight := n - i - 1
      rows := Array.ofFn (n := 2 ^ (n - i - 1)) fun p =>
        #[(cur.eval (domainPoint n i (2 * p.val))).val,
          (cur.eval (domainPoint n i (2 * p.val + 1))).val] }]
    let commit := rootOf tree
    s := chal.observe s (.digest commit)
    let witness := grind s params.commitPowBits
    let (_, s') := chal.checkWitness s params.commitPowBits witness
    let (beta, s'') := chal.sampleExt s'
    s := s''
    commits := commits.push commit
    witnesses := witnesses.push witness
    codewords := codewords.push cur
    roundTrees := roundTrees.push tree
    cur := (cur.fold beta).add (Poly.scale (beta * beta) (reduced (i + 1)))
  -- The final polynomial, padded to its length.
  let finalPoly : Poly := Array.ofFn (n := params.finalPolyLen) fun i => cur.getD i.val 0
  s := chal.observeAll s (finalMessage rounds finalPoly)
  let queryWitness := grind s params.queryPowBits
  let (_, s') := chal.checkWitness s params.queryPowBits queryWitness
  s := s'
  let indices := (chal.sampleIndices n params.numQueries s).toArray
  -- The openings.
  let inputOpenings := trees.map fun tree =>
    let reducedIndex (index : Nat) := index >>> (n - topOf tree)
    { openedValues := indices.map fun index =>
        (rowsAt tree (reducedIndex index)).map (·.map Fp.mk)
      openingProof := indices.map fun index => pathAt tree (reducedIndex index)
      : BatchOpening Fp (Array (List Nat)) }
  let commitPhaseOpenings := (Array.range rounds).map fun i =>
    let codeword := codewords.getD i #[]
    let tree := roundTrees.getD i #[]
    { logArity := 1
      siblingValues := indices.map fun index =>
        #[codeword.eval (domainPoint n i ((index >>> i) ^^^ 1))]
      openingProof := indices.map fun index => pathAt tree (index >>> (i + 1))
      : CommitPhaseStep Fp (Array (List Nat)) }
  return {
    params, shape, commitments, points, values
    proof := {
      commitPhaseCommits := commits
      commitPowWitnesses := witnesses
      inputOpenings
      commitPhaseOpenings
      finalPoly
      queryPowWitness := queryWitness } }

/-- Run the verifier on an instance. -/
def accepts (inst : Instance) : Bool :=
  verify (merkleMmcs hasher) (merkleMmcs hasher) chal 0 inst.params inst.shape inst.commitments
    inst.points inst.values inst.proof

/-! ## Instances -/

/-- The polynomial with coefficients `seed + 3 * i + i ^ 2`, of `2 ^ logDegree` coefficients. -/
def poly (seed logDegree : Nat) : Poly :=
  Array.ofFn (n := 2 ^ logDegree) fun i => Fp.of (seed + 3 * i.val + i.val * i.val)

/-- Two batches with matrices of three heights; one matrix is opened at two points. -/
def mixed : Instance :=
  prove { logBlowup := 1, logFinalPolyLen := 0, maxLogArity := 1, numQueries := 4,
          commitPowBits := 0, queryPowBits := 0 }
    #[#[⟨3, #[poly 1 3, poly 2 3], #[⟨40⟩, ⟨41⟩]⟩, ⟨1, #[poly 3 1, poly 4 1, poly 5 1], #[⟨42⟩]⟩],
      #[⟨2, #[poly 6 2], #[⟨43⟩]⟩, ⟨3, #[poly 7 3], #[⟨44⟩]⟩]]

/-- A final polynomial with two coefficients, and proof of work in both phases. -/
def withPow : Instance :=
  prove { logBlowup := 1, logFinalPolyLen := 1, maxLogArity := 1, numQueries := 3,
          commitPowBits := 2, queryPowBits := 3 }
    #[#[⟨3, #[poly 8 3], #[⟨50⟩]⟩, ⟨2, #[poly 9 2, poly 10 2], #[⟨51⟩]⟩]]

/-- A constant column next to a taller matrix: the reduced opening at the
height of the blowup is zero. -/
def withConstant : Instance :=
  prove { logBlowup := 2, logFinalPolyLen := 0, maxLogArity := 1, numQueries := 3,
          commitPowBits := 0, queryPowBits := 0 }
    #[#[⟨2, #[poly 11 2], #[⟨60⟩]⟩, ⟨0, #[poly 12 0], #[⟨61⟩]⟩]]

/-! ## Honest proofs are accepted -/

#guard accepts mixed
#guard accepts withPow
#guard accepts withConstant

-- The instances have the intended sizes.
#guard numRounds mixed.params mixed.shape == 3
#guard mixed.values.size == 2 * 2 + 3 + 1 + 1
#guard numRounds withPow.params withPow.shape == 2
#guard withPow.proof.finalPoly.size == 2

/-! ## Tampered instances are rejected -/

def bump (xs : Array Fp) (i : Nat) : Array Fp := xs.modify i (· + 1)

-- Any changed claimed value.
#guard (List.range mixed.values.size).all fun i =>
  !accepts { mixed with values := bump mixed.values i }

-- Any changed opening point.
#guard (List.range mixed.points.size).all fun i =>
  !accepts { mixed with points := bump mixed.points i }

-- A changed commitment.
#guard !accepts { mixed with commitments := mixed.commitments.modify 0 (· + 1) }

-- A changed coefficient of the final polynomial.
#guard !accepts { mixed with proof := { mixed.proof with finalPoly := bump mixed.proof.finalPoly 0 } }
#guard !accepts { withPow with
  proof := { withPow.proof with finalPoly := bump withPow.proof.finalPoly 1 } }

-- A changed commitment of a folding round.
#guard !accepts { mixed with
  proof := { mixed.proof with commitPhaseCommits := mixed.proof.commitPhaseCommits.modify 1 (· + 1) } }

/-- Change the sibling value of the first query in round `i`. -/
def bumpSibling (inst : Instance) (i : Nat) : Instance :=
  let openings := inst.proof.commitPhaseOpenings.modify i (fun o =>
    { o with siblingValues := o.siblingValues.modify 0 (fun v => bump v 0) })
  { inst with proof := { inst.proof with commitPhaseOpenings := openings } }

/-- Change the first opened entry of the first query in input batch `b`. -/
def bumpOpened (inst : Instance) (b : Nat) : Instance :=
  let openings := inst.proof.inputOpenings.modify b (fun o =>
    { o with openedValues := o.openedValues.modify 0 (fun rows => rows.modify 0 (fun row => bump row 0)) })
  { inst with proof := { inst.proof with inputOpenings := openings } }

/-- State another arity for round `i`. -/
def setArity (inst : Instance) (i arity : Nat) : Instance :=
  let openings := inst.proof.commitPhaseOpenings.modify i (fun o => { o with logArity := arity })
  { inst with proof := { inst.proof with commitPhaseOpenings := openings } }

-- A changed sibling value, in any round.
#guard (List.range 3).all fun i => !accepts (bumpSibling mixed i)

-- A changed opened entry of an input matrix.
#guard !accepts (bumpOpened mixed 0)
#guard !accepts (bumpOpened mixed 1)

-- A round of another arity.
#guard !accepts (setArity mixed 0 2)

-- A missing folding round.
#guard !accepts { mixed with proof := { mixed.proof with
  commitPhaseCommits := mixed.proof.commitPhaseCommits.pop } }

-- A wrong proof-of-work witness. The check has three bits, so most witnesses fail.
#guard ((List.range modulus).filter fun w =>
  accepts { withPow with proof := { withPow.proof with queryPowWitness := ⟨w⟩ } }).length < 40

-- Another shape for the same data.
#guard !accepts { mixed with shape := mixed.shape.map fun b => b.map fun m =>
  { m with logDegree := m.logDegree + 1 } }

-- More queries than the proof answers.
#guard !accepts { mixed with params := { mixed.params with numQueries := 5 } }

end CertiFriTest.Fri
